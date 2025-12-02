#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <termios.h>
#include <string.h>
#include <errno.h>
#include <pthread.h>
#include <math.h> 
#include <time.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <stdbool.h>
#include <sys/statvfs.h>
#include <sys/time.h>
#include "dirspec.h"  // 确保包含 private.h
#include "polyfit.h"
#include <dirent.h>
//修改的11.27-3round的数据，增加电压检测模块
//增加设备号读取函数，以及修改tf卡日志无法存入问题//位移计算区还是最原始的全部都计算的这个
//修改自11.22-6ul-feiling
//打包发送出现
//降采样位移输出不行，显示串口打不开，并且半小时的时间统计还是按照之前的没有进行秒数的统计
//进行6ull移植，挂载点为/mnt/tf.配置文件所在位置是在home下新建/data/config.txt文件
//加权平均又加上了 0.05 ！= -1、
//之前7.15未修改数据拟合的部分，吧重叠区加到了1024但是出现了有干扰现象，这里在进行去趋势去掉highpass
//9.9-bd-receive跑通后。修改了应答时间增加到了70秒。另外查看文文件夹出现切换文件出现数据没有存入的情况，解决丢失的2048个数据的问题
//上电管理控制，修改了send_and_verify_data函数以及send_spectrum_data函数,提前上电以及40秒延迟下电
//修改了GPS线程自行决定上电下电时间，前5分钟上电后5分钟下电
#define FRAME_START_BYTE 0x55  
#define ACC_FRAME_ID 0x51
#define ANGLE_FRAME_ID 0x53
#define FRAME_LENGTH 11    
#define BUFFER_SIZE 10000
#define PI 3.14159265358979323846  
#define G 9.80665f  // 重力加速度  
#define FILTER_WINDOW 5  // 中值滤波窗口大小  
#define FILTER_BUFFER_SIZE 1000  // 滤波缓冲区大小
#define TRUE 1 
#define SAMPLE_RATE 50    // 采样率（Hz）
#define N 1024        // FFT点数  
#define N_ 4          // N*N_ = 2048  
#define T 0.02f       // 采样周期  

#define OVERLAP_SIZE 2048
#define DATA_SIZE 4096
#define EFFECTIVE_SIZE (DATA_SIZE - OVERLAP_SIZE)  // 2048
#define fps 0.05
#define MAX_WAVES 10000    // 最大波数
#define MAX_HALF_HOUR_WAVES 10000 
#define JY901_SERIAL_PORT  "/dev/ttymxc2"
#define BD_OUTPUT_SERIAL_PORT "/dev/ttymxc1"
#define LOCATION_SERIAL_PORT  "/dev/ttymxc3"
#define LOCATION_4G_SERIAL_PORT  "/dev/ttymxc4"
#define DOWNDISP_SERIAL_PORT  "/dev/ttymxc6"
#define ADC_485SERIAL_PORT  "/dev/ttymxc7"
//比较9.6-6ull-rmc.c新增北斗重发策略
// 北斗配置文件路径
#define BD_CONFIG_FILE "/home/data/config-bd.txt"
// 默认设备号 (377)
#define DEFAULT_BD_ID 377
#define BD_RESEND_PATH  "/home/data/bd_resend"
//增加GPIO控制
#define GPIO1_DW "135"
#define GPIO2_4G "119"
#define GPIO4_BD "120"
#define GPIO_JY901 "115"
#define GPIO_232_CRTL "23"
#define GPIO_232_1_CRTL "26"
#define GPIO_232_2_CRTL "136"
#define GPIO_485_CRTL "22"
#define GPIO_485_CRTL_1 "27"
#define GPIO_485_CRTL_2 "137"
#define JM_CRTL "130"
#define PHY_CRTL "117"
#define QJY_CRTL "115"
#define GPIO_VCC_CRTL_3 "124"
#define GPIO_VCC_CRTL_2 "123"
#define GPIO_VCC_CRTL_1 "122"
#define GPIO_VCC_CRTL_6 "121"
#define GPIO_VCC_CRTL_5 "120"
#define GPIO_VCC_CRTL_4 "119"
#define TX_RING_BUFFER_SIZE  2048

//降采样需要FIFO结构
typedef struct {
    float data[TX_RING_BUFFER_SIZE];
    volatile int head; // next write index
    volatile int tail; // next read index
    volatile int count; // current stored points
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    bool running;
    } TxRingBuffer;
    
    
    static TxRingBuffer g_tx_queue;
    
    
    // Initialize the TX queue (call once in main before threads start)
    void init_tx_queue()
    {
    memset(&g_tx_queue, 0, sizeof(g_tx_queue));
    g_tx_queue.head = 0;
    g_tx_queue.tail = 0;
    g_tx_queue.count = 0;
    g_tx_queue.running = true;
    pthread_mutex_init(&g_tx_queue.mutex, NULL);
    pthread_cond_init(&g_tx_queue.cond, NULL);
    }

typedef struct {
   char message[1024];//存储完整待发送报文
}BeidouMessage;

// 使用一个简单的环形队列来缓存待发送的消息
#define BD_QUEUE_SIZE 10
static BeidouMessage bd_message_queue[BD_QUEUE_SIZE];
static int bd_queue_write_idx = 0;
static int bd_queue_read_idx = 0;
static int bd_queue_count = 0;
// 新增的全局变量，用于启动时的时间校准同步
static bool initial_time_calibrated = false;
static pthread_mutex_t time_calib_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t time_calib_cond = PTHREAD_COND_INITIALIZER;
// 用于线程同步的互斥锁和条件变量
static pthread_mutex_t bd_queue_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t bd_queue_cond = PTHREAD_COND_INITIALIZER;
//用于RMC解析的时间在GPS线程单独取出作为全局变量来在波i特征统计的时间里进行秒数据的获取来进行时间校准
static time_t last_utc_time_seconds = 0;  // 新增：存储最新UTC时间戳
static bool utc_time_valid = false;       // 新增：标记时间戳是否有效
static pthread_mutex_t utc_time_mutex = PTHREAD_MUTEX_INITIALIZER;  // 新增：互斥锁
static bool gps_powered_on = false;  // 位移计算线程通知GPS线程上电时间的确定
//新增电源控制
pthread_mutex_t gps_power_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t gps_power_cond = PTHREAD_COND_INITIALIZER;
volatile bool gps_thread_running  = true;  // 用于控制GPS线程退出
// 全局变量，用于双向串口通信
// 控制指定GPIO的指定属性
int gpio_ctrl(char *gpio_num, char *attr, char *value) {
    char file_path[100];
    snprintf(file_path, sizeof(file_path), "/sys/class/gpio/gpio%s/%s", gpio_num, attr);
    
    int fd = open(file_path, O_WRONLY);
    if (fd < 0) {
        printf("open %s error\n", file_path);
        char check_path[100];
        snprintf(check_path, sizeof(check_path), "/sys/class/gpio/gpio%s", gpio_num);
        if (access(check_path, F_OK) != 0) {
            printf("GPIO %s 未导出，请先调用 gpio_export()\n", gpio_num);
        }
        return -1;
    }
    
    int len = strlen(value);
    int ret = write(fd, value, len);
    if (ret < 0) {
        printf("write %s error\n", file_path);
        close(fd);
        return -2;
    }
    
    close(fd);
    return 0;
}
int gpio_export(char *argv)
{
   int GPIO_fd = open("/sys/class/gpio/export", O_WRONLY);
    if(GPIO_fd < 0){
        printf("open /sys/class/gpio/export error\n");
        return -1;
    }
    
   int len = strlen(argv);
    int ret = write(GPIO_fd, argv, len);
    if(ret < 0){
        printf("write /sys/class/gpio/export error\n");
        close(GPIO_fd);
        return -2;
    }
    
    close(GPIO_fd);
    return 0;
}
int gpio_unexport(char *argv)
{
   int GPIO_fd = open("/sys/class/gpio/unexport", O_WRONLY);
    if(GPIO_fd < 0){
        printf("open /sys/class/gpio/unexport error\n");
        return -1;
    }
    
   int len = strlen(argv);
    int ret = write(GPIO_fd, argv, len);
    if(ret < 0){
        printf("write /sys/class/gpio/unexport error\n");
        close(GPIO_fd);
        return -2;
    }
    
    close(GPIO_fd);
    return 0;
}

void gpio_init(){

    int reg1 =gpio_export(GPIO1_DW);
    if(reg1 < 0){
        printf("将GPIO1导入用户空间失败\n");
    }
    int reg5 =gpio_export(GPIO_JY901);
    if(reg5 < 0){
        printf("将GPIO_JY901导入用户空间失败\n");
    }
    int reg6 =gpio_export(GPIO_232_2_CRTL);
    if(reg6 < 0){
        printf("将GPIO_232_2_CRTL 导入用户空间失败\n");
    } 
    int reg7 =gpio_export(GPIO_232_CRTL);
    if(reg7 < 0){
        printf("将GPIO_232_CRTL 导入用户空间失败\n");
    }  
    int reg8 =gpio_export(GPIO_485_CRTL_2);
    if(reg8 < 0){
        printf("GPIO_485_CRTL_2 导入用户空间失败\n");
    } 
    int reg9 =gpio_export(PHY_CRTL);
    if(reg9< 0){
        printf("PHY_CRTL 导入用户空间失败\n");
    } 
    int reg10 =gpio_export(GPIO_485_CRTL_1);
    if(reg10 < 0){
        printf("GPIO_485_CRTL_1 导入用户空间失败\n");
    } 
    usleep(100000);
    gpio_ctrl(GPIO1_DW,"direction","out");

    gpio_ctrl(GPIO_JY901,"direction","out");
    gpio_ctrl(GPIO_232_2_CRTL,"direction","out");
    gpio_ctrl(GPIO_232_CRTL,"direction","out");
    gpio_ctrl(GPIO_485_CRTL_2,"direction","out");
    gpio_ctrl(GPIO_485_CRTL_1,"direction","out");
    gpio_ctrl(PHY_CRTL,"direction","out");

    gpio_ctrl(PHY_CRTL,"value","0");
    gpio_ctrl(GPIO_485_CRTL_1,"value","1");
 
    gpio_ctrl(GPIO_485_CRTL_2,"value","1");
    gpio_ctrl(GPIO_232_CRTL,"value","0");
    gpio_ctrl(GPIO_232_2_CRTL,"value","0");
    gpio_ctrl(GPIO_JY901,"value","1");
    gpio_ctrl(GPIO1_DW,"value","0");

}
// ==================== 新增：补发文件管理函数 ====================
// 获取北斗设备号的辅助函数
uint16_t get_beidou_device_id() {
    // 1. 尝试打开文件
    FILE *fp = fopen(BD_CONFIG_FILE, "r");
    if (!fp) {
        printf("[北斗] 配置文件未找到(%s)，使用默认设备号: %d\n", BD_CONFIG_FILE, DEFAULT_BD_ID);
        return DEFAULT_BD_ID;
    }

    char line[128];
    uint16_t device_id = DEFAULT_BD_ID;
    bool found = false;

    // 2. 读取一行
    if (fgets(line, sizeof(line), fp)) {
        // 去除可能的换行符，防止打印乱码
        size_t len = strlen(line);
        if (len > 0 && line[len-1] == '\n') line[len-1] = '\0';

        // --- 解析逻辑 ---
        // 情况 A: 格式为 "DeviceID=377"
        char *ptr = strstr(line, "DeviceID=");
        if (ptr) {
            // 指针移到等号后面
            device_id = (uint16_t)atoi(ptr + 9); 
            if (device_id > 0) found = true;
        } 
        // 情况 B: 格式为纯数字 "377"
        else {
            device_id = (uint16_t)atoi(line);
            if (device_id > 0) found = true;
        }
    }

    // 3. 关闭文件 (千万别忘，否则泄露句柄会导致程序后续卡死)
    fclose(fp);

    // 4. 输出结果
    if (found) {
        printf("[北斗] 读取配置成功，设备号: %d\n", device_id);
    } else {
        printf("[北斗] 配置解析失败(内容: %s)，使用默认设备号: %d\n", line, DEFAULT_BD_ID);
        device_id = DEFAULT_BD_ID;
    }

    return device_id;
}

// // 确保补发目录存在
void ensure_resend_directory_exists() {
    struct stat st = {0};
    if (stat(BD_RESEND_PATH, &st) == -1) {
        mkdir(BD_RESEND_PATH, 0755);
    }  
}

// 将发送失败的消息保存到补发文件
void save_message_for_resend(const char* message) {
    ensure_resend_directory_exists();
    char filepath[512];
    // 使用时间戳作为文件名，确保唯一性
    snprintf(filepath, sizeof(filepath), "%s%ld.txt", BD_RESEND_PATH, time(NULL));
    
    FILE* fp = fopen(filepath, "w");
    if (fp) {
        fprintf(fp, "%s", message);
        fclose(fp);
        printf("北斗消息已保存待补发: %s\n", filepath);
    } else {
        perror("保存补发文件失败");
    }
}


// 处理时间日志全局变量
static FILE *processing_log_file = NULL;
static pthread_mutex_t processing_log_mutex = PTHREAD_MUTEX_INITIALIZER;
static const char *PROCESSING_LOG_PATH = "/home/data/processing_time_log.txt";

typedef struct {
    int hour , minute ,seconds;
    int day , month , year ;
    double longitude , latitude;
    float speed ,course;
    int valid ;
}GPS_Data;


static int gps_fd =-1; //定位模块句柄
static int BD_output_fd =-1; 
static int downdisp_output_fd =-1; 
static int rs485_fd =-1; 

// 定义互斥锁和条件变量
char current_file_path[512] = {0}; 
pthread_mutex_t file_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t file_ready_cond = PTHREAD_COND_INITIALIZER;
int file_ready = 0;  // 文件就绪标志

// 全局GPS数据和互斥锁
static GPS_Data global_gps_data = {0};
static pthread_mutex_t gps_data_mutex = PTHREAD_MUTEX_INITIALIZER;
static time_t last_calibration = 0;
// 在文件开头添加函数声明
void get_current_folder_path(char* folder_path, size_t size);
void init_spectral_matrix(SpectralMatrix* SMout, EstimationParams* EP);

// 定义互斥锁
pthread_mutex_t path_mutex = PTHREAD_MUTEX_INITIALIZER;  // 初始化互斥锁

bool check_mount_point(const char* path); 
const char* get_direction_description(float direction); 
typedef struct {
    float ax, ay, az;
    float roll, pitch, yaw;
     float ax_filtered, ay_filtered, az_filtered;  // 滤波后的加速度  
    float ax_ned, ay_ned, az_ned;  // 转换到东北天坐标系的加速度
} SensorData; //定义结构体存储三周角度和加速度


// 1. 添加帧组结构体
typedef struct {
    uint8_t acc_frame[FRAME_LENGTH];    // 0x51 加速度帧
    uint8_t gyro_frame[FRAME_LENGTH];   // 0x52 角速度帧 
    uint8_t angle_frame[FRAME_LENGTH];  // 0x53 角度帧
    bool acc_ready;
    bool gyro_ready;
    bool angle_ready;
} FrameGroup;

// 结构体定义  
typedef struct {  
    float x[DATA_SIZE];  // 降采样缓冲区  
    float y[DATA_SIZE];  
    float z[DATA_SIZE];  
    int count;           // 当前缓冲区中的数据数量  
    int last_ds_index;   // 上一次降采样的位置  
    int remaining_points; // 跨轮次剩余未处理的点  
} DownsampleBuffer;

// ============== START: Added for Smoothed Downsample Sending ==============

// Struct for a single downsampled data point
typedef struct {
    float disp_z;
} DownsampledPoint;

#define DOWNSAMPLED_BUFFER_SIZE 256 // Should be enough to hold points from one batch (approx 82)

// Circular buffer for downsampled data
typedef struct {
    DownsampledPoint buffer[DOWNSAMPLED_BUFFER_SIZE];
    volatile int write_index;
    volatile int read_index;
    volatile int count;
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    volatile bool running;
} DownsampledBuffer_t;

// Global instance of the buffer
static DownsampledBuffer_t g_downsampled_buffer;

// Function prototype for the new sender thread
void* downdisp_sender_thread(void* arg);
void init_downsampled_buffer();

// ============== END: Added for Smoothed Downsample Sending ==============

// 1. 修改FilterBuffer结构体，添加滤波结果存储  
// 1. 首先修改FilterBuffer结构体  
typedef struct {  
    float buffer[FILTER_BUFFER_SIZE];     // 原始数据缓冲  
    float filtered_buffer[FILTER_BUFFER_SIZE]; // 滤波后的结果  
    int count;                            // 当前数据计数  
    int window_size;                      // 滤波窗口大小  
    bool has_valid_result;                // 是否有有效的滤波结果  
} FilterBuffer;

// 全局降采样缓冲区  
static DownsampleBuffer ds_buffer = {  
    .count = 0,  
    .last_ds_index = 0,  
    .remaining_points = 0  
}; 


/// 添加新的结构体用于位移计算  
// 修改位移数据结构，支持三轴数据  
// 修改位移数据结构，使用循环缓冲区  
typedef struct {  
    float *data_buffer_x;    // 东向加速度循环缓冲区  
    float *data_buffer_y;    // 北向加速度循环缓冲区  
    float *data_buffer_z;    // 天向加速度循环缓冲区  
    int buffer_size;         // 缓冲区总大小（比如4096，是处理单元2048的2倍）  
    int write_pos;          // 写入位置  
    int read_pos;           // 读取位置  
    int count;              // 当前数据计数  
    pthread_mutex_t mutex;   // 互斥锁  
    pthread_cond_t cond;     // 条件变量  
    int ready;              // 数据就绪标志

    // 添加overlap缓存
    float overlap_ax[OVERLAP_SIZE];  // 存储上一组的最后30个加速度
    float overlap_ay[OVERLAP_SIZE];
    float overlap_az[OVERLAP_SIZE];
    bool has_overlap;  // 标记是否有上一组的overlap数据  
    float overlap_disp_x[OVERLAP_SIZE];  // 用于存储上一轮最后30个位移
    float overlap_disp_y[OVERLAP_SIZE];
    float overlap_disp_z[OVERLAP_SIZE];
    int round;  // 当前处理轮次

    int current_round;    // 当前处理轮次
        // 累积的数据点数
    bool first_round_completed;  // 新增：标记第一轮是否完成
} displacement_data_t; 



typedef struct {
    uint8_t buffer[BUFFER_SIZE];
    volatile int write_index;
    volatile int read_index;
    pthread_mutex_t lock;
    pthread_cond_t frame_available;  // 有新数据可读
    pthread_cond_t space_available;  // 有新空间可写
    volatile int running;
    // 添加统计信息
    struct {
        uint64_t total_frames;
        uint64_t error_frames;
        uint64_t dropped_frames;
    } stats;
} SharedBuffer;

typedef struct {
    SharedBuffer sb; // 缓冲区
    int fd;          // 文件描述符
    displacement_data_t *disp_data;  // 添加位移数据结构指针
} ThreadArgs;//线程参数传递

// 添加波浪参数结构体  
typedef struct {  
    float wave_height;     // 波高  
    float wave_period;     // 波周期  
    int wave_count;        // 检测到的波浪数  
    float avg_height;      // 平均波高  
    float avg_period;      // 平均周期  

      // 新增字段  
    float h13;           // 1/3最高波平均波高  
    float t13;           // 1/3最高波平均周期  
    float h10;           // 1/10最高波平均波高  
    float t10;           // 1/10最高波平均周期  
    float tz;            // 零上交周期  
    float tp;            // 峰值周期 
} wave_params_t;  

// 定义单个波的数据结构  
typedef struct {  
    float height;     // 波高  
    float period;     // 周期  
    int start_idx;    // 开始索引  
    int end_idx;      // 结束索引  
    float peak;       // 波峰值  
    float trough;     // 波谷值  
} wave_info_t;

// 修改 DataLogger 结构体，分开波向和波浪特征文件  
typedef struct {  

    FILE *ned_file;           // 东北天坐标系加速度数据文件(consumer线程写入)  
    FILE *disp_file;          // 位移数据文件(仅displacement_thread写入)  
    FILE *wave_direction_file; // 波向数据文件(consumer线程写入)
    FILE *wave_params_file;   // 波浪参数特征文件(displacement_thread写入)
    char base_path[256];      
  
    bool is_initialized;      
    pthread_mutex_t file_mutex;
    int total_points;
    FILE *sensor_data_file;  // 新增统一的传感器数据文件 
    FILE *wave_details_file;   // 新增：单波详情文件（记录每个波的波高和周期）
    FILE *disp_down_file;  // 用于存储降采样后的位移数据 
    FILE *spectrum_results_file;  // 新增：谱分析结果文件
      char current_date[32];    // 当前文件的时间戳  
    time_t last_file_time;    // 上次创建文件的时间 
    char current_folder[512];  // 添加这个字段
} DataLogger;
 

int init_processing_log() {
    pthread_mutex_lock(&processing_log_mutex);
    
    // 确保/home/data目录存在
    if (mkdir("/home/data", 0755) == -1 && errno != EEXIST) {
        perror("创建/home/data目录失败");
        pthread_mutex_unlock(&processing_log_mutex);
        return -1;
    }
    
    // 打开日志文件（追加模式）
    processing_log_file = fopen(PROCESSING_LOG_PATH, "w");
    if (!processing_log_file) {
        perror("无法打开处理时间日志文件");
        pthread_mutex_unlock(&processing_log_mutex);
        return -1;
    }
    
    // 写入日志头信息
    time_t now = time(NULL);
    fprintf(processing_log_file, "\n=== 位移处理时间日志 [启动于 %s] ===\n", 
            ctime(&now));
    fflush(processing_log_file);
    
    pthread_mutex_unlock(&processing_log_mutex);
    return 0;
}
void log_processing_time(int round, double duration_sec) {
    pthread_mutex_lock(&processing_log_mutex);
    
    if (processing_log_file) {
        time_t now = time(NULL);
        struct tm *tm = localtime(&now);
        
        fprintf(processing_log_file, 
               "[%04d-%02d-%02d %02d:%02d:%02d] 轮次:%d 耗时:%.3f秒\n",
               tm->tm_year + 1900, tm->tm_mon + 1, tm->tm_mday,
               tm->tm_hour, tm->tm_min, tm->tm_sec,
               round, duration_sec);
        fflush(processing_log_file);
    }
    
    pthread_mutex_unlock(&processing_log_mutex);
}
void close_processing_log() {
    pthread_mutex_lock(&processing_log_mutex);
    
    if (processing_log_file) {
        time_t now = time(NULL);
        fprintf(processing_log_file, "=== 日志结束于 %s ===\n\n", ctime(&now));
        fclose(processing_log_file);
        processing_log_file = NULL;
    }
    
    pthread_mutex_unlock(&processing_log_mutex);
}

// 初始化数据记录器  
DataLogger* init_data_logger(void) {  
    DataLogger *logger = (DataLogger*)malloc(sizeof(DataLogger));  
    if (!logger) {  
        printf("Error: Failed to allocate memory for logger\n");  
        return NULL;  
    }  
    
    // 初始化结构体  
    memset(logger, 0, sizeof(DataLogger));  
    
    // 设置基础路(改)  
    //strcpy(logger->base_path, "/mnt/tf/wave_data");  
    strcpy(logger->base_path, "/mnt/tf/wave_data"); 
    // 检查TF卡是否挂载  （改）
    if (!check_mount_point("/mnt/tf")) {  
        printf("Error: TF card not mounted\n");  
        free(logger);  
        return NULL;  
    }  
    
    // 创建基础目录  
    mkdir(logger->base_path, 0777);  
    return logger;  
}  

// 创建新的数据文件  
bool create_new_data_files(DataLogger *logger) {  
    time_t now;  
    struct tm *timeinfo;  
    char date_path[512];   
    char filename[1024]; 
    time(&now);  
    timeinfo = localtime(&now);  
     // 将分钟向下取整到最近的30分钟  
    timeinfo->tm_min = (timeinfo->tm_min / 30) * 30;
    
  // 格式化日期和时间字符串 (YYYYMMDD_HHMM)  
    strftime(logger->current_date, sizeof(logger->current_date),   
             "%Y%m%d_%H%M", timeinfo);
    
    // 创建日期目录  
    snprintf(date_path, sizeof(date_path), "%s/%s",   
             logger->base_path, logger->current_date);  
    mkdir(date_path, 0777);  
  // 更新当前文件夹路径
    snprintf(logger->current_folder, sizeof(logger->current_folder), 
             "/mnt/tf/wave_data/%s", logger->current_date);

    // 确保所有缓冲数据写入并关闭当前文件  
    if (logger->disp_file) {  
        fflush(logger->disp_file);  
        fclose(logger->disp_file);  
        logger->disp_file = NULL;  
    }  
    if (logger->disp_down_file) {  
        fflush(logger->disp_down_file); 
        fsync(fileno(logger->disp_down_file));  
        fclose(logger->disp_down_file); 
        
        logger->disp_down_file = NULL;  
    }   
    if (logger->wave_direction_file) {  
        fflush(logger->wave_direction_file);  
        fclose(logger->wave_direction_file);  
        logger->wave_direction_file = NULL;  
    }  
    if (logger->wave_params_file) {  
        fflush(logger->wave_params_file);  
        fclose(logger->wave_params_file);  
        logger->wave_params_file = NULL;  
    }  
    if (logger->sensor_data_file) {  
        fflush(logger->sensor_data_file);  
        fclose(logger->sensor_data_file);  
        logger->sensor_data_file = NULL;  
    }  
    if (logger->wave_details_file) {  
        fflush(logger->wave_details_file);
        fsync(fileno(logger->wave_details_file));  
        fclose(logger->wave_details_file);  
        logger->wave_details_file = NULL;  
    } 
     
    if (logger->spectrum_results_file) {  
        fflush(logger->spectrum_results_file);  
        fsync(fileno(logger->spectrum_results_file));
        fclose(logger->spectrum_results_file);  
        logger->spectrum_results_file = NULL;  
    } 
    // 创建新文件  

 // 创建新文件，使用时间戳命名  
    snprintf(filename, sizeof(filename),   
             "%s/disp_down.csv", date_path);  
    logger->disp_down_file = fopen(filename, "w"); 
    snprintf(filename, sizeof(filename),   
             "%s/displacement_%s.csv", date_path, logger->current_date);  
    logger->disp_file = fopen(filename, "w");  
    
    snprintf(filename, sizeof(filename),   
             "%s/wave_direction_%s.csv", date_path, logger->current_date);  
    logger->wave_direction_file = fopen(filename, "w");  
    
    snprintf(filename, sizeof(filename),   
             "%s/wave_parameters_%s.csv", date_path, logger->current_date);  
    logger->wave_params_file = fopen(filename, "a");  
    // 创建统一的传感器数据文件  
    snprintf(filename, sizeof(filename),   
             "%s/sensor_data_%s.csv", date_path, logger->current_date);  
    logger->sensor_data_file = fopen(filename, "w");
    // 创建波浪详情文件  
    snprintf(filename, sizeof(filename),   
             "%s/wave_details_%s.csv", date_path, logger->current_date);  
    logger->wave_details_file = fopen(filename, "w");
    
    // 创建谱分析结果文件
    snprintf(filename, sizeof(filename),   
             "%s/spectrum_results_%s.csv", date_path, logger->current_date);  
    logger->spectrum_results_file = fopen(filename, "w");
   
    // 检查文件是否都创建成功  
    if (!logger->wave_details_file||!logger->sensor_data_file || 
        !logger->disp_file || !logger->wave_direction_file ||   
        !logger->wave_params_file||!logger->spectrum_results_file) {  
        printf("Error: Failed to create data files\n");  
        return false;  
    }  
        

 // 写入文件头  
fprintf(logger->disp_down_file,   
        "Index,DispX,DispY,DispZ,IsOverlap,Round,SampleRate,Timestamp\n");
   
    fprintf(logger->disp_file,   
            "Timestamp,round,index,DispX,DispY,DispZ,FilteredDispX,FilteredDispY,FilteredDispZ,overlap\n");  
    fprintf(logger->wave_direction_file,   
            "Timestamp,CurrentDirection,MainDirection,DirectionDescription\n");  
    fprintf(logger->wave_params_file,   
          "Timestamp,Round,WaveCount,MaxHeight,MaxPeriod,AvgHeight,AvgPeriod,"   "H1/3,T1/3,H1/10,T1/10,Tz,Tp\n");  
            //写入统一的文件头  
    fprintf(logger->sensor_data_file,   
            "Timestamp,"  
            "AccX,AccY,AccZ,"           // 原始加速度  
            "AccX_Filtered,AccY_Filtered,AccZ_Filtered," // 滤波后加速度  
            "Roll,Pitch,Yaw,"           // 角度数据  
            "AccN,AccE,AccD\n");        // 东北天坐标系加速度  
                // 写入波浪详情文件头  
     fprintf(logger->wave_details_file,   
             "Timestamp,单波高,单波周期\n"); 
             // 写入谱分析结果文件头
      
    
    return true;  
}  
// 修改 log_sensor_data 函数为统一记录函数  
void log_unified_sensor_data(DataLogger *logger, const SensorData *data) {
 if (!logger || !logger->is_initialized || !data) {  
        printf("Error: Invalid logger or data\n");  
        return;  
    } 
    char timestamp[32];
    time_t now;
    struct tm *timeinfo;
 time(&now);  
    timeinfo = localtime(&now);  
    strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", timeinfo); 

    if (logger->sensor_data_file) {  
        fprintf(logger->sensor_data_file,   
                "%s,"     // 时间戳  
                "%.6f,%.6f,%.6f,"  // 原始加速度  
                "%.6f,%.6f,%.6f,"  // 滤波后加速度  
                "%.6f,%.6f,%.6f,"  // 角度数据  
                "%.6f,%.6f,%.6f\n", // 东北天坐标系加速度  
                timestamp,  
                data->ax, data->ay, data->az,  
                data->ax_filtered, data->ay_filtered, data->az_filtered,  
                data->roll, data->pitch, data->yaw,  
                data->ax_ned, data->ay_ned, data->az_ned);  
        
        fflush(logger->sensor_data_file);   
    } else {  
        printf("Error: sensor_data_file is NULL\n");  
    }  
}  

// 记录位移数据  
void log_displacement_data(DataLogger *logger, const float *disp, const float *filtered_disp, int index, int data_type, int current_round)
 {
    if (!logger || !logger->is_initialized || !logger->disp_file) {
        printf("Error: Invalid logger or file for displacement logging\n");
        return;
    }

    time_t now;
    struct tm *timeinfo;
    char timestamp[32];
    
    time(&now);
    timeinfo = localtime(&now);
    strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", timeinfo);
    
    // 添加互斥锁保护文件写入
    pthread_mutex_lock(&logger->file_mutex);
    
    int write_success = fprintf(logger->disp_file, 
                              "%s,%d,%d,%.6f,%.6f,%.6f,%.6f,%.6f,%.6f,%d\n",
                              timestamp, 
                              current_round,  // 使用传入的轮次参数
                              index,
                              disp[0], disp[1], disp[2],
                              filtered_disp[0], filtered_disp[1], filtered_disp[2],
                              data_type);
    
    if (write_success < 0) {
        printf("Error writing displacement data to file\n");
    } else {
        // 立即刷新缓冲区
        fflush(logger->disp_file);
        
    }
    
    pthread_mutex_unlock(&logger->file_mutex);
}

// 分离波向记录函数  
void log_wave_direction(DataLogger *logger,   float current_direction,   float main_direction,  const char* direction_desc)
 {  
    if (!logger || !logger->is_initialized) return;  
    
    time_t now;  
    struct tm *timeinfo;  
    char timestamp[32];  
    
    time(&now);  
    timeinfo = localtime(&now);  
    strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", timeinfo);  
    
    fprintf(logger->wave_direction_file,   
            "%s,%.2f,%.2f,%s\n",  
            timestamp, current_direction, main_direction, direction_desc);  
            
    fflush(logger->wave_direction_file);  
}  

// 优化后的波浪参数记录函数  
void log_wave_parameters(DataLogger *logger,   int round,  wave_params_t *params)
 {  // 使用结构体参数  
    if (!logger || !logger->is_initialized) return;  
    time_t now;  
    struct tm *timeinfo;  
    char timestamp[32];  
    
    time(&now);  
    timeinfo = localtime(&now);  
    strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", timeinfo);  
    
    // 写入扩展的波浪参数  
    fprintf(logger->wave_params_file,   
            "%s,%d,%d,%.2f,%.2f,%.2f,%.2f,"  // 原有参数  
            "%.2f,%.2f,%.2f,%.2f,%.2f,%.2f\n",  // 新增参数  
            timestamp,  
            round,              // 轮次  
            params->wave_count, // 波数  
            params->wave_height,// 最大波高  
            params->wave_period,// 最大波高对应周期  
            params->avg_height, // 平均波高  
            params->avg_period, // 平均周期  
            params->h13,        // 1/3最高波波高  
            params->t13,        // 1/3最高波周期  
            params->h10,        // 1/10最高波波高  
            params->t10,        // 1/10最高波周期  
            params->tz,         // 零上交周期  
            params->tp          // 峰值周期  
    ); 
            
    fflush(logger->wave_params_file);  
}

// 修改关闭函数  
void close_data_logger(DataLogger *logger) {  
    if (!logger) return;    
    if (logger->disp_file) fclose(logger->disp_file);  
    if (logger->wave_direction_file) fclose(logger->wave_direction_file);  
    if (logger->wave_params_file) fclose(logger->wave_params_file);  
    
    free(logger);  
}  

// 检查挂载点是否可用  
bool check_mount_point(const char* path) {  
    struct statvfs stat;  
    
    // 尝试获取文件系统信息  
    if (statvfs(path, &stat) != 0) {  
        printf("Error: Cannot access mount point %s\n", path);  
        return false;  
    }  
    
    // 检查是否有可用空间和写入权限  
    if (stat.f_bavail == 0) {  
        printf("Error: No space available on %s\n", path);  
        return false;  
    }  
    
    // 尝试创建测试文件  
    char test_path[512];  
    snprintf(test_path, sizeof(test_path), "%s/.test_write", path);  
    FILE *test_file = fopen(test_path, "w");  
    if (!test_file) {  
        printf("Error: Cannot write to %s\n", path);  
        return false;  
    }  
    
    fclose(test_file);  
    remove(test_path);  
    return true;  
}  

// 获取波向描述  
const char* get_direction_description(float direction) {  
    // 确保角度在0-360度范围内  
    while (direction < 0) direction += 360;  
    while (direction >= 360) direction -= 360;  
    
    if ((direction > 348.75 && direction <= 360) ||   
        (direction >= 0 && direction <= 11.25))  
        return "北(N)";  
    else if (direction <= 33.75)  
        return "北东北(NNE)";  
    else if (direction <= 56.25)  
        return "东北(NE)";  
    else if (direction <= 78.75)  
        return "东东北(ENE)";  
    else if (direction <= 101.25)  
        return "东(E)";  
    else if (direction <= 123.75)  
        return "东东南(ESE)";  
    else if (direction <= 146.25)  
        return "东南(SE)";  
    else if (direction <= 168.75)  
        return "南东南(SSE)";  
    else if (direction <= 191.25)  
        return "南(S)";  
    else if (direction <= 213.75)  
        return "南西南(SSW)";  
    else if (direction <= 236.25)  
        return "西南(SW)";  
    else if (direction <= 258.75)  
        return "西西南(WSW)";  
    else if (direction <= 281.25)  
        return "西(W)";  
    else if (direction <= 303.75)  
        return "西西北(WNW)";  
    else if (direction <= 326.25)  
        return "西北(NW)";  
    else  
        return "��西北(NNW)";  
} 
void init_buffer(SharedBuffer *sb) {
    memset(sb->buffer, 0, BUFFER_SIZE);
    sb->write_index = 0;
    sb->read_index = 0;
    sb->running = 1;
    memset(&sb->stats, 0, sizeof(sb->stats));
    pthread_mutex_init(&sb->lock, NULL);
    pthread_cond_init(&sb->frame_available, NULL);
    pthread_cond_init(&sb->space_available, NULL);
}

void cleanup_buffer(SharedBuffer *sb) {
    sb->running = 0;
    pthread_mutex_destroy(&sb->lock);
    pthread_cond_destroy(&sb->frame_available);
} //清理缓冲区
// 记录东北天坐标系数据
void log_ned_data(DataLogger *logger, const SensorData *data) {
    if (!logger || !logger->is_initialized || !data) {
        printf("Error: Invalid logger or data for NED logging\n");
        return;
    }

    char timestamp[32];
    time_t now;
    struct tm *timeinfo;
    
    // 修改为使用time()而不是gettimeofday()
    time(&now);
    timeinfo = localtime(&now);
    strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", timeinfo);

    if (logger->ned_file) {
        fprintf(logger->ned_file, 
               "%s,%.6f,%.6f,%.6f\n",
               timestamp,
               data->ax_ned, data->ay_ned, data->az_ned);
        fflush(logger->ned_file);
        printf("已记录东北天坐标系数据: %.6f, %.6f, %.6f\n",
               data->ax_ned, data->ay_ned, data->az_ned);
    } else {
        printf("Error: ned_file is NULL\n");
    }
}
//记录单个波浪波高波周期
void log_wave_detail(DataLogger *logger, float height, float period) {  
    if (!logger || !logger->is_initialized || !logger->wave_details_file) {  
        return;  
    }  
    
    // 获取当前时间戳  
    time_t now;  
    struct tm *timeinfo;  
    char timestamp[32];  
    
    time(&now);  
    timeinfo = localtime(&now);  
    strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", timeinfo);  
    
    // 写入波浪详情  
    pthread_mutex_lock(&logger->file_mutex);  
    fprintf(logger->wave_details_file, "%s,%.3f,%.3f\n",  
            timestamp, height, period);  
    fflush(logger->wave_details_file);  
    fsync(fileno(logger->wave_details_file));
    pthread_mutex_unlock(&logger->file_mutex);  
} 

//配置串口的函数， fd是最开始的USB0传感器模块设备节点
int set_uart(int fd, int speed, int bits, char check, int stop) {
    struct termios newtio, oldtio;
    if (tcgetattr(fd, &oldtio) != 0) {
        printf("tcgetattr oldtio is error\n");
        return -1;
    }
    bzero(&newtio, sizeof(newtio));
    newtio.c_cflag |= CLOCAL | CREAD;
    newtio.c_cflag &= ~CSIZE;

    switch (bits) {
        case 7:
            newtio.c_cflag |= CS7;
            break;
        case 8:
            newtio.c_cflag |= CS8;
            break;
    }

    switch (check) {
        case 'o':
            newtio.c_cflag |= PARENB;
            newtio.c_cflag |= PARODD;
            newtio.c_cflag |= (INPCK | ISTRIP);
            break;
        case 'E':
            newtio.c_cflag |= PARENB;
            newtio.c_cflag &= ~PARODD;
            newtio.c_cflag |= (INPCK | ISTRIP);
            break;
        case 'N':
            newtio.c_cflag &= ~PARENB;
            break;
    }

    switch (speed) {
        case 9600:
            cfsetispeed(&newtio, B9600);
            cfsetospeed(&newtio, B9600);
            break;
        case 115200:
            cfsetispeed(&newtio, B115200);
            cfsetospeed(&newtio, B115200);
            break;
    }

    switch (stop) {
        case 1:
            newtio.c_cflag &= ~CSTOPB;
            break;
        case 2:
            newtio.c_cflag |= CSTOPB;
            break;
    }

    tcflush(fd, TCIFLUSH);
    tcsetattr(fd, TCSANOW, &newtio);
    return 0;
}
//
void RS485_serial_init() {
    rs485_fd= open(ADC_485SERIAL_PORT, O_RDWR | O_NOCTTY);
    if (rs485_fd < 0) {
        perror("无法打开adc采集串口");
        return;
    }
    if (set_uart(rs485_fd, 9600, 8, 'N', 1) < 0) {
        perror("adc串口配置失败");
        close(rs485_fd);
        rs485_fd = -1;
    }
}
// Modbus CRC16 计算
uint16_t calculate_crc16(const unsigned char *buffer, int length) {
    uint16_t crc = 0xFFFF;
    for (int i = 0; i < length; i++) {
        crc ^= buffer[i];
        for (int j = 0; j < 8; j++) {
            if (crc & 0x0001) crc = (crc >> 1) ^ 0xA001;
            else crc = crc >> 1;
        }
    }
    return crc;
}

// 读取电压函数 (使用全局 rs485_fd)
float read_battery_voltage() {
    // 1. 检查串口是否有效
    if (rs485_fd < 0) {
        // 尝试临死抢救一下
        RS485_serial_init();
        if (rs485_fd < 0) {
            printf("[Voltage] 串口未就绪，返回默认值\n");
            return 13.0f;
        }
    }

    // 2. Modbus 读取指令 (地址01, 功能03, 寄存器0000, 2个字)
    unsigned char cmd[8] = {0x01, 0x03, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00};
    uint16_t crc = calculate_crc16(cmd, 6);
    cmd[6] = crc & 0xFF;
    cmd[7] = (crc >> 8) & 0xFF;

    // 3. 发送指令 (加锁保护，防止多线程冲突)
    printf("[Modbus] 发送指令: ");
    for(int i=0; i<8; i++) printf("%02X ", cmd[i]);
    printf("\n");
    tcflush(rs485_fd, TCIOFLUSH);
    write(rs485_fd, cmd, 8);
    //usleep(50000); // 等待50ms传输

    // 4. 接收响应
    // unsigned char resp[32];
    // int len = read(rs485_fd, resp, sizeof(resp));

    // 2. 等待响应 (2秒超时)
    unsigned char resp[64] = {0};
    fd_set readfds;
    struct timeval timeout = {2, 0};
    FD_ZERO(&readfds);
    FD_SET(rs485_fd, &readfds);

    printf("[Modbus] 等待响应...\n");
    if (select(rs485_fd + 1, &readfds, NULL, NULL, &timeout) > 0) {
        // 稍等一下让数据传完
        usleep(50000); 
        int len = read(rs485_fd, resp, sizeof(resp));
        
        printf("[Modbus] 收到 %d 字节: ", len);
        for(int i=0; i<len; i++) printf("%02X ", resp[i]);
        printf("\n");

        // 3. 解析 (至少9字节: 01 03 04 [Data] CRC CRC)
        if (len >= 9 && resp[0] == 0x01 && resp[1] == 0x03 && resp[2] == 0x04) {
            // 大端转浮点
            uint32_t temp = (resp[3] << 24) | (resp[4] << 16) | (resp[5] << 8) | resp[6];
            float voltage = *(float*)&temp;
            printf(">>> 解析成功! 电压 = %.2f V <<<\n", voltage);
            return voltage;
        } else {
            printf("[Error] 数据格式错误或长度不足\n");
        }
    } else {
        printf("[Error] 读取超时 (设备没接? 波特率不对?)\n");
    }

    printf("[Voltage] Read Failed or Invalid, use default.\n");
    return 13.0f; // 失败返回默认值
}
void BD_output_serial_init() {
    BD_output_fd= open(BD_OUTPUT_SERIAL_PORT, O_RDWR | O_NOCTTY);
    if (BD_output_fd < 0) {
        perror("无法打开北斗串口");
        return;
    }
    if (set_uart(BD_output_fd, 115200, 8, 'N', 1) < 0) {
        perror("输出串口配置失败");
        close(BD_output_fd);
        BD_output_fd = -1;
    }
}
void downdisp_output_serial_init() {
    downdisp_output_fd= open(DOWNDISP_SERIAL_PORT, O_RDWR | O_NOCTTY);
    if (downdisp_output_fd < 0) {
        perror("无法打开降采样串口");
        return;
    }
    if (set_uart(downdisp_output_fd, 115200, 8, 'N', 1) < 0) {
        perror("降采样输出串口配置失败");
        close(downdisp_output_fd);
        downdisp_output_fd = -1;
    }
}

void init_gps_serial() {
    gps_fd = open(LOCATION_SERIAL_PORT, O_WRONLY | O_NOCTTY);
    
    if (gps_fd < 0) {
        perror("无法打开gps串口");
        return;
    }
    if (set_uart(gps_fd, 115200, 8, 'N', 1) < 0) {
        perror("gps串口配置失败");
        close(gps_fd);
        return;

    }
    
}

char* strtok_adv(char** stringp, const char* delim) {
    if (stringp == NULL || *stringp == NULL) return NULL;
    char* start = *stringp;
    char* p = strpbrk(start, delim);
    if (p == NULL) {
        *stringp = NULL;
    } else {
        *p = '\0';
        *stringp = p + 1;
    }
    return start;
}


time_t parse_rmc(const char *line, GPS_Data* data) {
    char buffer[256]; 
    strncpy(buffer, line, sizeof(buffer)-1); 
    buffer[sizeof(buffer)-1] = '\0';
    char* context = buffer; 
    char* token; char* tokens[20]; 
    int count = 0;
    while ((token = strtok_adv(&context, ",")) != NULL && count < 20) { tokens[count++] = token; }
    if (count < 10 || tokens[2][0] != 'A') { data->valid = false; return -1; }
    char* time_str = tokens[1]; 
    char* date_str = tokens[9];
    if (strlen(time_str) < 6 || strlen(date_str) < 6) { data->valid = false; return -1; }
    int utc_hour, utc_minute, utc_seconds;
     int utc_day, utc_month, utc_year;
    sscanf(time_str, "%2d%2d%2d", &utc_hour, &utc_minute, &utc_seconds);
    sscanf(date_str, "%2d%2d%2d", &utc_day, &utc_month, &utc_year);
    int full_utc_year = (utc_year >= 70) ? (1900 + utc_year) : (2000 + utc_year);
    struct tm tm_utc = { .tm_sec = utc_seconds, .tm_min = utc_minute, .tm_hour = utc_hour,
                         .tm_mday = utc_day, .tm_mon = utc_month - 1, .tm_year = full_utc_year - 1900, .tm_isdst = 0 };
    time_t utc_time_seconds = timegm(&tm_utc);
    if (utc_time_seconds == -1) { data->valid = false; return -1; }

     // ================== DEBUG LOGGING START ==================
     printf("[DEBUG_TIME] Raw RMC Date: %s, Raw RMC Time: %s\n", date_str, time_str);
     printf("[DEBUG_TIME] Parsed UTC: %04d-%02d-%02d %02d:%02d:%02d\n", 
            full_utc_year, utc_month, utc_day, utc_hour, utc_minute, utc_seconds);
     // ================== DEBUG LOGGING END ====================
    time_t beijing_time_seconds = utc_time_seconds + 8 * 3600;
    struct tm* beijing_tm = gmtime(&beijing_time_seconds);
    if (beijing_tm) {
        data->year = beijing_tm->tm_year + 1900;
        data->month = beijing_tm->tm_mon + 1; 
        data->day = beijing_tm->tm_mday;
        data->hour = beijing_tm->tm_hour; 
        data->minute = beijing_tm->tm_min; 
        data->seconds = beijing_tm->tm_sec;
    }
    double lat = atof(tokens[3]);
    double lon = atof(tokens[5]);
    data->latitude = (int)(lat / 100) + fmod(lat, 100) / 60.0; 
    if (tokens[4][0] == 'S') data->latitude = -data->latitude;
    data->longitude = (int)(lon / 100) + fmod(lon, 100) / 60.0; 
    if (tokens[6][0] == 'W') data->longitude = -data->longitude;
    if (strncmp(tokens[0], "$BDRMC", 6) == 0) { data->longitude += 0.0002; }
    data->valid = true;
    // printf("================= GPS RMC 解析结果 =================\n");
    // printf("原始语句: %s\n", line);
    // printf("解析状态: 成功\n");
    // printf("UTC 时间: %04d-%02d-%02d %02d:%02d:%02d\n", full_utc_year, utc_month, utc_day, utc_hour, utc_minute, utc_seconds);
    // printf("北京时间: %04d-%02d-%02d %02d:%02d:%02d\n", data->year, data->month, data->day, data->hour, data->minute, data->seconds);
    // printf("纬度: %f, 经度: %f\n", data->latitude, data->longitude);
    // printf("UTC time_t 值: %ld\n", (long)utc_time_seconds);
    // printf("====================================================\n\n");
    return utc_time_seconds;
}

//时间校准函数
void calibrate_system_time(time_t utc_timestamp) {
    struct timeval tv = { .tv_sec = utc_timestamp, .tv_usec = 0 };

    printf("\n[DEBUG_TIME] Calibrating with UTC timestamp: %ld\n", (long)utc_timestamp);
    printf(">>> 正在尝试校准系统时间...\n");
    if (settimeofday(&tv, NULL) == 0) {
        // 为了方便查看，打印设置后的本地时间
        time_t now = time(NULL);
        printf(">>> 系统时间已校准成功！\n");
        printf(">>> 当前系统本地时间: %s", ctime(&now)); // ctime自带换行符
    } else {
        perror(">>> 时间校准失败 (settimeofday)");
        printf(">>> 请检查是否使用了 'sudo' (root权限) 来运行本程序。\n");
    }
}


// 计算XOR校验和（从$后到*前的内容）

    uint8_t calculate_beidou_checksum(const char* data) {
    uint8_t checksum = 0;
    if (*data == '$') data++; // 跳过起始符$
    while (*data && *data != '*') { // 计算到*前的内容
        checksum ^= *data;
        data++;
    }
    return checksum;
}

// 二进制转十六进制（保持原样）
size_t StrToHex(char *hex, const char *str, size_t len) {
    size_t i, j;
    for(i = 0, j = 0; i < len; i++) {
        snprintf(&hex[j], 3, "%02X", (unsigned char)str[i]);
        j += 2;
    }
    hex[j] = '\0';
    return j;
}

// 北斗波特征数据发送函数（完整协议格式）
void send_wave_features_to_beidou(const GPS_Data* gps_data, float h13, float t13, float h10, float t10,float hmax, float t_hmax, float havg, float tavg, float voltage) {
    const char BD_HEAD[] = "$CCTCQ,15950011,2,1,2,";
    char binary_data[80] = {0};  // 二进制数据缓冲区
    char hex_data[256] = {0};    // 十六进制字符串缓冲区
    int pos = 0;

    // 1. 打包二进制数据（严格按协议顺序）
    // 时间数据（6字节）
    binary_data[pos++] = gps_data->year - 2000;
    binary_data[pos++] = gps_data->month;
    binary_data[pos++] = gps_data->day;
    binary_data[pos++] = gps_data->hour;
    binary_data[pos++] = gps_data->minute;
    binary_data[pos++] = gps_data->seconds;
    uint16_t device_id = get_beidou_device_id();
    // 设备号（2字节）
    // binary_data[pos++] = 0x00;  // 高字节
    // binary_data[pos++] = 0x64;  // 低字节
    // 设备号（2字节），大端模式（高字节在前）
    // 例如 377 (0x0179) -> High: 0x01, Low: 0x79
    binary_data[pos++] = (device_id >> 8) & 0xFF;  // 高字节
    binary_data[pos++] = device_id & 0xFF;         // 低字节
 
    // 经度数据（4字节）
    float abs_lon = fabsf(gps_data->longitude);
    memcpy(&binary_data[pos], &abs_lon, 4); pos += 4;
    // 经度标识（1字节）
    binary_data[pos++] = (gps_data->longitude >= 0) ? 'E' : 'W';
    // 纬度数据（4字节）
    float abs_lat = fabsf(gps_data->latitude);
    memcpy(&binary_data[pos], &abs_lat, 4); pos += 4;
    // 纬度标识（1字节）
    binary_data[pos++] = (gps_data->latitude >= 0) ? 'N' : 'S';
  

    // 波特征数据（32字节）
    memcpy(&binary_data[pos], &h13, 4); pos += 4;
    memcpy(&binary_data[pos], &t13, 4); pos += 4;
    memcpy(&binary_data[pos], &h10, 4); pos += 4;
    memcpy(&binary_data[pos], &t10, 4); pos += 4;
    memcpy(&binary_data[pos], &hmax, 4); pos += 4;
    memcpy(&binary_data[pos], &t_hmax, 4); pos += 4;
    memcpy(&binary_data[pos], &havg, 4); pos += 4;
    memcpy(&binary_data[pos], &tavg, 4); pos += 4;
    memcpy(&binary_data[pos], &voltage, 4); pos += 4; //dianya
    // 2. 转换为十六进制字符串
    StrToHex(hex_data, binary_data, pos);

    // 3. 拼接待校验内容（协议头 + 十六进制数据）
    char raw_message[512];
    snprintf(raw_message, sizeof(raw_message), "%s%s,0", 
             BD_HEAD + 1, hex_data); // +1跳过$

    // 4. 计算XOR校验和
    uint8_t checksum = calculate_beidou_checksum(raw_message);

    // 5. 构建最终北斗报文
    char final_msg[512];
    int msg_len = snprintf(final_msg, sizeof(final_msg), 
                         "%s%s,0*%02X\r\n",  // 格式: $...*<校验和>\r\n
                         BD_HEAD, hex_data, checksum);

    // // 6. 发送数据
    // if (BD_output_fd >= 0) {
    //     if (write(BD_output_fd, final_msg, msg_len) != msg_len) {
    //         perror("北斗波特征数据发送失败");
    //     } else {
    //         printf("北斗数据已发送: H1/3=%.3f, T1/3=%.3f\n", h13, t13);
    //         // 调试输出完整报文
    //         printf("完整报文: %s", final_msg);
    //     }
    // }

    // 【核心改变】将打包好的消息放入队列，而不是直接发送
    pthread_mutex_lock(&bd_queue_mutex);
    if (bd_queue_count < BD_QUEUE_SIZE) {
        strncpy(bd_message_queue[bd_queue_write_idx].message, final_msg, sizeof(BeidouMessage)-1);
        bd_queue_write_idx = (bd_queue_write_idx + 1) % BD_QUEUE_SIZE;
        bd_queue_count++;
        printf("新北斗消息已放入发送队列。\n");
        // 唤醒发送线程
        pthread_cond_signal(&bd_queue_cond);
    } else {
        printf("警告：北斗发送队列已满，消息被丢弃！\n");
    }
    pthread_mutex_unlock(&bd_queue_mutex);
}

// ==================== 新增：北斗发送核心逻辑函数 ====================
// 新增函数：当GPS数据无效时发送波特征数据（使用系统时间作为后备）
void send_wave_features_without_gps(float h13, float t13, float h10, float t10, float hmax, float t_hmax,float havg, float tavg,float voltage) {
    const char BD_HEAD[] = "$CCTCQ,15950011,2,1,2,";
    char binary_data[80] = {0};  // 二进制数据缓冲区（与有GPS时保持一致大小）
    char hex_data[256] = {0};    // 十六进制字符串缓冲区
    int pos = 0;
    
    // 使用系统时间作为后备时间
    time_t current_time = time(NULL);
    struct tm *tm_info = localtime(&current_time);
    
    int year = tm_info->tm_year + 1900;
    int month = tm_info->tm_mon + 1;
    int day = tm_info->tm_mday;
    int hour = tm_info->tm_hour;
    int minute = tm_info->tm_min;
    int second = tm_info->tm_sec;
    
    printf("警告：GPS数据无效，使用系统时间作为后备: %04d-%02d-%02d %02d:%02d:%02d\n", 
           year, month, day, hour, minute, second);
    // 1. 打包二进制数据（严格按协议顺序）
 
    // 1. 打包二进制数据（严格按协议顺序）
    // 时间数据（6字节）- 使用系统时间
    binary_data[pos++] = year - 2000;  // 只取年份后两位
    binary_data[pos++] = month;
    binary_data[pos++] = day;
    binary_data[pos++] = hour;
    binary_data[pos++] = minute;
    binary_data[pos++] = second;
    //新增读取设备号
    uint16_t device_id = get_beidou_device_id();
    // 设备号（2字节）
    // binary_data[pos++] = 0x00;  // 高字节
    // binary_data[pos++] = 0x64;  // 低字节
        // 设备号（2字节），大端模式（高字节在前）
    // 例如 377 (0x0179) -> High: 0x01, Low: 0x79
    binary_data[pos++] = (device_id >> 8) & 0xFF;  // 高字节
    binary_data[pos++] = device_id & 0xFF;         // 低字节
    // 波特征数据（32字节）
    memcpy(&binary_data[pos], &h13, 4); pos += 4;
    memcpy(&binary_data[pos], &t13, 4); pos += 4;
    memcpy(&binary_data[pos], &h10, 4); pos += 4;
    memcpy(&binary_data[pos], &t10, 4); pos += 4;
    memcpy(&binary_data[pos], &hmax, 4); pos += 4;
    memcpy(&binary_data[pos], &t_hmax, 4); pos += 4;
    memcpy(&binary_data[pos], &havg, 4); pos += 4;
    memcpy(&binary_data[pos], &tavg, 4); pos += 4;
    memcpy(&binary_data[pos], &voltage, 4); pos += 4; 
    // 2. 转换为十六进制字符串
    StrToHex(hex_data, binary_data, pos);

    // 3. 拼接待校验内容（协议头 + 十六进制数据）
    char raw_message[512];
    snprintf(raw_message, sizeof(raw_message), "%s%s,0", 
             BD_HEAD + 1, hex_data); // +1跳过$

    // 4. 计算XOR校验和
    uint8_t checksum = calculate_beidou_checksum(raw_message);

    // 5. 构建最终北斗报文
    char final_msg[512];
    int msg_len = snprintf(final_msg, sizeof(final_msg), 
                         "%s%s,0*%02X\r\n",  // 格式: $...*<校验和>\r\n
                         BD_HEAD, hex_data, checksum);

    // 放入发送队列
    pthread_mutex_lock(&bd_queue_mutex);
    if (bd_queue_count < BD_QUEUE_SIZE) {
        strncpy(bd_message_queue[bd_queue_write_idx].message, final_msg, sizeof(BeidouMessage)-1);
        bd_queue_write_idx = (bd_queue_write_idx + 1) % BD_QUEUE_SIZE;
        bd_queue_count++;
        printf("无GPS数据的北斗消息已放入发送队列（使用系统时间）。\n");
        // 唤醒发送线程
        pthread_cond_signal(&bd_queue_cond);
    } else {
        printf("警告：北斗发送队列已满，消息被丢弃！\n");
    }
    pthread_mutex_unlock(&bd_queue_mutex);
    
    printf("北斗数据已发送(无定位): H1/3=%.3f, T1/3=%.3f, H1/10=%.3f, T1/10=%.3f\n",
           h13, t13, h10, t10);
}
// 清空串口接收缓冲区
void clear_serial_buffer(int fd) {
    tcflush(fd, TCIFLUSH);
}


bool wait_for_ack(int fd, int timeout_sec) {
    char read_buffer[256];
    char line_buffer[256];
    int line_pos = 0;
    
    fd_set read_fds;
    struct timeval timeout;
    
    time_t start_time = time(NULL);
    while (difftime(time(NULL), start_time) < timeout_sec) {
        FD_ZERO(&read_fds);
        FD_SET(fd, &read_fds);
        
        // select的超时设为1秒，这样可以快速响应，同时循环检查总超时
        timeout.tv_sec = 1;
        timeout.tv_usec = 0;
        
        int ret = select(fd + 1, &read_fds, NULL, NULL, &timeout);

        if (ret < 0) {
            perror("wait_for_ack: select error");
            return false; // select出错，直接返回失败
        }

        if (ret > 0 && FD_ISSET(fd, &read_fds)) {
            int bytes_read = read(fd, read_buffer, sizeof(read_buffer) - 1);
            if (bytes_read > 0) {
                read_buffer[bytes_read] = '\0'; 

                // 逐字节处理接收到的数据，以拼接成行
                for (int i = 0; i < bytes_read; ++i) {
                    // 当遇到换行符时，说明一行数据接收完毕
                    if ((read_buffer[i] == '\n' || read_buffer[i] == '\r') && line_pos > 0) {
                        line_buffer[line_pos] = '\0';

                        // --- 核心解析逻辑 ---
                        // 创建一个临时副本用于分词，因为分词会修改字符串
                        char temp_line[256];
                        strncpy(temp_line, line_buffer, sizeof(temp_line)-1);
                        temp_line[sizeof(temp_line)-1] = '\0';

                        char* context = temp_line;
                        char* tokens[10];
                        int count = 0;
                        
                        // 使用健壮的分割函数
                        while (count < 10 && (tokens[count] = strtok_adv(&context, ",")) != NULL) {
                            count++;
                        }
                        
                        // 协议格式: $BDFKI,时间,类型,状态,...
                        // 索引:      0     1    2    3
                        // 检查字段数是否足够，第0个字段是否包含"BDFKI"，第3个字段是否为"Y"
                        if (count >= 4 && strstr(tokens[0], "BDFKI") != NULL) {
                            if (tokens[3][0] == 'Y' && tokens[3][1] == '\0') {
                                printf("收到成功应答: %s\n", line_buffer);
                                return true; // 确认成功
                            }
                        }
                        // 如果不是我们想要的应答，或者应答是失败的，就重置行缓冲，继续接收下一行
                        line_pos = 0;
                    } 
                    // 如果不是换行符，就加入到行缓冲
                    else if (read_buffer[i] != '\n' && read_buffer[i] != '\r') {
                         if (line_pos < sizeof(line_buffer) - 1) {
                            line_buffer[line_pos++] = read_buffer[i];
                         }
                    }
                }
            } else if (bytes_read < 0) {
                perror("wait_for_ack: read error");
                return false; // 读取出错
            }
        }
    }

    printf("等待北斗应答超时 (%d 秒)。\n", timeout_sec);
    return false; // 超时
}

// 核心发送函数，包含重试逻辑
bool send_and_verify(const char* message) {
    if (BD_output_fd < 0) return false;
    // 步骤 1: 定义一个“成功标志”，默认为失败
     bool success = false;
    // 上电
    printf("北斗模块发送前上电...\n");
    gpio_ctrl(GPIO_232_2_CRTL, "value", "1");  // GPIO3输出高电平上电
    sleep(40);  // 等待30秒稳定时间

    // 第一次尝试
    printf("北斗发送尝试 1/2: %s", message);
    clear_serial_buffer(BD_output_fd);
    write(BD_output_fd, message, strlen(message));
    if (wait_for_ack(BD_output_fd, 70)) {
        printf("发送成功 (首次尝试)。\n");
        success = true;
    }

    // 第二次尝试
    printf("北斗发送尝试 2/2: %s", message);
    clear_serial_buffer(BD_output_fd);
    write(BD_output_fd, message, strlen(message));
    if (wait_for_ack(BD_output_fd, 60)) {
        printf("发送成功 (重试后)。\n");
        success = true;
    }
    if (!success) {
    printf("发送失败 (两次尝试后)。\n");
    }
    sleep(40);
    gpio_ctrl(GPIO_232_2_CRTL, "value", "0");  // GPIO3输出低电平关闭
    printf("北斗模块发送完成，已断电...\n");
    return success;
}

// 修正后的 process_resend_files 函数 (兼容性更好)
void process_resend_files() {
    

    DIR *d;
    struct dirent *dir;
    
    d = opendir(BD_RESEND_PATH);
    if (!d) {
        perror("无法打开补发目录");
        return;
    }

    // 每次只处理一个文件
    while ((dir = readdir(d)) != NULL) {
        // 跳过 "." 和 ".."
        if (strcmp(dir->d_name, ".") == 0 || strcmp(dir->d_name, "..") == 0) {
            continue;
        }

        char filepath[512];
        snprintf(filepath, sizeof(filepath), "%s%s", BD_RESEND_PATH, dir->d_name);

        struct stat st;
        if (stat(filepath, &st) == 0) {
            // 使用 S_ISREG 宏来判断是否是常规文件
            if (S_ISREG(st.st_mode)) {
                char message[1024];
                FILE* fp = fopen(filepath, "r");
                if (fp) {
                    if (fgets(message, sizeof(message), fp)) {
                        printf("尝试补发文件: %s\n", filepath);
                        if (send_and_verify(message)) {
                            remove(filepath);
                            printf("补发成功，已删除文件: %s\n", filepath);
                        } else {
                            printf("补发失败，文件保留: %s\n", filepath);
                        }
                    }
                    fclose(fp);
                }
                // 找到并处理了一个文件后就退出，实现“每次补发一个”
                break; 
            }
        }
    }
    closedir(d);
}


// ==================== 新增：北斗发送线程主函数 ====================
void* beidou_sender_thread(void* arg) {
    printf("北斗发送线程已启动。\n");
    ensure_resend_directory_exists();

    while (1) {
        char message_to_send[1024] = {0};

        // 1. 检查队列中是否有新消息
        pthread_mutex_lock(&bd_queue_mutex);
        if (bd_queue_count > 0) {
            strncpy(message_to_send, bd_message_queue[bd_queue_read_idx].message, sizeof(message_to_send)-1);
            bd_queue_read_idx = (bd_queue_read_idx + 1) % BD_QUEUE_SIZE;
            bd_queue_count--;
        }
        pthread_mutex_unlock(&bd_queue_mutex);

        // 如果有新消息，优先发送
        if (strlen(message_to_send) > 0) {
            if (!send_and_verify(message_to_send)) {
                save_message_for_resend(message_to_send);
            }
        } else {
            // 2. 如果没有新消息，检查是否有文件需要补发
            process_resend_files();
        }

        // 3. 等待，避免CPU空转
        // 使用带有超时的条件等待，这样有新消息时能立刻响应
        pthread_mutex_lock(&bd_queue_mutex);
        if (bd_queue_count == 0) {
            struct timespec ts;
            clock_gettime(CLOCK_REALTIME, &ts);
            ts.tv_sec += 5; // 如果队列为空，最多等待5秒
            pthread_cond_timedwait(&bd_queue_cond, &bd_queue_mutex, &ts);
        }
        pthread_mutex_unlock(&bd_queue_mutex);
    }
    return NULL;
}
size_t total_bytes =0 ;


//定义串口写入函数往/dev/ttyS0串口发
void write_to_serial(const char *port, const char *data) {
    int fd = open(port, O_WRONLY);
    set_uart(fd, 115200, 8, 'N', 1);
    if (fd != -1) {
        write(fd, data, strlen(data));
        close(fd);
        printf("电台串口打不开\n");
    }
    
}

// 1. 首先定义半小时统计结构
typedef struct {
    wave_info_t waves[MAX_WAVES];  // 存储半小时内的所有波
    int wave_count;
    time_t start_time;
    // 半小时统计结果
    float h13;  // 1/3最高波高
    float t13;  // 1/3波周期
    float h10;  // 1/10最高波高
    float t10;  // 1/10波周期
    float havg; //新增平均波高
    float tavg; //新增平均波周期
    float hmax; // 新增：最大波高
    float t_hmax; // 新增：最大波高对应的周期
    float voltage; 
} HalfHourStats;

//帧校验函数
uint8_t calculate_checksum(uint8_t *buffer, int length) {
    uint8_t checksum = 0;//
    for (int i = 0; i < length - 1; i++) {
        checksum += buffer[i];
    }
    return checksum & 0xFF;
}

float parse_value(uint8_t high, uint8_t low, float scale) {
    int16_t value = ((int16_t)high << 8) | low;
    return value / 32768.0f * scale*G;
} //解析加速度数据函数

float parse_value2(uint8_t high, uint8_t low, float scale) {
    int16_t value = ((int16_t)high << 8) | low;
    return value / 32768.0f * scale;
} //解析角度数据函数

void parse_acc_data(uint8_t *frame, SensorData *data) {

     uint8_t checksum = calculate_checksum(frame,FRAME_LENGTH);
    if (checksum != frame[FRAME_LENGTH - 1]) {
        printf("校验失败，丢弃帧\n");
        return;
    }
    data->ax = parse_value(frame[3], frame[2], 16.0f);
    data->ay = parse_value(frame[5], frame[4], 16.0f);
    data->az = parse_value(frame[7], frame[6], 16.0f);
  
}
void parse_angle_data(uint8_t *frame, SensorData *data) {
     uint8_t checksum = calculate_checksum(frame,FRAME_LENGTH);
    if (checksum != frame[FRAME_LENGTH - 1]) {
        printf("校验失败，丢弃帧\n");
        return;
    }
    data->roll = parse_value2(frame[3], frame[2], 180.0f);
    data->pitch = parse_value2(frame[5], frame[4], 180.0f);
    data->yaw = parse_value2(frame[7], frame[6], 180.0f);
 
}


//验证帧是否有效
int validate_frame(uint8_t *frame, int length) {
    if (frame[0] != FRAME_START_BYTE) {
        return 0;
    }
    
    // 验证帧ID
    if (frame[1] != ACC_FRAME_ID && frame[1] != ANGLE_FRAME_ID) {
        return 0;
    }
    
    // 计算并验证校验和
    uint8_t sum = 0;
    for (int i = 0; i < length - 1; i++) {
        sum += frame[i];
    }
    return (sum == frame[length - 1]);
}
// 初始化滤波缓冲区  

// 2. 修改中值滤波函数实现  
void init_filter_buffer(FilterBuffer *fb) {  
    memset(fb->buffer, 0, sizeof(fb->buffer));  
    memset(fb->filtered_buffer, 0, sizeof(fb->filtered_buffer));  
    fb->count = 0;  
    fb->window_size = FILTER_WINDOW;  
    fb->has_valid_result = false;  
} 
// 插入排序  
void DataInsertSort(float *num, int len) {  
    int i, j;  
    float temp;  
    for(i = 1; i < len; i++) {  
        temp = num[i];  
        for(j = i - 1; ((j > -1) && (num[j] > temp)); j--) {  
            num[j + 1] = num[j];  
        }  
        num[j + 1] = temp;  
    }  
}  

float apply_median_filter(FilterBuffer *fb, float new_value) {  
    // 存储新值  
    if(fb->count < FILTER_BUFFER_SIZE) {  
        fb->buffer[fb->count++] = new_value;  
    } else {  
        // 缓冲区已满，移动数据  
        memmove(fb->buffer, fb->buffer + 1, (FILTER_BUFFER_SIZE - 1) * sizeof(float));  
        fb->buffer[FILTER_BUFFER_SIZE - 1] = new_value;  
    }  

    // 如果数据点不足5个，返回原值  
    if(fb->count < FILTER_WINDOW) {  
        return new_value;  
    }  

    // 构建5点滤波窗口  
    float window[FILTER_WINDOW];  
    int start_idx = fb->count >= FILTER_BUFFER_SIZE ?   
                   FILTER_BUFFER_SIZE - FILTER_WINDOW :   
                   fb->count - FILTER_WINDOW;  
    
    // 复制最近的5个点到窗口  
    memcpy(window, &fb->buffer[start_idx], FILTER_WINDOW * sizeof(float));  
    
    // 排序  
    DataInsertSort(window, FILTER_WINDOW);  
    
    // 取中值  
    float filtered_value = window[FILTER_WINDOW / 2];  
    fb->has_valid_result = true;  
    
    return filtered_value;  
}   

// 坐标转换函数  
void transform_to_ned(SensorData *data) {  
    float xsin, xcos, ysin, ycos, zsin, zcos;  
    float r_x = data->roll;  
    float r_y = data->pitch;  
    float r_z = data->yaw;  

    xsin = sin(r_x * PI / 180.0f);  
    xcos = cos(r_x * PI / 180.0f);  
    ysin = sin(r_y * PI / 180.0f);  
    ycos = cos(r_y * PI / 180.0f);  
    zsin = sin(r_z * PI / 180.0f);  
    zcos = cos(r_z * PI / 180.0f);  

    // 转换到东北天坐标系  
    data->ax_ned = ycos * zcos * data->ax_filtered +   
                   (xsin * ysin * zcos - xcos * zsin) * data->ay_filtered +   
                   (xcos * ysin * zcos + xsin * zsin) * data->az_filtered;  

    data->ay_ned = ycos * zsin * data->ax_filtered +   
                   (xsin * ysin * zsin + xcos * zcos) * data->ay_filtered +   
                   (xcos * ysin * zsin - xsin * zcos) * data->az_filtered;  

    data->az_ned = -ysin * data->ax_filtered +   
                   xsin * ycos * data->ay_filtered +   
                   xcos * ycos * data->az_filtered - G;  
                   
}


/// FFT函数代码，计算位移使用
short FFT(short int dir, long m, float *x, float *y)
{
	long n, i, i1, j, k, i2, l, l1, l2;
	float c1, c2, tx, ty, t1, t2, u1, u2, z;

	/* Calculate the number of points */
	n = 1;
	for (i = 0; i<m; i++)
		n *= 2;

	/* Do the bit reversal */
	i2 = n >> 1;
	j = 0;
	for (i = 0; i<n - 1; i++) 
	{
		if (i < j) 
		{
			tx = x[i];
			ty = y[i];
			x[i] = x[j];
			y[i] = y[j];
			x[j] = tx;
			y[j] = ty;
		}
		k = i2;
		while (k <= j) 
		{
			j -= k;
			k >>= 1;
		}
		j += k;
	}

	/* Compute the FFT */
	c1 = -1.0;
	c2 = 0.0;
	l2 = 1;
	for (l = 0; l<m; l++) 
	{
		l1 = l2;
		l2 <<= 1;
		u1 = 1.0;
		u2 = 0.0;
		for (j = 0; j<l1; j++) 
		{
			for (i = j; i<n; i += l2) 
			{
				i1 = i + l1;
				t1 = u1 * x[i1] - u2 * y[i1];
				t2 = u1 * y[i1] + u2 * x[i1];
				x[i1] = x[i] - t1;
				y[i1] = y[i] - t2;
				x[i] += t1;
				y[i] += t2;
			}
			z = u1 * c1 - u2 * c2;
			u2 = u1 * c2 + u2 * c1;
			u1 = z;
		}
		c2 = sqrt((1.0 - c1) / 2.0);
		if (dir == 1)
			c2 = -c2;
		c1 = sqrt((1.0 + c1) / 2.0);
	}

	/* Scaling for forward transform */
	if (dir == 1) 
	{
		for (i = 0; i<n; i++) 
		{
			x[i]=x[i];
			y[i]=y[i];
		}
	}

	return(TRUE);
}

//highpass
void filter(float *b, int nb, float *a, int na, float *x, int nx, float *zi, float *y)
{
    int m, i;
    for (m = 0; m < nx; m++)
    {
        y[m] = b[0] * x[m] + zi[0];
        for (i = 1; i < na - 1; i++)
        {
            zi[i - 1] = b[i] * x[m] + zi[i] - a[i] * y[m];           
        }
        zi[na - 2] = b[na - 1] * x[m] - a[na - 1] * y[m];
    }    
}
void ffOneChanCat(float *b, int nb, float *a, int na, float *y, int ny, float *zi, int nz, int nfact, int L, float *yout)  
{  
    int i,j,nytemp;  
    float temp;  
    float *ytemp;  
    float *ytemp2;  
    float *ztemp;  
    
    memcpy(yout, y, sizeof(float) * ny);  
    nytemp = ny + nfact * 2;  
    
    // 修改内存分配方式  
    ytemp = (float *)malloc(sizeof(float) * nytemp);  
    ytemp2 = (float *)malloc(sizeof(float) * nytemp);  
    ztemp = (float *)malloc(sizeof(float) * nz);  

    // 检查内存分配是否成功  
    if (ytemp == NULL || ytemp2 == NULL || ztemp == NULL) {  
        // 处理内存分配失败  
        if (ytemp) free(ytemp);  
        if (ytemp2) free(ytemp2);  
        if (ztemp) free(ztemp);  
        return;  
    }  

    for (i = 0; i < L; i++)  
    {  
        for (j = 0; j < nfact; j++)  
        {  
            ytemp[j] = 2 * yout[0] - yout[nfact - j];  
            ytemp[ny + nfact + j] = 2 * yout[ny - 1] - yout[ny - 2 - j];  
        }  
        memcpy(ytemp + nfact, yout, sizeof(float) * ny);  

        for (j = 0; j < nz; j++)  
        {  
            ztemp[j] = zi[i * nz + j] * ytemp[0];  
        }  
        
        filter(b + i * nb, nb, a + i * na, na, ytemp, nytemp, ztemp, ytemp2);  
        
        for (j = 0; j < nytemp / 2; j++)  
        {  
            temp = ytemp2[j];  
            ytemp2[j] = ytemp2[nytemp - 1 - j];  
            ytemp2[nytemp - 1 - j] = temp;  
        }  
        
        for (j = 0; j < nz; j++)  
        {  
            ztemp[j] = zi[i * nz + j] * ytemp2[0];  
        }  
        
        filter(b + i * nb, nb, a + i * na, na, ytemp2, nytemp, ztemp, ytemp);  
        
        for (j = 0; j < ny; j++)  
        {  
            yout[j] = ytemp[nytemp - 1 - nfact - j];  
        }  
    }  

    // 修改内存释放方式  
    free(ytemp);  
    free(ytemp2);  
    free(ztemp);  
}  


void highpass(float *data, int size, float fpass, float fs, float *output)
{
	int nfact=24, L=4;
    /* design filter in MATLAB and copy parameters below */
    /* IIR filter with multiple sections */
   
    /* a and b are both Lx3. zi is Lx2. */
		float a[12]= {1,-1.99871166027128,0.998739430457888,
              1,-1.99574525452028,0.995786011173638,
              1,-1.98428730925064,0.984379475599762,
              1,-1.9996815384382,0.999705910752683};

		float b[12] = {1.36063398560772,-2.72124792587638,1.36063398560772,
									 2.63144081297523,-5.26286001785068,2.63144081297523,
									 15.3478386864872,-30.6956588428952,15.3478386864872,
									 0.0177968546247123,-0.0355933924829478,0.0177968546247123};

		float zi[8] = {-0.638804516535767,0.639714432779077,
               -2.10126725851712,2.10350140395164,
               -15.1467883101707,15.1499288224797,
               -0.00479987492159749,0.00480369719357578};
//         float a[12] = {1,-1.99804728979425,0.99810975281605,
//                1,-1.9935941273825,0.993685732661858,
//                1,-1.97645440388677,0.976660966653345,
//                1,-1.9995040672114,0.999558900758489};

// float b[12] = {1.36019978567079,-2.72035448369172,1.36019978567079,
//                2.62864479382639,-5.25724102095621,2.62864479382639,
//                15.2877032002406,-30.5753648709593,15.2877032002406,
//                0.0177955096997465,-0.0355903067289943,0.0177955096997465};

// float zi[8] = {-0.638370316589011,0.639734752710235,
//                -2.09847123934324,2.10181889690186,
//                -15.0866528238402,15.0913451452793,
//                -0.00479852999672016,0.0048042629546091};
    /* call ffOneChanCat */
									 
	
    ffOneChanCat(b, 3, a, 3, data, size, zi, 2, nfact, L, output);
}

// 修改位移计算函数
int calculate_displacement(float *dataBuf, float *Dis_Src_Data)  
{  
    float dt = T;  
    float df = 1.0f / ((N*N_) * dt);  
    float Nyq = 1.0f / (2 * dt);  
    float omega = -Nyq;  
    float p[4];
    
    int end = (N*N_); 
    float *dis_r;
    
    // 使用malloc 
    float *acc_r = (float *)malloc(N * N_ * sizeof(float));  
    float *acc_i = (float *)malloc(N * N_ * sizeof(float));  
    float *disr = (float *)malloc(N * N_ * sizeof(float));  
    float *t = (float *)malloc(N * N_ * sizeof(float));  
    float *quadratic_term = (float *)malloc(N * N_ * sizeof(float));

    
    if (!acc_r || !acc_i || !disr || !t) {  
        // 处理内存分配失败  
        return -1;  
    }  



    // 复制数据并初始化  
    for (int i = 0; i < (N*N_); i++) {  
        acc_r[i] = dataBuf[i];  
        acc_i[i] = 0.0f;  
    }  
    int poly_n = 3;	//去2次项
    // 执行FFT  
    FFT(1, (int)(log(N*N_) / log(2)), acc_r, acc_i);  
 
    // 位移计算  
    for (int i = (N*N_) / 2; i < end; i++) {  
        if (omega != 0.0f) {  
            float t = 2 * PI * omega * 2 * PI * omega;  
            acc_r[i] = -acc_r[i] / t;  
            acc_i[i] = -acc_i[i] / t;  
        } else {  
            acc_r[i] = 0.0f;  
            acc_i[i] = 0.0f;  
        }  
        if (i == (N*N_) - 1) {  
            i = -1;  
            end = (N*N_) / 2;  
        }  
        omega += df; 
  
    }  
    // 逆FFT  
    FFT(-1, (int)(log(N*N_) / log(2)), acc_r, acc_i);  
    dis_r = acc_r;

	for (int i = 0; i < (N*N_); i++)
	{
		dis_r[i] = dis_r[i] / (N*N_);
	}

	for (int i = 0; i < (N*N_); i++)
	{
		disr[i] = dis_r[i];
	}
	for (int i = 0; i < (N*N_); i++)
	{
		t[i] = dt * i;
	}
    
    polyfit((N*N_), t, disr, poly_n, p);
	polyval((N*N_), t, quadratic_term, poly_n, p);
	
	for (int i = 0; i < (N*N_); i++)
	{
		disr[i] = disr[i] - quadratic_term[i];
		Dis_Src_Data[i] = disr[i];
	}
	
    // 释放内存  
    free(acc_r);  
    free(acc_i);  
    free(disr);  
    free(t);  
    free(quadratic_term);

    return 0;  
}  

// 波向计算函数  
float  BX_Data(float ax, float ay, float az,  float roll, float pitch, float yaw)
 {  
    float Ax, Ay;  
    double wave_direction = 0.0;  
    
    // 计算三角函数值  
    float xSin = sin(roll * PI / 180.0);  
    float xCos = cos(roll * PI / 180.0);  
    float ySin = sin(pitch * PI / 180.0);  
    float yCos = cos(pitch * PI / 180.0);  
    float zSin = sin(yaw * PI / 180.0);  
    float zCos = cos(yaw * PI / 180.0);  
    
    // 计算东北天坐标系下的水平加速度分量  
    Ax = yCos*zCos * ax +   
         (xSin*ySin*zCos - xCos*zSin) * ay +   
         (xCos*ySin*zCos + xSin*zSin) * az;  
    
    Ay = yCos*zSin * ax +   
         (xSin*ySin*zSin + xCos*zCos) * ay +   
         (xCos*ySin*zSin - xSin*zCos) * az;  

    // 根据象限判断波向角度  
    if (Ax == 0 && Ay == 0) {  
        return -1;  // 无效值  
    }  
    if (Ax == 0 && Ay > 0) {  
        wave_direction = 90.0;  
    }  
    if (Ax == 0 && Ay < 0) {  
        wave_direction = 270.0;  
    }  
    if (Ax < 0 && Ay == 0) {  
        wave_direction = 180.0;  
    }  
    if (Ax < 0 && Ay > 0) {  
        wave_direction = 180.0 - atan(-Ay/Ax) * 180.0/PI;  
    }  
    if (Ax < 0 && Ay < 0) {  
        wave_direction = 180.0 + atan(Ay/Ax) * 180.0/PI;  
    }  
    if (Ax > 0 && Ay == 0) {  
        wave_direction = 0.0;  
    }  
    if (Ax > 0 && Ay > 0) {  
        wave_direction = atan(Ay/Ax) * 180.0/PI;  
    }  
    if (Ax > 0 && Ay < 0) {  
        wave_direction = 360.0 - atan(-Ay/Ax) * 180.0/PI;  
    }  
    
    return (float)wave_direction;  
}  

// 计算主波向函数  
float BxRet(float *directions, int len) {  
    // 定义16个方向区间的统计数组  
    int num[16] = {0};        // 计数器  
    float sum[16] = {0.0};    // 角度和  
    
    // 遍历所有波向数据进行��计  
    for(int i = 0; i < len; i++) {  
        float angle = directions[i];  
        
        // N方向特殊处理 (348.76~360 和 0~11.25)  
        if((angle >= 0 && angle <= 11.25) || (angle > 348.75 && angle <= 360)) {  
            if(angle >= 0 && angle <= 11.25) {  
                angle += 360;  // 为了计算平均值，将小角度加360  
            }  
            sum[0] += angle;  
            num[0]++;  
            continue;  
        }  
        
        // 其他方向的判断  
        if(angle <= 33.75) {  
            sum[1] += angle; num[1]++;  // NNE  
        } else if(angle <= 56.25) {  
            sum[2] += angle; num[2]++;  // NE  
        } else if(angle <= 78.75) {  
            sum[3] += angle; num[3]++;  // ENE  
        } else if(angle <= 101.25) {  
            sum[4] += angle; num[4]++;  // E  
        } else if(angle <= 123.75) {  
            sum[5] += angle; num[5]++;  // ESE  
        } else if(angle <= 146.25) {  
            sum[6] += angle; num[6]++;  // SE  
        } else if(angle <= 168.75) {  
            sum[7] += angle; num[7]++;  // SSE  
        } else if(angle <= 191.25) {  
            sum[8] += angle; num[8]++;  // S  
        } else if(angle <= 213.75) {  
            sum[9] += angle; num[9]++;  // SSW  
        } else if(angle <= 236.25) {  
            sum[10] += angle; num[10]++; // SW  
        } else if(angle <= 258.75) {  
            sum[11] += angle; num[11]++; // WSW  
        } else if(angle <= 281.25) {  
            sum[12] += angle; num[12]++; // W  
        } else if(angle <= 303.75) {  
            sum[13] += angle; num[13]++; // WNW  
        } else if(angle <= 326.25) {  
            sum[14] += angle; num[14]++; // NW  
        } else if(angle <= 348.75) {  
            sum[15] += angle; num[15]++; // NNW  
        }  
    }  
    
    // 找出样����数最多的方向区间  
    int max_count = num[0];  
    int max_index = 0;  
    for(int i = 1; i < 16; i++) {  
        if(num[i] > max_count) {  
            max_count = num[i];  
            max_index = i;  
        }  
    }  
    
    // 计算平均方向  
    float main_direction = (max_count > 0) ? sum[max_index] / max_count : -1;  
    
    // 处理北向的特殊情况  
    if(max_index == 0 && main_direction > 360) {  
        main_direction -= 360;  
    }  
    // printf("BxRet函数返回值: %.2f\n", main_direction);  
    return main_direction;  
}  


void process_downsample(DataLogger *logger,    const float *filtered_x, const float *filtered_y,   const float *filtered_z,   int data_length,   int base_index,    int round,   bool is_overlap) {  
    const int DOWNSAMPLE_WINDOW = 25; // 50Hz → 2Hz  
    // 如果有跨轮次剩余数据，先补充到缓冲区  
    for (int i = 0; i < ds_buffer.remaining_points; i++) {  
        int buf_idx = ds_buffer.count % DATA_SIZE;  
        ds_buffer.x[buf_idx] = ds_buffer.x[ds_buffer.last_ds_index + i];  
        ds_buffer.y[buf_idx] = ds_buffer.y[ds_buffer.last_ds_index + i];  
        ds_buffer.z[buf_idx] = ds_buffer.z[ds_buffer.last_ds_index + i];  
        ds_buffer.count++;  
    }  

    // 将新数据添加到降采样缓冲区  
    for (int i = 0; i < data_length; i++) {  
        int buf_idx = ds_buffer.count % DATA_SIZE;  
        ds_buffer.x[buf_idx] = filtered_x[i];  
        ds_buffer.y[buf_idx] = filtered_y[i];  
        ds_buffer.z[buf_idx] = filtered_z[i];  
        ds_buffer.count++;  

        // 当累积足够的点时进行降采样  
        if ((ds_buffer.count - ds_buffer.last_ds_index) >= DOWNSAMPLE_WINDOW) {  
            float ds_x = 0, ds_y = 0, ds_z = 0;  
            int start_idx = ds_buffer.last_ds_index;  

             // 直接取最后一个点
             ds_x = ds_buffer.x[(ds_buffer.last_ds_index + DOWNSAMPLE_WINDOW - 1) % DATA_SIZE];
             ds_y = ds_buffer.y[(ds_buffer.last_ds_index + DOWNSAMPLE_WINDOW - 1) % DATA_SIZE];
             ds_z = ds_buffer.z[(ds_buffer.last_ds_index + DOWNSAMPLE_WINDOW - 1) % DATA_SIZE];


            // 获取时间戳  
            time_t now = time(NULL);  
            struct tm *timeinfo = localtime(&now);  
            char timestamp[32];  
            strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", timeinfo);  

         // 存储降采样数据  
            fprintf(logger->disp_down_file,  
                    "%d,%.6f,%.6f,%.6f,%d,%d,2Hz,%s\n",  
                    base_index + i,  
                    ds_x,  
                    ds_y,  
                    ds_z,  
                    is_overlap,  
                    round,  
                    timestamp);

        // 直接发送z轴降采样数据到串口
            // NEW CODE: Enqueue the point for the sender thread

                 // ==================================================
                 pthread_mutex_lock(&g_tx_queue.mutex);

                 // 只要队列没满，就往里塞
                 if (g_tx_queue.count < TX_RING_BUFFER_SIZE) {
                     g_tx_queue.data[g_tx_queue.head] = ds_z;
                     // 移动头指针，如果到了末尾自动回到开头 (环形)
                     g_tx_queue.head = (g_tx_queue.head + 1) % TX_RING_BUFFER_SIZE;
                     g_tx_queue.count++;
                     
                     // 通知发送线程：有活干了
                     pthread_cond_signal(&g_tx_queue.cond);
                 } else {
                     // 只有当积压了2048个点(17分钟)没发出去时，才会进这里
                     // 这种情况下只能丢弃新数据，保护旧数据不被覆盖
                     printf("严重警告: 发送队列已满，新数据被丢弃! 请检查串口连接。\n");
                 }
     
                 pthread_mutex_unlock(&g_tx_queue.mutex);
                 // ==================================================

            // 更新最后降采样位置  
            ds_buffer.last_ds_index += DOWNSAMPLE_WINDOW;  
        }  
    }  

    // 保存未完成降采样的点到下一轮  
    ds_buffer.remaining_points = ds_buffer.count - ds_buffer.last_ds_index;  
    for (int i = 0; i < ds_buffer.remaining_points; i++) {  
        int idx = (ds_buffer.last_ds_index + i) % DATA_SIZE;  
        ds_buffer.x[i] = ds_buffer.x[idx];  
        ds_buffer.y[i] = ds_buffer.y[idx];  
        ds_buffer.z[i] = ds_buffer.z[idx];  
    }  

    // 重置缓冲区计数  
    ds_buffer.count = ds_buffer.remaining_points;  
    ds_buffer.last_ds_index = 0;  
}


void* downdisp_sender_thread(void* arg)
{
printf("降采样数据发送线程已启动 (TX_RING_QUEUE)...\n");
// each loop we will attempt to take up to 2 points and send them together
// to match "每秒2个点" while ensuring interval > 1s.
while (1) {
pthread_mutex_lock(&g_tx_queue.mutex);
// wait until at least 1 point is available (we will send 1 or 2 points)
while (g_tx_queue.count == 0 && g_tx_queue.running) {
pthread_cond_wait(&g_tx_queue.cond, &g_tx_queue.mutex);
}
if (!g_tx_queue.running && g_tx_queue.count == 0) {
pthread_mutex_unlock(&g_tx_queue.mutex);
break;
}
// decide how many points to take: ideally 2, but if only 1 available, take 1
int take = (g_tx_queue.count >= 2) ? 2 : 1;

float pts[2] = {0.0f, 0.0f};
for (int i = 0; i < take; ++i) {
pts[i] = g_tx_queue.data[g_tx_queue.tail];
g_tx_queue.tail = (g_tx_queue.tail + 1) % TX_RING_BUFFER_SIZE;
}
g_tx_queue.count -= take;
pthread_mutex_unlock(&g_tx_queue.mutex);
//Format and send: send both points in one write so receiver sees them close together
// Format example: "$1.234\n$5.678\n"
char txbuf[128];
if (take == 2) {
snprintf(txbuf, sizeof(txbuf), "$%.3f\n$%.3f\n", pts[0], pts[1]);
} else { // take == 1
snprintf(txbuf, sizeof(txbuf), "$%.3f\n", pts[0]);
}
if (downdisp_output_fd >= 0) {
ssize_t wrote = write(downdisp_output_fd, txbuf, strlen(txbuf));
if (wrote < 0) {
perror("写入降采样串口失败 (发送线程)");
}
} else {
// If serial not open, print for debug
printf("downdisp_output_fd invalid, would send: %s", txbuf);
}
// Sleep to meet hardware restriction: interval > 1s and average 2Hz.
// We send 2 points per iteration (or 1 if only 1 available).
// Sleep slightly over 1s to be safe.
usleep(1100000); // 1.1 second
}
printf("降采样数据发送线程已停止。\n");
return NULL;
}



// 波高比较函数（从大到小排序）
int compare_waves_by_height(const void *a, const void *b) {
    wave_info_t *wave_a = (wave_info_t *)a;
    wave_info_t *wave_b = (wave_info_t *)b;
    
    // 返回负数表示a排在b前面（降序）
    if (wave_a->height > wave_b->height) return -1;
    if (wave_a->height < wave_b->height) return 1;
    return 0;
}


// 新增函数：记录半小时统计数据
void log_wave_statistics(DataLogger *logger, float h13, float t13, float h10, float t10) {
    if (!logger || !logger->is_initialized || !logger->wave_details_file) {  
        return;  
    }  
    
    // 获取当前时间戳  
    time_t now;  
    struct tm *timeinfo;  
    char timestamp[32];  
    
    time(&now);  
    timeinfo = localtime(&now);  
    strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", timeinfo);  
    
    // 写入波浪统计详情  
    pthread_mutex_lock(&logger->file_mutex);  
    fprintf(logger->wave_details_file, 
            "%s,HALF_HOUR_STATS,H1/3=%.3f,T1/3=%.3f,H1/10=%.3f,T1/10=%.3f\n",  
            timestamp, h13, t13, h10, t10);
    fflush(logger->wave_details_file); 
    fsync(fileno(logger->wave_details_file));  
    pthread_mutex_unlock(&logger->file_mutex);  
}
// 2. 计算半小时统计的函数S0是波高波周期输出口
void calculate_half_hour_statistics(HalfHourStats *stats,DataLogger *logger) {
    if (stats->wave_count == 0) return;
    
    // 按波高排序（从大到小）
    qsort(stats->waves, stats->wave_count, sizeof(wave_info_t), compare_waves_by_height);
       
    // 新增：获取最大波高和其对应的周期
    if (stats->wave_count > 0) {
        stats->hmax = stats->waves[0].height;
        stats->t_hmax = stats->waves[0].period;
    } else {
        stats->hmax = 0;
        stats->t_hmax = 0;
    }
    // 计算1/3最高波统计
    int n_third = stats->wave_count / 3;
    if (n_third == 0) n_third = 1;
    float sum_height_third = 0;
    float sum_period_third = 0;
    
    // 计算1/10最高波统计
    int n_tenth = stats->wave_count / 10;
    if (n_tenth == 0) n_tenth = 1;
    float sum_height_tenth = 0;
    float sum_period_tenth = 0;

        // 计算平均波高和周期（新增）
    float sum_height_avg = 0;
    float sum_period_avg = 0;
    
    // 计算统计值
    for (int i = 0; i < stats->wave_count; i++) {
        sum_height_avg += stats->waves[i].height;
        sum_period_avg += stats->waves[i].period;
        if (i < n_third) {
            sum_height_third += stats->waves[i].height;
            sum_period_third += stats->waves[i].period;
        }
        if (i < n_tenth) {
            sum_height_tenth += stats->waves[i].height;
            sum_period_tenth += stats->waves[i].period;
        }
    }
    
    // 保存结果
    stats->h13 = sum_height_third / n_third;
    stats->t13 = sum_period_third / n_third;
    stats->h10 = sum_height_tenth / n_tenth;
    stats->t10 = sum_period_tenth / n_tenth;
    stats->havg = sum_height_avg / stats->wave_count;  // 新增平均波高
    stats->tavg = sum_period_avg / stats->wave_count; // 新增平均周期
    stats->voltage = read_battery_voltage();
    
     // 3. 输出到串口
    char buffer[200];
    snprintf(buffer, sizeof(buffer), 
             "半小时统计,1/3波高%.3f,1/3波周期%.3f,1/10波高%.3f,1/10波周期%.3f\n",
             stats->h13, stats->t13,
             stats->h10, stats->t10);
   
    //write_to_serial("/dev/ttymxc2", buffer);

    // 4. 写入到wave_details_file
    if (logger) {
        log_wave_statistics(logger, stats->h13, stats->t13, stats->h10, stats->t10);
    }

    // 5. 发送波特征数据到北斗 - 新增功能
    GPS_Data current_gps;
    pthread_mutex_lock(&gps_data_mutex);
    current_gps = global_gps_data;  // 安全复制GPS数据
    pthread_mutex_unlock(&gps_data_mutex);
    //新增时间校准；
      // 获取UTC时间戳
        time_t utc_time_seconds;
        bool time_valid;
        
        pthread_mutex_lock(&utc_time_mutex);
        utc_time_seconds = last_utc_time_seconds;
        time_valid = utc_time_valid;
        pthread_mutex_unlock(&utc_time_mutex);
        
        if (time_valid) {
            calibrate_system_time(utc_time_seconds);
        } else {
            printf("UTC时间戳无效，无法校准系统时间\n");
        }

    // 检查GPS数据有效性并发送波特征
    if (current_gps.valid) {
        send_wave_features_to_beidou(&current_gps, 
                                   stats->h13, stats->t13, 
                                   stats->h10, stats->t10,stats->hmax,stats->t_hmax,stats->havg, stats->tavg,stats->voltage);
        printf("半小时波特征已发送到北斗: H1/3=%.3f, T1/3=%.3f, H1/10=%.3f, T1/10=%.3f\n",
               stats->h13, stats->t13, stats->h10, stats->t10);
    } else {
        send_wave_features_without_gps(stats->h13, stats->t13, 
                                  stats->h10, stats->t10, stats->hmax,stats->t_hmax,stats->havg, stats->tavg,stats->voltage);
        printf("半小时波特征已发送到北斗(GPS无效): H1/3=%.3f, T1/3=%.3f, H1/10=%.3f, T1/10=%.3f\n",
           stats->h13, stats->t13, stats->h10, stats->t10);
      
    }
}


void calculate_wave_parameters(const float *z_displacement, int data_len, float sample_rate, wave_params_t *params, bool is_first_round, int *prev_start_idx_global, 
    float *prev_max_value, float *prev_min_value,DataLogger *logger,HalfHourStats *half_hour_stats,int current_data_start) 
{
    float dt = 1.0f / sample_rate;
    int start_idx;
    float max_value, min_value;

    // 初始化索引和极值
    if (is_first_round) {
        start_idx = -1;
        max_value = -1000.0f;
        min_value = 1000.0f;
    } else {
        // 全局索引转局部索引
        start_idx = *prev_start_idx_global - current_data_start;

        // 检查索引有效性
        if (start_idx < -OVERLAP_SIZE  || start_idx >= data_len) {
            start_idx = -1;
            max_value = -1000.0f;
            min_value = 1000.0f;
        } else {
            max_value = *prev_max_value;
            min_value = *prev_min_value;
        }
    }

    // 遍历数据检测上跨零点
    for (int i = 1; i < data_len; i++) {
        if (z_displacement[i-1] <= 0 && z_displacement[i] > 0) {
            if (start_idx != -1 ) {
                // 计算波周期（使用局部索引）
                float period = (i - start_idx) * dt;
                float height = max_value - min_value;

                // 存储有效波形
                if (height > 0.01f && period > 0.05f && period < 40.0f) {
                    // 记录波形到日志和统计
                    log_wave_detail(logger, height, period);
                    if (half_hour_stats->wave_count < MAX_WAVES) {
                        half_hour_stats->waves[half_hour_stats->wave_count].height = height;
                        half_hour_stats->waves[half_hour_stats->wave_count].period = period;
                        half_hour_stats->wave_count++;
                    }
                }
            }
            // 重置为新的波形起点
            start_idx = i;
            max_value = -1000.0f;
            min_value = 1000.0f;
        }

        // 更新极值
        if (start_idx >= 0) {
            if (z_displacement[i] > max_value) max_value = z_displacement[i];
            if (z_displacement[i] < min_value) min_value = z_displacement[i];
        }
    }

    // 保存状态（局部索引转全局索引）
    if (start_idx >= 0) {
        *prev_start_idx_global = start_idx + current_data_start;
    } else {
        *prev_start_idx_global = -1;
    }
    *prev_max_value = max_value;
    *prev_min_value = min_value;
}
//
void *producer(void *arg) {
    ThreadArgs *args = (ThreadArgs *)arg;
    SharedBuffer *sb = &args->sb;
    int fd = args->fd;
    
    // 定义读取缓冲区和帧缓冲区
    uint8_t read_buffer[256];                  // 串口读取缓冲区
    uint8_t frame_buffer[FRAME_LENGTH];        // 单帧数据缓冲区
    uint8_t temp_buffer[2048];     // 临时缓冲区，用于处理跨帧数据
    int temp_buffer_size = 0;                  // 临时缓冲区中的数据量
    
    while (sb->running) {
        // 从串口读取数据
        int bytes_read = read(fd, read_buffer, sizeof(read_buffer));
        
        if (bytes_read > 0) {
            // 处理读取到的数据
            for (int i = 0; i < bytes_read; i++) {
                // 将数据添加到临时缓冲区
                 if (temp_buffer_size < sizeof(temp_buffer)) {
       temp_buffer[temp_buffer_size++] = read_buffer[i];
       } else {

          printf("temp_buffer_size 超出范围\n");
          // 当临时缓冲区满时，清除前2030个字节
                    printf("警告:temp_buffer已满,当前大小：%d,清除前2030个字节\n", temp_buffer_size);
                    memmove(temp_buffer, temp_buffer + 2030, temp_buffer_size - 2030);
                    temp_buffer_size -= 2030;  // 更新缓冲区大小
                  }
               
                // 查找完整帧
                while (temp_buffer_size >= FRAME_LENGTH) {
                    // 查找帧头
                    int frame_start = -1;
                    for (int j = 0; j <= temp_buffer_size - FRAME_LENGTH; j++) {
                        if (temp_buffer[j] == FRAME_START_BYTE) {
                            frame_start = j;
                            break;
                        }
                    }
                    
                    if (frame_start == -1) {
                        // 没找到帧头，保留最后10个字节（可能包含部分帧头）
                        if (temp_buffer_size > 10) {
                            memmove(temp_buffer, temp_buffer + temp_buffer_size - 10, 10);
                            temp_buffer_size = 10;
                        }
                        break;
                    }
                    
                    // 如果找到帧头，但数据不足一帧，等待更多数据
                    if (frame_start + FRAME_LENGTH > temp_buffer_size) {
                        if (frame_start > 0) {
                            memmove(temp_buffer, temp_buffer + frame_start, temp_buffer_size - frame_start);
                            temp_buffer_size -= frame_start;
                        }
                        break;
                    }
                    
                    // 复制完整帧到frame_buffer
                    memcpy(frame_buffer, temp_buffer + frame_start, FRAME_LENGTH);
                    
                    // 验证校验和
                    if (calculate_checksum(frame_buffer, FRAME_LENGTH) == frame_buffer[FRAME_LENGTH - 1]) { 
                    printf("\n");  
  
                        pthread_mutex_lock(&sb->lock);
                
                        // 计算可用空间
                        int available_space = (sb->read_index - sb->write_index + BUFFER_SIZE - 1) % BUFFER_SIZE;
                        
                        // 如果空间不足，等待消费者读取
                        while (available_space < FRAME_LENGTH && sb->running) {
                            pthread_cond_wait(&sb->space_available, &sb->lock);
                            available_space = (sb->read_index - sb->write_index + BUFFER_SIZE - 1) % BUFFER_SIZE;
                        }
                        
                        if (!sb->running) {
                            pthread_mutex_unlock(&sb->lock);
                            return NULL;
                        }
                        
                        // 写入有效帧到环形缓冲区
                        if (sb->write_index + FRAME_LENGTH <= BUFFER_SIZE) {
                            memcpy(sb->buffer + sb->write_index, frame_buffer, FRAME_LENGTH);
                        } else {
                            // 处理回环
                            int first_part = BUFFER_SIZE - sb->write_index;
                            int second_part = FRAME_LENGTH - first_part;
                            memcpy(sb->buffer + sb->write_index, frame_buffer, first_part);
                            memcpy(sb->buffer, frame_buffer + first_part, second_part);
                        }
                        
                        sb->write_index = (sb->write_index + FRAME_LENGTH) % BUFFER_SIZE;
                        sb->stats.total_frames++;
                        
                        // 通知消费��有新数据
                     
                        pthread_cond_signal(&sb->frame_available);
                        pthread_mutex_unlock(&sb->lock);
                    } else {
                        // 校验和错误，记录统计
                        sb->stats.error_frames++;
                    }
                    
                    // 移除已处理的帧数据
                    int remaining = temp_buffer_size - (frame_start + FRAME_LENGTH);
                    if (remaining > 0) {
                        memmove(temp_buffer, 
                               temp_buffer + frame_start + FRAME_LENGTH, 
                               remaining);
                        temp_buffer_size = remaining;
                    } else {
                        temp_buffer_size = 0;
                    }
                }
            }
        } else if (bytes_read < 0 && errno != EAGAIN && errno != EWOULDBLOCK) {
            perror("串口读取错误");
            break;
           
        }
        
        usleep(1000);  // 1ms延迟，避免过度占用CPU
    }
    return NULL;
}


void *consumer(void *arg) {  
    ThreadArgs *args = (ThreadArgs *)arg;  
    SharedBuffer *sb = &args->sb;  
    displacement_data_t *disp_data = args->disp_data;  
    SensorData data = {0};  
    uint8_t frame[FRAME_LENGTH];  
    FrameGroup frame_group = {0};
    // 为三个轴初始化滤波器  
    FilterBuffer filter_x, filter_y, filter_z;  
    init_filter_buffer(&filter_x);  
    init_filter_buffer(&filter_y);  
    init_filter_buffer(&filter_z);  

    int acc_count = 0;
    int angle_count = 0;
    int ned_count = 0;
    
     // 初始化数据记录器  
    DataLogger *logger = init_data_logger();  
    if (!logger) {  
        printf("Error: Could not initialize data logger\n");  
        return NULL;  
    }
// 创建新的数据文件  
    if (!create_new_data_files(logger)) {  
        close_data_logger(logger);  
        return NULL;  
         printf("【消费者线程】创建新的数据文件失败");
    }
    logger->is_initialized = true; 
    // 波向计算相关变量  
    float wave_directions[ N * N_] = {0};  
    int direction_count = 0; 

    while (sb->running) {  
        pthread_mutex_lock(&sb->lock);  
        
        // 计算可读数据量  
        int available_data = (sb->write_index - sb->read_index + BUFFER_SIZE) % BUFFER_SIZE;  
        
        // 如果没有足够的数据，等待生产者  
        while (available_data < FRAME_LENGTH && sb->running) {  
            pthread_cond_wait(&sb->frame_available, &sb->lock);  
            available_data = (sb->write_index - sb->read_index + BUFFER_SIZE) % BUFFER_SIZE;  
        }  
        
        if (!sb->running) {  
            pthread_mutex_unlock(&sb->lock);  
            break;  
        }  
   
        // 读取数据  
        if (sb->read_index + FRAME_LENGTH <= BUFFER_SIZE) {  
            memcpy(frame, sb->buffer + sb->read_index, FRAME_LENGTH);  
        } else {  
            int first_part = BUFFER_SIZE - sb->read_index;  
            int second_part = FRAME_LENGTH - first_part;  
            memcpy(frame, sb->buffer + sb->read_index, first_part);  
            memcpy(frame + first_part, sb->buffer, second_part);  
        }  
        
        sb->read_index = (sb->read_index + FRAME_LENGTH) % BUFFER_SIZE;  
        pthread_cond_signal(&sb->space_available);  
        pthread_mutex_unlock(&sb->lock);  
        
        switch(frame[1]) {
            case ACC_FRAME_ID:  // 0x51
                memcpy(frame_group.acc_frame, frame, FRAME_LENGTH);
                frame_group.acc_ready = true;
             

                break;
            case 0x52:  // 陀螺仪帧
                memcpy(frame_group.gyro_frame, frame, FRAME_LENGTH);
                frame_group.gyro_ready = true;
                break;
            case ANGLE_FRAME_ID:  // 0x53
                memcpy(frame_group.angle_frame, frame, FRAME_LENGTH);
                frame_group.angle_ready = true;
           
                break;
        }
            

 // 当三帧都准备好时，进行解析和处理
        if (frame_group.acc_ready && frame_group.gyro_ready && frame_group.angle_ready) {
            // 解析加速度数据
            parse_acc_data(frame_group.acc_frame, &data);

            // 应用中值滤波
            data.ax_filtered = apply_median_filter(&filter_x, data.ax);
            data.ay_filtered = apply_median_filter(&filter_y, data.ay);
            data.az_filtered = apply_median_filter(&filter_z, data.az);
            // 解析角度数据
            parse_angle_data(frame_group.angle_frame, &data);
 
            // 转换到东北天坐标系
            transform_to_ned(&data);
            // 使用已转换的东北天加速度和角度计算波向  
            float current_direction = BX_Data(  
                data.ax_ned,    // 东北天坐标系下的加速度  
                data.ay_ned,   
                data.az_ned,  
                data.roll,      // 原始角度数据  
                data.pitch,  
                data.yaw  
            ); 

            const char* direction_desc;  

            // 存储有效的波向数据  
            if (current_direction >= 0) {  
                //  printf("Storing direction %.2f at index %d\n", current_direction, direction_count);  
                wave_directions[direction_count++] = current_direction;  
                
                // ��累积到2048组数据时，计算主波向  
                if (direction_count >=  N * N_) {  
                    // printf("开始计算主波向，数据量: %d\n", direction_count); 
    
                    // 计算主波向  
                    float main_direction = BxRet(wave_directions,  N * N_);  
                  const char* direction_desc = get_direction_description(main_direction);  
                     // 输出对应的方位描述  
    
                    if((main_direction > 348.75 && main_direction <= 360) ||   
                       (main_direction >= 0 && main_direction <= 11.25))  
                        direction_desc = "北(N)";  
                    else if(main_direction <= 33.75)  
                        direction_desc = "北东北(NNE)";  
                    else if(main_direction <= 56.25)  
                        direction_desc = "东北(NE)";  
                    else if(main_direction <= 78.75)  
                        direction_desc = "东东北(ENE)";  
                    else if(main_direction <= 101.25)  
                        direction_desc = "东(E)";  
                    else if(main_direction <= 123.75)  
                        direction_desc = "东东南(ESE)";  
                    else if(main_direction <= 146.25)  
                        direction_desc = "东南(SE)";  
                    else if(main_direction <= 168.75)  
                        direction_desc = "南东南(SSE)";  
                    else if(main_direction <= 191.25)  
                        direction_desc = "南(S)";  
                    else if(main_direction <= 213.75)  
                        direction_desc = "南西南(SSW)";  
                    else if(main_direction <= 236.25)  
                        direction_desc = "西南(SW)";  
                    else if(main_direction <= 258.75)  
                        direction_desc = "西西南(WSW)";  
                    else if(main_direction <= 281.25)  
                        direction_desc = "��(W)";  
                    else if(main_direction <= 303.75)  
                        direction_desc = "���西北(WNW)";  
                    else if(main_direction <= 326.25)  
                        direction_desc = "西北(NW)";  
                    else  
                        direction_desc = "北西北(NNW)";  
                    
                    printf("方位描述: %s\n", direction_desc);  
                    printf("统计样本数: %d\n",  N * N_);  
                    printf("===================================\n");  
                 
                    // 记录波向数据  
                    log_wave_direction(logger, current_direction, main_direction, direction_desc); 
                    // 重置计数器，开始新一轮统计  
                    direction_count = 0;
                       }  
            } 
            
            // 存储转换后的数据到位移计算缓冲区  
            pthread_mutex_lock(&disp_data->mutex);
            // 存储东北天数据
            disp_data->data_buffer_x[disp_data->write_pos] = data.ax_ned;
            disp_data->data_buffer_y[disp_data->write_pos] = data.ay_ned;
            disp_data->data_buffer_z[disp_data->write_pos] = data.az_ned;
            
            disp_data->write_pos = (disp_data->write_pos + 1) % disp_data->buffer_size;
            disp_data->count++;

            // 修改触发条件判断  
   // 检查是否需要触发位移计算                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
    if (!disp_data->first_round_completed && disp_data->count >= N * N_) {  
        disp_data->ready = 1;  
        pthread_cond_signal(&disp_data->cond);  
       
    }  
    else if (disp_data->first_round_completed && disp_data->count >= EFFECTIVE_SIZE) {  
        disp_data->ready = 1;  
        pthread_cond_signal(&disp_data->cond);  
    } 

            pthread_mutex_unlock(&disp_data->mutex);

             // 记录数据  
   if (logger && logger->is_initialized) {  
    log_unified_sensor_data(logger, &data);  }

    // 在这里重置标志位，确保数据处理完成后立即重置  
    frame_group.acc_ready = false;  
    frame_group.gyro_ready = false;  
    frame_group.angle_ready = false; 
        }  
    }  
    // 清理资源  
    close_data_logger(logger); 
    return NULL;  
}

// 在位移线程的降采样数据处理后添加
void notify_data_ready(DataLogger *logger, const char *current_folder) {
    // 确保数据写入完成
    if (logger->disp_down_file) {
        fflush(logger->disp_down_file);
        fsync(fileno(logger->disp_down_file));
    }
    
    pthread_mutex_lock(&file_mutex);
    strncpy(current_file_path, current_folder, sizeof(current_file_path) - 1);
    file_ready = 1;
    printf("位移线程: 数据写入完成，通知谱分析线程\n");
 
    pthread_cond_signal(&file_ready_cond);
    pthread_mutex_unlock(&file_mutex);
}
// 在文件开头添加全局变量
static char completed_folder_path[512] = {0};  // 存储已完成的文件夹路径

// 添加全局变量记录当前处理时间
static time_t current_processing_time = 0;//记录文件夹的创建时间也就是采集启动处理写入文件了，方便在谱分析打包发送的

bool is_half_hour_point(time_t current_time) {
    struct tm *tm_info = localtime(&current_time);
    // 添加调试输出
    printf("当前时间: %02d:%02d:%02d\n", 
           tm_info->tm_hour, tm_info->tm_min, tm_info->tm_sec);
           
    // 放宽条件，允许一定误差
    return (tm_info->tm_min == 0 || tm_info->tm_min == 30) && 
           (tm_info->tm_sec >= 0 && tm_info->tm_sec < 85);  // 给85秒的容差,4096/50+2.6~2.8的处理时间，大约每轮84点多的时间，设置容差是85秒应该是没问题。
}
// 获取下一个整点或半点时间
time_t get_next_half_hour(time_t current_time) {
    struct tm *tm_info = localtime(&current_time);
    
    // 调整到下一个30分钟整点
    if (tm_info->tm_min < 30) {
        tm_info->tm_min = 30;
    } else {
        tm_info->tm_min = 0;
        tm_info->tm_hour += 1;
    }
    tm_info->tm_sec = 0;
    
    return mktime(tm_info);
}


// GPS电源控制函数
void manage_gps_power() {
    time_t current_time = time(NULL);
    struct tm *tm_info = localtime(&current_time);
    
    // 检查是否到达GPS上电时间点（28分或58分）
    if ((tm_info->tm_min == 23 || tm_info->tm_min == 53) && 
        tm_info->tm_sec < 85 && 
        !gps_powered_on) {
        
        printf("位移线程: 即将到达半小时节点，准备上电GPS\n");
        
        // 上电GPS
        //gpio_ctrl("4", "value", "1");
        
          // 更新GPS电源状态并通知GPS线程
        pthread_mutex_lock(&gps_power_mutex);
        gps_powered_on = true;
        pthread_cond_signal(&gps_power_cond);
        pthread_mutex_unlock(&gps_power_mutex);
        
        printf("GPS模块已上电，等待稳定...\n");
    }
    
    // 检查是否到达GPS断电时间点（3分或33分）
    else if ((tm_info->tm_min == 4 || tm_info->tm_min == 34) && 
             tm_info->tm_sec < 85 && 
             gps_powered_on) {
        
        printf("位移线程: 半小时统计已完成，准备断电GPS\n");
        
        // 断电GPS
        // sleep(40);  // 确保数据处理完成
        gpio_ctrl(GPIO1_DW, "value", "0");
       
         // 更新GPS电源状态
        pthread_mutex_lock(&gps_power_mutex);
        gps_powered_on = false;
        pthread_cond_signal(&gps_power_cond);
        pthread_mutex_unlock(&gps_power_mutex);
        
        
        printf("GPS模块已断电\n");
    }
}
// //位移计算线程新增

//位移计算线程新增
void *displacement_thread(void *arg) {  
    displacement_data_t *disp_data = (displacement_data_t *)arg;  
    int displacement_count = 0;
    static time_t last_file_time = 0;  // 添加文件时间管理

    // 在位移计算线程开始处添加全局累积偏移量
    int64_t global_data_offset = 0;  // 数据起始全局偏移量

// 在位移计算线程的开头部分
    pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
    pthread_cond_t cond = PTHREAD_COND_INITIALIZER;
    int displacement_ready = 0;  // 标志位，指示数据是否准备好
    printf("位移线程: 初始化启动\n");
 // 1. 初始化
    HalfHourStats half_hour_stats = {0};
    half_hour_stats.start_time = time(NULL);
    // char current_file_path[512] = {0};  // 存储当前文件路径

    // 在displacement_thread函数中的全局变量定义  
    bool is_first_round = true;  // 标记是否是第一轮  
    int prev_start_idx = -1;     // 上一轮最后一个上跨零点索引  
    float prev_max_value = -1000.0f;  // 上一轮最大值  
    float prev_min_value = 1000.0f;   // 上一轮最小值 
        
   // 初始化数据记录器  
    DataLogger *logger = init_data_logger();  
    if (!logger) {  
        printf("Error: Could not initialize logger\n");  
        return NULL;  
    }  
    time_t last_file_switch_time = time(NULL);
  // 初始化第一个文件  
    time_t current_time = time(NULL);  
    if (create_new_data_files(logger)) {  
        last_file_time = current_time;  
        printf("Created initial data files at: %s\n", logger->current_date);  
    }
    logger->is_initialized = true; 
    // 为计算缓冲区分配内存  
    float *calc_buffer_x = (float *)malloc(N * N_ * sizeof(float));  
    float *calc_buffer_y = (float *)malloc(N * N_ * sizeof(float));  
    float *calc_buffer_z = (float *)malloc(N * N_ * sizeof(float)); 
    
    // 为三轴位移结果分配内存  
    float *result_buffer_x = (float *)malloc(N * N_ * sizeof(float));  
    float *result_buffer_y = (float *)malloc(N * N_ * sizeof(float));  
    float *result_buffer_z = (float *)malloc(N * N_ * sizeof(float));  

      // 为滤波后的位移结果分配内存  
    float *filtered_x = (float *)malloc(N * N_ * sizeof(float));  
    float *filtered_y = (float *)malloc(N * N_ * sizeof(float));  
    float *filtered_z = (float *)malloc(N * N_ * sizeof(float));  

    // 分配overlap区域的位移结果缓冲区
    float *overlap_disp_x = (float *)malloc(OVERLAP_SIZE * sizeof(float));
    float *overlap_disp_y = (float *)malloc(OVERLAP_SIZE * sizeof(float));
    float *overlap_disp_z = (float *)malloc(OVERLAP_SIZE * sizeof(float));
    printf("位移线程: 分配内存、缓冲区完成\n");
    //判断是否分配成功
if (!calc_buffer_x || !calc_buffer_y || !calc_buffer_z || !result_buffer_x || !result_buffer_y || !result_buffer_z || !filtered_x || !filtered_y || !filtered_z) {  
        perror("Failed to allocate buffers");  
      // 清理已分配的内存  
        if (calc_buffer_x) free(calc_buffer_x);  
        if (calc_buffer_y) free(calc_buffer_y);  
        if (calc_buffer_z) free(calc_buffer_z);  
        if (result_buffer_x) free(result_buffer_x);  
        if (result_buffer_y) free(result_buffer_y);  
        if (result_buffer_z) free(result_buffer_z);  
        if (filtered_x) free(filtered_x);  
        if (filtered_y) free(filtered_y);  
        if (filtered_z) free(filtered_z);
        close_data_logger(logger);  
        return NULL; 
    }  
    int round = 0;
    int total_points_saved = 0;
    // 在displacement_thread中添加数据处理计数器  
    int processed_data_count = 0;  
    int total_rounds = 0;  

      // 添加时间统计变量
    struct timespec start_processing, end_processing;
    double processing_duration_sec;
    char time_stats[256];

    while (1) {
        pthread_mutex_lock(&disp_data->mutex);
        while (!disp_data->ready) {
            pthread_cond_wait(&disp_data->cond, &disp_data->mutex);
        }
    
         // 记录开始处理时间
        clock_gettime(CLOCK_MONOTONIC, &start_processing);

        round++;  // 轮次计数增加
        printf("\n=== 开始处理第 %d 轮数据 ===\n", round);
        total_rounds++;  
    int current_process_size = (!disp_data->first_round_completed) ?   
                             (DATA_SIZE - OVERLAP_SIZE) : EFFECTIVE_SIZE;  
    
        
        // 1. 构建加速度数据
        if (!disp_data->first_round_completed) {
            // 读取完整2048个加速度数据
            for (int i = 0; i < DATA_SIZE; i++) {
                int pos = (disp_data->read_pos + i) % disp_data->buffer_size;
                calc_buffer_x[i] = disp_data->data_buffer_x[pos];
                calc_buffer_y[i] = disp_data->data_buffer_y[pos];
                calc_buffer_z[i] = disp_data->data_buffer_z[pos];
            }
            
            // 计算位移
            calculate_displacement(calc_buffer_x, result_buffer_x);
            calculate_displacement(calc_buffer_y, result_buffer_y);
            calculate_displacement(calc_buffer_z, result_buffer_z);
        
            memcpy(filtered_x, result_buffer_x, N * N_ * sizeof(float));
            memcpy(filtered_y, result_buffer_y, N * N_ * sizeof(float));
            memcpy(filtered_z, result_buffer_z, N * N_ * sizeof(float));
              // 对前2018个点进行降采样  
            process_downsample(logger, filtered_x, filtered_y, filtered_z,  
                      DATA_SIZE - OVERLAP_SIZE,  
                      (round - 1) * EFFECTIVE_SIZE,  
                      round, false);

   
            wave_params_t wave_params;  
            calculate_wave_parameters(  
                filtered_z,                           // 滤波后的Z轴位移数据  
                DATA_SIZE - OVERLAP_SIZE,             // 使用前2018个点  
                SAMPLE_RATE,                                  // 采样率  
                &wave_params,                         // 输出波浪参数  
                is_first_round,                       // 是否是第一轮  
                &prev_start_idx,                      // 上一轮最后一个上跨零点索引  
                &prev_max_value,                      // 上一轮的最大值  
                &prev_min_value ,                      // 上一轮的最小值  
                logger,                               // 传入logger 
                &half_hour_stats,
                0
            ); 
            
            // 只存储前2018个位移数据
            for (int i = 0; i < DATA_SIZE - OVERLAP_SIZE; i++) {
                float disp[3] = {result_buffer_x[i], result_buffer_y[i], result_buffer_z[i]};
                float filtered_disp[3] = {filtered_x[i], filtered_y[i], filtered_z[i]};
                int base_index = (round - 1) * EFFECTIVE_SIZE;
                log_displacement_data(logger, disp, filtered_disp, base_index + i, 0, round);
                total_points_saved++;
            }
            log_wave_parameters(logger, round, &wave_params); 

            // 保存最后30个加速度和位移数据供下一轮使用
            memcpy(disp_data->overlap_ax, 
                   calc_buffer_x + (DATA_SIZE - OVERLAP_SIZE), 
                   OVERLAP_SIZE * sizeof(float));
            memcpy(disp_data->overlap_ay, 
                   calc_buffer_y + (DATA_SIZE - OVERLAP_SIZE), 
                   OVERLAP_SIZE * sizeof(float));
            memcpy(disp_data->overlap_az, 
                   calc_buffer_z + (DATA_SIZE - OVERLAP_SIZE), 
                   OVERLAP_SIZE * sizeof(float));
            
            memcpy(disp_data->overlap_disp_x, 
                   filtered_x + (DATA_SIZE - OVERLAP_SIZE), 
                   OVERLAP_SIZE * sizeof(float));
            memcpy(disp_data->overlap_disp_y, 
                   filtered_y + (DATA_SIZE - OVERLAP_SIZE), 
                   OVERLAP_SIZE * sizeof(float));
            memcpy(disp_data->overlap_disp_z, 
                   filtered_z + (DATA_SIZE - OVERLAP_SIZE), 
                   OVERLAP_SIZE * sizeof(float));
                   disp_data->first_round_completed = true;  // 设置完成标志

                       // 更新全局偏移量
            global_data_offset += (DATA_SIZE - OVERLAP_SIZE);
            disp_data->first_round_completed = true;
            } else {

            // 创建临时缓冲区用于波形分析和降采样  
            float *wave_calc_buffer_x = (float *)malloc(EFFECTIVE_SIZE * sizeof(float));  
            float *wave_calc_buffer_y = (float *)malloc(EFFECTIVE_SIZE * sizeof(float));
            float *wave_calc_buffer = (float *)malloc(EFFECTIVE_SIZE * sizeof(float));  
             if (!wave_calc_buffer) {  
            // printf("Failed to allocate wave calculation buffer\n");  
            return NULL;  
             } 
            // printf("后续轮次处理(2018点)\n");
            // 使用上一轮保存的30个加速度作为本轮前30个
            memcpy(calc_buffer_x, disp_data->overlap_ax, OVERLAP_SIZE * sizeof(float));
            memcpy(calc_buffer_y, disp_data->overlap_ay, OVERLAP_SIZE * sizeof(float));
            memcpy(calc_buffer_z, disp_data->overlap_az, OVERLAP_SIZE * sizeof(float));
            
            // 读取新的2018个加速度数据
            for (int i = 0; i < EFFECTIVE_SIZE; i++) {
                int pos = (disp_data->read_pos + i) % disp_data->buffer_size;
                calc_buffer_x[OVERLAP_SIZE + i] = disp_data->data_buffer_x[pos];
                calc_buffer_y[OVERLAP_SIZE + i] = disp_data->data_buffer_y[pos];
                calc_buffer_z[OVERLAP_SIZE + i] = disp_data->data_buffer_z[pos];
            }
            
            // 计算位移
            calculate_displacement(calc_buffer_x, result_buffer_x);
            calculate_displacement(calc_buffer_y, result_buffer_y);
            calculate_displacement(calc_buffer_z, result_buffer_z);
            
            // // 高通滤波
            // highpass(result_buffer_x, DATA_SIZE, fps, 50, filtered_x);
            // highpass(result_buffer_y, DATA_SIZE, fps, 50, filtered_y);
            // highpass(result_buffer_z, DATA_SIZE, fps, 50, filtered_z);
            memcpy(filtered_x, result_buffer_x, N * N_ * sizeof(float));
            memcpy(filtered_y, result_buffer_y, N * N_ * sizeof(float));
            memcpy(filtered_z, result_buffer_z, N * N_ * sizeof(float));
            
            // 处理前30个点的加权平均
            for (int i = 0; i < OVERLAP_SIZE; i++) {
                float w1 = 1.0f - (float)i/(OVERLAP_SIZE-1);  // 上一轮权重
                float w2 = (float)i/(OVERLAP_SIZE-1);         // 本轮权重

                wave_calc_buffer_x[i] = w1 * disp_data->overlap_disp_x[i] + w2 * filtered_x[i]; 
                wave_calc_buffer_y[i] = w1 * disp_data->overlap_disp_y[i] + w2 * filtered_y[i]; 
                wave_calc_buffer[i] = w1 * disp_data->overlap_disp_z[i] + w2 * filtered_z[i]; 
                
            // 原始位移数据  
                float disp[3] = {result_buffer_x[i], result_buffer_y[i], result_buffer_z[i]}; 
                // 计算加权平均
                float avg_x = w1 * disp_data->overlap_disp_x[i] + w2 * filtered_x[i];
                float avg_y = w1 * disp_data->overlap_disp_y[i] + w2 * filtered_y[i];
                float avg_z = w1 * disp_data->overlap_disp_z[i] + w2 * filtered_z[i];
                
                
                // 存储加权平均后的前30个点
                float avg_disp[3] = {avg_x, avg_y, avg_z};
                int base_index = (round - 1) * EFFECTIVE_SIZE;
                log_displacement_data(logger, avg_disp, avg_disp, base_index + i, 1, round);
                total_points_saved++;
            }
             // 复制后续1988个点  
             // 复制后续1988个点的X轴数据  
        memcpy(wave_calc_buffer_x + OVERLAP_SIZE,  filtered_x + OVERLAP_SIZE, (EFFECTIVE_SIZE - OVERLAP_SIZE) * sizeof(float));
        memcpy(wave_calc_buffer_y + OVERLAP_SIZE,  filtered_y + OVERLAP_SIZE, (EFFECTIVE_SIZE - OVERLAP_SIZE) * sizeof(float));
        memcpy(wave_calc_buffer + OVERLAP_SIZE,  filtered_z + OVERLAP_SIZE,  (EFFECTIVE_SIZE - OVERLAP_SIZE) * sizeof(float)); 

        // 计算当前数据块的实际起始偏移量
        int64_t current_block_offset = global_data_offset - OVERLAP_SIZE;
                // 调用上跨零点函数  
        wave_params_t wave_params;  
        calculate_wave_parameters(  
            wave_calc_buffer,                     // 使用准备好的2018个连续点  
            EFFECTIVE_SIZE,                       // 2018个点  
            SAMPLE_RATE,  
            &wave_params,  
            is_first_round,  
            &prev_start_idx,  
            &prev_max_value,  
            &prev_min_value ,
            logger,
            &half_hour_stats  ,
            current_block_offset        // 当前数据块起始偏移量
        );  


   // 对完整的2018个连续点进行一次降采样  
    process_downsample(logger,  wave_calc_buffer_x,  wave_calc_buffer_y,  wave_calc_buffer, EFFECTIVE_SIZE,  (round - 1) * EFFECTIVE_SIZE,    round,  false);  
    log_wave_parameters(logger, round, &wave_params);
    // 释放临时缓冲区  
    free(wave_calc_buffer_x);  
    free(wave_calc_buffer_y);
    free(wave_calc_buffer);
     // 存储后续1988个点(31-2018)
    for (int i = OVERLAP_SIZE; i < DATA_SIZE - OVERLAP_SIZE; i++) {
        float disp[3] = {result_buffer_x[i], result_buffer_y[i], result_buffer_z[i]};
        float filtered_disp[3] = {filtered_x[i], filtered_y[i], filtered_z[i]};
        int base_index = (round - 1) * EFFECTIVE_SIZE;
        log_displacement_data(logger, disp, filtered_disp, base_index + i, 0, round);
        total_points_saved++;}
  
    
            // 保存最后30个加速度数据供下一轮使用
    memcpy(disp_data->overlap_ax, calc_buffer_x + (DATA_SIZE - OVERLAP_SIZE), OVERLAP_SIZE * sizeof(float));
    memcpy(disp_data->overlap_ay, calc_buffer_y + (DATA_SIZE - OVERLAP_SIZE), OVERLAP_SIZE * sizeof(float));
    memcpy(disp_data->overlap_az, calc_buffer_z + (DATA_SIZE - OVERLAP_SIZE), OVERLAP_SIZE * sizeof(float));

    // 保存最后30个位移数据供下一轮使用
    memcpy(disp_data->overlap_disp_x, filtered_x + (DATA_SIZE - OVERLAP_SIZE), OVERLAP_SIZE * sizeof(float));
    memcpy(disp_data->overlap_disp_y,  filtered_y + (DATA_SIZE - OVERLAP_SIZE),OVERLAP_SIZE * sizeof(float));
    memcpy(disp_data->overlap_disp_z, filtered_z + (DATA_SIZE - OVERLAP_SIZE), OVERLAP_SIZE * sizeof(float));
    // 更新全局偏移量，每次增加有效数据的大小
    global_data_offset += EFFECTIVE_SIZE;
        }
        printf("--第%d轮数据已经计算并写入缓存区---\n",round);
              // 记录结束处理时间
        clock_gettime(CLOCK_MONOTONIC, &end_processing);
        
        // 计算处理时间（毫秒）
        processing_duration_sec = (end_processing.tv_sec - start_processing.tv_sec) + 
                                (end_processing.tv_nsec - start_processing.tv_nsec) /  1000000000.0; 
        log_processing_time(round, processing_duration_sec);
        // 格式化统计信息并输出到串口
        snprintf(time_stats, sizeof(time_stats), 
                "[位移计算统计] 轮次:%d 数据处理时间:%.2f秒\n", 
                round, processing_duration_sec);
        //write_to_serial("/dev/ttymxc1", time_stats);
        manage_gps_power();//决定上电还是断电
 // 在所有数据处理完成后，更新状态之前添加文件切换检查  
        current_time = time(NULL);  
        if(is_half_hour_point(current_time) && (current_time - last_file_time>85)) {  

            // 更新当前处理时间
            current_processing_time = current_time;

            // 将time_t转换为可读字符串
            char time_str[64];
            struct tm *tm_info = localtime(&current_processing_time);
            strftime(time_str, sizeof(time_str), "%Y-%m-%d %H:%M:%S", tm_info);

            // 调用debug_print，传递字符串
            printf("[位移计算线程] 数据处理完成时间：\n");
            printf("%s\n",time_str);
            printf("[位移计算线程] 准备切换文件 \n");
            // 确保当前轮次的数据完全写入  
            if (logger->disp_file) {  
                fflush(logger->disp_file);  
                fsync(fileno(logger->disp_file));
            }  
            if (logger->disp_down_file) {  
                fflush(logger->disp_down_file);
                fsync(fileno(logger->disp_down_file));  
            }  
            printf("[位移计算线程] 文件已保存\n");
      // 保存当前（即将完成）的文件夹路径
           
                char date_path[512];
            snprintf(date_path, sizeof(date_path), "%s/%s",   
                    logger->base_path, logger->current_date);
            strncpy(completed_folder_path, date_path, strlen(date_path) );
            // completed_folder_path[sizeof(completed_folder_path) - 1] = '\0';
            // debug_print("[位移计算线程] 已完成的文件夹路径:");
            // debug_print(completed_folder_path);

            // 同步执行波特征统计(新增)
            calculate_half_hour_statistics(&half_hour_stats,logger);
            memset(&half_hour_stats, 0, sizeof(HalfHourStats));
            half_hour_stats.start_time = current_time;
            printf("[位移计算线程] 波特征统计完成\n");
    
            if (create_new_data_files(logger)) {  
                printf("[位移计算线程] 新创建的文件夹路径:");
                printf("%s\n",logger->current_folder);  // 打印新创建的文件夹路径
                  // 4. 通知谱分析线程
                pthread_mutex_lock(&file_mutex);
                strncpy(current_file_path, completed_folder_path, strlen(completed_folder_path) );

                file_ready = 1;
                printf("[位移计算线程] file_ready = 1\n");  // 调试输出
                printf("[位移计算线程] 新文件已创建，路径\n");  // 调试输出
                pthread_cond_signal(&file_ready_cond);
                pthread_mutex_unlock(&file_mutex);
                
                last_file_time = current_time;
            }  
            else {
                //debug_print("[位移计算线程] 创建新文件失败");
                printf("[位移计算线程] 创建新文件失败\n");
           }
        }  
     
        // 更新状态
        disp_data->ready = 0;
        disp_data->read_pos = (disp_data->read_pos + EFFECTIVE_SIZE) % disp_data->buffer_size;
        disp_data->count -= EFFECTIVE_SIZE;
        
        pthread_mutex_unlock(&disp_data->mutex);
        
      
    }
    // 清理资源
    free(calc_buffer_x);   // 
      
    free(filtered_x);
    free(filtered_y);
    free(filtered_z);
    free(overlap_disp_x);
    free(overlap_disp_y);
    free(overlap_disp_z);
    close_data_logger(logger);
    close_processing_log();
    
}
// 建议使用统一的时间管理
time_t get_aligned_time() {
    time_t now = time(NULL);
    return now - (now % 1800); // 对齐到半小时
}
// 读取降采样数据的函数

float** read_disp_down_data(const char* full_path, int* data_count) {
    char filename[512];
     snprintf(filename, sizeof(filename), "%s/disp_down.csv", full_path);

    FILE* file = fopen(filename, "r");
    if (!file) {
        perror("无法打开文件");
        return NULL;
    }

    // 读取文件行数以确定数据大小
    char line[5000];
    *data_count = 0;
    while (fgets(line, sizeof(line), file)) {
        (*data_count)++;
    }
    rewind(file);  // 重置文件指针到开头

     // 计算实际需要读取的数据量（128的倍数）
    int actual_count = (*data_count) - ((*data_count) % 128);  // 向下取到128的倍数
    if (actual_count == 0) {
        fclose(file);
        return NULL;  // 如果没有足够的数据，返回NULL
    }


   // 分配内存以存储位移数据
    float** disp_data = (float**)malloc(3 * sizeof(float*));  // 三个轴的数据
    for (int i = 0; i < 3; i++) {

        disp_data[i] = (float*)malloc(actual_count * sizeof(float));
    }
      // 读取数据
    int index = 0;
    while (fgets(line, sizeof(line), file) && index < actual_count) {
        float disp_x, disp_y, disp_z;
        sscanf(line, "%*d,%f,%f,%f", &disp_x, &disp_y, &disp_z);  // 读取 DispX, DispY, DispZ
        disp_data[0][index] = disp_x;  // DispX
        disp_data[1][index] = disp_y;  // DispY
        disp_data[2][index] = disp_z;  // DispZ
        index++;
    }

    fclose(file);
    *data_count = actual_count;//更新实际读取到的数据
    return disp_data;
}

// 获取当前时间并构建文件夹路径(改)
void get_current_folder_path(char* folder_path, size_t size) {
     pthread_mutex_lock(&path_mutex);
    time_t now = time(NULL);
    struct tm *timeinfo = localtime(&now);
    char timestamp[32];
    strftime(timestamp, sizeof(timestamp), "%Y%m%d_%H%M", timeinfo); // 格式化为 YYYYMMDD_HHMM

    snprintf(folder_path, size, "/mnt/tf/wave_data/%s", timestamp); // 构建文件夹路径
        pthread_mutex_unlock(&path_mutex);
}


// 在 dirspec 函数结束前或 spectrum_analysis_thread 中添加以下代码
void print_spectrum_results(SpectralMatrix *SMout) {
    printf("\n=== 方向谱分析结果 ===\n");
    
    // 1. 打印基本信息
    printf("频率点数: %d\n", SMout->freq_size);
    printf("方向点数: %d\n", SMout->dir_size);
    printf("X轴方向: %.2f度\n", SMout->xaxisdir);
    
    // 2. 打印频率数组（前5个点）
    printf("\n频率数组 (Hz) [前5个点]:\n");
    for (int i = 0; i < 5 && i < SMout->freq_size; i++) {
        printf("%.4f ", SMout->freqs[i]);
    }
    printf("...\n");
    
    // 3. 打印方向数组（前5个点）
    printf("\n方向数组 (度) [前5个点]:\n");
    for (int i = 0; i < 5 && i < SMout->dir_size; i++) {printf("%.2f ", SMout->dirs[i]);
    }
    printf("...\n");
   
     // 发送能量密度矩阵到串口
    char buffer[1024];  // 定义一个足够大的缓冲区
    int offset = 0;     // 缓冲区的当前位置
    // 4. 打印能量密度矩阵（5x5的样本）
    printf("\n能量密度矩阵 [5x5样本]:\n");
    printf("     方向→\n频率↓\n");
    for (int i = 0; i < 5 && i < SMout->freq_size; i++) {
        for (int j = 0; j < 5 && j < SMout->dir_size; j++) {
            printf("%.2e+%.2ei  ", 
                   SMout->S[i][j].real,
                   SMout->S[i][j].imag);
        }
        printf("\n");
    }
    // 格式化能量密度矩阵为字符串
    for (int i = 0; i < SMout->freq_size; i++) {
        for (int j = 0; j < SMout->dir_size; j++) {
            offset += snprintf(buffer + offset, sizeof(buffer) - offset, "%.2e+%.2ei, ",
                               SMout->S[i][j].real, SMout->S[i][j].imag);
            if (offset >= sizeof(buffer) - 50) {  // 确保有足够的空间
                //write_to_serial("/dev/ttymxc2", buffer);
                offset = 0;  // 重置缓冲区
            }
        }
    }

    // 发送缓冲区中剩余的数据
    if (offset > 0) {
        //write_to_serial("/dev/ttymxc2", buffer);
    }
    
    // 5. 打印最大能量位置
    float max_energy = 0;
    int max_freq_idx = 0;
    int max_dir_idx = 0;
    
    for (int i = 0; i < SMout->freq_size; i++) {
        for (int j = 0; j < SMout->dir_size; j++) {
           float energy = SMout->S[i][j].real * SMout->S[i][j].real + 
                          SMout->S[i][j].imag * SMout->S[i][j].imag;
            if (energy > max_energy) {
                max_energy = energy;
                max_freq_idx = i;
                max_dir_idx = j;
            }
        }
    }
    
    printf("\n最大能量点:\n");
    printf("频率: %.4f Hz\n", SMout->freqs[max_freq_idx]);
    printf("方向: %.2f 度\n", SMout->dirs[max_dir_idx]);
    printf("能量: %.2e+%.2ei\n", 
           SMout->S[max_freq_idx][max_dir_idx].real,
           SMout->S[max_freq_idx][max_dir_idx].imag);
    
    printf("\n=== 打印完成 ===\n");
}

// 添加函数声明
void write_spectrum_results(DataLogger *logger, SpectralMatrix *SMout);

void write_spectrum_results(DataLogger *logger, SpectralMatrix *SMout) {
    if (!logger )
    {
        printf("错误: Logger未初始化\n");
    
    }
    if (!logger->spectrum_results_file)
    {
       printf("错误: 谱分析结果文件未打开\n");
    
    }
    if (!SMout)
    {
        printf("错误: SMout为空\n");
        
    }

    // 获取当前时间戳
    time_t now;
    struct tm *timeinfo;
    char timestamp[32];
    time(&now);
    timeinfo = localtime(&now);
    strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", timeinfo);

    printf("开始写入谱分析结果\n");
    printf("频率点数: %d, 方向点数: %d\n", SMout->freq_size, SMout->dir_size);
// 写入头部信息
    fprintf(logger->spectrum_results_file, "%f\n", SMout->xaxisdir); // x轴方向
    fprintf(logger->spectrum_results_file, "%d\n", SMout->freq_size); // 频率分组数
    fprintf(logger->spectrum_results_file, "%d\n", SMout->dir_size); // 方向分组数

    // 写入频率列表
    for (int i = 0; i < SMout->freq_size; i++) {
        fprintf(logger->spectrum_results_file, "%f\n", SMout->freqs[i]);
    }

    // 写入方向列表
    for (int i = 0; i < SMout->dir_size; i++) {
        fprintf(logger->spectrum_results_file, "%f\n", SMout->dirs[i]);
    }
     printf(" 写入方向列表成功\n");
    // 写入结束标记
    fprintf(logger->spectrum_results_file, "999\n");

    // 写入频谱密度矩阵
    for (int i = 0; i < SMout->freq_size; i++) {
        for (int j = 0; j < SMout->dir_size; j++) {
            if (fprintf(logger->spectrum_results_file, "%f\n", SMout->S[i][j].real) < 0) {
                printf("错误: 写入谱分析结果失败\n");
                return;
            }
           //printf(" //写入谱分析结果成功\n");
        }
    }
  
    printf(" 写入谱分析结果成功\n");
    // 确保数据写入磁盘
    fflush(logger->spectrum_results_file);
    fsync(fileno(logger->spectrum_results_file));
    printf("谱分析结果写入完成\n");

}

// 辅助函数：检查文件是否就绪
bool is_file_ready(const char* filename) {
    struct stat st;
    if (stat(filename, &st) == 0) {
        // 文件存在且大小大于0
        return st.st_size > 0;
    }
    return false;
}

void free_spectral_matrix(SpectralMatrix* SMout, int nfft_half) {
    if (SMout) {
        if (SMout->S) {
            for (int i = 0; i < nfft_half; i++) {
                if (SMout->S[i]) {
                    free(SMout->S[i]);
                }
            }
            free(SMout->S);
            SMout->S = NULL;
        }
        if (SMout->freqs) {
            free(SMout->freqs);
            SMout->freqs = NULL;
        }
        if (SMout->dirs) {
            free(SMout->dirs);
            SMout->dirs = NULL;
        }
    }
}

// 添加内存管理相关的辅助函数
void init_spectral_matrix(SpectralMatrix* SMout, EstimationParams* EP) {
    SMout->S = (Complex**)malloc(EP->nfft/2 * sizeof(Complex*));
    if (!SMout->S) {
        printf("Failed to allocate SMout->S\n");
        return;
    }
    
    for (int i = 0; i < EP->nfft/2; i++) {
        SMout->S[i] = (Complex*)malloc(EP->dres * sizeof(Complex));
        if (!SMout->S[i]) {
            printf("Failed to allocate SMout->S[%d]\n", i);
            // 清理已分配的内存
            for (int j = 0; j < i; j++) {
                free(SMout->S[j]);
            }
            free(SMout->S);
            SMout->S = NULL;
            return;
        }
    }
    
    SMout->freqs = (float*)malloc(EP->nfft/2 * sizeof(float));
    SMout->dirs = (float*)malloc(EP->dres * sizeof(float));
    
    if (!SMout->freqs || !SMout->dirs) {
        printf("Failed to allocate SMout freqs/dirs\n");
        free_spectral_matrix(SMout, EP->nfft/2);
        return;
    }
    
    SMout->freq_size = EP->nfft/2;
    SMout->dir_size = EP->dres;
    SMout->xaxisdir = 90.0;
    strcpy(SMout->funit, "Hz");
    strcpy(SMout->dunit, "deg");
}


void cleanup_instrument_data(InstrumentData* ID) {
    if (ID) {
        if (ID->data) {
            for (int i = 0; i < ID->szd; i++) {
                if (ID->data[i]) {
                    free(ID->data[i]);
                }
            }
            free(ID->data);
            ID->data = NULL;
        }
        
        if (ID->layout) {
            for (int i = 0; i < 3; i++) {
                if (ID->layout[i]) {
                    free(ID->layout[i]);
                }
            }
            free(ID->layout);
            ID->layout = NULL;
        }
    }
}
 char last_processed_folder[512] = {0};  // 修改为静态变量

//新增设备号配置函数
int read_device_id(const char *file_path, short *device_id) {
    FILE *file = fopen(file_path, "r");
    if (!file) {
        perror("无法打开配置文件");
        //
        return -1;
    }

    char line[256];
    while (fgets(line, sizeof(line), file)) {
        if (strncmp(line, "DeviceID=", 9) == 0) {
            // 解析设备号
            // sscanf(line + 9, "%x", device_id);  // 读取十六进制数
            // 修改为读取十进制数并转为short
            *device_id =(short)atoi(line + 9);
            fclose(file);
            return 0;
            printf("[谱分析线程] 成功读取设备号:\n");
        
        }
    }

    fclose(file);
    fprintf(stderr, "未找到设备号配置\n");
 
    return -1;
}


// 获取当前时间戳，为了打包发送
time_t get_current_timestamp() {
    time_t now;
    time(&now);
    return now; // 返回秒级时间戳
}

// 串口发送包
void uart_send_data(unsigned char *data, int length) {

    int fd1 = open(LOCATION_4G_SERIAL_PORT, O_RDWR | O_NOCTTY);
    if(fd1<0){

        perror("打开4G串口失败");
    }
   if( set_uart(fd1, 115200 ,8,'N', 1)){

    perror("配置4G串口失败");
    close(fd1);
   };//GAI 115200
    int total_written = 0;
    while (total_written < length) {
        int written = write(fd1, data + total_written, length - total_written);
        if (written < 0) {
            printf("不能写进串口\n");
            perror("写入串口失败");
            break;
        }
        total_written 
+= written;
    }

    printf("发送包成功\n");
}

 // 打包发送频谱数据函数
void send_spectrum_data(SpectralMatrix *SMout, short device_id) {
    if (!SMout) {
        fprintf(stderr, "错误: SMout为空\n");
        printf("SMout为空\n");
        return;
    }
    sleep(100);
    printf("4G模块发送前上电...\n");
    gpio_ctrl(GPIO_232_CRTL, "value", "1");  // GPIO3输出高电平上电
    sleep(40);  // 等待30秒稳定时间
    // 获取当前时间戳
    // time_t Unix_Sec = get_current_timestamp();
    // 使用数据处理完成的前30分钟的时间作为数据包时间戳
    time_t data_timestamp = current_processing_time - 1800;
    

    // // 使用与位移计算线程相同的时间对齐函数，强制转换为某个时间点
    // time_t Unix_Sec = get_aligned_time();
    // 发送频谱数据
    for (int i = 0; i < SMout->freq_size; i++) {
        unsigned char sendBuf[2048];//发送缓冲区增大
        int num = 0; // 数据包长度计数器
        // 清除 sendBuf
        memset(sendBuf, 0, sizeof(sendBuf));//新增防止缓存区出现问题。
        // 数据包头
        sendBuf[num++] = 0xFF;
        sendBuf[num++] = 0xFF;
        sendBuf[num++] = 0x02;
        sendBuf[num++] = 0xDD;
          // 设备号
        sendBuf[num++] = (device_id >> 8) & 0xFF;  // 高字节
        sendBuf[num++] = device_id & 0xFF;         // 低字节
        // 包号
        sendBuf[num++] = i + 1;
        // 时间戳
        unsigned char *cBuf = (unsigned char *) &data_timestamp;
        for (int m = 0; m < 4; m++) {
            sendBuf[num++] = cBuf[3 - m];
        }
        // 频谱数据
        for (int j = 0; j < SMout->dir_size; j++) {
            cBuf = (unsigned char *) & (SMout->S[i][j].real);
            for (int m = 0; m < 4; m++) {
                sendBuf[num++] = cBuf[m];
            }
        }

        // 数据包尾
        sendBuf[num++] = 0xFF;
        sendBuf[num++] = 0xFE;
        sendBuf[num++] = 0x0D;
        sendBuf[num++] = 0x0A;

        // // 发送数据
         uart_send_data(sendBuf, num);
        //debug_print_hex(sendBuf, num); 
    }
    sleep(40);  // 确保数据传输完成
    gpio_ctrl(GPIO_232_CRTL, "value", "0");  // 断电
    printf("4G模块发送完成，已断电...\n");
}
// 修改后的谱分析线程函数
void* spectrum_analysis_thread(void* arg) {
    printf("[谱分析线程] 启动");
      // 读取设备号（不变）
      //修改为short类型
    short device_id;
    if (read_device_id("/home/data/config.txt", &device_id) != 0) {
        return NULL;  // 读取失败，退出线程
    }
    DataLogger *logger = init_data_logger();  // 初始化 DataLogger

    if (!logger) {printf("[谱分析线程] 初始化 DataLogger 失败");
        return NULL;
    }
     // 2. 创建必要的文件 - 添加这一步
    if (!create_new_data_files(logger)) {
        printf("[谱分析线程] 创建数据文件失败");
        free(logger);
        return NULL;
    }
    printf("[谱分析线程] 初始化 DataLogger 成功");
    // 初始化参数结构体
    InstrumentData ID = {0};
    SpectralMatrix SM = {0};
    EstimationParams EP = {
        .dres = 180,
        .nfft =64 , //256修改为128，这样SMout是64*180，需要对讲采样的2HZ数据进行128倍处理
        .noverlap = 0,
        .iter = 100,
        .method = "DFTM",
        .smooth = "ON"
    };
    SpectralMatrix SMout = {0};
    printf("[谱分析线程] 成功初始化参数结构体");

    while (1) {
        
        // 等待文件就绪信号
        pthread_mutex_lock(&file_mutex);
        while (!file_ready) {
            printf("[谱分析线程] 等待新文件...");
            pthread_cond_wait(&file_ready_cond, &file_mutex);
        }

        char current_folder[512] = {0};
        printf("[谱分析线程] 打印收到的文件路径\n");
        printf("s%\n",current_file_path);

       // 安全复制路径
        strncpy(current_folder, current_file_path, strlen(current_file_path));
    
        file_ready = 0;
        printf("[谱分析线程] file_ready = 0");
        pthread_mutex_unlock(&file_mutex);
        printf("[谱分析线程] 准备读取文件\n");

         // 打印当前文件夹路径进行调试
        printf("[谱分析线程] 当前文件夹路径:");
        printf("%s\n",current_folder);
        printf("[谱分析线程] 上次处理的文件夹路径:");
        printf("%s\n",last_processed_folder);

         // 检查路径是否为空
        if (strlen(current_folder) == 0) {
            printf("[谱分析线程] 错误：收到空路径");
            continue;
        }

        // 检查是否是新的文件夹
        if (strcmp(current_folder, last_processed_folder) == 0) {
           printf("[谱分析线程] 警告：重复处理相同文件夹");
            continue;
        }
        else{
            printf("[谱分析线程] 新文件夹，开始处理");
             // 关闭现有文件
            if (logger->spectrum_results_file) {
            fflush(logger->spectrum_results_file);
            fsync(fileno(logger->spectrum_results_file));
            fclose(logger->spectrum_results_file);
            logger->spectrum_results_file = NULL; }
             
        // 创建新的谱分析结果文件
        char spectrum_path[1024];
        snprintf(spectrum_path, sizeof(spectrum_path), "%s/spectrum_results.csv", current_folder);
        
        // 打开新文件
        logger->spectrum_results_file = fopen(spectrum_path, "w");
        if (!logger->spectrum_results_file) {
            printf("[谱分析线程] 错误：无法创建谱分析结果文件");
            // 尝试创建目录（如果需要）
            char dir_cmd[1024];
            snprintf(dir_cmd, sizeof(dir_cmd), "mkdir -p %s", current_folder);
            system(dir_cmd);
            
            // 再次尝试
            logger->spectrum_results_file = fopen(spectrum_path, "w");
            if (!logger->spectrum_results_file) {
                printf("[谱分析线程] 第二次尝试创建文件失败，跳过处理");
                continue;
            }
        }
        printf("[谱分析线程] 成功创建谱分析结果文件: ");
        printf("%s\n",spectrum_path);
        }
        
   // 确保降采样文件存在且可读
         char filename[1024];
        snprintf(filename, sizeof(filename), "%s/disp_down.csv", current_folder);
          if (access(filename, R_OK) != 0) {
            printf("[谱分析线程] 错误：无法访问文件 ");
            continue;
        }

        printf("[谱分析线程] 开始读取数据文件");
        // 读取数据
        int data_count;
       
        float** disp_data = read_disp_down_data(current_folder, &data_count);

        if (!disp_data || data_count <= 0) {
            printf("[谱分析线程] 错误：文件夹不存在");
            continue;
        }

        printf("[谱分析线程] 成功读取位移数据");

        // 初始化 ID 结构体
        ID.ndat = data_count;
        ID.szd = 3;
        ID.fs = 2;
        ID.depth = 65.0;
        printf("[谱分析线程] 成功初始化ID结构体");
        // 分配并设置 ID.data
        ID.data = (float**)malloc(ID.szd * sizeof(float*));
        if (!ID.data) {
            printf("[谱分析线程] Failed to allocate ID.data");
            goto cleanup;
        }else{
            printf("[谱分析线程] 成功分配ID.data");
        }   
        
        for (int i = 0; i < ID.szd; i++) {
            ID.data[i] = (float*)malloc(ID.ndat * sizeof(float));
            if (!ID.data[i]) {
                printf("[谱分析线程] Failed to allocate ");
                goto cleanup;
            }else{
                printf("[谱分析线程] 成功分配ID.data");
            }
            for (int j = 0; j < ID.ndat; j++) {
                ID.data[i][j] = (float)disp_data[i][j];
            }
        }

        // 分配并设置 ID.layout
        ID.layout = (float**)malloc(3 * sizeof(float*));
        if (!ID.layout) {
            printf("Failed to allocate ID.layout\n");
            goto cleanup;
        }else{
            printf("[谱分析线程] 成功分配ID.layout");
        }
        
        for (int i = 0; i < 3; i++) {
            ID.layout[i] = (float*)malloc(ID.szd * sizeof(float));
            if (!ID.layout[i]) {
                printf("[谱分析线程] Failed to allocate ");
                goto cleanup;
            }else{
                printf("[谱分析线程] 成功分配ID.layout");
            }
            for (int j = 0; j < ID.szd; j++) {
                ID.layout[i][j] = (i == 2) ? ID.depth : 0.0;
            }
        }

        // 初始化 SMout
        init_spectral_matrix(&SMout, &EP);
        if (!SMout.S || !SMout.freqs || !SMout.dirs) {
            printf("[谱分析线程] Failed to initialize SMout");
            goto cleanup;
        }else{
            printf("[谱分析线程] 成功初始化SMout");
        }

        // 调用谱分析函数
        dirspec(&ID, &SM, &EP, &SMout);
        printf("[谱分析线程] 成功调用dirspec");

    //打包发送（在SMout中拿到他的Smout.s数据）
    // 发送频谱数据
        //send_spectrum_data(&SMout, device_id, debug_fd);
        send_spectrum_data(&SMout, device_id);
        // 打印和保存结果
        print_spectrum_results(&SMout);
        printf("[谱分析线程] 成功打印结果");
           // 将结果写入文件
        write_spectrum_results(logger, &SMout);  // 添加这一行
        printf("[谱分析线程] 成功写入文件");
        printf("[谱分析线程] 完成谱分析处理");


        // 确保数据处理成功后才更新
        strncpy(last_processed_folder, current_folder, sizeof(last_processed_folder) - 1);
        // debug_print("[谱分析线程] 已更新处理文件夹路径");

          // 发送数据到串口
        char buffer[1024];
        int offset = 0;
        
        // 格式化能量密度矩阵为字符串并发送到串口
        for (int i = 0; i < SMout.freq_size; i++) {
            for (int j = 0; j < SMout.dir_size; j++) {
                offset += snprintf(buffer + offset, sizeof(buffer) - offset, 
                                 "%.2e, ",
                                 SMout.S[i][j].real);
                if (offset >= sizeof(buffer) - 50) {
                    //write_to_serial("/dev/ttymxc2", buffer);
                    offset = 0;
                }
            }
        }
        printf("[谱分析线程] 开始发送剩余数据");  // 调试输出
        // 发送剩余数据
        if (offset > 0) {
            //write_to_serial("/dev/ttymxc2", buffer);
        }

cleanup:
        printf("[谱分析线程] 开始清理资源");  // 调试输出
        // 清理资源
        cleanup_instrument_data(&ID);
        free_spectral_matrix(&SMout, EP.nfft/2);
        
        if (disp_data) {
            for (int i = 0; i < 3; i++) {
                if (disp_data[i]) {
                    free(disp_data[i]);
                }
            }
            free(disp_data);
        }
        // debug_print("[谱分析线程] 成功清理资源");
        // strcpy(last_processed_folder, current_folder);
        
    }
// 清理 DataLogger
    if (logger) {
        if (logger->spectrum_results_file) {
            fclose(logger->spectrum_results_file);
        }
        free(logger);
    }
    return NULL;
    }
//volatile int  gps_thread_running = 1;

void* gps_thread_func(void* arg) {
        printf("GPS thread started.\n");
        int gps_fd_local = -1; 
        // --- 2. 数据读取与解析 ---
        char read_buf[1024];
        static char full_buffer[4096] = {0}; // 静态局部变量，用于跨次read拼接数据
        static size_t total_bytes = 0;
        gps_fd_local = open(LOCATION_SERIAL_PORT, O_RDONLY | O_NOCTTY); 
        if (set_uart(gps_fd_local, 115200, 8, 'N', 1) < 0) { 
                    perror("GPS Thread: Failed to configure GPS serial port");
                    close(gps_fd_local);
                    gps_fd_local = -1;
                
                }
        printf("GPS线程：执行首次主动上电以校准系统时间...\n");
        //得先导出来
        gpio_ctrl(GPIO1_DW, "value", "1"); // 主动上电
        printf("GPS模块已上电，等待稳定...\n");
        //sleep(100);
        
        bool is_calibrated_in_this_phase = false;
        time_t calibration_start_time = time(NULL);

             // 循环尝试校准，超时时间为5分钟 (300秒)
        while (time(NULL) - calibration_start_time < 300) {

           int readbytes = read(gps_fd_local, read_buf, sizeof(read_buf) - 1);
     
             if (readbytes > 0) {
                 // 将读取到的新数据追加到 full_buffer
                 read_buf[readbytes] = '\0';
                 if (total_bytes + readbytes >= sizeof(full_buffer)) {
                     fprintf(stderr, "GPS线程：拼接缓冲区溢出! 重置缓冲区。\n");
                     total_bytes = 0;
             }
                memcpy(full_buffer + total_bytes, read_buf, readbytes);
            total_bytes += readbytes;
            full_buffer[total_bytes] = '\0';
     
                 char* next_line_start = full_buffer;
                 char* line_end;
     
                 while ((line_end = strchr(next_line_start, '\n')) != NULL) {
                     *line_end = '\0';
                 char* line = next_line_start;
     
                     if (strstr(line, "$BDRMC")) {
                         GPS_Data temp_data = {0};
                  time_t utc_time_seconds = parse_rmc(line, &temp_data);

                         if (temp_data.valid) {
                             // 1. 执行首次系统时间校准
                             calibrate_system_time(utc_time_seconds);
                             is_calibrated_in_this_phase = true;
                             printf("GPS线程：首次时间校准成功！\n");
     
                             // 2. 更新全局数据
                             pthread_mutex_lock(&gps_data_mutex);
                            global_gps_data = temp_data;
                             pthread_mutex_unlock(&gps_data_mutex);
     
                             pthread_mutex_lock(&utc_time_mutex);
                             last_utc_time_seconds = utc_time_seconds;
                             utc_time_valid = true;
                           pthread_mutex_unlock(&utc_time_mutex);
     
                            // 3. 发送信号通知主线程
                             pthread_mutex_lock(&time_calib_mutex);
                             if (!initial_time_calibrated) {
                                 initial_time_calibrated = true;
                                 pthread_cond_signal(&time_calib_cond);
                             }
                            pthread_mutex_unlock(&time_calib_mutex);
     
                             // 4. 跳出内层while循环
                             break;
                         }
                     }
                     next_line_start = line_end + 1;
                 }
     
                size_t remaining_len = strlen(next_line_start);
                if (remaining_len > 0 && next_line_start != full_buffer) {
                     memmove(full_buffer, next_line_start, remaining_len);
                }
                 total_bytes = remaining_len;
                 full_buffer[total_bytes] = '\0';
     
                 if (is_calibrated_in_this_phase) {
                     break;
                 }
             } else {
                 // 读取出错或无数据
                 perror("GPS线程(首次校准)：读取串口时出错或无数据");
                 usleep(200000);
             }
        }
        
    
        gpio_ctrl(GPIO1_DW, "value", "0"); // 任务完成，下电
        printf("GPS线程：首次校准任务完成，模块已下电。\n");
    
        // 容错处理：如果超时，也必须通知主线程
        if (!is_calibrated_in_this_phase) {
            printf("警告：GPS首次校准超时！程序将使用当前系统时间继续...\n");
            pthread_mutex_lock(&time_calib_mutex);
            if (!initial_time_calibrated) {
                initial_time_calibrated = true;
                pthread_cond_signal(&time_calib_cond);
            }
            pthread_mutex_unlock(&time_calib_mutex);
        }
    
        /*****************************************************************
         * 阶段 2: 进入常规工作模式，被动等待通知
         *****************************************************************/
        printf("GPS线程：进入常规工作模式，等待电源控制信号...\n");

        // 线程主循环
        while (gps_thread_running) {
            // --- 1. 自动重连逻辑 ---

        pthread_mutex_lock(&gps_power_mutex);
        while (!gps_powered_on && gps_thread_running) {
            // GPS未上电，先关闭可能打开的串口
            if (gps_fd_local >= 0) {
                close(gps_fd_local);
                gps_fd_local = -1;
                printf("GPS线程: GPS已断电，关闭串口\n");
            }
            // 等待GPS上电信号（非阻塞等待）
            pthread_cond_wait(&gps_power_cond, &gps_power_mutex);
        }
        pthread_mutex_unlock(&gps_power_mutex);
           // 检查线程是否需要退出
        if (!gps_thread_running) {
            break;
        }
        gpio_ctrl(GPIO1_DW, "value", "1");  // 上电
        printf("GPS线程: GPS已上电，等待40秒稳定...\n");
        //sleep(40);  // 40秒延迟（在GPS线程内，不影响位移计算）
    
            if (gps_fd_local < 0) {
                gps_fd_local = open(LOCATION_SERIAL_PORT, O_RDONLY | O_NOCTTY); // 只读模式
                if (gps_fd_local < 0) {
                    perror("GPS Thread: Cannot open GPS serial port. Retrying in 5 seconds...");
                    sleep(5); // 等待5秒后重试
                    continue; // 继续下一次循环
                }
                if (set_uart(gps_fd_local, 115200, 8, 'N', 1) < 0) { 
                    perror("GPS Thread: Failed to configure GPS serial port");
                    close(gps_fd_local);
                    gps_fd_local = -1;
                    sleep(5);
                    continue;
                }
                printf("GPS Thread: Serial port %s opened and configured successfully.\n", LOCATION_SERIAL_PORT);
            }
            
            
    
            int readbytes = read(gps_fd_local, read_buf, sizeof(read_buf) - 1);
    
            if (readbytes > 0) {
                read_buf[readbytes] = '\0';
    
                // 检查拼接后的缓冲区是否会溢出
                if (total_bytes + readbytes >= sizeof(full_buffer)) {
                    fprintf(stderr, "GPS Thread: Full buffer overflow! Resetting buffer.\n");
                    total_bytes = 0; // 清空
                }
                // 拼接新数据
                memcpy(full_buffer + total_bytes, read_buf, readbytes);
                total_bytes += readbytes;
                full_buffer[total_bytes] = '\0';
    
                char* next_line_start = full_buffer;
                char* line_end;
                
                // 循环处理缓冲区中所有完整的行
                while ((line_end = strchr(next_line_start, '\n')) != NULL) {
                    *line_end = '\0'; // 将换行符替换为字符串结束符，得到一行
                    char* line = next_line_start;
    
                    if ( strstr(line, "$BDRMC")) {
                        GPS_Data temp_data = {0}; // 使用局部临时变量
                        time_t utc_time_seconds = parse_rmc(line, &temp_data);
    
                        if (temp_data.valid) {
                            // 更新全局变量
                            pthread_mutex_lock(&gps_data_mutex);
                            global_gps_data = temp_data; // 结构体直接拷贝
                            pthread_mutex_unlock(&gps_data_mutex);
                            
                            // printf("GPS Thread: Parsed valid RMC sentence. Time: %02d:%02d:%02d\n", temp_data.hour, temp_data.minute, temp_data.seconds);
                            pthread_mutex_lock(&utc_time_mutex);
                            last_utc_time_seconds = utc_time_seconds;
                            utc_time_valid = true;
                            pthread_mutex_unlock(&utc_time_mutex);

                            // 每30分钟校准时间
                            // time_t now = time(NULL);
                            // if (difftime(now, last_calibration) >= 1800) { // 1800秒 = 30分钟
                            //     calibrate_system_time(utc_time_seconds);
                            //     last_calibration = now;
                            // }
                        }
                    }
                    next_line_start = line_end + 1; // 准备处理下一行
                }
                
                // 将缓冲区中剩余的不完整数据移到开头
                size_t remaining_len = strlen(next_line_start);
                if (remaining_len > 0 && next_line_start != full_buffer) {
                    memmove(full_buffer, next_line_start, remaining_len);
                }
                total_bytes = remaining_len;
                full_buffer[total_bytes] = '\0';
    
            } else if (readbytes == 0) {
                // 没有读到数据，短暂休眠
                usleep(100000); // 100ms
            } else {
                // 读取出错
                perror("GPS Thread: read() error");
                close(gps_fd_local);
                gps_fd_local = -1; // 标记文件描述符失效，以便下次循环时重连
                sleep(1);
            }
        }
    
        // --- 3. 线程退出清理 ---
        if (gps_fd_local >= 0) {
            close(gps_fd_local);}

        printf("GPS thread finished.\n");
        return NULL;
    }
// 添加等待函数
void wait_for_start_time() {
    time_t now = time(NULL);
    struct tm *tm = localtime(&now);
    
    // 计算下一个整点或半点
    if (tm->tm_min >= 30) {
        tm->tm_min = 0;
        tm->tm_hour += 1;
    } else {
        tm->tm_min = 30;
    }
    tm->tm_sec = 0;
    
    time_t start_time = mktime(tm);
    
    // 打印等待信息
    char current_time[64], target_time[64];
    strftime(current_time, sizeof(current_time), "%Y-%m-%d %H:%M:%S", localtime(&now));
    strftime(target_time, sizeof(target_time), "%Y-%m-%d %H:%M:%S", localtime(&start_time));
    printf("程序启动时间：");
    printf("%s\n",current_time);
    printf("等待到达时间点：");
    printf("%s\n",target_time);
    // 等待到达启动时间点
    while (time(NULL) < start_time) {
        usleep(1000);
    }
    
    printf("到达时间点，程序开始运行");
}
int main() {

    sleep(3);
    char log_path[256];

    // 1. 智能选择路径 (防崩溃机制)
    if (check_mount_point("/mnt/tf")) {
        // 只有在挂载成功时，才往卡里写
        snprintf(log_path, sizeof(log_path), "/mnt/tf/wave_test_log.txt");
    } else {
        snprintf(log_path, sizeof(log_path), "/home/data/wave_fallback_log.txt");
        // 确保目录存在
        mkdir("/home/data", 0777);
    }

    if (freopen(log_path, "a", stdout) == NULL) {
        perror("重定向 stdout 失败");

    } else {
        freopen(log_path, "a", stderr);
    }

    // 3. 禁用缓冲 (关键)
    setbuf(stdout, NULL);
    setbuf(stderr, NULL);

    downdisp_output_serial_init();
    BD_output_serial_init();
    RS485_serial_init();
    if (geteuid() != 0) {
        fprintf(stderr, "警告：非root用户运行，时间校准功能将失效\n");
    }
    gpio_init();
    init_tx_queue(); // 初始化降采样数据发送缓冲区
     // 2. 创建并仅启动GPS线程
    printf(">>> 主程序：启动GPS线程进行首次校时...\n");
   //创建gps线程
    pthread_t gps_tid;
      if(pthread_create(&gps_tid, NULL, gps_thread_func, NULL)!=0){
        perror("创建GPS解析线程失败");
        return -1;
      }
      printf("创建GPS线程成功\n");
      // 3. 等待GPS校准完成的信号
        printf(">>> 主程序：等待GPS校准完成...\n");
       pthread_mutex_lock(&time_calib_mutex);
       while (!initial_time_calibrated) {
           pthread_cond_wait(&time_calib_cond, &time_calib_mutex);
        }
        pthread_mutex_unlock(&time_calib_mutex);
        printf(">>> 主程序：收到校准信号，准备对齐时间...\n");

   // 添加等待函数，等到整点或半点才开始
   //wait_for_start_time();

 
    int fd = open(JY901_SERIAL_PORT, O_RDWR | O_NOCTTY | O_NDELAY);//UART5.传感器
    if (fd == -1) {
        perror("无法打开串口设备");
        printf(" 无法打开串口设备");
        return -1;
    }

    printf("成功打开串口\n");
    fcntl(fd, F_SETFL, 0);

    if (set_uart(fd, 115200, 8, 'N', 1) < 0) {
        perror("串口配置失败");
        close(fd);
        return -1;
    }
    printf("成功配置串口\n");
    SharedBuffer sb;
    init_buffer(&sb);

   
    // ThreadArgs args = { .sb = sb, .fd = fd };

    // 在main函数中初始化位移数据结构  
    displacement_data_t disp_data = {
        .buffer_size = DATA_SIZE * 4,  // 确保缓冲区足够大
        .write_pos = 0,
        .read_pos = 0,
        .count = 0,
        .ready = 0,
        .has_overlap = false,  // 初始没有overlap数据
        .first_round_completed = false,  // 新增：标记第一轮是否完成
    };
    
    // 初始化互斥锁和条件变量
    pthread_mutex_init(&disp_data.mutex, NULL);
    pthread_cond_init(&disp_data.cond, NULL);
    
    // 分配缓冲区

    disp_data.data_buffer_x = (float *)malloc(disp_data.buffer_size * sizeof(float));
    disp_data.data_buffer_y = (float *)malloc(disp_data.buffer_size * sizeof(float));
    disp_data.data_buffer_z = (float *)malloc(disp_data.buffer_size * sizeof(float));

    if (!disp_data.data_buffer_x || !disp_data.data_buffer_y || !disp_data.data_buffer_z) {  
      printf("内存分配失败\n");
              return -1;  
    }  

    // 初始化线程参数  
    ThreadArgs args = {  
        .sb = sb,  
        .fd = fd,  
        .disp_data = &disp_data  // 传递位移数据结构的地址  
    };  

    // 检查内存分配  
    if (!disp_data.data_buffer_x || !disp_data.data_buffer_y || !disp_data.data_buffer_z) {  
        perror("Failed to allocate displacement buffers");  
        // 清理已分配的资源  
        return -1;  
    }  
    if (init_processing_log() != 0) {
        printf("警告：处理时间日志初始化失败（不影响主流程）\n");
    }
    // 创建位移计算线程  
    pthread_t disp_thread;  
    pthread_create(&disp_thread, NULL, displacement_thread, &disp_data);  
   
    pthread_t prod, cons;
    if (pthread_create(&prod, NULL, producer, &args) != 0) {
        perror("创建生产者线程失败");
        close(fd);
        return -1;
    }
    printf("创建生产者线程成功\n");
    //debug_print(" 创建生产者线程成功");
    if (pthread_create(&cons, NULL, consumer, &args.sb) != 0) {
        perror("创建消费者线程失败");
        close(fd);
        return -1;
    }
    printf("创建消费者线程成功\n");
  
       // 创建谱分析线程
    pthread_t spectrum_thread;
    if (pthread_create(&spectrum_thread, NULL, spectrum_analysis_thread, &disp_data) != 0) {
        perror("创建谱分析线程失败");
        return -1;
    }
    printf("创建谱分析线程线程成功\n");
    //【新增】创建北斗发送线程
    pthread_t beidou_thread;
    if (pthread_create(&beidou_thread, NULL, beidou_sender_thread, NULL) != 0) {
        perror("创建北斗发送线程失败");
      
        return -1;
    }
    printf("创建北斗发送线程成功\n");
    //debug_print("[谱分析线程] 创建谱分析线程线程成功");
    pthread_t downdisp_thread;
    if (pthread_create(&downdisp_thread, NULL, downdisp_sender_thread, NULL) != 0) {
        perror("创建降采样发送线程失败");
        return -1;
    }
    printf("创建降采样发送线程成功\n");

    pthread_join(prod, NULL);
    pthread_join(cons, NULL);
    pthread_join(spectrum_thread, NULL);
    pthread_join(gps_tid,NULL);
    pthread_join(beidou_thread,NULL);
    pthread_join(downdisp_thread,NULL);
    close_processing_log();
    printf("系统退出：处理时间日志已保存至 /home/data/processing_time_log.txt\n");
    printf(" 成功清理资源");
    // 清理资源  
    free(disp_data.data_buffer_x);  
    free(disp_data.data_buffer_y);  
    free(disp_data.data_buffer_z);  
    pthread_mutex_destroy(&disp_data.mutex);  
    pthread_cond_destroy(&disp_data.cond);    // 在程序结束时关闭调试串口
  
   printf(" 成功关闭调试串口");
    return 0;
}
