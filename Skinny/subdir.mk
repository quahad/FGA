################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CPP_SRCS += \
./Skinny-Num-Helper.cpp \
./skinny.cpp

OBJS += \
./Skinny-Num-Helper.o \
./skinny.o

CPP_DEPS += \
./Skinny-Num-Helper.d \
./skinny.d


# Each subdirectory must supply rules for building sources it contributes
./%.o: ./%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -I/home/hossein/mybrial/include -std=c++0x -O3 -g -c -fmessage-length=0 -fopenmp -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


