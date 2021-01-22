################################################################################
# Automatically-generated file. Do not edit!
################################################################################

-include ../makefile.init

RM := rm -rf

CPP_SRCS += \
./Cipher-Helper.cpp \
./Cipher.cpp

OBJS += \
./Cipher-Helper.o \
./Cipher.o

CPP_DEPS += \
./Cipher-Helper.d \
./Cipher.d


# Each subdirectory must supply rules for building sources it contributes
./%.o: ./%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -I/home/hossein/mybrial/include -std=c++0x -march=native -O3 -g -c -fmessage-length=0 -fopenmp -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


LIBS := -lbrial -lbrial_groebner -lm4ri

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(strip $(CC_DEPS)),)
-include $(CC_DEPS)
endif
ifneq ($(strip $(C++_DEPS)),)
-include $(C++_DEPS)
endif
ifneq ($(strip $(C_UPPER_DEPS)),)
-include $(C_UPPER_DEPS)
endif
ifneq ($(strip $(CXX_DEPS)),)
-include $(CXX_DEPS)
endif
ifneq ($(strip $(CPP_DEPS)),)
-include $(CPP_DEPS)
endif
ifneq ($(strip $(C_DEPS)),)
-include $(C_DEPS)
endif
endif

-include ../makefile.defs

# Add inputs and outputs from these tool invocations to the build variables
# All Target
all: Cipher-Helper

# Tool invocations
Cipher-Helper: $(OBJS) $(USER_OBJS)
	@echo 'Building target: $@'
	@echo 'Invoking: GCC C++ Linker'
	g++ -L"/home/hossein/mybrial/lib" -fopenmp -march=native -o "Cipher-Helper" $(OBJS) $(USER_OBJS) $(LIBS)
	@echo 'Finished building target: $@'
	@echo ' '

# Other Targets
clean:
	-$(RM) $(CC_DEPS) $(C++_DEPS) $(EXECUTABLES) $(C_UPPER_DEPS) $(CXX_DEPS) $(OBJS) $(CPP_DEPS) $(C_DEPS) Cipher-Helper
	-@echo ' '

.PHONY: all clean dependents

-include ../makefile.targets
