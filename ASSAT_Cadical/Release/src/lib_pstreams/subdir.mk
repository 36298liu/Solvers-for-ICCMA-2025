################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CC_SRCS += \
../src/lib_pstreams/test_minimum.cc \
../src/lib_pstreams/test_pstreams.cc 

OBJS += \
./src/lib_pstreams/test_minimum.o \
./src/lib_pstreams/test_pstreams.o 

CC_DEPS += \
./src/lib_pstreams/test_minimum.d \
./src/lib_pstreams/test_pstreams.d 


# Each subdirectory must supply rules for building sources it contributes
src/lib_pstreams/%.o: ../src/lib_pstreams/%.cc
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -std=c++0x -DNDEBUG -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -I../src/glucose -I../src/precosat -O3 -Wextra -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@:%.o=%.d)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


