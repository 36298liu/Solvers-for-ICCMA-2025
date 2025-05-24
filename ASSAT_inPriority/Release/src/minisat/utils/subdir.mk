################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CC_SRCS += \
../src/minisat/utils/Options.cc \
../src/minisat/utils/System.cc 

CC_DEPS += \
./src/minisat/utils/Options.d \
./src/minisat/utils/System.d 

OBJS += \
./src/minisat/utils/Options.o \
./src/minisat/utils/System.o 


# Each subdirectory must supply rules for building sources it contributes
src/minisat/utils/%.o: ../src/minisat/utils/%.cc
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	clang++ -DNDEBUG -DMINISAT_CONSTANTS_AS_MACROS -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/minisat -I../src/allsat/ -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -w -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


