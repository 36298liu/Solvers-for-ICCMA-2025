################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CC_SRCS += \
../src/minisat/core/Main.cc \
../src/minisat/core/Solver.cc 

CC_DEPS += \
./src/minisat/core/Main.d \
./src/minisat/core/Solver.d 

OBJS += \
./src/minisat/core/Main.o \
./src/minisat/core/Solver.o 


# Each subdirectory must supply rules for building sources it contributes
src/minisat/core/%.o: ../src/minisat/core/%.cc
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	clang++ -g -DNDEBUG -DMINISAT_CONSTANTS_AS_MACROS -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/minisat -I../src/allsat/ -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -w -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


