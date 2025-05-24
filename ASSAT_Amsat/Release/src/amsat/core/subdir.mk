################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CC_SRCS += \
../src/amsat/core/Solver.cc \
../src/amsat/core/eliminateVars.cc \
../src/amsat/core/Main.cc

CC_DEPS += \
./src/amsat/core/Solver.d \
./src/amsat/core/eliminateVars.d \
./src/amsat/core/Main.d

OBJS += \
./src/amsat/core/Solver.o \
./src/amsat/core/eliminateVars.o \
./src/amsat/core/Main.o


# Each subdirectory must supply rules for building sources it contributes
src/amsat/core/%.o: ../src/amsat/core/%.cc
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	clang++ -g -DNDEBUG -DMINISAT_CONSTANTS_AS_MACROS -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/  -I../src/allsat/ -I../src/amsat -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -w -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


