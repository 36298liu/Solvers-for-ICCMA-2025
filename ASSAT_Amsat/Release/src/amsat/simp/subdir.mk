################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CC_SRCS += \
../src/amsat/simp/SimpSolver.cc \
../src/amsat/simp/Main.cc \

CC_DEPS += \
./src/amsat/simp/SimpSolver.d \
./src/amsat/simp/Main.d 

OBJS += \
./src/amsat/simp/SimpSolver.o \
./src/amsat/simp/Main.o \


# Each subdirectory must supply rules for building sources it contributes
src/amsat/simp/%.o: ../src/amsat/simp/%.cc
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	clang++ -g -DNDEBUG -DMINISAT_CONSTANTS_AS_MACROS -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/amsat -I../src/allsat/  -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -w -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


