################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CC_SRCS += \
../src/minisat/simp/Main.cc \
../src/minisat/simp/SimpSolver.cc 

CC_DEPS += \
./src/minisat/simp/Main.d \
./src/minisat/simp/SimpSolver.d 

OBJS += \
./src/minisat/simp/Main.o \
./src/minisat/simp/SimpSolver.o 


# Each subdirectory must supply rules for building sources it contributes
src/minisat/simp/%.o: ../src/minisat/simp/%.cc
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	clang++ -g -DNDEBUG -DMINISAT_CONSTANTS_AS_MACROS -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/minisat -I../src/allsat/ -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -w -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


