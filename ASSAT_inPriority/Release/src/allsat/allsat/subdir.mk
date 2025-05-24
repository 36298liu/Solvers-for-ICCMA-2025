################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CC_SRCS += \
../src/allsat/allsat/AccessSolver.cc \
../src/allsat/allsat/AllClauseAllSATSolver.cc \
../src/allsat/allsat/AllSATSolver.cc \
../src/allsat/allsat/Main.cc \
../src/allsat/allsat/NaiveAllSATSolver.cc \
../src/allsat/allsat/SmartAllSATSolver.cc \
../src/allsat/allsat/SmartBlockingAllSATSolver.cc 

CC_DEPS += \
./src/allsat/allsat/AccessSolver.d \
./src/allsat/allsat/AllClauseAllSATSolver.d \
./src/allsat/allsat/AllSATSolver.d \
./src/allsat/allsat/Main.d \
./src/allsat/allsat/NaiveAllSATSolver.d \
./src/allsat/allsat/SmartAllSATSolver.d \
./src/allsat/allsat/SmartBlockingAllSATSolver.d 

OBJS += \
./src/allsat/allsat/AccessSolver.o \
./src/allsat/allsat/AllClauseAllSATSolver.o \
./src/allsat/allsat/AllSATSolver.o \
./src/allsat/allsat/Main.o \
./src/allsat/allsat/NaiveAllSATSolver.o \
./src/allsat/allsat/SmartAllSATSolver.o \
./src/allsat/allsat/SmartBlockingAllSATSolver.o 


# Each subdirectory must supply rules for building sources it contributes
src/allsat/allsat/%.o: ../src/allsat/allsat/%.cc
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -std=c++0x -DNDEBUG -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/allsat/allsat -I../src/allsat/ -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -Wextra -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


