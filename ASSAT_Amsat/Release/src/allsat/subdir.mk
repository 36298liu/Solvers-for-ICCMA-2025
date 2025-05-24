################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CC_SRCS += \
../src/allsat/AccessSolver.cc \
../src/allsat/AllClauseAllSATSolver.cc \
../src/allsat/AllSATSolver.cc \
../src/allsat/Main.cc \
../src/allsat/NaiveAllSATSolver.cc \
../src/allsat/SmartAllSATSolver.cc \
../src/allsat/SmartBlockingAllSATSolver.cc 

CC_DEPS += \
./src/allsat/AccessSolver.d \
./src/allsat/AllClauseAllSATSolver.d \
./src/allsat/AllSATSolver.d \
./src/allsat/Main.d \
./src/allsat/NaiveAllSATSolver.d \
./src/allsat/SmartAllSATSolver.d \
./src/allsat/SmartBlockingAllSATSolver.d 

OBJS += \
./src/allsat/AccessSolver.o \
./src/allsat/AllClauseAllSATSolver.o \
./src/allsat/AllSATSolver.o \
./src/allsat/Main.o \
./src/allsat/NaiveAllSATSolver.o \
./src/allsat/SmartAllSATSolver.o \
./src/allsat/SmartBlockingAllSATSolver.o 


# Each subdirectory must supply rules for building sources it contributes
src/allsat/%.o: ../src/allsat/%.cc
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	clang++ -DNDEBUG -DMINISAT_CONSTANTS_AS_MACROS -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/amsat -I../src/allsat/ -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -w -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


