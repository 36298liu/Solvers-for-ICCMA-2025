################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CPP_SRCS += \
../src/fastformat/src/shwild/api.cpp \
../src/fastformat/src/shwild/architecture_sanity_check.cpp \
../src/fastformat/src/shwild/matches.cpp \
../src/fastformat/src/shwild/pattern.cpp 

OBJS += \
./src/fastformat/src/shwild/api.o \
./src/fastformat/src/shwild/architecture_sanity_check.o \
./src/fastformat/src/shwild/matches.o \
./src/fastformat/src/shwild/pattern.o 

CPP_DEPS += \
./src/fastformat/src/shwild/api.d \
./src/fastformat/src/shwild/architecture_sanity_check.d \
./src/fastformat/src/shwild/matches.d \
./src/fastformat/src/shwild/pattern.d 


# Each subdirectory must supply rules for building sources it contributes
src/fastformat/src/shwild/%.o: ../src/fastformat/src/shwild/%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	clang++ -g -DNDEBUG -DMINISAT_CONSTANTS_AS_MACROS -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/minisat -I../src/allsat/ -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -w -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


