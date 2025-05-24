################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CPP_SRCS += \
../src/fastformat/src/api.cpp \
../src/fastformat/src/fmt_cache.cpp \
../src/fastformat/src/fmt_spec_defect_handlers.cpp \
../src/fastformat/src/init_code_strings.cpp \
../src/fastformat/src/memory_pool.cpp \
../src/fastformat/src/replacements.cpp \
../src/fastformat/src/snprintf.cpp 

OBJS += \
./src/fastformat/src/api.o \
./src/fastformat/src/fmt_cache.o \
./src/fastformat/src/fmt_spec_defect_handlers.o \
./src/fastformat/src/init_code_strings.o \
./src/fastformat/src/memory_pool.o \
./src/fastformat/src/replacements.o \
./src/fastformat/src/snprintf.o 

CPP_DEPS += \
./src/fastformat/src/api.d \
./src/fastformat/src/fmt_cache.d \
./src/fastformat/src/fmt_spec_defect_handlers.d \
./src/fastformat/src/init_code_strings.d \
./src/fastformat/src/memory_pool.d \
./src/fastformat/src/replacements.d \
./src/fastformat/src/snprintf.d 


# Each subdirectory must supply rules for building sources it contributes
src/fastformat/src/%.o: ../src/fastformat/src/%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	clang++ -g -DNDEBUG -DMINISAT_CONSTANTS_AS_MACROS -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/amsat -I../src/allsat/ -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -w -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


