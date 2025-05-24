################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CPP_SRCS += \
../src/AF.cpp \
../src/ArgSemSAT.cpp \
../src/Argument.cpp \
../src/CompleteSemantics.cpp \
../src/ConfigurationComplete.cpp \
../src/ConfigurationPreferred.cpp \
../src/ConfigurationSemiStable.cpp \
../src/ConfigurationStable.cpp \
../src/Encoding.cpp \
../src/GroundedSemantics.cpp \
../src/Labelling.cpp \
../src/OrClause.cpp \
../src/PreferredSemantics.cpp \
../src/SATFormulae.cpp \
../src/Semantics.cpp \
../src/SemistableSemantics.cpp \
../src/SetArguments.cpp \
../src/StableSemantics.cpp \
../src/misc.cpp 

OBJS += \
./src/AF.o \
./src/ArgSemSAT.o \
./src/Argument.o \
./src/CompleteSemantics.o \
./src/ConfigurationComplete.o \
./src/ConfigurationPreferred.o \
./src/ConfigurationSemiStable.o \
./src/ConfigurationStable.o \
./src/Encoding.o \
./src/GroundedSemantics.o \
./src/Labelling.o \
./src/OrClause.o \
./src/PreferredSemantics.o \
./src/SATFormulae.o \
./src/Semantics.o \
./src/SemistableSemantics.o \
./src/SetArguments.o \
./src/StableSemantics.o \
./src/misc.o 

CPP_DEPS += \
./src/AF.d \
./src/ArgSemSAT.d \
./src/Argument.d \
./src/CompleteSemantics.d \
./src/ConfigurationComplete.d \
./src/ConfigurationPreferred.d \
./src/ConfigurationSemiStable.d \
./src/ConfigurationStable.d \
./src/Encoding.d \
./src/GroundedSemantics.d \
./src/Labelling.d \
./src/OrClause.d \
./src/PreferredSemantics.d \
./src/SATFormulae.d \
./src/Semantics.d \
./src/SemistableSemantics.d \
./src/SetArguments.d \
./src/StableSemantics.d \
./src/misc.d 


# Each subdirectory must supply rules for building sources it contributes
src/%.o: ../src/%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	clang++ -g -DNDEBUG -DMINISAT_CONSTANTS_AS_MACROS -DNLOGPRECO -DNSTATSPRECO -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -I../src/ -I../src/minisat -I../src/allsat/ -I../src/stlsoft/include -I../src/fastformat/include -I../unittests/gtest -I../unittests/gtest/include -O3 -w -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


