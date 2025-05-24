################################################################################
# Automatically-generated file. Do not edit!
################################################################################

-include ../makefile.init

RM := rm -rf

# All of the sources participating in the build are defined here
-include sources.mk
-include src/minisat/utils/subdir.mk
-include src/minisat/simp/subdir.mk
-include src/minisat/core/subdir.mk
-include src/fastformat/src/shwild/subdir.mk
-include src/fastformat/src/subdir.mk
-include src/allsat/subdir.mk
-include src/subdir.mk
-include subdir.mk
-include objects.mk

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(strip $(CC_DEPS)),)
-include $(CC_DEPS)
endif
ifneq ($(strip $(C++_DEPS)),)
-include $(C++_DEPS)
endif
ifneq ($(strip $(C_UPPER_DEPS)),)
-include $(C_UPPER_DEPS)
endif
ifneq ($(strip $(CXX_DEPS)),)
-include $(CXX_DEPS)
endif
ifneq ($(strip $(CPP_DEPS)),)
-include $(CPP_DEPS)
endif
ifneq ($(strip $(C_DEPS)),)
-include $(C_DEPS)
endif
endif

-include ../makefile.defs

# Add inputs and outputs from these tool invocations to the build variables 

# All Target
all:
	$(MAKE) --no-print-directory pre-build
	$(MAKE) --no-print-directory main-build

# Main-build Target
main-build: ArgSemSAT

# Tool invocations
ArgSemSAT: $(OBJS) $(USER_OBJS)
	@echo 'Building target: $@'
	@echo 'Invoking: GCC C++ Linker'
	clang++  -o "ASSAT_inPriority" $(OBJS) $(USER_OBJS) $(LIBS)
	@echo 'Finished building target: $@'
	@echo ' '

# Other Targets
clean:
	-$(RM) $(CC_DEPS)$(C++_DEPS)$(EXECUTABLES)$(C_UPPER_DEPS)$(CXX_DEPS)$(OBJS)$(CPP_DEPS)$(C_DEPS) ASSAT_inPriority
	-@echo ' '

pre-build:
	-if [ "$$(hg -q id > /dev/null 2>&1; echo $$?)" = "0" ]; then echo "HG(\"\$$Revision: $$(hg -q id -n) [$$(hg -q id)]\$$\");" >  ../src/hgversion.h; sed -i ../ASSAT_inPriority.doxyfile -e "s/\$$Revision: .*\$$/\$$Revision: $$(hg -q id -n) [$$(hg -q id)] \$$/g"; fi
	-@echo ' '

.PHONY: all clean dependents main-build pre-build

-include ../makefile.targets

