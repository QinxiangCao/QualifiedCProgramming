CC ?= cc
CFLAGS ?= -O2
CPPFLAGS += -I../../verification -DMINISAT_QCP_NATIVE_RUNTIME -DVEC_QCP_NATIVE_RUNTIME
LDLIBS += -lm
BUILD_DIR ?= .native-build
SOURCES = solver_qcp_support.c solver_qcp_analysis.c \
          solver_qcp_solver_propagate.c solver_qcp_state_search.c \
          vec_qcp.c main_qcp.c
OBJECTS = $(SOURCES:%.c=$(BUILD_DIR)/%.o)

.PHONY: all clean
all: $(BUILD_DIR)/minisat

$(BUILD_DIR)/minisat: $(OBJECTS)
	$(CC) $(LDFLAGS) $^ $(LDLIBS) -o $@

$(BUILD_DIR)/%.o: %.c
	@mkdir -p $(BUILD_DIR)
	$(CC) $(CPPFLAGS) $(CFLAGS) -std=gnu11 -MMD -MP -c $< -o $@

-include $(OBJECTS:.o=.d)

clean:
	rm -f $(OBJECTS) $(OBJECTS:.o=.d) $(BUILD_DIR)/minisat
