ARCH := rv32i
MINILUA := ../src/host/minilua

DYNASM_DIR := ../dynasm
DYNASM := $(DYNASM_DIR)/dynasm.lua

HOST_CC := gcc -m32
HOST_CFLAGS := -I$(DYNASM_DIR)
HOST_LDFLAGS :=

RM := rm -f

DASC_FILES := $(wildcard *.dasc)

.PHONY: all clean distclean

all: $(ARCH)
	./$(ARCH)

dump:
	$(MINILUA) $(DYNASM) --dumpdef
	$(MINILUA) $(DYNASM) --dumparch $(ARCH)

clean:
	$(RM) *.o
	$(RM) $(DASC_FILES:.dasc=.c)

distclean: clean
	$(RM) *~

%.c: %.dasc $(DYNASM_DIR)/dasm_$(ARCH).lua
	$(MINILUA) $(DYNASM) -o $@ $<

%.o: %.c $(DYNASM_DIR)/dasm_proto.h $(DYNASM_DIR)/dasm_$(ARCH).h
	$(HOST_CC) $(HOST_CFLAGS) -c -o $@ $<

$(ARCH): $(ARCH).o
	$(HOST_CC) $(HOST_LDFLAGS) -o $@ $<
