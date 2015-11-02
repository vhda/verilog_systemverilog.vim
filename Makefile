V	 ?= 0

SILENT   = $(SILENT_$(V))
SILENT_0 = @
SILENT_1 =

.PHONY: help test

all: test

test:
	$(SILENT) vim -T dumb -E -c 'source test/run_test.vim'

help:
	@echo "Test targets:"
	@echo ""
	@echo "make test - Run addon tests"
	@echo
	@echo "Options:"
	@echo "V=1       - Enable verbose mode"
