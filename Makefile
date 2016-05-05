V	 ?= 0

SILENT   = $(SILENT_$(V))
SILENT_0 = @
SILENT_1 =

.PHONY: help test test-fold test-indent

all: test

test: test-fold test-indent

test-fold:
	$(SILENT) vim -T dumb -E \
		-c 'source test/functions.vim' \
		-c 'source test/run_test.vim' \
		-c 'call RunTestFold()'

test-indent:
	$(SILENT) vim -T dumb -E \
		-c 'source test/functions.vim' \
		-c 'source test/run_test.vim' \
		-c 'call RunTestIndent()'

performance:
	$(SILENT) time vim -T dumb -E \
		--cmd 'silent edit test/indent.sv' \
		--cmd 'normal gg=G' \
		--cmd 'quit!'

profile:
	$(SILENT) vim -T dumb -E \
		--cmd 'profile start verilog_profile.result' \
		--cmd 'profile! file indent/verilog_systemverilog.vim' \
		-c 'source test/functions.vim' \
		-c 'source test/run_test.vim'

help:
	@echo "Test targets:"
	@echo ""
	@echo "make test        - Run addon tests"
	@echo "make performance - Measure performance"
	@echo "make profile     - Measure performance using vims built in profiler"
	@echo
	@echo "Options:"
	@echo "V=1       - Enable verbose mode"
