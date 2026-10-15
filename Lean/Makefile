LAKE ?= lake

ifeq ($(OS),Windows_NT)
LEAN_GENERATE := cmd /c run-example-lean-windows.cmd
else
LEAN_GENERATE := bash run-example-lean-linux.sh
endif

.PHONY: all build generate llm-bench-generate qcp-demos-llm-generate qcp-demos-llm-build qcp-demos-llm-proofs-build llm-bench-build clean

all: build

build:
	cd compcert_lib && $(LAKE) build
	cd unifysl && $(LAKE) build Unifysl
	cd auxlibs && $(LAKE) build
	cd sets && $(LAKE) build
	cd listlib && $(LAKE) build
	cd fixedpoints && $(LAKE) build
	cd maxminlib && $(LAKE) build
	cd flocq && $(LAKE) build
	cd SeparationLogic && $(LAKE) build
	cd MonadLib && $(LAKE) build
	cd examples && $(LAKE) build

generate:
	cd .. && $(LEAN_GENERATE) all

llm-bench-generate:
	cd .. && $(LEAN_GENERATE) llm-bench

qcp-demos-llm-generate:
	cd .. && $(LEAN_GENERATE) qcp-demos-llm

qcp-demos-llm-build: qcp-demos-llm-generate
	cd examples && $(LAKE) -R build QCPDemosLLM

# Compatibility entry point: the registered library includes both VCs and proofs.
qcp-demos-llm-proofs-build: qcp-demos-llm-generate
	cd examples && $(LAKE) -R build QCPDemosLLM

llm-bench-build:
	cd examples && $(LAKE) build LLMBench

clean:
	cd examples && $(LAKE) clean
	cd MonadLib && $(LAKE) clean
	cd SeparationLogic && $(LAKE) clean
	cd flocq && $(LAKE) clean
	cd maxminlib && $(LAKE) clean
	cd fixedpoints && $(LAKE) clean
	cd listlib && $(LAKE) clean
	cd sets && $(LAKE) clean
	cd auxlibs && $(LAKE) clean
	cd unifysl && $(LAKE) clean
	cd compcert_lib && $(LAKE) clean
