LAKE ?= lake

ifeq ($(OS),Windows_NT)
QCP_DEMOS_LLM_LEAN_GENERATE := cmd /c run-example-lean-windows.cmd
else
QCP_DEMOS_LLM_LEAN_GENERATE := bash run-example-lean-linux.sh
endif

.PHONY: all build qcp-demos-llm-generate qcp-demos-llm-build qcp-demos-llm-proofs-build clean

all: build

build:
	cd compcert_lib && $(LAKE) build
	cd unifysl && $(LAKE) build Unifysl
	cd auxlibs && $(LAKE) build
	cd sets && $(LAKE) build
	cd listlib && $(LAKE) build
	cd fixedpoints && $(LAKE) build
	cd SeparationLogic && $(LAKE) build
	cd MonadLib && $(LAKE) build
	cd examples && $(LAKE) build

qcp-demos-llm-generate:
	cd .. && $(QCP_DEMOS_LLM_LEAN_GENERATE)

qcp-demos-llm-build: qcp-demos-llm-generate
	cd examples && $(LAKE) -R build QCPDemosLLMGenerated

qcp-demos-llm-proofs-build: qcp-demos-llm-generate
	cd examples && $(LAKE) -R build QCPDemosLLMProofs

clean:
	cd examples && $(LAKE) clean
	cd MonadLib && $(LAKE) clean
	cd SeparationLogic && $(LAKE) clean
	cd fixedpoints && $(LAKE) clean
	cd listlib && $(LAKE) clean
	cd sets && $(LAKE) clean
	cd auxlibs && $(LAKE) clean
	cd unifysl && $(LAKE) clean
	cd compcert_lib && $(LAKE) clean
