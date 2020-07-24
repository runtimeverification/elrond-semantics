# Settings
# --------

BUILD_DIR := .build
DEPS_DIR  := deps
DEFN_DIR  := $(BUILD_DIR)/defn

K_SUBMODULE := $(DEPS_DIR)/k
ifneq (,$(wildcard deps/k/k-distribution/target/release/k/bin/*))
  K_RELEASE ?= $(abspath $(K_SUBMODULE)/k-distribution/target/release/k)
else
  K_RELEASE ?= $(dir $(shell which kompile))..
endif
K_BIN := $(K_RELEASE)/bin
K_LIB := $(K_RELEASE)/lib
export K_RELEASE

ifneq ($(RELEASE),)
    K_BUILD_TYPE := Release
else
    K_BUILD_TYPE := Debug
endif

ELROND_DELEGATION_SUBMODULE := $(DEPS_DIR)/sc-delegation-rs

PATH := $(K_BIN):$(PATH)
export PATH

.PHONY: all clean deps                                                     \
        build build-llvm build-haskell                                     \
        test test-execution test-simple test-prove                         \
        test-conformance test-conformance-parse test-conformance-supported \
        elrond-test                                                        \
        media presentations reports

all: build

clean:
	rm -rf $(BUILD_DIR)

# Build Dependencies (K Submodule)
# --------------------------------

K_JAR := $(K_SUBMODULE)/k-distribution/target/release/k/lib/java/kernel-1.0-SNAPSHOT.jar

deps: $(K_JAR) $(TANGLER)

$(K_JAR):
	cd $(K_SUBMODULE) && mvn package -DskipTests -Dproject.build.type=$(K_BUILD_TYPE)

# Building Definition
# -------------------

KOMPILE_OPTS         := --emit-json
LLVM_KOMPILE_OPTS    :=
HASKELL_KOMPILE_OPTS :=

tangle_selector := k

SOURCE_FILES       := data         \
                      elrond       \
                      kwasm-lemmas \
                      numeric      \
                      test         \
                      wasm         \
                      wasm-text    \
                      wrc20
EXTRA_SOURCE_FILES :=
ALL_SOURCE_FILES   := $(patsubst %, %.md, $(SOURCE_FILES)) $(EXTRA_SOURCE_FILES)

build: build-llvm build-haskell

ifneq (,$(RELEASE))
    KOMPILE_OPTS += -O2
else
    KOMPILE_OPTS += --debug
endif

ifeq (,$(RELEASE))
    LLVM_KOMPILE_OPTS += -g
endif

KOMPILE_LLVM := kompile --backend llvm --md-selector "$(tangle_selector)" \
                $(KOMPILE_OPTS)                                           \
                $(addprefix -ccopt ,$(LLVM_KOMPILE_OPTS))

KOMPILE_HASKELL := kompile --backend haskell --md-selector "$(tangle_selector)" \
                   $(KOMPILE_OPTS)                                              \
                   $(HASKELL_KOMPILE_OPTS)

### LLVM

llvm_dir           := $(DEFN_DIR)/llvm
llvm_files         := $(ALL_SOURCE_FILES)
llvm_main_module   := MANDOS
llvm_syntax_module := $(llvm_main_module)-SYNTAX
llvm_main_file     := elrond
llvm_kompiled      := $(llvm_dir)/$(llvm_main_file)-kompiled/interpreter

build-llvm: $(llvm_kompiled)

$(llvm_kompiled): $(llvm_files)
	$(KOMPILE_LLVM) $(llvm_main_file).md      \
	    --directory $(llvm_dir) -I $(CURDIR)  \
	    --main-module $(llvm_main_module)     \
	    --syntax-module $(llvm_syntax_module)

### Haskell

haskell_dir           := $(DEFN_DIR)/haskell
haskell_files         := $(ALL_SOURCE_FILES)
haskell_main_module   := WASM-TEXT
haskell_syntax_module := $(haskell_main_module)-SYNTAX
haskell_main_file     := wasm-text
haskell_kompiled      := $(haskell_dir)/$(haskell_main_file)-kompiled/definition.kore

build-haskell: $(haskell_kompiled)

$(haskell_kompiled): $(haskell_files)
	$(KOMPILE_HASKELL) $(haskell_main_file).md   \
	    --directory $(haskell_dir) -I $(CURDIR)  \
	    --main-module $(haskell_main_module)     \
	    --syntax-module $(haskell_syntax_module)

# Testing
# -------

TEST  := ./kwasm
CHECK := git --no-pager diff --no-index --ignore-all-space -R

TEST_CONCRETE_BACKEND := llvm
TEST_SYMBOLIC_BACKEND := haskell

KPROVE_MODULE := KWASM-LEMMAS
KPROVE_OPTS   :=

tests/proofs/functions-spec.k.prove: KPROVE_MODULE = FUNCTIONS-LEMMAS
tests/proofs/wrc20-spec.k.prove:     KPROVE_MODULE = WRC20-LEMMAS

test: test-execution test-prove

# Generic Test Harnesses

tests/%.run: tests/% $(llvm_kompiled)
	$(TEST) run --backend $(TEST_CONCRETE_BACKEND) $< > tests/$*.$(TEST_CONCRETE_BACKEND)-out
	$(CHECK) tests/$*.$(TEST_CONCRETE_BACKEND)-out tests/success-$(TEST_CONCRETE_BACKEND).out
	rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/%.run-term: tests/% $(llvm_kompiled)
	$(TEST) run --backend $(TEST_CONCRETE_BACKEND) $< > tests/$*.$(TEST_CONCRETE_BACKEND)-out
	grep --after-context=2 "<instrs>" tests/$*.$(TEST_CONCRETE_BACKEND)-out > tests/$*.$(TEST_CONCRETE_BACKEND)-out-term
	$(CHECK) tests/$*.$(TEST_CONCRETE_BACKEND)-out-term tests/success-k.out
	rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out
	rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out-term

tests/%.parse: tests/% $(llvm_kompiled)
	$(TEST) kast --backend $(TEST_CONCRETE_BACKEND) $< kast > $@-out
	rm -rf $@-out

tests/%.prove: tests/% $(haskell_kompiled)
	$(TEST) prove --backend $(TEST_SYMBOLIC_BACKEND) $< --format-failures --def-module $(KPROVE_MODULE) \
	$(KPROVE_OPTS)

### Execution Tests

test-execution: test-simple

simple_tests         := $(wildcard tests/simple/*.wast)
simple_tests_failing := $(shell cat tests/failing.simple)
simple_tests_passing := $(filter-out $(simple_tests_failing), $(simple_tests))

test-simple: $(simple_tests_passing:=.run)

### Conformance Tests

conformance_tests:=$(wildcard tests/wasm-tests/test/core/*.wast)
unsupported_conformance_tests:=$(patsubst %, tests/wasm-tests/test/core/%, $(shell cat tests/conformance/unsupported-$(TEST_CONCRETE_BACKEND).txt))
unparseable_conformance_tests:=$(patsubst %, tests/wasm-tests/test/core/%, $(shell cat tests/conformance/unparseable.txt))
parseable_conformance_tests:=$(filter-out $(unparseable_conformance_tests), $(conformance_tests))
supported_conformance_tests:=$(filter-out $(unsupported_conformance_tests), $(parseable_conformance_tests))

test-conformance-parse: $(parseable_conformance_tests:=.parse)
test-conformance-supported: $(supported_conformance_tests:=.run-term)

test-conformance: test-conformance-parse test-conformance-supported

### Proof Tests

proof_tests:=$(wildcard tests/proofs/*-spec.k)

test-prove: $(proof_tests:=.prove)

### Elrond tests

elrond-deps:
	cd $(ELROND_DELEGATION_SUBMODULE) && rustup toolchain install nightly && rustup target add wasm32-unknown-unknown  && rustc --version && cargo install wasm-snip && cargo build

ELROND_RUNTIME_JSON := src/elrond-runtime.wat.json
ELROND_LOADED       := src/elrond-runtime.loaded.wat
ELROND_LOADED_JSON  := src/elrond-runtime.loaded.json

elrond-loaded: $(ELROND_LOADED_JSON) $(ELROND_LOADED)

elrond-clean-sources:
	rm $(ELROND_RUNTIME_JSON) $(ELROND_LOADED_JSON)

$(ELROND_LOADED): $(ELROND_RUNTIME_JSON)
	$(TEST) run --backend $(TEST_CONCRETE_BACKEND) $< --parser cat > $(ELROND_LOADED)

$(ELROND_LOADED_JSON): $(ELROND_RUNTIME_JSON)
	$(TEST) run --backend $(TEST_CONCRETE_BACKEND) $< --parser cat --output json > $@

$(ELROND_RUNTIME_JSON):
	echo "noop" | $(TEST) kast - json > $@

ELROND_TESTS_DIR=$(DEPS_DIR)/sc-delegation-rs/test/integration/main
elrond_tests=$(sort $(wildcard $(ELROND_TESTS_DIR)/*.steps.json))
elrond-test:
	python3 run-elrond-tests.py $(elrond_tests)

# Presentation
# ------------

media: presentations reports

media/%.pdf: TO_FORMAT=beamer
presentations: $(patsubst %.md, %.pdf, $(wildcard media/*-presentation-*.md))

media/201903-report-chalmers.pdf: TO_FORMAT=latex
reports: media/201903-report-chalmers.pdf

media/%.pdf: media/%.md media/citations.md
	cat $^ | pandoc --from markdown-latex_macros --to $(TO_FORMAT) --filter pandoc-citeproc --output $@

media-clean:
	rm media/*.pdf
