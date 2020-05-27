UPPER_STEPS = step4_if_fn_do step5_tco step6_file step7_quote step8_macros step9_try stepA_mal
STEPS = step0_repl step1_read_print step2_eval step3_env $(UPPER_STEPS)

all: build

$(addprefix target/release/,$(STEPS)): build RUST_SOURCE

RUST_SOURCE:

dist: mal

mal: stepA_mal
	cp $< $@

build:
	cargo build --release

.PHONY: clean

clean:
	cargo clean
