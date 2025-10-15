# Alpenglow Consensus Protocol Verification Makefile

.PHONY: help verify-correct verify-byzantine verify-proofs verify-all clean syntax-check install-deps

# TLA+ Tools configuration
TLA_TOOLS = $$HOME/tla/tla2tools.jar
JAVA_OPTS = -XX:+UseParallelGC
SPEC_FILE = Alpenglow.tla

# Log files
CORRECT_LOG = correct-normal-verification.log
BYZANTINE_LOG = byzantine-verification.log
PROOFS_LOG = proofs-verification.log

# Default target
help:
	@echo "Alpenglow Consensus Protocol Verification"
	@echo "=========================================="
	@echo ""
	@echo "Available targets:"
	@echo "  verify-correct    - Run TLC with correct normal config (~20 min)"
	@echo "  verify-byzantine  - Run TLC with Byzantine config (~55 min)"
	@echo "  verify-proofs     - Run TLAPS proof verification"
	@echo "  verify-all        - Run all verifications (correct + byzantine + proofs)"
	@echo "  syntax-check      - Check TLA+ syntax only"
	@echo "  clean             - Clean temporary verification files and logs"
	@echo "  install-deps      - Install TLA+ tools and dependencies"
	@echo ""
	@echo "Log files:"
	@echo "  $(CORRECT_LOG)   - Correct normal model verification output"
	@echo "  $(BYZANTINE_LOG)  - Byzantine model verification output"
	@echo "  $(PROOFS_LOG)     - TLAPS proof verification output"
	@echo ""
	@echo "Requirements:"
	@echo "  - TLA+ Tools (TLC model checker)"
	@echo "  - TLAPS (TLA+ Proof System) for proof verification"
	@echo "  - Java 11+"

# Verify with correct normal configuration (all nodes correct)
verify-correct:
	@echo "========================================"
	@echo "Running TLC Model Checking"
	@echo "Config: AlpenglowCorrectNormalModelConfig.cfg"
	@echo "Expected runtime: ~20 minutes"
	@echo "Log file: $(CORRECT_LOG)"
	@echo "========================================"
	@echo ""
	@date
	@java -Xmx12g $(JAVA_OPTS) -cp $(TLA_TOOLS) tlc2.TLC \
		-config AlpenglowCorrectNormalModelConfig.cfg \
		-workers auto \
		-maxSetSize 1000000 \
		-coverage 1 \
		$(SPEC_FILE) 2>&1 | tee $(CORRECT_LOG)
	@echo ""
	@echo "✓ Correct normal verification completed"
	@echo "✓ Results saved to $(CORRECT_LOG)"
	@date

# Verify with Byzantine configuration (with Byzantine nodes)
verify-byzantine:
	@echo "========================================"
	@echo "Running TLC Model Checking"
	@echo "Config: AlpenglowByzantineModelConfig.cfg"
	@echo "Expected runtime: ~55 minutes"
	@echo "Log file: $(BYZANTINE_LOG)"
	@echo "========================================"
	@echo ""
	@date
	@java -Xmx12g $(JAVA_OPTS) -cp $(TLA_TOOLS) tlc2.TLC \
		-config AlpenglowByzantineModelConfig.cfg \
		-workers auto \
		-maxSetSize 1000000 \
		-coverage 1 \
		$(SPEC_FILE) 2>&1 | tee $(BYZANTINE_LOG)
	@echo ""
	@echo "✓ Byzantine verification completed"
	@echo "✓ Results saved to $(BYZANTINE_LOG)"
	@date

# Verify proofs with TLAPS
verify-proofs:
	@echo "========================================"
	@echo "Running TLAPS Proof Verification"
	@echo "Spec: $(SPEC_FILE)"
	@echo "Log file: $(PROOFS_LOG)"
	@echo "========================================"
	@echo ""
	@date
	@$$HOME/Downloads/tlapm/bin/tlapm $(SPEC_FILE) 2>&1 | tee $(PROOFS_LOG)
	@echo ""
	@echo "✓ Proof verification completed"
	@echo "✓ Results saved to $(PROOFS_LOG)"
	@date

# Run all verifications
verify-all:
	@echo "========================================"
	@echo "Running Complete Verification Suite"
	@echo "========================================"
	@echo ""
	@echo "This will run:"
	@echo "  1. Correct normal model verification (~20 min)"
	@echo "  2. Byzantine model verification (~55 min)"
	@echo "  3. TLAPS proof verification"
	@echo ""
	@echo "Total expected runtime: ~80+ minutes"
	@echo ""
	@date
	@echo ""
	@$(MAKE) verify-correct
	@echo ""
	@$(MAKE) verify-byzantine
	@echo ""
	@$(MAKE) verify-proofs
	@echo ""
	@echo "========================================"
	@echo "✓ All verifications completed!"
	@echo "========================================"
	@echo ""
	@echo "Summary of log files:"
	@echo "  - $(CORRECT_LOG)"
	@echo "  - $(BYZANTINE_LOG)"
	@echo "  - $(PROOFS_LOG)"
	@date

# Syntax check only
syntax-check:
	@echo "Checking TLA+ syntax..."
	@java -cp $(TLA_TOOLS) tla2sany.SANY $(SPEC_FILE)
	@echo "✓ Syntax check passed"

# Quick verification for development (reduced state space)
verify-quick:
	@echo "Running quick verification (reduced coverage)..."
	@java -Xmx8g $(JAVA_OPTS) -cp $(TLA_TOOLS) tlc2.TLC \
		-config AlpenglowCorrectNormalModelConfig.cfg \
		-workers auto \
		-maxSetSize 100000 \
		-coverage 1 \
		-depth 30 \
		$(SPEC_FILE)

# Clean temporary files and logs
clean:
	@echo "Cleaning verification files and logs..."
	@rm -f *.log
	@rm -f *.out *.st *.dot
	@rm -rf states/
	@rm -rf .tlacache/
	@echo "✓ Cleaned temporary files and logs"

# Install dependencies (macOS)
install-deps:
	@echo "Installing TLA+ tools..."
	@echo "Note: This assumes you have Java 11+ installed"
	@echo ""
	@if [ ! -d "$$HOME/tla" ]; then mkdir -p $$HOME/tla; fi
	@if [ ! -f "$$HOME/tla/tla2tools.jar" ]; then \
		echo "Downloading tla2tools.jar..."; \
		curl -L -o $$HOME/tla/tla2tools.jar https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar; \
	else \
		echo "tla2tools.jar already exists"; \
	fi
	@echo ""
	@echo "For TLAPS (proof verification), install from:"
	@echo "  https://github.com/tlaplus/tlapm/releases"
	@echo ""
	@echo "✓ TLA+ tools setup complete"

# Development check (syntax + quick verification)
dev-check: syntax-check verify-quick
	@echo "✓ Development checks passed"

# View logs
view-correct-log:
	@if [ -f $(CORRECT_LOG) ]; then \
		less $(CORRECT_LOG); \
	else \
		echo "Log file $(CORRECT_LOG) not found. Run 'make verify-correct' first."; \
	fi

view-byzantine-log:
	@if [ -f $(BYZANTINE_LOG) ]; then \
		less $(BYZANTINE_LOG); \
	else \
		echo "Log file $(BYZANTINE_LOG) not found. Run 'make verify-byzantine' first."; \
	fi

view-proofs-log:
	@if [ -f $(PROOFS_LOG) ]; then \
		less $(PROOFS_LOG); \
	else \
		echo "Log file $(PROOFS_LOG) not found. Run 'make verify-proofs' first."; \
	fi

# Show verification summary
summary:
	@echo "Verification Summary"
	@echo "===================="
	@echo ""
	@if [ -f $(CORRECT_LOG) ]; then \
		echo "Correct Normal Model:"; \
		echo "  Status: $$(grep -q 'Model checking completed' $(CORRECT_LOG) && echo '✓ PASSED' || echo '✗ CHECK LOG')"; \
		echo "  Log: $(CORRECT_LOG)"; \
	else \
		echo "Correct Normal Model: NOT RUN"; \
	fi
	@echo ""
	@if [ -f $(BYZANTINE_LOG) ]; then \
		echo "Byzantine Model:"; \
		echo "  Status: $$(grep -q 'Model checking completed' $(BYZANTINE_LOG) && echo '✓ PASSED' || echo '✗ CHECK LOG')"; \
		echo "  Log: $(BYZANTINE_LOG)"; \
	else \
		echo "Byzantine Model: NOT RUN"; \
	fi
	@echo ""
	@if [ -f $(PROOFS_LOG) ]; then \
		echo "TLAPS Proofs:"; \
		echo "  Status: $$(grep -q 'proved' $(PROOFS_LOG) && echo '✓ VERIFIED' || echo '✗ CHECK LOG')"; \
		echo "  Log: $(PROOFS_LOG)"; \
	else \
		echo "TLAPS Proofs: NOT RUN"; \
	fi
