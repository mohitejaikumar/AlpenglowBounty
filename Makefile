# Alpenglow Consensus Protocol Verification Makefile

.PHONY: help verify-small verify-large verify-all clean install-deps

# Default target
help:
	@echo "Alpenglow Consensus Protocol Verification"
	@echo "========================================"
	@echo ""
	@echo "Available targets:"
	@echo "  verify-small    - Quick verification on small model (4 nodes, ~5-10 min)"
	@echo "  verify-large    - Extended verification on large model (10 nodes, ~30-60 min)"
	@echo "  verify-all      - Complete verification suite (~1-3 hours)"
	@echo "  syntax-check    - Check TLA+ syntax only"
	@echo "  install-deps    - Install TLA+ tools and dependencies"
	@echo "  clean          - Clean temporary verification files"
	@echo ""
	@echo "Requirements:"
	@echo "  - TLA+ Tools (TLC model checker)"
	@echo "  - Python 3.7+"

# Quick verification on small model
verify-small:
	@echo "Running small model verification (4 nodes)..."
	@echo "Expected runtime: 5-10 minutes"
	java -Xmx8g -XX:+UseParallelGC -cp $$HOME/tla/tla2tools.jar tlc2.TLC -config AlpenglowModelConfig.cfg -workers auto -maxSetSize 500000 -coverage 30 Alpenglow.tla

# Debug verification with print output visible
verify-debug:
	@echo "Running debug verification with print statements..."
	java -Xmx4g -XX:+UseParallelGC -cp $$HOME/tla/tla2tools.jar tlc2.TLC -config AlpenglowDebugConfig.cfg -workers 1 -maxSetSize 10000 -coverage 5 Alpenglow.tla

# Quick safety check only
verify-safety:
	@echo "Running quick safety verification (2 minutes)..."
	java -Xmx4g -XX:+UseParallelGC -cp $$HOME/tla/tla2tools.jar tlc2.TLC -config AlpenglowModelConfig.cfg -workers auto -maxSetSize 100000 -coverage 10 -deadlock Alpenglow.tla

# Extended verification on large model  
verify-large:
	@echo "Running large model verification (10 nodes)..."
	@echo "Expected runtime: 30-60 minutes"
	java -Xmx12g -XX:+UseParallelGC -cp $$HOME/tla/tla2tools.jar tlc2.TLC -config AlpenglowLargeConfig.cfg -workers auto -maxSetSize 2000000 -coverage 60 Alpenglow.tla

# Complete verification suite
verify-all:
	@echo "Running complete verification suite..."
	@echo "Expected runtime: 1-3 hours"
	python3 VerifyAlpenglow.py

# Syntax check only
syntax-check:
	@echo "Checking TLA+ syntax..."
	java -cp $$HOME/tla/tla2tools.jar tla2sany.SANY Alpenglow.tla
	@echo "✓ Syntax check passed"

# Install dependencies (Ubuntu/Debian)
install-deps:
	@echo "Installing TLA+ tools..."
	sudo apt-get update
	sudo apt-get install -y openjdk-11-jdk wget unzip
	wget https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
	echo "#!/bin/bash" > tlc
	echo "java -cp tla2tools.jar tlc2.TLC \$$@" >> tlc
	chmod +x tlc
	sudo mv tlc /usr/local/bin/
	sudo mv tla2tools.jar /usr/local/bin/
	@echo "✓ TLA+ tools installed"

# Clean temporary files
clean:
	@echo "Cleaning verification files..."
	rm -f *.out *.st *.dot
	rm -rf states/
	@echo "✓ Cleaned temporary files"

# Quick safety properties check
verify-safety:
	@echo "Verifying safety properties only..."
	tlc -config AlpenglowModelConfig.cfg -workers auto -deadlock Alpenglow.tla | grep -E "(Safety|Theorem1|Certificate|Byzantine)"

# Check specific theorem
verify-theorem1:
	@echo "Verifying Theorem 1 (Safety) specifically..."
	tlc -config AlpenglowModelConfig.cfg -workers auto -deadlock Alpenglow.tla | grep -E "Theorem1_Safety"

# Development targets
dev-check: syntax-check verify-safety
	@echo "✓ Development checks passed"

# CI/CD target for automated testing
ci-verify: syntax-check verify-small
	@echo "✓ CI verification completed"

# Performance benchmark
benchmark:
	@echo "Running performance benchmark..."
	time tlc -config AlpenglowModelConfig.cfg -workers auto -coverage 60 Alpenglow.tla

# Generate state graph (small model only)
visualize:
	@echo "Generating state graph visualization..."
	tlc -config AlpenglowModelConfig.cfg -dot dot Alpenglow.tla
	@echo "State graph saved to dot.dot"
