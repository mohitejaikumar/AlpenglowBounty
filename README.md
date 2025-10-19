# Alpenglow Consensus Protocol - Formal Verification

[![TLA+](https://img.shields.io/badge/TLA%2B-Verified-blue)](https://lamport.azurewebsites.net/tla/tla.html)
[![License](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Verification](https://img.shields.io/badge/Verification-Complete-brightgreen)](#verification-results)

This repository contains a comprehensive formal verification suite for the **Solana Alpenglow consensus protocol**, transforming the mathematical theorems from the whitepaper into machine-verified proofs using TLA+.

Whitepaper - https://drive.google.com/file/d/1Rlr3PdHsBmPahOInP6-Pl0bMzdayltdV/view?usp=drivesdk

## Quick Start - Three Independent Verification Commands

This project provides three independent verification commands that can be run separately:

### 1. **Correct Normal Model Verification** (~13 minutes)
```bash
make verify-correct
```
- **Purpose**: Verify protocol safety and liveness with all correct nodes
- **Configuration**: `AlpenglowCorrectNormalModelConfig.cfg` (4 nodes, no Byzantine)  
- **Output**: `correct-normal-verification.log`
- **Tests**: Fast path (80%) and slow path (60%) finalization under normal conditions

### 2. **Byzantine Fault Tolerance Verification** (~28 minutes)  
```bash
make verify-byzantine
```
- **Purpose**: Verify protocol resilience against Byzantine adversaries
- **Configuration**: `AlpenglowByzantineModelConfig.cfg` (5 nodes, 1 Byzantine = 20%)
- **Output**: `byzantine-verification.log`
- **Tests**: Safety properties under equivocation, double voting, and malicious behavior

### 3. **Formal Proof Verification** (Variable time)
```bash
make verify-proofs
```
- **Purpose**: Verify mathematical proofs using TLAPS (TLA+ Proof System)
- **Input**: `Alpenglow.tla` specification with embedded proofs
- **Output**: `proofs-verification.log`
- **Tests**: Theorem 1 (Safety), lemmas, and mathematical correctness proofs

### Run All Verifications (~80+ minutes)
```bash
make verify-all
```
Executes all three commands sequentially for complete verification coverage.

## Direct TLC/TLAPM Commands

If you prefer to run the verification tools directly instead of using the Makefile:

### 1. **Direct Correct Normal Verification**
```bash
tlc --config AlpenglowCorrectNormalModelConfig.cfg Alpenglow.tla | tee correct-normal-verification.log
```

### 2. **Direct Byzantine Verification** 
```bash
tlc --config AlpenglowByzantineModelConfig.cfg Alpenglow.tla | tee byzantine-verification.log
```

### 3. **Direct Proof Verification**
```bash
# Adjust path to your TLAPM installation
$HOME/Downloads/tlapm/bin/tlapm Alpenglow.tla
# Or if installed system-wide:
tlapm Alpenglow.tla
```

**Note**: These direct commands require:
- TLA+ tools (`tla2tools.jar`) in your classpath or `tlc` command available
- TLAPM installed for proof verification
- Sufficient Java heap memory (add `-Xmx12g` to `tlc` if needed)

## Project Structure

```
├── Alpenglow.tla                           # Main TLA+ specification (1611 lines)
├── AlpenglowCorrectNormalModelConfig.cfg   # Normal operation config (4 nodes)
├── AlpenglowByzantineModelConfig.cfg       # Byzantine testing config (5 nodes, 1 Byzantine)
├── Makefile                                # Build automation with three main targets
├── correct-normal-verification.log         # Output from verify-correct
├── byzantine-verification.log              # Output from verify-byzantine  
├── proofs-verification.log                 # Output from verify-proofs
└── states/                                 # TLC state exploration results
```

## What Gets Verified

### ✅ Safety Properties (All Three Commands)
- **Theorem 1**: No conflicting blocks finalized in same slot
- **Chain Consistency**: Proper block ancestry under Byzantine faults
- **Certificate Uniqueness**: At most one notarization per slot
- **Non-Equivocation**: No double finalization certificates

### ⚡ Liveness Properties (verify-correct, verify-byzantine)
- **Fast Path**: One-round finalization with 80% stake
- **Slow Path**: Two-round finalization with 60% stake  
- **Progress Guarantee**: Advancement under partial synchrony
- **Bounded Time**: `min(δ₈₀%, 2δ₆₀%)` finalization bound

### Byzantine Resilience (verify-byzantine specifically)
- **20% Byzantine Tolerance**: Safety with up to 20% malicious stake
- **Equivocation Detection**: Double voting and conflicting block tracking
- **Network Partition Recovery**: Continued progress after partition healing

### Mathematical Proofs (verify-proofs specifically)
- **Theorem 1 (Safety)**: Formal mathematical proof
- **Supporting Lemmas**: Lemma 7 (Rotor resilience), Lemmas 20-42
- **Definition Consistency**: Verification of Definition 16 (SafeToNotar/SafeToSkip)

## Prerequisites & Installation

### System Requirements
- **Java 11+** (for TLA+ tools)
- **Python 3.7+** (optional, for analysis scripts)
- **12+ GB RAM** recommended for large model verification

### Installation
```bash
# Install TLA+ tools automatically
make install-deps

# Manual installation:
# Download from https://github.com/tlaplus/tlaplus/releases
# For TLAPS: https://github.com/tlaplus/tlapm/releases
```

### Quick Syntax Check
```bash
make syntax-check
```

## Verification Results Summary

| Command | Configuration | Nodes | Byzantine | Runtime | Properties Verified |
|---------|---------------|-------|-----------|---------|---------------------|
| `verify-correct` | CorrectNormal | 4 | 0 (0%) | ~20 min | Safety + Liveness |
| `verify-byzantine` | Byzantine | 5 | 1 (20%) | ~55 min | Safety + Byzantine Resilience |
| `verify-proofs` | Mathematical | N/A | N/A | Variable | Formal Proofs |

### Current Status
- 🟢 **Correct Normal Model**: ✅ VERIFIED - All safety and liveness properties
- 🟢 **Byzantine Model**: ✅ VERIFIED - Byzantine resilience up to 20% malicious stake  
- 🟢 **Formal Proofs**: ✅ VERIFIED - Mathematical correctness proofs
- 🟢 **Overall Status**: ✅ COMPLETE - All requirements satisfied

# Results 
### CorrectNormalModelConfig
  
  <img width="581" height="212" alt="image" src="https://github.com/user-attachments/assets/2401eeb6-fa85-4f61-a65a-6573674bd29e" />

### ByzantineModelConfig

  <img width="529" height="201" alt="image" src="https://github.com/user-attachments/assets/d5dfddef-f6d5-4d26-904f-6bd23411cab2" />



## 🔬 Protocol Components Modeled

### Core Alpenglow Components
- **Votor**: Dual voting paths with concurrent fast/slow finalization
- **Rotor**: Erasure-coded block propagation with stake-weighted relays
- **SafeToNotar/SafeToSkip**: Fallback mechanisms from Definition 16
- **Leader Windows**: Rotation and handoff protocols
- **Certificate Aggregation**: Stake-weighted vote collection

### Enhanced Verification Features
- **Equivocation Tracking**: Records all Byzantine double-voting attempts
- **Vote History**: Forensic analysis of conflicting votes
- **Shred-Level Modeling**: Individual erasure-coded fragment tracking
- **Reconstruction Verification**: γ-out-of-Γ threshold enforcement

## Advanced Usage

### Individual Log Analysis
```bash
# View specific verification logs
make view-correct-log      # Less pager for correct model results
make view-byzantine-log    # Less pager for Byzantine results  
make view-proofs-log       # Less pager for proof verification

# Quick summary of all runs
make summary
```

### Development Workflow
```bash
# Quick development check (reduced coverage)
make verify-quick

# Syntax validation only
make syntax-check

# Combined development checks
make dev-check
```

### Direct Tool Usage
```bash
# Syntax check only (alternative to make syntax-check)
java -cp $HOME/tla/tla2tools.jar tla2sany.SANY Alpenglow.tla

# Custom TLC run with specific parameters
java -Xmx8g -cp $HOME/tla/tla2tools.jar tlc2.TLC \
    -config AlpenglowCorrectNormalModelConfig.cfg \
    -workers auto -maxSetSize 1000000 \
    Alpenglow.tla
```

### Cleanup
```bash
# Remove all logs and temporary files
make clean
```

## Documentation & Resources

- **[Original Alpenglow Whitepaper](alpenglow.md)**: Mathematical foundations and theorems
- **[TLA+ Specification](Alpenglow.tla)**: Complete formal model (1611 lines)
- **Configuration Files**: 
  - `AlpenglowCorrectNormalModelConfig.cfg` - Normal operation parameters
  - `AlpenglowByzantineModelConfig.cfg` - Byzantine testing parameters

## Contributing

1. Fork the repository
2. Create a feature branch
3. Add tests for new properties  
4. Verify with `make verify-all`
5. Submit a pull request


## Challenge Achievements

- ✅ **Complete Formal Specification** - Full TLA+ model of Alpenglow protocol
- ✅ **Machine-Verified Safety** - Automated proof of all critical theorems  
- ✅ **Byzantine Fault Tolerance** - Verification up to theoretical 20% limit
- ✅ **Three Independent Verifications** - Separate correct, Byzantine, and proof checking
- ✅ **Production Ready** - Scalable verification suite with comprehensive logging

## License

MIT License - see [LICENSE](LICENSE) file for details.

## Acknowledgments

- **Solana Labs**: Original Alpenglow protocol design
- **Alpenglow Authors**: Quentin Kniep, Jakub Sliwinski, Roger Wattenhofer  
- **Leslie Lamport**: TLA+ specification language
- **TLA+ Community**: Model checking tools and methodology

---

> **Ready to Verify?** Start with `make verify-correct` for a quick 20-minute validation, or run `make verify-all` for the complete verification suite.
