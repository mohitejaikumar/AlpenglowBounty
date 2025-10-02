#!/bin/bash

echo "=== Running Alpenglow Debug Verification with Print Statements ==="
echo "This will show the protocol execution step by step..."
echo ""

# Run TLC with debug config and capture all output
java -Xmx2g -XX:+UseParallelGC -cp $HOME/tla/tla2tools.jar tlc2.TLC \
    -config AlpenglowDebugConfig.cfg \
    -workers 1 \
    -maxSetSize 5000 \
    -coverage 3 \
    Alpenglow.tla \
    2>&1 | tee verification_output.log

echo ""
echo "=== Print Statements Output ==="
echo "Look for lines containing:"
echo "  - 'ROTOR: Leader' - block dissemination"
echo "  - 'VOTE: Node' - voting actions"  
echo "  - 'FAST FINALIZE' - fast path finalization"
echo "  - 'SLOW FINALIZE' - slow path finalization"
echo "  - '=== CONSENSUS STATE ===' - state summaries"

