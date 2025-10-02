#!/usr/bin/env python3

import re

def extract_logs(input_file, output_file):
    """
    Extract logs related to:
    1. SLOT ADVANCE CHECK (multi-line entries)
    2. FINAL VOTE operations (TRYING/SKIPPING, multi-line entries) 
    3. Notarization votes (single-line entries)
    """
    
    filtered_logs = []
    
    with open(input_file, 'r') as f:
        lines = f.readlines()
    
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        
        # Check for SLOT ADVANCE CHECK entries
        if '<< "=== SLOT ADVANCE CHECK ===' in line:
            # Found start of SLOT ADVANCE CHECK entry
            entry_lines = [lines[i]]
            i += 1
            
            # Continue reading until we find the end marker
            while i < len(lines):
                entry_lines.append(lines[i])
                if '"===" >>' in lines[i].strip():
                    break
                i += 1
            
            filtered_logs.extend(entry_lines)
            
        # Check for FINAL VOTE entries
        elif ('<< "=== TRYING FINAL VOTE ===' in line or 
              '<< "=== SKIPPING FINAL VOTE ===' in line):
            # Found start of FINAL VOTE entry
            entry_lines = [lines[i]]
            i += 1
            
            # Continue reading until we find the end marker
            while i < len(lines):
                entry_lines.append(lines[i])
                if '"===" >>' in lines[i].strip():
                    break
                i += 1
            
            filtered_logs.extend(entry_lines)
            
        # Check for Notarization votes (single line entries)
        elif 'Notarization votes for' in line:
            filtered_logs.append(lines[i])
            
        i += 1
    
    # Write filtered logs to output file
    with open(output_file, 'w') as f:
        f.writelines(filtered_logs)
    
    print(f"Filtered {len(filtered_logs)} lines from {len(lines)} total lines")
    print(f"Filtered logs saved to: {output_file}")

if __name__ == "__main__":
    input_file = "/Users/jaikumarmohite/Developer/alpenglow.log"
    output_file = "/Users/jaikumarmohite/Developer/alpenglow_filtered.log"
    extract_logs(input_file, output_file)
