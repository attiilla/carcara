#!/bin/bash
# Receives a folder <folder_name> as argument, then tries to produce a proof for every problem in <folder_name> and it's 
# subfolders, then stores those proofs in <folder_name>_solutions (the proofs are stored in their respective subfolders)

arg=$1
cleaning=$2
timeout_duration=300

if [ "$arg" != "clear" ]; then
    if [ -d "$arg" ]; then
        # Create the solutions directory by appending "_solutions" to the input directory name
        solutions_dir="${arg}_solutions"
        mkdir -p "$solutions_dir"
        
        # Find all .smt2 files recursively
        find "$arg" -type f -name "*.smt2" | while read -r file; do
            # Remove (get-unsat-core) from problem files
            last_line=$(tail -n 1 "$file")
            if [ "$last_line" == "(get-unsat-core)" ]; then
                sed -i '$ d' "$file"
            fi
            
            # Get relative path and create output directory structure
            rel_path="${file#$arg/}"
            output_dir="$solutions_dir/$(dirname "$rel_path")"
            mkdir -p "$output_dir"
            
            base_name=$(basename "$file" .smt2)
            output="$output_dir/$base_name.alethe"
            
            # Run cvc5 command with timeout
            echo "[$(date '+%Y-%m-%d %H:%M:%S')]Processing $file..."
            if timeout $timeout_duration cvc5 --dump-proofs --simplification=none --proof-format=alethe --proof-alethe-res-pivots --dag-thresh=0 --proof-granularity=theory-rewrite "$file" > "$output"; then
                # Process the output file if command succeeded
                {
                    # Read first line separately
                    IFS= read -r first_line
                    
                    # Skip first line if it's exactly "unsat"
                    if [ "$first_line" != "unsat" ]; then
                        echo "$first_line"
                    fi
                    
                    # Copy the rest of the file
                    cat
                    
                    # Remove trailing blank lines
                } < "$output" | sed -e :a -e '/^\n*$/{$d;N;ba' -e '}' > "$output.tmp"
                mv "$output.tmp" "$output"
                
                # Print completion message with timestamp
                echo "[$(date '+%Y-%m-%d %H:%M:%S')] Created: $output"
                echo
            else
                # Handle timeout
                timeout_status=$?
                if [ $timeout_status -eq 124 ]; then
                    echo "[$(date '+%Y-%m-%d %H:%M:%S')] Timeout: $file (after $timeout_duration seconds)"
                    echo
                    rm -f "$output"  # Remove partial output if any
                else
                    echo "[$(date '+%Y-%m-%d %H:%M:%S')] Error processing: $file (exit code $timeout_status)"
                    echo
                    rm -f "$output"  # Remove partial output if any
                fi
            fi
        done
    else
        echo "Directory $arg does not exist."
    fi    
else
    # Clear mode - remove all .alethe and .Calethe files in the specified directory and subdirectories
    echo "Cleaning up .Calethe files in $cleaning..."

    find "$cleaning" -type f -name "*.Calethe" -delete
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] Cleanup completed"
fi