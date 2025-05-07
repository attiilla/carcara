#!/bin/bash
arg=$1
cleaning=$2

if [ "$arg" != "clear" ]; then
    if [ -d "$arg" ]; then
        for file in "$arg"/*.smt2; do
            #remove (get-unsat-core) from problem files
            last_line=$(tail -n 1 "$file")
            if [ "$last_line" == "(get-unsat-core)" ]; then
                sed -i '$ d' "$file"
            fi
            base_name=$(basename "$file" .smt2)
            output="$arg/$base_name.alethe"
            #--enum-inst makes the proof generating too slow, add when testing for large sets in server
            cvc5 --dump-proofs --simplification=none --proof-format=alethe --proof-alethe-res-pivots --dag-thresh=0 --proof-granularity=theory-rewrite "$file" > "$output"
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
        done
    else
        echo "Directory $arg does not exist."
    fi    
else
    for file in "$cleaning"/*.alethe; do
        rm "$file"
    done 

    for file in "$cleaning"/*.Calethe; do
        rm "$file"
    done 
fi

