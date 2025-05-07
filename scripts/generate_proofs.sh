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
            timeout 300s cvc5 --dump-proofs --simplification=none --enum-inst --proof-format=alethe --proof-alethe-res-pivots --dag-thresh=0 --proof-granularity=theory-rewrite "$file" > "$output"
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

