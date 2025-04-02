#!/bin/bash
dir=$1
if [ -d "$dir" ]; then
    for file in "$dir"/*.alethe; do
        base_name=$(basename "$file" .alethe)
        problem="$dir/$base_name.smt2"
        read -r first_line < "$file"
        if [ "$first_line" == "unknown" ]; then
            mkdir -p "$dir"/unknowns
            mv "$file" "$dir"/unknowns
            mv "$problem" "$dir"/unknowns
        fi
    done
else
    echo "Directory $dir does not exist."
fi