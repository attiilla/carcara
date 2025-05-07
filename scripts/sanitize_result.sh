#!/bin/bash

# Check if folder path is provided
if [ $# -ne 1 ]; then
    echo "Usage: $0 <folder_path>"
    exit 1
fi

folder="$1"

# Check if folder exists
if [ ! -d "$folder" ]; then
    echo "Error: Folder '$folder' does not exist."
    exit 1
fi

# Process each file in the folder
for file in "$folder"/*; do
    # Skip directories
    if [ -d "$file" ]; then
        continue
    fi

    # Check if first line contains "FORBIDDEN"
    if [ -f "$file" ] && [ -s "$file" ]; then
        first_line=$(head -n 1 "$file")
        if [[ "$first_line" == "unsat" ]]; then
            # Remove first line
            tail -n +2 "$file" > "$file.tmp" && mv "$file.tmp" "$file"
        fi
    fi

    # Remove trailing empty lines (leaving just one)
    if [ -f "$file" ]; then
        # Read the file, strip multiple trailing newlines, and ensure one remains
        content=$(cat "$file")
        # Remove all trailing newlines, then add one back
        printf "%s\n" "$(echo -n "$content" | sed -e :a -e '/^\n*$/{$d;N;ba' -e '}')" > "$file.tmp"
        mv "$file.tmp" "$file"
    fi
done

