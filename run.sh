#!/bin/bash

# Check if folder path is provided
if [ $# -lt 1 ]; then
    echo "Usage: $0 <folder_path>"
    exit 1
fi
folder="$1"
shift
# Check if folder exists
if [ ! -d "$folder" ]; then
    echo "Error: Folder '$folder' does not exist."
    exit 1
fi

prove=false
log=false
sharing=false

# Process remaining arguments (1 or 2)
for arg in "$@"; do
    case "$arg" in
        prove)
            prove=true
            ;;
        log)
            log=true
            ;;
        sharing)
            sharing=true
            ;;
        *)
            echo "Error: Invalid argument '$arg'. Only 'prove', 'sharing' and 'log' are allowed."
            exit 1
            ;;
    esac
done

if [ "$prove" = true ]; then
    ./scripts/generate_proofs.sh clear "$folder"
    #echo "./scripts/generate_proofs.sh clear "$folder""
    ./scripts/generate_proofs.sh "$folder"
    #echo "./scripts/generate_proofs.sh "$folder""
fi

./scripts/filter_unknowns.sh "$folder"
./scripts/sanitize_result.sh "$folder"

if [ "$log" = true ]; then
    if [ "$sharing" = true ]; then
        ./scripts/check_folder.sh "$folder" sharing > run.log
    else
        ./scripts/check_folder.sh "$folder" > run.log
    fi
else
    if [ "$sharing" = true ]; then
        ./scripts/check_folder.sh "$folder" sharing
    else
        ./scripts/check_folder.sh "$folder"
    fi
fi
