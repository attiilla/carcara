#!/bin/bash

# Define the function to process each file
process_file() {
    local alethe_file="$1"
    local smt2_file="$2"
    local sharing="$3"
    local base_name="${alethe_file%.*}"  # Remove the extension to get the base name
    local original_lines compressed_lines diff diff_status
    
    # Run the first command
    ./target/debug/carcara check -i --allow-int-real-subtyping --expand-let-bindings "$alethe_file" "$smt2_file" > /dev/null 2>/dev/null
    if [ $? -ne 0 ]; then
        echo "Failed on checking the original proof $alethe_file"
        return 1
    fi

    # Run the second command 
    if [ "$sharing" = true ]; then
        ./target/debug/carcara compress --allow-int-real-subtyping --expand-let-bindings "$alethe_file" "$smt2_file" > "${base_name}.Calethe" 2>/dev/null
    else
        ./target/debug/carcara compress --allow-int-real-subtyping --expand-let-bindings --no-print-with-sharing "$alethe_file" "$smt2_file" > "${base_name}.Calethe" 2>/dev/null
    fi
    
    if [ $? -ne 0 ]; then
        echo "Failed on compressing $alethe_file"
        return 2
    fi

    # Run the third command
    output=$(./target/debug/carcara check -i --allow-int-real-subtyping --expand-let-bindings "${base_name}.Calethe" "$smt2_file" 2>/dev/null)
    if [ $? -ne 0 ]; then
        echo "Failed on checking the compressed proof ${base_name}.Calethe"
        return 3
    fi
    
    return 0
}

if [ $# -lt 1 ]; then
    echo "Usage: $0 <folder_path> <args>"
    exit 1
fi

dir=$1
shift
total=0
worked=0
check_err=0
compress_err=0
post_check_err=0
sharing=false

# Define counters for line difference comparisons
positive_diff=0
negative_diff=0
zero_diff=0

for arg in "$@"; do
    case "$arg" in
        sharing)
            sharing=true
            ;;
        *)
            echo "Error: Invalid argument '$arg'. Only 'sharing' is allowed."
            exit 1
            ;;
    esac
done

# Find all .alethe files in the sample directory and its subdirectories
while IFS= read -r -d '' alethe_file; do
    # Extract the corresponding .smt2 file
    smt2_file="${alethe_file%.alethe}.smt2"
    compressed_file="${alethe_file%.alethe}.Calethe"
    # Check if the paired .smt2 file exists
    if [ -f "$smt2_file" ]; then
        # Process the files and store the result
        output=$(process_file "$alethe_file" "$smt2_file" "$sharing")
        return_value=$?
        echo "$output"

        # Check the return value of the process_file function
        case $return_value in
            0)  
                # Count lines in both files
                original_lines=$(wc -l < "$alethe_file")
                compressed_lines=$(wc -l < "$compressed_file")
                echo "Counting"
                echo "$alethe_file: $original_lines"
                echo "$compressed_file: $compressed_lines"
                difference=$((original_lines - compressed_lines))
                echo "$alethe_file - Line difference: $difference"
                ((worked++))
                if [ "$difference" -lt 0 ]; then
                    ((negative_diff++))
                elif [ "$difference" -gt 0 ]; then
                    ((positive_diff++))
                else
                    ((zero_diff++))
                fi
                ;;
            1)
                ((check_err++))
                ;;
            2)
                ((compress_err++))
                ;;
            *)
                ((post_check_err++))
                ;;
        esac
        ((total++))
    else
        echo "Error: Matching .smt2 file not found for $alethe_file"
    fi
done < <(find $dir -maxdepth 1 -type f -name '*.alethe' -print0)

echo ""
echo "Worked on $worked examples out of $total"
echo "$check_err cases are invalid from cvc5"
echo "$compress_err cases couldn't be compressed"
echo "$post_check_err cases are invalid after compression"
echo ""
echo "Line difference summary:"
echo "Positive difference (compressed is smaller): $positive_diff"
echo "Negative difference (compressed is greater): $negative_diff"
echo "No difference: $zero_diff"