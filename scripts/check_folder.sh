#!/bin/bash
# Receives a folder <folder_name> as argument, then tries to compress and check every proof in <folder_name>_solutions and it's subfolders

# Define the function to process each file
process_file() {
    local alethe_file="$1"
    local smt2_file="$2"
    local sharing="$3"
    local elaborating="$4"
    local base_name="${alethe_file%.*}"  # Remove the extension to get the base name
    local original_lines compressed_lines
    # Create a temp file for compression stats
    local stats_file=$(mktemp)
    # Run the first command
    ./target/debug/carcara check -i --allow-int-real-subtyping --expand-let-bindings "$alethe_file" "$smt2_file" > /dev/null 2>/dev/null
    if [ $? -ne 0 ]; then
        echo "$alethe_file;;;;;;;;"
        return 1
    fi

    if [ "$elaborating" = true ]; then
        ./target/debug/carcara elaborate -i --allow-int-real-subtyping --expand-let-bindings "$alethe_file" "$smt2_file" --pipeline polyeq lia-generic local reordering hole > "${base_name}.Ealethe" 2>/dev/null
        if [ $? -ne 0 ]; then
            echo "$alethe_file;;;;;;;;"
        return 2
    fi
    alethe_file="${base_name}.Ealethe"
    fi
    
    if [ "$sharing" = true ]; then
        ./target/debug/carcara compress --allow-int-real-subtyping --expand-let-bindings --stats "$alethe_file" "$smt2_file" > "${base_name}.Calethe" 2>"$stats_file"
    else
        ./target/debug/carcara compress --allow-int-real-subtyping --expand-let-bindings --no-print-with-sharing --stats "$alethe_file" "$smt2_file" > "${base_name}.Calethe" 2>"$stats_file"
    fi
    
    local stats_content=$(grep -v '^\[' "$stats_file")
    rm "$stats_file"

    if [ $? -ne 0 ]; then
        echo "$alethe_file;;;;;;;;"
        return 3
    fi

    # Run the third command
    output=$(./target/debug/carcara check -i --allow-int-real-subtyping --expand-let-bindings "${base_name}.Calethe" "$smt2_file" 2>/dev/null)
    if [ $? -ne 0 ]; then
        echo "$alethe_file;;;;;;;;"
        return 4
    fi
    echo "$stats_content"
    return 0
}

if [ $# -lt 1 ]; then
    echo "Usage: $0 <folder_path> <args>"
    exit 1
fi

base_dir="$1"
shift
total=0
worked=0
check_err=0
elab_err=0
compress_err=0
post_check_err=0
sharing=false
elaborating=false

# Define counters for line difference comparisons
positive_diff=0
negative_diff=0
zero_diff=0

for arg in "$@"; do
    case "$arg" in
        sharing)
            sharing=true
            ;;
        elaborate)
            elaborating=true
            ;;
        *)
            echo "Error: Invalid argument '$arg'. Only 'sharing' and 'elaborate' are allowed."
            exit 1
            ;;
    esac
done

# Check if the solutions folder exists
solutions_dir="${base_dir}_solutions_T"
if [ ! -d "$solutions_dir" ]; then
    echo "Error: Solutions directory '$solutions_dir' not found"
    exit 1
fi

# Create or initialize the results CSV file
results_csv="${base_dir}/results.csv"
if [ ! -f "$results_csv" ]; then
    echo "proof_name;collect_units;fix;reinsert;rebuild;total time;original_lines;compressed_lines;line_difference;checker_err;elab_err;compress_err;invalid_compress;worked" > "$results_csv"
fi

# Find all .alethe files in the solutions directory and its subdirectories
while IFS= read -r -d '' alethe_file; do
    base_name="${alethe_file%.*}"

    # Get the relative path from the solutions directory
    relative_path="${alethe_file#$solutions_dir/}"
    
    # Construct the corresponding .smt2 file path in the base directory
    smt2_file="${base_dir}/${relative_path%.alethe}.smt2"
    
    # The compressed file stays in the same location as the alethe file
    compressed_file="${alethe_file%.alethe}.Calethe"
    
    # Check if the paired .smt2 file exists
    if [ -f "$smt2_file" ]; then
        # Process the files and store the result
        output=$(process_file "$alethe_file" "$smt2_file" "$sharing" "$elaborating")
        
        return_value=$?
        #echo "$results_csv"
        # Check the return value of the process_file function
        case $return_value in
            0)  
                # Count lines in both files
                original_lines=$(wc -l < "$alethe_file")
                compressed_lines=$(wc -l < "$compressed_file")
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
                echo "$output;;;;;1;" >> "$results_csv"
                ;;
            1)
                ((check_err++))
                echo "$output;1;;;;;" >> "$results_csv"
                ;;
            2)
                ((elab_err++))
                echo "$output;;1;;;;" >> "$results_csv"
                ;;
            3)
                ((compress_err++))
                echo "$output;;;1;;;" >> "$results_csv"
                ;;
            *)
                ((post_check_err++))
                line_count=$(wc -l < "$base_name.alethe")
                echo "$output;;;;1 ($line_count);;" >> "$results_csv"
                ;;
        esac
        ((total++))
    else
        echo "Error: Matching .smt2 file not found for $alethe_file (expected at $smt2_file)"
    fi
done < <(find "$solutions_dir" -type f -name '*.alethe' -print0)

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