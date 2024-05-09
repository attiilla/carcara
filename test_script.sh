#!/bin/bash

# Define the function to process each file
process_file() {
    local alethe_file="$1"
    local smt2_file="$2"
    local base_name="${alethe_file%.*}"  # Remove the extension to get the base name
    
    # Run the first command
    ./target/debug/carcara elaborate -i --allow-int-real-subtyping --expand-let-bindings "$alethe_file" "$smt2_file" >> "${base_name}.ealethe" 2>/dev/null

    # Run the second command
    ./target/debug/carcara compress -i --allow-int-real-subtyping "${base_name}.ealethe" "$smt2_file" >> "${base_name}.calethe" 2>/dev/null
    
    # Check the return value of the second command
    if [ $? -ne 0 ]; then
        echo "Failed on compressing $alethe_file"
        return 1
    fi
    local first_line=$(head -n 1 "${base_name}.calethe")
    if [ "$first_line" == "There is no collectable clauses." ]; then
        echo "There is no collectable clauses in $alethe_file"
        return 2
    fi

    # Run third command
    output=$(./target/debug/carcara check -i --allow-int-real-subtyping --expand-let-bindings "${base_name}.calethe" "$smt2_file" 2>/dev/null)
    if [ "$output" == "valid" ]; then
        echo "Worked on $alethe_file"
    elif [ "$output" == "holey" ]; then
        echo "Holey on $alethe_file"
        return 3 
    else
        echo "Checker failed on $alethe_file"
        return 4
    fi
    return 0
}

total=0
worked=0
holey=0
not_compressable=0
check_failed=0
compress_failed=0
# Find all .alethe files in the sample directory and its subdirectories
while IFS= read -r -d '' alethe_file; do
    # Extract the corresponding .smt2 file
    smt2_file="${alethe_file%.alethe}.smt2"
    
    # Check if the paired .smt2 file exists
    if [ -f "$smt2_file" ]; then
        # Process the files and store the result
        result=$(process_file "$alethe_file" "$smt2_file"; echo $?)
        return_value="$(echo "$result" | awk 'NR==2')"
        result="$(echo "$result" | awk 'NR==1')"
        echo "$result"
        # Check the return value of the process_file function
        case $return_value in
            0)
                ((worked++))
                ;;
            1)
                ((compress_failed++))
                ;;
            2)
                ((worked++))
                ((not_compressable++))
                ;;
            3)
                ((holey++))
                ;;
            *)
                ((check_failed++))
                ;;
        esac
        ((total++))
    else
        echo "Error: Matching .smt2 file not found for $alethe_file"
    fi
done < <(find ./sample/ -type f -name '*.alethe' -print0)
echo ""
echo "Worked on $worked examples out of $total"
echo "$holey cases are holey"
echo "$not_compressable are not compressible"
echo "$compress_failed failed on compression"
echo "$check_failed failed on checking"
