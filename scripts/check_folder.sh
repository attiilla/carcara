#!/bin/bash

# Define the function to process each file
process_file() {
    local alethe_file="$1"
    local smt2_file="$2"
    local base_name="${alethe_file%.*}"  # Remove the extension to get the base name
    

    # Run the first command
    ./target/debug/carcara check -i --allow-int-real-subtyping --expand-let-bindings "$alethe_file" "$smt2_file" > /dev/null 2>/dev/null
    if [ $? -ne 0 ]; then
        echo "Failed on checking the original proof $alethe_file"
        return 1
    fi

    # Run the second command 
    # --no-print-with-sharing off
    ./target/debug/carcara compress --allow-int-real-subtyping --expand-let-bindings "$alethe_file" "$smt2_file" > "${base_name}.Calethe" 2>/dev/null
    if [ $? -ne 0 ]; then
        echo "Failed on compressing $alethe_file"
        return 2
    fi

    # Run the third command
    output=$(./target/debug/carcara check -i --allow-int-real-subtyping --expand-let-bindings "${base_name}.Calethe" "$smt2_file" 2>/dev/null)
    if [ $? -ne 0 ]; then
        echo "Failed on checking the compressed proof ${base_name}.Calethe"
        #rm "${base_name}.Calethe"
        return 3
    fi

    echo "$alethe_file - $output"
}
dir=$1
total=0
worked=0
check_err=0
compress_err=0
post_check_err=0
# Find all .alethe files in the sample directory and its subdirectories
while IFS= read -r -d '' alethe_file; do
    # Extract the corresponding .smt2 file
    smt2_file="${alethe_file%.alethe}.smt2"
    
    # Check if the paired .smt2 file exists
    if [ -f "$smt2_file" ]; then
        # Process the files and store the result
        
        #process_file "$alethe_file" "$smt2_file"
        #return_value=$?

        output=$(process_file "$alethe_file" "$smt2_file")
        return_value=$?
        echo "$output"

        #echo "For $smt2_file the result is:$result"
        #return_value="$(echo "$result" colega| awk 'NR==2')"
        #result="$(echo "$result"| awk 'NR==1')"
        #echo "result=$result"
        #echo "return value=$return_value"
        # Check the return value of the process_file function
        case $return_value in
            0)
                ((worked++))
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
