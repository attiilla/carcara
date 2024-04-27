find ./sample/ -type f -name '*.ealethe' -print0 | while IFS= read -r -d '' ealethe_file; do
    rm "$ealethe_file"
done

find ./sample/ -type f -name '*.calethe' -print0 | while IFS= read -r -d '' calethe_file; do
    rm "$calethe_file"
done