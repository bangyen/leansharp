#!/bin/bash

# Check that all .lean files in the source directories are imported in their root files.
# This script fails if any imports are missing, ensuring the linters check all files.

SEARCH_DIRS=("LeanSharp" "Tests")
MATCHES=()

for dir in "${SEARCH_DIRS[@]}"; do
    root_file="${dir}.lean"

    if [ ! -f "$root_file" ]; then
        MATCHES+=("Missing root file: ${root_file}")
        continue
    fi

    while IFS= read -r file; do
        module="${file%.lean}"
        module="${module//\//.}"

        if ! grep -q "^import $module" "$root_file"; then
            MATCHES+=("${root_file}: missing 'import ${module}'")
        fi
    done < <(git ls-files "${dir}/*.lean")
done

if [ ${#MATCHES[@]} -gt 0 ]; then
    echo "ERROR: Missing imports found. All modules must be imported in their root files."
    printf "%s\n" "${MATCHES[@]}"
    exit 1
fi

echo "✓ All modules are successfully imported in their root files."
exit 0