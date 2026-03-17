#!/bin/bash

# Check that all Lean files include a module description block.
# We require at least one '/-!' doc block in each file.

MATCHES=()

while IFS= read -r file_path; do
    [ -z "$file_path" ] && continue

    if ! grep -qE '^[[:space:]]*/-!' "$file_path"; then
        MATCHES+=("$file_path")
    fi
done < <(git ls-files '*.lean')

if [ "${#MATCHES[@]}" -gt 0 ]; then
    echo "ERROR: Missing module description blocks in Lean files."
    echo "Add a '/-! ... -/' block describing why each file exists."
    printf "%s\n" "${MATCHES[@]}"
    exit 1
fi

echo "✓ All Lean files include a module description block."
exit 0
