#!/bin/bash

# Check that Lean files do not exceed a maximum line count.
# Override the default threshold with MAX_LEAN_FILE_LINES.

MAX_LINES="${MAX_LEAN_FILE_LINES:-300}"

if ! [[ "$MAX_LINES" =~ ^[0-9]+$ ]] || [ "$MAX_LINES" -le 0 ]; then
    echo "ERROR: MAX_LEAN_FILE_LINES must be a positive integer."
    exit 1
fi

MATCHES=()

while IFS= read -r file_path; do
    [ -z "$file_path" ] && continue

    line_count="$(wc -l < "$file_path" | tr -d ' ')"
    if [ "$line_count" -gt "$MAX_LINES" ]; then
        MATCHES+=("$file_path:$line_count")
    fi
done < <(git ls-files '*.lean')

if [ "${#MATCHES[@]}" -gt 0 ]; then
    echo "ERROR: Found Lean files longer than ${MAX_LINES} lines."
    echo "Split large files into smaller modules where possible."
    printf "%s\n" "${MATCHES[@]}"
    exit 1
fi

echo "✓ All Lean files are within ${MAX_LINES} lines."
exit 0
