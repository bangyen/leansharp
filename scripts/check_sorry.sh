#!/bin/bash

# Search for 'sorry' markers in the source directories.
# This script fails if any sorry markers are found, ensuring proof completeness.

SEARCH_DIRS=("LeanSharp" "Tests")

MATCHES=$(grep -rn "sorry" "${SEARCH_DIRS[@]}")

if [ -n "$MATCHES" ]; then
    echo "ERROR: 'sorry' markers found in source directories. All proofs must be completed."
    echo "$MATCHES"
    exit 1
fi

echo "✓ No 'sorry' markers found in source directories."
exit 0
