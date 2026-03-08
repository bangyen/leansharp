#!/bin/bash

# Search for 'sorry' markers in the LeanSharp source directory.
# This script fails if any sorry markers are found, ensuring proof completeness.

SEARCH_DIR="LeanSharp"

if grep -rn "sorry" "$SEARCH_DIR"; then
    echo "ERROR: 'sorry' markers found in $SEARCH_DIR. All proofs must be completed before merging."
    exit 1
fi

echo "✓ No 'sorry' markers found in $SEARCH_DIR."
exit 0
