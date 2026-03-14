#!/bin/bash

# Search for 'axiom' declarations in the source directories.
# This script fails if any axioms are found, ensuring all results are proved within Lean.

SEARCH_DIRS=("LeanSharp" "Tests")

MATCHES=$(grep -rn "^axiom " "${SEARCH_DIRS[@]}")

if [ -n "$MATCHES" ]; then
    echo "ERROR: Unverified 'axiom' declarations found in source directories."
    echo "All theorems must be formally proved. Replace axioms with theorems."
    echo "$MATCHES"
    exit 1
fi

echo "✓ No axiom declarations found. All theorems formally proved."
exit 0
