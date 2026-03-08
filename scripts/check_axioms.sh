#!/bin/bash

# Search for 'axiom' declarations in the LeanSharp source directory.
# This script fails if any axioms are found, ensuring all results are proved within Lean.

SEARCH_DIR="LeanSharp"

if grep -rn "^axiom " "$SEARCH_DIR/"; then
    echo "ERROR: Unverified 'axiom' declarations found in $SEARCH_DIR source."
    echo "All theorems must be formally proved. Replace axioms with theorems."
    exit 1
fi

echo "✓ No axiom declarations found. All theorems formally proved."
exit 0
