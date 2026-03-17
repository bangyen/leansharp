#!/bin/bash

# Search for 'set_option' directives in Lean source files.
# This script fails if any are found, keeping file behavior deterministic.

MATCHES=$(git grep -nE '^[[:space:]]*set_option[[:space:]]+' -- '*.lean')

if [ -n "$MATCHES" ]; then
    echo "ERROR: 'set_option' directives found in source directories."
    echo "Move option changes to local attributes or remove them."
    echo "$MATCHES"
    exit 1
fi

echo "✓ No 'set_option' directives found in source directories."
exit 0
