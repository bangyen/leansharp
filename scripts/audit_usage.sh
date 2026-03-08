#!/bin/bash

# Formalized Audit Script: Identifies public symbols with low external usage.
# This helps maintain a clean API by identifying candidates for 'private' visibility.

SEARCH_DIR="LeanSharp"

# Get all lemmas, theorems, and defs that are not already private or protected
grep -rE "^(lemma|theorem|def|abbrev|noncomputable def|noncomputable lemma|noncomputable theorem)" "$SEARCH_DIR" | grep -v "private" | grep -v "protected" | while read -r line; do
    file=$(echo "$line" | cut -d: -f1)
    
    # Extract symbol name, handling common signatures
    symbol=$(echo "$line" | cut -d: -f2- | sed -E 's/^(lemma|theorem|def|abbrev|noncomputable def|noncomputable lemma|noncomputable theorem) ([^ (:]+).*/\2/')
    
    # Skip common noise and very short symbols
    if [[ "$symbol" =~ ^(W|d|Ω|L|w)$ ]]; then continue; fi

    # Count occurrences in the whole project (excluding the definition and keywords/comments)
    count=$(grep -rw "$symbol" "$SEARCH_DIR" | grep -v "$file" | wc -l)
    
    # If count is 0, it is a strong candidate for being private or deleted
    if [ "$count" -eq 0 ]; then
        echo "AUDIT WARNING: '$symbol' in $file has 0 uses outside its defining file. Consider making it 'private'."
    fi
done

exit 0
