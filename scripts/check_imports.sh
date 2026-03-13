#!/usr/bin/env bash

ROOT_FILE="LeanSharp.lean"
SRC_DIR="LeanSharp"
EXIT_CODE=0

# Find all lean files and convert paths to Lean module names
for file in $(find "$SRC_DIR" -type f -name "*.lean"); do
    # Convert 'LeanSharp/Core/Curvature.lean' to 'LeanSharp.Core.Curvature'
    module=$(echo "$file" | sed 's/\.lean$//' | tr '/' '.')
    
    # Check if the root file contains the import statement
    if ! grep -q "^import $module" "$ROOT_FILE"; then
        echo "Error: Missing import for $module in $ROOT_FILE"
        EXIT_CODE=1
    fi
done

if [ $EXIT_CODE -eq 0 ]; then
    echo "Check passed: All source files are imported in $ROOT_FILE."
fi

exit $EXIT_CODE
