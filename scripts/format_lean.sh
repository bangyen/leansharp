#!/bin/bash

set -euo pipefail

# Format Lean files by:
# 1) collapsing repeated blank lines
# 2) sorting the first contiguous import block alphabetically
# By default, this targets all tracked .lean files.

collect_targets() {
    if [ "$#" -gt 0 ]; then
        printf '%s\n' "$@"
        return
    fi

    git ls-files '*.lean'
}

format_file() {
    local file_path="$1"
    local temp_file
    local sorted_file

    if [ ! -f "$file_path" ]; then
        echo "Skipping missing file: $file_path"
        return
    fi

    temp_file="$(mktemp)"
    sorted_file="$(mktemp)"
    awk '
        {
            if ($0 ~ /^[[:space:]]*$/) {
                blank_count += 1
                if (blank_count <= 1) {
                    print
                }
            } else {
                blank_count = 0
                print
            }
        }
    ' "$file_path" > "$temp_file"

    awk '
        BEGIN {
            import_start = 0
            import_end = 0
        }
        {
            lines[NR] = $0
            if (import_start == 0 && $0 ~ /^import[[:space:]]+/) {
                import_start = NR
            } else if (import_start > 0 && import_end == 0 && $0 !~ /^import[[:space:]]+/) {
                import_end = NR - 1
            }
        }
        END {
            if (NR == 0) {
                exit
            }

            if (import_start == 0) {
                for (i = 1; i <= NR; i++) {
                    print lines[i]
                }
                exit
            }

            if (import_end == 0) {
                import_end = NR
            }

            for (i = 1; i < import_start; i++) {
                print lines[i]
            }

            for (i = import_start; i <= import_end; i++) {
                print lines[i] | "LC_ALL=C sort"
            }
            close("LC_ALL=C sort")

            for (i = import_end + 1; i <= NR; i++) {
                print lines[i]
            }
        }
    ' "$temp_file" > "$sorted_file"

    mv "$sorted_file" "$file_path"
    rm -f "$temp_file"
}

main() {
    local targets=()
    local line

    while IFS= read -r line; do
        targets+=("$line")
    done < <(collect_targets "$@")

    if [ "${#targets[@]}" -eq 0 ]; then
        echo "No .lean files found."
        exit 0
    fi

    for file_path in "${targets[@]}"; do
        format_file "$file_path"
    done

    echo "Formatted ${#targets[@]} Lean file(s)."
}

main "$@"
