#!/bin/bash

# Compare the outputted policies in the policies/ folder between the most recent commit and the one before it.

# Exit on any error
set -e

# Create output directories
mkdir -p outputs/before outputs/after outputs/diffs

# Get the hash of the previous commit
PREV_COMMIT=$(git rev-parse HEAD~1)
CURR_COMMIT=$(git rev-parse HEAD)
REPO_DIR=$(pwd)

echo "Comparing compiler outputs for code at:"
echo "Previous commit: $PREV_COMMIT"
echo "Current commit:  $CURR_COMMIT"
echo ""

# Create a temporary directory for the previous commit
TEMP_DIR=$(mktemp -d)
echo "Created temporary directory: $TEMP_DIR"

# Copy current repository state to temp directory
echo "Copying repository content at previous commit..."
git archive $PREV_COMMIT | tar x -C $TEMP_DIR

# Find all .txt files in subdirectories of policies/ except toy/ at previous commit
txt_files=$(find policies/ -path "policies/toy" -prune -o -name "*.txt" -print)

# Function to convert a path to a safe filename
path_to_safe_name() {
    echo "$1" | sed 's/\//_/g'
}

# Compile each file using the previous commit's code
cd $TEMP_DIR
for file in $txt_files; do
    echo "Compiling $file with previous code..."
    safe_name=$(path_to_safe_name "$file")
    output_file="$REPO_DIR/outputs/before/${safe_name%.txt}_compiled.rs"
    cargo run -p paralegal-compiler -- "$file" --out "$output_file"
done

# Go back to the original directory
cd $REPO_DIR

# Create a summary file
summary_file="outputs/summary.md"
echo "# Compiler Output Comparison" > $summary_file
echo "" >> $summary_file
echo "**Previous commit:** $PREV_COMMIT" >> $summary_file
echo "**Current commit:** $CURR_COMMIT" >> $summary_file
echo "**Generated:** $(date)" >> $summary_file
echo "" >> $summary_file
echo "## Changes detected" >> $summary_file
echo "" >> $summary_file

# Compile each file using the current code
for file in $txt_files; do
    echo "Compiling $file with current code..."
    safe_name=$(path_to_safe_name "$file")
    output_file="outputs/after/${safe_name%.txt}_compiled.rs"
    cargo run -p paralegal-compiler -- "$file" --out "$output_file"
    
    # Generate diff
    before_file="outputs/before/${safe_name%.txt}_compiled.rs"
    after_file="$output_file"
    diff_file="outputs/diffs/${safe_name%.txt}_diff.txt"
    
    echo "Generating diff for $file..."
    if diff -u "$before_file" "$after_file" > "$diff_file" 2>/dev/null; then
        echo "  No changes detected in $file"
    else
        echo "  Changes detected in $file"
        # Count added/removed lines
        added=$(grep -c "^+" "$diff_file" || echo 0)
        removed=$(grep -c "^-" "$diff_file" || echo 0)
        
        # Adjust to not count the diff header
        added=$((added - 1))
        removed=$((removed - 1))
        
        echo "### $file" >> $summary_file
        echo "- Added lines: $added" >> $summary_file
        echo "- Removed lines: $removed" >> $summary_file
        echo "- [View diff](diffs/$(basename $diff_file))" >> $summary_file
        echo "" >> $summary_file
    fi
done

# Clean up
rm -rf $TEMP_DIR

echo ""
echo "Comparison complete. Results are in outputs/diffs directory."
echo "See outputs/summary.md for a summary of changes."