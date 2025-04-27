#!/bin/bash

# Navigate to the policies directory
cd policies

# Loop through all subdirectories except "toy"
for dir in */; do
    # Skip the "toy" directory
    if [ "$dir" = "toy/" ]; then
        continue
    fi

    echo "Processing directory: $dir"
    
    # Enter the subdirectory
    cd "$dir"
    
    # Loop through all .txt files
    for file in *.txt; do
        # Check if file exists (to handle case where no .txt files exist)
        if [ -f "$file" ]; then
            echo "Processing file: $file"
            
            # Run the compiler
            cargo run -p paralegal-compiler -- "$file" --bin
            
            # Check if compiled_policy.rs was created
            if [ -f "compiled_policy.rs" ]; then
                # Copy to playground
                cp compiled_policy.rs ~/paralegal-playground/src/main.rs
                
                # Run cargo check in playground directory
                echo "Running cargo check for $file..."
                (cd ~/paralegal-playground && RUSTFLAGS=-Awarnings cargo check)
                
                # Remove the compiled_policy.rs file
                rm compiled_policy.rs
            else
                echo "Error: compiled_policy.rs was not created for $file"
            fi
        fi
    done
    
    # Go back to policies directory
    cd ..
done

# Clean up the playground main.rs file as well
rm ~/paralegal-playground/src/main.rs