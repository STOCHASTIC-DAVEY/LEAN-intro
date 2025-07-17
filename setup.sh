#!/bin/bash

# Lean 4 Setup Script for GitHub Codespaces
# This script installs Lean 4 and mathlib

set -e  # Exit on any error

echo "🚀 Setting up Lean 4 and mathlib in GitHub Codespaces..."
echo ""

# 1. Install elan (Lean version manager)
echo "📦 Installing elan (Lean version manager)..."
if ! command -v elan &> /dev/null; then
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
    # Ensure PATH is set for current session
    source ~/.profile
    export PATH="$HOME/.elan/bin:$PATH"
    # Also add to bashrc for future sessions
    if ! grep -q ".elan/bin" ~/.bashrc; then
        echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
    fi
    echo "✅ elan installed successfully"
else
    echo "✅ elan already installed"
fi

# Ensure PATH is set for current session even if elan was already installed
export PATH="$HOME/.elan/bin:$PATH"

# 2. Verify Lean installation
echo ""
echo "🔍 Verifying Lean installation..."
if command -v lean &> /dev/null; then
    echo "✅ Lean $(lean --version | cut -d' ' -f3) is installed"
else
    echo "❌ Lean installation failed"
    exit 1
fi

# 3. Create Lean project with mathlib
echo ""
echo "📚 Creating Lean project with mathlib..."
if [ ! -f "lakefile.lean" ]; then
    # Initialize new Lean project
    lake init LeanProject
    cd LeanProject
    
    # Add mathlib dependency
    echo "Adding mathlib dependency..."
    cat > lakefile.lean << 'EOF'
import Lake
open Lake DSL

package «LeanProject» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LeanProject» where
  -- add library configuration options here
EOF

    # Get mathlib cache and build
    echo "📥 Downloading mathlib cache..."
    lake exe cache get
    
    echo "🔨 Building project..."
    lake build
    
    echo "✅ Lean project with mathlib created successfully"
else
    echo "✅ Lean project already exists"
fi

# 4. Install VS Code extension
echo ""
echo "🔧 Installing Lean 4 VS Code extension..."
code --install-extension leanprover.lean4
echo "✅ Lean 4 VS Code extension installed"

echo ""
echo "🎉 Setup complete! Lean 4 with mathlib is now ready."
echo "🔬 You can now use 'import Mathlib' in your Lean files!"