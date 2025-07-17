#!/bin/bash

# Lean 4 Setup Script for GitHub Codespaces
# This script installs Lean 4 and mathlib

set -e  # Exit on any error

echo "🚀 Setting up Lean 4 in GitHub Codespaces..."
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

# 3. Install VS Code extension
echo ""
echo "🔧 Installing Lean 4 VS Code extension..."

# Try multiple methods to ensure extension installation works
if code --install-extension leanprover.lean4 --force &> /dev/null; then
    echo "✅ Lean 4 VS Code extension installed via command line"
elif code --install-extension leanprover.lean4 &> /dev/null; then
    echo "✅ Lean 4 VS Code extension installed"
else
    echo "⚠️  Automatic installation may have failed"
fi

# Verify installation
if code --list-extensions | grep -q "leanprover.lean4"; then
    echo "✅ Lean 4 extension confirmed in extension list"
else
    echo "⚠️  Extension not found in list - manual installation may be needed"
    echo "   Go to Extensions view (Ctrl+Shift+X) and search for 'lean4'"
fi

# 4. Get mathlib cache for faster compilation
echo ""
echo "📚 Getting mathlib cache..."
if command -v lake &> /dev/null; then
    # Create lakefile.lean if missing, with mathlib dependency
    if [ ! -f "lakefile.lean" ]; then
        echo "📝 No Lake config file found. Initializing Lake project with mathlib..."
        cat > lakefile.lean <<EOF
import Lake
open Lake DSL

package LEANintro

lean_lib LEANintro

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
EOF
    else
        # Add mathlib dependency if missing
        if ! grep -q 'require mathlib' lakefile.lean; then
            echo "🔗 Adding mathlib dependency to lakefile.lean..."
            echo '
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
' >> lakefile.lean
        fi
    fi
    echo "🔄 Updating lake..."
    lake update
    echo "📥 Downloading precompiled mathlib libraries..."
    lake -R mathlib cache get
    echo "✅ Mathlib cache downloaded successfully"
else
    echo "⚠️  Lake not found - skipping mathlib cache"
fi