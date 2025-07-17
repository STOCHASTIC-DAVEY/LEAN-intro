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

# 3. Install VS Code extension
echo ""
echo "🔧 Installing Lean 4 VS Code extension..."
code --install-extension leanprover.lean4
echo "✅ Lean 4 VS Code extension installed"

echo ""
echo "🎉 Setup complete! Lean 4 is now installed."
echo "   • Lean 4 with elan version manager"
echo "   • Lean 4 VS Code extension"
echo ""
echo "💡 To use mathlib in a project:"
echo "   1. Create a new directory: mkdir my-project && cd my-project"
echo "   2. Initialize with mathlib: lake init MyProject && lake exe cache get"
echo "   3. Add mathlib to lakefile.lean: echo 'require mathlib from git "https://github.com/leanprover-community/mathlib4.git"' >> lakefile.lean"
echo "   4. Update dependencies: lake update && lake exe cache get"
echo ""
echo "📚 Useful resources:"
echo "   • Lean 4 Manual: https://leanprover.github.io/lean4/doc/"
echo "   • Mathematics in Lean: https://leanprover-community.github.io/mathematics_in_lean/"
echo "   • Mathlib Docs: https://leanprover-community.github.io/mathlib4_docs/"
echo "   • Lean Zulip Chat: https://leanprover.zulipchat.com/"
