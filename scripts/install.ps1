# SLOP Installation Script for Windows
#
# Usage:
#   .\install.ps1              # Install to %LOCALAPPDATA%\slop
#   $env:SLOP_PREFIX="C:\slop" ; .\install.ps1  # Install to custom location
#

$ErrorActionPreference = "Stop"

$InstallDir = if ($env:SLOP_PREFIX) { $env:SLOP_PREFIX } else { "$env:LOCALAPPDATA\slop" }
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path

Write-Host "Installing SLOP to $InstallDir..."
Write-Host ""

# Create directories
New-Item -ItemType Directory -Force -Path "$InstallDir\bin" | Out-Null
New-Item -ItemType Directory -Force -Path "$InstallDir\lib" | Out-Null
New-Item -ItemType Directory -Force -Path "$InstallDir\spec" | Out-Null
New-Item -ItemType Directory -Force -Path "$InstallDir\examples" | Out-Null

# Copy binaries
Write-Host "  Installing binaries..."
Copy-Item -Force "$ScriptDir\bin\*" "$InstallDir\bin\"

# Copy libraries
Write-Host "  Installing libraries..."
Copy-Item -Recurse -Force "$ScriptDir\lib\*" "$InstallDir\lib\"

# Copy specs
Write-Host "  Installing specs..."
Copy-Item -Recurse -Force "$ScriptDir\spec\*" "$InstallDir\spec\"

# Copy examples
Write-Host "  Installing examples..."
Copy-Item -Recurse -Force "$ScriptDir\examples\*" "$InstallDir\examples\"

# Add to PATH
$CurrentPath = [Environment]::GetEnvironmentVariable("Path", "User")
$BinPath = "$InstallDir\bin"

if ($CurrentPath -notlike "*$BinPath*") {
    Write-Host ""
    Write-Host "Adding $BinPath to PATH..."
    [Environment]::SetEnvironmentVariable("Path", "$CurrentPath;$BinPath", "User")
    Write-Host "  PATH updated (restart terminal to apply)"
}

Write-Host ""
Write-Host "SLOP installed successfully!"
Write-Host ""
Write-Host "  Commands:"
Write-Host "    slop              Python CLI (parse, transpile, build, fill)"
Write-Host "    slop-parser       Native parser"
Write-Host "    slop-checker      Native type checker"
Write-Host "    slop-compiler     Native compiler (type check + transpile)"
Write-Host "    slop-tester       Native test runner"
Write-Host ""
Write-Host "  Locations:"
Write-Host "    Binaries:  $InstallDir\bin\"
Write-Host "    Libraries: $InstallDir\lib\"
Write-Host "    Specs:     $InstallDir\spec\"
Write-Host "    Examples:  $InstallDir\examples\"
Write-Host ""

# Check Python availability
try {
    $pythonVersion = python --version 2>&1
    Write-Host "Python: $pythonVersion"
} catch {
    Write-Host "Warning: Python not found. The 'slop' command requires Python 3.11+."
}
Write-Host ""
Write-Host "Try: slop --help"
