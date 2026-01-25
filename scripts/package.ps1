# SLOP Distribution Packaging Script for Windows
#
# Usage:
#   $env:RELEASE_VERSION="v0.1.0" ; .\package.ps1
#

$ErrorActionPreference = "Stop"

$Version = if ($env:RELEASE_VERSION) { $env:RELEASE_VERSION } else { "dev" }
$DistName = "slop-$Version-windows-x64"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$RootDir = Split-Path -Parent $ScriptDir

Write-Host "Packaging SLOP $Version for Windows x64..."
Write-Host ""

# Create distribution directory structure
New-Item -ItemType Directory -Force -Path "dist\$DistName\bin" | Out-Null
New-Item -ItemType Directory -Force -Path "dist\$DistName\lib\std" | Out-Null
New-Item -ItemType Directory -Force -Path "dist\$DistName\lib\runtime" | Out-Null
New-Item -ItemType Directory -Force -Path "dist\$DistName\lib\python" | Out-Null
New-Item -ItemType Directory -Force -Path "dist\$DistName\spec" | Out-Null
New-Item -ItemType Directory -Force -Path "dist\$DistName\examples" | Out-Null

# Copy binaries
Write-Host "  Copying binaries..."
Copy-Item "$RootDir\bootstrap\bin\*" "dist\$DistName\bin\"

# Copy standard library
Write-Host "  Copying standard library..."
Copy-Item -Recurse "$RootDir\lib\std\*" "dist\$DistName\lib\std\"

# Copy runtime header
Write-Host "  Copying runtime..."
Copy-Item "$RootDir\bootstrap\runtime\slop_runtime.h" "dist\$DistName\lib\runtime\"

# Copy Python tools (as a proper package)
Write-Host "  Copying Python tools..."
New-Item -ItemType Directory -Force -Path "dist\$DistName\lib\python\slop" | Out-Null
Copy-Item -Recurse "$RootDir\src\slop\*" "dist\$DistName\lib\python\slop\"

# Create slop wrapper script for Python CLI
Write-Host "  Creating slop wrapper..."
$WrapperContent = @'
@echo off
setlocal
set SCRIPT_DIR=%~dp0
set SLOP_ROOT=%SCRIPT_DIR%..
set PYTHONPATH=%SLOP_ROOT%\lib\python;%PYTHONPATH%
python -m slop.cli %*
'@
Set-Content -Path "dist\$DistName\bin\slop.cmd" -Value $WrapperContent

# Copy specs
Write-Host "  Copying specs..."
Copy-Item "$RootDir\spec\*.md" "dist\$DistName\spec\"

# Copy examples
Write-Host "  Copying examples..."
Copy-Item -Recurse "$RootDir\examples\*" "dist\$DistName\examples\"

# Copy docs
Write-Host "  Copying docs..."
if (Test-Path "$RootDir\LICENSE") {
    Copy-Item "$RootDir\LICENSE" "dist\$DistName\"
}
if (Test-Path "$RootDir\README.md") {
    Copy-Item "$RootDir\README.md" "dist\$DistName\"
}

# Copy Windows installer
Copy-Item "$ScriptDir\install.ps1" "dist\$DistName\"

# Create archive
Write-Host ""
Write-Host "  Creating archive..."
Compress-Archive -Path "dist\$DistName" -DestinationPath "dist\$DistName.zip" -Force

Write-Host ""
Write-Host "Created: dist\$DistName.zip"

# Show contents
Write-Host ""
Write-Host "Package contents:"
Get-ChildItem "dist\$DistName" -Recurse | Select-Object FullName
