#!/bin/sh

## Build the native slop toolchain

# Build the parser
cd lib/compiler/parser
slop build
mv ./slop-parser ../../../bin

## Build the checker
cd ../checker
slop build
mv ./slop-checker ../../../bin

## Build the tester
cd ../tester
slop build
mv ./slop-tester ../../../bin

## Build the merged compiler (checker + transpiler)
cd ../compiler
slop build
mv ./slop-compiler ../../../bin
