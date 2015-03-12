#!/bin/sh

echo Building stat benchmarks
ghc --make CSharp -fcontext-stack=40 -DGATHER_STATS -fforce-recomp

echo Running stat benchmarks
./CSharp
