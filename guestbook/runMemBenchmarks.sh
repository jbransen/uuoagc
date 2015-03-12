#!/bin/sh

echo Building memory benchmark
ghc --make GuestbookMem -prof -fforce-recomp

echo Running memory benchmark
./GuestbookMem +RTS -h

echo Converting to pdf
hp2ps GuestbookMem.hp
ps2pdf GuestbookMem.ps
