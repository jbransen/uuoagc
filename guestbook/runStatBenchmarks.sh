#!/bin/sh

if [ ! -f "large_guestbook.txt" ]; then
	echo Generating tests
	ghc --make Testing
	./Testing
fi

echo Building stat benchmarks
ghc --make GuestbookAG_Lazy  -DGATHER_STATS -fforce-recomp
ghc --make GuestbookAG_nonHO -DGATHER_STATS -fforce-recomp
ghc --make GuestbookAG       -DGATHER_STATS -fforce-recomp

echo Running stat benchmarks
echo GuestbookAG_Lazy
./GuestbookAG_Lazy
echo GuestbookAG_nonHO
./GuestbookAG_nonHO
echo GuestbookAG
./GuestbookAG
