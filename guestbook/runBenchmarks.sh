#!/bin/sh

if [ ! -f "large_guestbook.txt" ]; then
	echo Generating tests
	ghc --make Testing
	./Testing
fi

echo Building time benchmarks
ghc --make GuestbookAG_Lazy  -DMEASURE_TIME -fforce-recomp
ghc --make GuestbookAG_nonHO -DMEASURE_TIME -fforce-recomp
ghc --make GuestbookAG       -DMEASURE_TIME -fforce-recomp

echo Running time benchmarks
rm GuestbookAG_Lazy_np.csv
rm GuestbookAG_nonHO_np.csv
rm GuestbookAG_np.csv
./GuestbookAG_Lazy  --csv GuestbookAG_Lazy_np.csv
./GuestbookAG_nonHO --csv GuestbookAG_nonHO_np.csv
./GuestbookAG       --csv GuestbookAG_np.csv

echo Processing runtimes
ghc --make ProcessTimings
./ProcessTimings GuestbookAG_Lazy_np.csv GuestbookAG_Lazy.csv
./ProcessTimings GuestbookAG_nonHO_np.csv GuestbookAG_nonHO.csv
./ProcessTimings GuestbookAG_np.csv GuestbookAG.csv

echo Creating barchart
barchart criterion --summary-comparison GuestbookAG_Lazy.csv GuestbookAG_nonHO.csv GuestbookAG.csv --pdf --colors="black silver gainsboro grey darkgrey" -t "Guestbook example"
