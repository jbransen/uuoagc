#!/bin/sh

echo Building benchmarks
ghc --make CSharp_Lazy  -fforce-recomp -fcontext-stack=40
ghc --make CSharp_nonHO -fforce-recomp -fcontext-stack=40
ghc --make CSharp       -fforce-recomp -fcontext-stack=40

echo Running benchmarks
rm CSharp_Lazy_np.csv
rm CSharp_nonHO_np.csv
rm CSharp_np.csv
./CSharp_Lazy  --csv CSharp_Lazy_np.csv
./CSharp_nonHO --csv CSharp_nonHO_np.csv
./CSharp       --csv CSharp_np.csv

echo Processing runtimes
# ghc --make ../../guestbook/ProcessTimings
../../guestbook/ProcessTimings CSharp_Lazy_np.csv CSharp_Lazy.csv
../../guestbook/ProcessTimings CSharp_nonHO_np.csv CSharp_nonHO.csv
../../guestbook/ProcessTimings CSharp_np.csv CSharp.csv


echo Creating barchart
barchart criterion --summary-comparison CSharp_Lazy.csv CSharp_nonHO.csv CSharp.csv --pdf --colors="black silver gainsboro grey darkgrey" -t "C# example"
