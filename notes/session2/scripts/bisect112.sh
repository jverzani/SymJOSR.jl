#!/bin/bash
# precompile SymJOSR on Julia 1.12 with only the first N source files included
SP=$1
files=(fetch osr heads predicates utilities sums integration testsuite)
for n in 2 3 4 5 6 7 8; do
  d=$SP/bis$n; rm -rf $d; cp -R $SP/wt112 $d; rm -rf $d/.git
  inc=""; for f in "${files[@]:0:$n}"; do inc="$inc"$'\n'"include(\"$f.jl\")"; done
  python3 - "$d/src/SymJOSR.jl" "$inc" <<'PY'
import sys, re
p, inc = sys.argv[1], sys.argv[2]
s = open(p).read()
s = re.sub(r'(include\("[a-z]+\.jl"\)\n)+', inc.strip()+"\n", s)
open(p, 'w').write(s)
PY
  rm -rf ~/.julia/compiled/v1.12/SymJOSR
  t=$(date +%s)
  (cd $d && timeout 360 julia +1.12 --project=. -e 'using SymJOSR' > $d.log 2>&1); rc=$?
  echo "first $n files (${files[$((n-1))]}): rc=$rc $(( $(date +%s) - t )) s"
  [ $rc -ne 0 ] && { tail -3 $d.log; break; }
done
