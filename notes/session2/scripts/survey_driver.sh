#!/bin/bash
# runs survey2.jl, killing it when one problem runs past 60 s; that problem goes to HANG
SP=$1; cd /Users/jverzani/julia/SymJOSR.jl
OUT=$SP/survey.tsv; HANG=$SP/survey_hang.tsv; PROG=$SP/survey.prog
touch $HANG
while true; do
  rm -f $PROG
  julia --project=. $SP/survey2.jl $OUT $HANG $PROG > $SP/survey2.log 2>&1 &
  pid=$!
  last=""; since=$(date +%s)
  while kill -0 $pid 2>/dev/null; do
    sleep 5
    cur=$(cat $PROG 2>/dev/null)
    if [ "$cur" != "$last" ]; then last=$cur; since=$(date +%s); fi
    if [ -n "$cur" ] && [ "$cur" != "DONE" ] && [ $(( $(date +%s) - since )) -gt 60 ]; then
      kill -9 $pid; wait $pid 2>/dev/null
      printf "%s\thang\n" "$cur" >> $HANG
      echo "hang: $cur"
      break
    fi
  done
  [ "$(cat $PROG 2>/dev/null)" = "DONE" ] && { echo "survey done"; break; }
  kill -0 $pid 2>/dev/null || [ -n "$(tail -1 $HANG | grep -F "$last")" ] || { echo "julia exited early"; tail -5 $SP/survey2.log; break; }
done
