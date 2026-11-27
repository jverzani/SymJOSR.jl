# python3 -I driver.py PICKS SHARD NSHARDS OUT: runs worker.jl over its shard of PICKS;
# kills and restarts the worker when RischIntegrate overruns (60 s, plus a grace).
import subprocess, sys, select, time, os
picks, shard, nsh, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
here = os.path.dirname(os.path.abspath(__file__))
todo = [l.rstrip('\n') for i, l in enumerate(open(picks)) if i % nsh == shard]
done = set()
if os.path.exists(out):
    for l in open(out):
        a = l.split('\t')
        if a[0] == 'RISCH': done.add(a[1] + '\t' + a[2])
todo = [p for p in todo if p not in done]
fo = open(out, 'a')
def start():
    p = subprocess.Popen(['julia', '+1.13.4', '--heap-size-hint=4G', '--project=' + here, os.path.join(here, 'worker.jl')],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, bufsize=1)
    while True:
        l = p.stdout.readline()
        if not l: raise SystemExit('worker died at start')
        if l.startswith('READY'): return p
def readline(p, timeout):
    r, _, _ = select.select([p.stdout], [], [], timeout)
    return p.stdout.readline() if r else None
p = start()
for item in todo:
    p.stdin.write(item + '\n'); p.stdin.flush()
    got_osr = False; t0 = time.time()
    while True:
        limit = 150 if not got_osr else 65
        l = readline(p, limit)
        if l is None or l == '':
            f, i = item.split('\t')
            if not got_osr: fo.write(f'OSR\t{f}\t{i}\ttimeout\t{time.time()-t0:.3f}\t0\t0\tkilled\n')
            fo.write(f'RISCH\t{f}\t{i}\ttimeout\t{limit}\t0\t0\tkilled\n'); fo.flush()
            p.kill(); p.wait(); p = start(); break
        if l.startswith('OSR'): got_osr = True; fo.write(l); fo.flush()
        elif l.startswith('RISCH'): fo.write(l); fo.flush(); break
p.stdin.close(); p.wait()
