import collections, glob, re, statistics as st
rows = collections.defaultdict(dict)
for fn in glob.glob('results.tsv'):
    for l in open(fn, encoding='utf-8'):
        a = l.rstrip('\n').split('\t'); rows[(a[1], int(a[2]))][a[0]] = a
pw = {(a[0], int(a[1])): a for a in (l.rstrip('\n').split('\t') for l in open('rescore_out.tsv', encoding='utf-8'))}
def rstat(k, r):
    s = r[3]
    if s == 'verified': return 'verified'
    if s == 'wrong': return 'wrong'
    if s == 'timeout': return 'timeout'
    if k in pw:
        p = pw[k]
        if p[2] == 'piecewise': return 'pw-verified' if p[4] == p[3] else ('pw-partial' if int(p[4]) > 0 else 'pw-unverified')
        return 'verified' if p[4] == p[3] else 'unevaluated'
    m = r[7]
    if m.startswith('NotElementary'): return 'not-elementary'
    if m.startswith('RischNotImplemented'): return 'not-implemented'
    return 'error' if s == 'error' or re.match(r'^\w+Error', m) else 'unevaluated'
ok = {'verified', 'pw-verified'}
sec = lambda f: f.split('/')[0]
T = collections.Counter(); TS = collections.defaultdict(collections.Counter)
RS = collections.Counter(); OS = collections.Counter(); cross = collections.Counter()
both = []; only_o = []; only_r = []; wrong = []
for k, v in rows.items():
    o, r = v['OSR'], v['RISCH']; os_, rs = o[3], rstat(k, r)
    OS[os_] += 1; RS[rs] += 1
    a, b = os_ == 'verified', rs in ok
    cat = {(1,1): 'both', (1,0): 'only SymJOSR', (0,1): 'only Risch', (0,0): 'neither'}[(a, b)]
    T[cat] += 1; TS[sec(k[0])][cat] += 1
    if a and not b: cross[rs] += 1; only_o.append((k, rs, o))
    if b and not a: only_r.append((k, os_, r))
    if a and b: both.append((k, o, r, rs))
    if os_ == 'wrong' or rs == 'wrong': wrong.append((k, os_, rs, o[7][:90], r[7][:90]))
print('N', len(rows)); print('OSR', dict(OS)); print('RISCH', dict(RS)); print(dict(T))
print('\nper section: both / only SymJOSR / only Risch / neither')
for s in sorted(TS): c = TS[s]; print(f'{s:16s} {sum(c.values()):4d}  {c["both"]:4d} {c["only SymJOSR"]:4d} {c["only Risch"]:4d} {c["neither"]:4d}')
print('\nRisch status where only SymJOSR solves:', dict(cross))
print('SymJOSR status where only Risch solves:', dict(collections.Counter(x[1] for x in only_r)))
# sizes, single-expression answers only
single = [(k, int(o[5]), int(o[6]), int(r[5]), int(r[6])) for k, o, r, rs in both if rs == 'verified' and int(r[5]) > 0]
for nm, i, j in (('leafcount', 1, 3), ('ops', 2, 4)):
    sh_o = sum(x[i] < x[j] for x in single); sh_r = sum(x[i] > x[j] for x in single); eq = sum(x[i] == x[j] for x in single)
    rat = [x[j] / x[i] for x in single if x[i] > 0]
    print(f'\n{nm}: {len(single)} pairs; SymJOSR shorter {sh_o}, Risch shorter {sh_r}, equal {eq}; median Risch/SymJOSR {st.median(rat):.2f}; quartiles {st.quantiles(rat, n=4)}')
    for s in sorted(TS):
        xs = [x for x in single if sec(x[0][0]) == s]
        if xs: print(f'   {s:16s} n={len(xs):3d} SymJOSR shorter {sum(x[i] < x[j] for x in xs):3d}, Risch shorter {sum(x[i] > x[j] for x in xs):3d}, equal {sum(x[i] == x[j] for x in xs):3d}, median ratio {st.median([x[j]/x[i] for x in xs]):.2f}')
ident = sum(1 for k, o, r, rs in both if rs == 'verified' and o[7] == r[7]); print('identical strings', ident)
# times
tb = [(float(o[4]), float(r[4])) for k, o, r, rs in both]
print('\ntime (both solved): median SymJOSR %.2fs, Risch %.2fs; SymJOSR faster in %d of %d' % (st.median(x[0] for x in tb), st.median(x[1] for x in tb), sum(x[0] < x[1] for x in tb), len(tb)))
print('pw-verified among both', sum(1 for x in both if x[3] == 'pw-verified'))
print('\nwrong:'); [print(w) for w in wrong]
