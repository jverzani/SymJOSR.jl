#!/usr/bin/env python3
"""
Compare the OpenSymbolicRules Integration rule files with RUBI's, file by file.

For each rule file that RUBI 4.16.1 loads (in the order of Rubi.m), counts the rules in
RUBI's .m file (the `Int[...] := ...` definitions; commented-out rules are not counted)
and in the corresponding OSR JSON file (the entries of "rules"), and how many of RUBI's
rules use With[...] or Module[...]. Reports the empty OSR files, the partial ones, and
the OSR rule files that RUBI 4.16.1 does not load.

Usage:
    python3 compare_osr_rubi.py RUBI_DIR OSR_DIR [--markdown]

    RUBI_DIR  a checkout of https://github.com/RuleBasedIntegration/Rubi (the directory
              that has Rubi/Rubi.m)
    OSR_DIR   a checkout of https://github.com/OpenSymbolicRules/Integration (the
              directory that has rules/)

The list of files RUBI loads is read from Rubi/Rubi.m, the LoadRules[FileNameJoin[...]]
calls in order. OSR file names are RUBI's with spaces replaced by '-'.

Written for SymJOSR.jl (notes/session2), 2026-11-24. At OSR a6a19ab and RUBI 61e9c18 it
reports 199 files, 7,432 rules in RUBI, 5,439 in OSR: 30 empty files (1,113 rules), 95
partial files (880 rules short, 860 With/Module rules in them), 22 OSR files not loaded.
"""
import glob
import json
import os
import re
import sys


def rubi_load_order(rubi_dir):
    """The rule files Rubi.m loads, in order, as base names ('1.1.1.2 (a+b x)^m ...')."""
    text = open(os.path.join(rubi_dir, "Rubi", "Rubi.m"), encoding="utf-8").read()
    out = []
    for m in re.finditer(r'LoadRules\[FileNameJoin\[\{([^}]*)\}\]\]', text):
        parts = re.findall(r'"([^"]*)"', m.group(1))
        # rule files only: their names start with a section number ("1.1.1.2 ...")
        if parts and re.match(r"\d", parts[-1]):
            out.append(parts[-1])
    return out


def rubi_rules(path):
    """The rules of a RUBI .m file, each as its text (a rule may span lines)."""
    rules, cur = [], None
    for line in open(path, encoding="utf-8", errors="replace"):
        if line.startswith("Int["):
            if cur is not None:
                rules.append(cur)
            cur = line
        elif cur is not None:
            if line.strip() == "" or line.startswith("(*"):
                rules.append(cur)
                cur = None
            else:
                cur += line
    if cur is not None:
        rules.append(cur)
    return rules


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if len(args) != 2:
        sys.exit(__doc__)
    rubi_dir, osr_dir = args
    markdown = "--markdown" in sys.argv

    order = rubi_load_order(rubi_dir)
    mfiles = {os.path.basename(p)[:-2]: p for p in
              glob.glob(os.path.join(rubi_dir, "Rubi", "IntegrationRules", "**", "*.m"), recursive=True)}
    rules_root = os.path.join(osr_dir, "rules")
    jfiles = {os.path.basename(p)[:-5]: p for p in
              glob.glob(os.path.join(rules_root, "**", "*.json"), recursive=True)
              if not p.endswith("meta.json")}

    rows = []   # (name, rubi rules, rubi With/Module rules, osr rules or None)
    for name in order:
        m = mfiles.get(name)
        j = jfiles.get(name.replace(" ", "-"))
        rs = rubi_rules(m) if m else []
        scoped = sum(1 for r in rs if "With[" in r or "Module[" in r)
        n_osr = len(json.load(open(j, encoding="utf-8"))["rules"]) if j else None
        rows.append((name, len(rs), scoped, n_osr))

    loaded = {name.replace(" ", "-") for name in order}
    not_loaded = sorted(os.path.relpath(p, rules_root) for b, p in jfiles.items() if b not in loaded)
    empty = [r for r in rows if r[3] == 0]
    partial = sorted((r for r in rows if r[3] and r[3] < r[1]), key=lambda r: r[3] - r[1])
    absent = [r for r in rows if r[3] is None]
    more = [r for r in rows if r[3] and r[3] > r[1]]

    tr, to = sum(r[1] for r in rows), sum(r[3] or 0 for r in rows)
    print(f"Files RUBI loads: {len(rows)}; rules in RUBI: {tr}; in OSR: {to}; missing: {tr - to}")

    def table(header, items):
        if markdown:
            print("| " + " | ".join(header) + " |")
            print("|:--|" + "--:|" * (len(header) - 1))
            for it in items:
                print("| " + " | ".join(str(x) for x in it) + " |")
        else:
            for it in items:
                print("  " + "\t".join(str(x) for x in it))

    print(f"\nEmpty in OSR: {len(empty)} files, {sum(r[1] for r in empty)} RUBI rules")
    table(["RUBI file", "rules in RUBI"], [(r[0], r[1]) for r in empty])
    print(f"\nPartial in OSR: {len(partial)} files, {sum(r[1] - r[3] for r in partial)} rules short; "
          f"With/Module rules in RUBI's versions: {sum(r[2] for r in partial)}")
    table(["RUBI file", "RUBI", "OSR", "short", "With/Module in RUBI"],
          [(r[0], r[1], r[3], r[1] - r[3], r[2]) for r in partial])
    print(f"\nNot in OSR at all: {len(absent)}")
    table(["RUBI file"], [(r[0],) for r in absent])
    print(f"\nMore rules in OSR than in RUBI: {len(more)}")
    table(["RUBI file", "RUBI", "OSR"], [(r[0], r[1], r[3]) for r in more])
    print(f"\nOSR rule files that RUBI 4.16.1 does not load: {len(not_loaded)}")
    table(["OSR file", "rules"],
          [(p, len(json.load(open(os.path.join(rules_root, p), encoding="utf-8"))["rules"])) for p in not_loaded])


if __name__ == "__main__":
    main()
