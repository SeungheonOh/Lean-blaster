#!/usr/bin/env python3
"""Compare blaster verdicts against the Lean oracle.  Usage: check.py <rundir> [<rundir> ...]"""
import collections, json, os, sys


def load(path):
    res = collections.defaultdict(list)
    exitc = None
    if not os.path.exists(path):
        return None, None
    for ln in open(path, errors="replace"):
        ln = ln.strip()
        if ln.startswith("EXIT "):
            exitc = int(ln.split()[1])
            continue
        try:
            m = json.loads(ln)
        except Exception:
            continue
        res[m["pos"]["line"]].append((m["severity"], m["data"]))
    return res, exitc


def verdict(msgs):
    if msgs is None:
        return "MISSING"
    texts = [d for s, d in msgs if s != "warning" or "Undetermined" in d]
    for s, d in msgs:
        if "✅ Valid" in d:
            return "VALID"
    for s, d in msgs:
        if "Falsified" in d:
            return "FALSIFIED"
    for s, d in msgs:
        if "Undetermined" in d:
            return "UNDET"
    errs = [d for s, d in msgs if s == "error"]
    if errs:
        return "ERROR"
    return "NONE"


def oracle(msgs):
    if not msgs:
        return None
    for s, d in msgs:
        if s == "error":
            return "OERR"
        if d.strip() in ("true", "false"):
            return d.strip()
    return None


def main():
    allstats = collections.Counter()
    hits, comp, errors, missing = [], [], collections.Counter(), 0
    for D in sys.argv[1:]:
        props = [json.loads(l) for l in open(os.path.join(D, "props.jsonl"))]
        cache = {}
        for p in props:
            tag = p["tag"]
            if tag not in cache:
                cache[tag] = (load(os.path.join(D, f"blast_{tag}.json")), load(os.path.join(D, f"oracle_{tag}.json")))
            (bres, bexit), (ores, oexit) = cache[tag]
            if bres is None or ores is None:
                allstats[(p["mode"], "notrun")] += 1
                continue
            o = oracle(ores.get(p["line"]))
            if o is None or o == "OERR":
                allstats[(p["mode"], "oracle-" + str(o))] += 1
                continue
            msgs = bres.get(p["line"])
            v = verdict(msgs) if msgs is not None else ("MISSING" if bexit != 0 else "NONE")
            allstats[(p["mode"], v, o)] += 1
            if v == "VALID" and o == "false":
                hits.append((D, p))
            elif v == "FALSIFIED" and o == "true" and p["mode"] == "ground":
                comp.append((D, p, "ground-falsified-but-true"))
            elif v == "FALSIFIED" and o == "true":
                comp.append((D, p, "quant-falsified-bounded-true"))
            elif v == "ERROR":
                e = [d for s, d in msgs if s == "error"][0]
                errors[e.split("\n")[0][:140]] += 1
    for k, c in sorted(allstats.items()):
        print(k, c)
    print("\n=== UNSOUND HITS:", len(hits))
    for D, p in hits:
        print(f"[{D.split('/')[-1]} {p['tag']}:{p['line']}] {p['prop']}")
    print("\n=== completeness candidates:", len(comp))
    for D, p, k in comp[:40]:
        print(f"[{k} {p['tag']}:{p['line']}] {p['prop'][:300]}")
    print("\n=== error classes")
    for e, c in errors.most_common(40):
        print(c, e)


if __name__ == "__main__":
    main()
