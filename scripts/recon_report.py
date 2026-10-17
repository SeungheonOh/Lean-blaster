#!/usr/bin/env python3
"""Summarize proof reconstruction statistics produced by `scripts/recon_coverage.sh`."""
import json
import sys
from collections import Counter, defaultdict


def main(path):
    rows = [json.loads(l) for l in open(path) if l.strip()]
    groups = defaultdict(list)
    for r in rows:
        kind = "testOptimize" if r["label"].startswith("testOptimize") else r["label"]
        if kind != "testOptimize":
            kind = "blaster(" + ("smt" if r["residual"].startswith("smt") or r["residual"] == "none" else "optimizer") + ")"
        groups[kind].append(r)
    print(f"{'category':<22} {'total':>6} {'kernel-checked':>15} {'rate':>7}")
    for kind, rs in sorted(groups.items()):
        ok = sum(1 for r in rs if r["success"])
        print(f"{kind:<22} {len(rs):>6} {ok:>15} {100.0 * ok / max(1, len(rs)):>6.1f}%")
    total = len(rows)
    ok = sum(1 for r in rows if r["success"])
    print(f"{'all':<22} {total:>6} {ok:>15} {100.0 * ok / max(1, total):>6.1f}%")
    # attempts whose only unresolved obligations are unsound rewrites (correctly refused)
    def unsound_only(r):
        if r["success"]:
            return False
        ms = [m for l, m in r.get("labels", {}).items()]
        refused = sum(m.get("refused:unsound", 0) for m in ms)
        failed = sum(m.get("failed", 0) for m in ms)
        return refused > 0 and failed == 0
    refused = sum(1 for r in rows if unsound_only(r))
    print(f"{'refused (unsound)':<22} {refused:>6}")
    print(f"{'all except refused':<22} {total - refused:>6} {ok:>15} {100.0 * ok / max(1, total - refused):>6.1f}%")
    methods = Counter()
    for r in rows:
        for m, n in r["methods"].items():
            methods[m] += n
    print("\nproof obligations discharged by method:", dict(methods))
    print("explicit steps:", sum(r["explicit"] for r in rows),
          " definitional steps:", sum(r["defeq"] for r in rows),
          " proof obligations:", sum(r["holes"] for r in rows),
          " unresolved:", sum(r["unresolved"] for r in rows))
    reasons = Counter()
    for r in rows:
        if not r["success"]:
            f = r["failure"]
            if "unresolved proof obligation" in f:
                reasons["unresolved obligations"] += 1
            elif "residual goal" in f:
                reasons["smt residual not proved"] += 1
            elif "kernel" in f:
                reasons["kernel rejection"] += 1
            else:
                reasons[f[:60]] += 1
    print("failure reasons:", dict(reasons))
    labels = defaultdict(Counter)
    for r in rows:
        for l, ms in r.get("labels", {}).items():
            for m, n in ms.items():
                labels[l][m] += n
    if labels:
        print("\nproof obligations per rewrite site (top 40):")
        top = sorted(labels.items(), key=lambda kv: -sum(kv[1].values()))[:40]
        for l, ms in top:
            print(f"  {sum(ms.values()):>6}  {l:<70} {dict(ms)}")
    per_file = defaultdict(lambda: [0, 0])
    for r in rows:
        per_file[r["file"]][0] += 1
        per_file[r["file"]][1] += r["success"]
    if "-v" in sys.argv:
        print()
        for f, (t, s) in sorted(per_file.items()):
            print(f"{s:>4}/{t:<4} {f}")


if __name__ == "__main__":
    main(sys.argv[1])
