#!/bin/bash
# Usage: run.sh <rundir> [parallel] [file-timeout-seconds]
# Runs every blast_*.lean / oracle_*.lean in <rundir> with `lake env lean --json`, writing *.json next to them.
D="$1"; P="${2:-6}"; T="${3:-900}"
cd /home/sho/fun/Lean-blaster-staging-audit || exit 1
ls "$D"/blast_*.lean "$D"/oracle_*.lean | while read -r f; do
  [ -s "${f%.lean}.json" ] || echo "$f"
done | xargs -P "$P" -I{} sh -c 'f="$1"; timeout '"$T"' lake env lean --json "$f" > "${f%.lean}.json.tmp" 2>&1; echo "EXIT $?" >> "${f%.lean}.json.tmp"; mv "${f%.lean}.json.tmp" "${f%.lean}.json"' _ {}
