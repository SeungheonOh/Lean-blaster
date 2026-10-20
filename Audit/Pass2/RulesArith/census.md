# Rule census — Nat / Int / Relational / Eq / Const / Utils (staging worktree)

Status legend: **P** = proven in `Obligations.lean` (theorem name given); **D** = disproven (counterexample
in `Obligations.lean`); **U** = unproven, no counterexample found. Side conditions are the ones the *code*
checks (literal-ness via `isNatValue?`/`isIntValue?` = raw `Expr.lit`/`Int.ofNat lit`/`Int.negSucc lit`;
"hyp" = an exact-syntax entry in `hypothesisMap`). All Nat/Int rules are keyed on the monomorphic heads
`Nat.add`/`Int.add`/…, so the types are fixed; LT/LE rules are keyed on the carrier only (instance unchecked,
REPORT #7).

## OptimizeNat.lean

| # | Rule (as implemented) | file:line | Side condition checked | Status / obligation |
|---|---|---|---|---|
| N1 | `0 + n ⇒ n` | OptimizeNat.lean:23 | op1 = lit 0 | P `N1_zero_add` |
| N2 | `N1 + N2 ⇒ N1 "+" N2` | :24 | both lits | P `N2_add_cst` |
| N3 | `N1 + (N2 + n) ⇒ (N1"+"N2) + n` | :34-37 | lits | P `N3_add_assoc_cst` |
| N4 | `n - n ⇒ 0` | :56 | ptr-eq | P `N4_sub_self` |
| N5 | `0 - n ⇒ 0` (returns op1) | :58 | op1 = lit 0 | P `N5_zero_sub` |
| N6 | `n - 0 ⇒ n` | :59 | op2 = lit 0 | P `N6_sub_zero` |
| N7 | `N1 - N2 ⇒ N1 "-" N2` (meta `Nat.sub`, truncating) | :60 | lits | P `N7_sub_cst` |
| N8 | `N1 - (N2 + n) ⇒ (N1"-"N2) - n` | :70-75 | lits | P `N8_cst_sub_add` |
| N9 | `(N1 - n) - N2 ⇒ (N1"-"N2) - n` | :87-89 | lits | P `N9_cst_sub_sub` |
| N10 | `(n - N1) - N2 ⇒ n - (N1"+"N2)` | :90-92 | lits | P `N10_sub_cst_sub` |
| N11 | `(N1 + n) - N2 ⇒ (N1"-"N2) + n` | :93-97 | `Nat.ble N2 N1` | P `N11_add_cst_sub` |
| N12 | `n ^ 0 ⇒ 1` (incl. 0^0) | :122 | op2 = lit 0 | P `N12_pow_zero` |
| N13 | `N1 ^ N2 ⇒ N1 "^" N2` | :123 | lits | P `N13_pow_cst` |
| N14 | `0 * n ⇒ 0` | :141 | op1 = lit 0 | P `N14_zero_mul` |
| N15 | `1 * n ⇒ n` | :142 | op1 = lit 1 | P `N15_one_mul` |
| N16 | `N1 * N2 ⇒ N1 "*" N2` | :143 | lits | P `N16_mul_cst` |
| N17 | `N1 * (N2 * n) ⇒ (N1"*"N2) * n` | :154-158 | lits | P `N17_mul_assoc_cst` |
| N18 | `n * n^m ⇒ n ^ (1 + m)` | :163-171 | ptr-eq | P `N18_mul_pow` |
| N19 | `(m*n)/m ⇒ n`, `(n*m)/m ⇒ n` | :181-187 | hyp `0<m` or `¬(0=m)` (or m lit ≠0) | P `N19a/N19b_mul_div_cancel` |
| N20 | `n / n ⇒ 1` | :195-199 | hyp `0<n` or `¬(0=n)` | P `N20_div_self` |
| N21 | `n / 0 ⇒ 0` | :222 | op2 = lit 0 | P `N21_div_zero` |
| N22 | `n / 1 ⇒ n` | :223 | op2 = lit 1 | P `N22_div_one` |
| N23 | `0 / n ⇒ 0` | :224 | op1 = lit 0 | P `N23_zero_div` |
| N24 | `N1 / N2 ⇒ N1 "/" N2` | :225 | lits | P `N24_div_cst` |
| N25 | `(n / N1) / N2 ⇒ n / (N1"*"N2)` | :245-247 | lits | P `N25_div_div` |
| N26 | `(N1*n)/N2 ⇒ ((N1/g)*n)/(N2/g)`, g = gcd (either arg order) | :248-253 | g ≠ 1; N2 ≠ 0 only by arm order (:222) | P `N26_mul_div_gcd` |
| N27 | `n % n ⇒ 0` (incl. 0 % 0) | :265 | ptr-eq | P `N27_mod_self` |
| N28 | `(m*n) % m ⇒ 0`, `(n*m) % m ⇒ 0` | :266-270 | none (no hyp needed) | P `N28a/N28b` |
| N29 | `n % 0 ⇒ n` | :289 | lit 0 | P `N29_mod_zero` |
| N30 | `n % 1 ⇒ 0` | :290 | lit 1 | P `N30_mod_one` |
| N31 | `0 % n ⇒ 0` | :291 | lit 0 | P `N31_zero_mod` |
| N32 | `N1 % N2 ⇒ N1 "%" N2` | :292 | lits | P `N32_mod_cst` |
| N33 | `(N1*n) % N2 ⇒ 0` | :304-310 | `N1 % N2 = 0` (N2≠0,1 by arm order) | P `N33_mul_mod_cst` (holds even for N2 = 0) |
| N34 | `Nat.beq x y ⇒ @BEq.beq Nat instBEqOfDecidableEq x y` | :317-320 | isOptimizeRecCall | P `N34_beq` |
| N35 | `Nat.ble x y ⇒ decide' (x ≤ y)` | :327-331 | isOptimizeRecCall | P `N35_ble` |

Doc/code notes (OptimizeNat): `optimizeNatMul` doc says "N1 + N2 ==> N1 "*" N2" (typo, code is `*`);
the `n / 0 ⇒ 0` arm returns `op2` (the literal 0) — fine. No doc-vs-code semantic mismatch.

