import Blaster
/- Smt/Term.lean:414 `strLitSmt s := "\"{s}\""` emits Lean strings into SMT-LIB with no escaping:
   non-ASCII chars are seen by Z3 as several chars, `\u{..}` sequences are interpreted by Z3,
   and `"` terminates the literal (SMT-LIB escapes `"` as `""`). -/

-- (1) "é" is 1 char in Lean, 2 bytes in the SMT literal
theorem bad1 : ∀ s : String, s = "é" → s.length = 2 := by blaster
theorem bad1_false : ¬ (∀ s : String, s = "é" → s.length = 2) := by
  intro h; have := h "é" rfl; exact absurd this (by decide)

-- (2) backslash-u escape interpreted by Z3: Lean "\\u{41}" (6 chars) ≠ "A"
theorem bad2 : ∀ s : String, s = "\\u{41}" → s = "A" := by blaster
theorem bad2_false : ¬ (∀ s : String, s = "\\u{41}" → s = "A") := by
  intro h; have := h "\\u{41}" rfl; simp at this

-- (3) quote: Lean "a\"\"b" (4 chars: a " " b) becomes SMT "a""b" = a"b (3 chars)
theorem bad3 : ∀ s : String, s = "a\"\"b" → s.length = 3 := by blaster
theorem bad3_false : ¬ (∀ s : String, s = "a\"\"b" → s.length = 3) := by
  intro h; have := h "a\"\"b" rfl; exact absurd this (by decide)

theorem c1 : False := bad1_false bad1
theorem c2 : False := bad2_false bad2
theorem c3 : False := bad3_false bad3
