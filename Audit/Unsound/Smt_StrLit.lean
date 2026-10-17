import Blaster

#eval "é".length
#eval "\\u{61}".length

theorem bad_utf8 : ∀ (s : String), s.length = 1 → s ++ "é" ≠ s ++ "e" → (s ++ "é").length = 3 := by blaster
example : False := by
  have h := bad_utf8 "a" (by decide) (by decide)
  revert h; decide

theorem bad_esc : ∀ (s : String), s.length = 1 → s ++ "\\u{61}" = s ++ "a" := by blaster
example : False := by
  have h := bad_esc "a" (by decide)
  revert h; decide

-- embedded double quotes: Lean "\"\"" has 2 chars, SMT `""""` has 1
theorem bad_quote : ∀ (s : String), s.length = 1 → (s ++ "\"\"").length = 2 := by blaster
example : False := by
  have h := bad_quote "a" (by decide)
  revert h; decide

#eval "abc".replace "" "x"
#eval "aaa".replace "aa" "b"
