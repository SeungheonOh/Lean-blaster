import Blaster

-- Candidate false claims. Each #blaster currently defaults to expecting Valid.
#blaster (timeout: 5) (gen-cex: 0) (dump-smt-lib: 1)
  [∀ (α : Type) (p : α → Bool), (∃ x, p x = true) ∨ (∃ x, p x = false)]

#blaster (timeout: 5) (gen-cex: 0) (dump-smt-lib: 1)
  [∀ (f : Empty → Empty) (g : (Empty → Empty) → Bool), g f = true]

#blaster (timeout: 5) (gen-cex: 0) (dump-smt-lib: 1)
  [∀ s : String, (s ++ "é").length = s.length + 2]

#blaster (timeout: 5) (gen-cex: 0) (dump-smt-lib: 1)
  [∀ s : String, s ++ "\\u{41}" = s ++ "A"]

#blaster (timeout: 5) (gen-cex: 0) (dump-smt-lib: 1)
  [∀ s : String, s ++ "a\"\"b" = s ++ "a\"b"]
