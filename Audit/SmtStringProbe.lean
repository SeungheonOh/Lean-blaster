import Blaster

-- A string literal containing a quote must be escaped as an SMT-LIB string.
#blaster (gen-cex: 0) (solve-result: 1) [∀ s : String, s = "a\"b"]
