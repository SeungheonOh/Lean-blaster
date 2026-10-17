import Blaster

namespace BlasterAudit

#blaster (only-optimize: 1) (gen-cex: 0) (solve-result: 2)
  [∃ (_ : Empty), 0 < 1]

theorem first_conjunct_valid : ∀ [Inhabited Empty], ∃ (_ : Empty), True := by
  intro inst
  exact ⟨default, trivial⟩

theorem leaked_instance :
    (∀ [Inhabited Empty], ∃ (_ : Empty), True) ∧
    (∃ (_ : Empty), 0 < 1) := by
  blaster (only-optimize: 1)

theorem leaked_instance_false : False := by
  obtain ⟨x, _⟩ := leaked_instance.2
  cases x

end BlasterAudit
