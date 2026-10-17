import Blaster

namespace BlasterAudit

def alwaysFalseLE : LE Nat := ⟨fun _ _ => False⟩
def alwaysFalseLT : LT Nat := ⟨fun _ _ => False⟩

theorem custom_le_wrong : @LE.le Nat alwaysFalseLE 0 1 := by
  blaster (only-optimize: 1)

theorem custom_le_false : False := by
  exact custom_le_wrong

theorem custom_lt_wrong : @LT.lt Nat alwaysFalseLT 0 1 := by
  blaster (only-optimize: 1)

theorem custom_lt_false : False := by
  exact custom_lt_wrong

end BlasterAudit
