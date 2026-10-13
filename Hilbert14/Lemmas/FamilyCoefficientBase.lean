import Hilbert14.Lemmas.FamilyConcrete
import Hilbert14.Lemmas.ObstructionCoefficient

/-! Identification of the family's polynomial B with its
coefficient-ring expression in k[x,y]. -/

namespace Hilbert14
variable (k : Type*) [Field k]

theorem familyB_eq_C_bPoly : familyB k = Polynomial.C (bPoly k) := by
  simp only [familyB,bPoly,x,y,map_add,map_sub,map_mul,map_pow,map_ofNat]

end Hilbert14
