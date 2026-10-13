import Hilbert14.Lemmas.FamilyDenominators
import Hilbert14.Lemmas.IntersectionNoPole

/-! The concrete regularity identities and polynomial family
for G=a, H=a+b and B=H²−G³ in Kuroda's example. -/

namespace Hilbert14
noncomputable section
variable (k : Type*) [Field k]

/-- The polynomial B = H²−G³, where H=a+b and G=a in the fraction field. -/
def familyB : Poly k :=
  (2*x k^2-x k)*y k + (x k^10+2*x k^9-2*x k^8)*y k^2-x k^15*y k^3

def familyBdivX : Poly k :=
  (2*x k-1)*y k + (x k^9+2*x k^8-2*x k^7)*y k^2-x k^14*y k^3

def familyH : Rat k := a k+b k

theorem family_embed_x_ne_zero : embed k (x k) ≠ 0 := by
  exact fun h => (x_prime k).ne_zero ((embed_injective k) (h.trans (map_zero _).symm))

theorem embed_s_ne_zero : embed k (1+x k^7*y k) ≠ 0 := by
  exact fun h => regularDenominator_ne_zero k ((embed_injective k) (h.trans (map_zero _).symm))

theorem familyH_formula : familyH k =
    embed k (x k)^5*embed k (y k)+embed k (x k)^4*embed k (y k)+(embed k (x k))⁻¹^3 := by
  simp only [familyH,a,b]
  ring

theorem familyB_formula : familyH k^2-a k^3 = embed k (familyB k) := by
  rw [familyH_formula]
  simp only [a,familyB,map_add,map_sub,map_mul,map_pow,map_ofNat]
  field_simp [family_embed_x_ne_zero k]
  ring

theorem familyB_factor : familyB k = x k*familyBdivX k := by
  simp only [familyB,familyBdivX]
  ring

theorem familyB_cube_H : embed k (familyB k)^3*familyH k =
    embed k ((familyBdivX k)^3*(x k^8*y k+x k^7*y k+1)) := by
  rw [familyB_factor,familyH_formula]
  simp only [map_mul,map_add,map_pow,map_one]
  field_simp [family_embed_x_ne_zero k]

theorem a_mul_x_sq : a k*embed k (x k)^2 = embed k (1+x k^7*y k) := by
  simp only [a,map_add,map_one,map_mul,map_pow]
  field_simp [family_embed_x_ne_zero k]
  ring

theorem a_ne_zero : a k≠0 := by
  intro h
  have he := a_mul_x_sq k
  rw [h,zero_mul] at he
  exact embed_s_ne_zero k he.symm

theorem a_inverse_formula : (a k)⁻¹ = embed k (x k)^2 / embed k (1+x k^7*y k) := by
  apply (eq_div_iff (embed_s_ne_zero k)).mpr
  rw [← a_mul_x_sq, ← mul_assoc, inv_mul_cancel₀ (a_ne_zero k),one_mul]

theorem shifted_coordinate_formula : c k-familyH k*(a k)⁻¹ =
    embed k (z k)-embed k (x k^7*y k)/embed k (1+x k^7*y k) := by
  have hs : 1+embed k (x k)^7*embed k (y k)≠0 := by
    simpa only [map_add,map_one,map_mul,map_pow] using embed_s_ne_zero k
  rw [familyH_formula,a_inverse_formula]
  simp only [c,map_add,map_mul,map_pow,map_one]
  field_simp [family_embed_x_ne_zero k,hs]
  ring

def xLocal : Subalgebra k (Rat k) :=
  Family.powersDenominator (embed k) (x k) (family_embed_x_ne_zero k)

def regularLocal : Subalgebra k (Rat k) :=
  Family.powersDenominator (embed k) (1+x k^7*y k) (embed_s_ne_zero k)

theorem embed_mem_xLocal (p : Poly k) : embed k p ∈ xLocal k :=
  Family.mem_powersDenominator _ _ _ p

theorem embed_mem_regularLocal (p : Poly k) : embed k p ∈ regularLocal k :=
  Family.mem_powersDenominator _ _ _ p

theorem a_mem_xLocal : a k ∈ xLocal k := by
  have hx := embed_mem_xLocal k (x k)
  have hy := embed_mem_xLocal k (y k)
  have hi : (embed k (x k))⁻¹ ∈ xLocal k := Family.inv_mem_powersDenominator _ _ _
  exact (xLocal k).add_mem ((xLocal k).mul_mem ((xLocal k).pow_mem hx 5) hy)
    ((xLocal k).pow_mem hi 2)

theorem familyH_mem_xLocal : familyH k ∈ xLocal k := by
  rw [familyH_formula]
  have hx := embed_mem_xLocal k (x k)
  have hy := embed_mem_xLocal k (y k)
  have hi : (embed k (x k))⁻¹ ∈ xLocal k := Family.inv_mem_powersDenominator _ _ _
  exact (xLocal k).add_mem ((xLocal k).add_mem
    ((xLocal k).mul_mem ((xLocal k).pow_mem hx 5) hy)
    ((xLocal k).mul_mem ((xLocal k).pow_mem hx 4) hy)) ((xLocal k).pow_mem hi 3)

theorem c_mem_xLocal : c k ∈ xLocal k :=
  (xLocal k).add_mem (embed_mem_xLocal k (z k)) (Family.inv_mem_powersDenominator _ _ _)

theorem inverse_a_mem_regularLocal : (a k)⁻¹ ∈ regularLocal k := by
  rw [a_inverse_formula,div_eq_mul_inv]
  exact (regularLocal k).mul_mem ((regularLocal k).pow_mem (embed_mem_regularLocal k (x k)) 2)
    (Family.inv_mem_powersDenominator _ _ _)

theorem shifted_coordinate_mem_regularLocal : c k-familyH k*(a k)⁻¹ ∈ regularLocal k := by
  rw [shifted_coordinate_formula,div_eq_mul_inv]
  exact (regularLocal k).sub_mem (embed_mem_regularLocal k (z k))
    ((regularLocal k).mul_mem (embed_mem_regularLocal k (x k^7*y k))
      (Family.inv_mem_powersDenominator _ _ _))

theorem family_algebra_le_xLocal : Algebra.adjoin k {familyH k,a k} ≤ xLocal k :=
  Algebra.adjoin_le (by
    intro q hq
    rcases (show q=familyH k ∨ q=a k by simpa using hq) with rfl | rfl
    · exact familyH_mem_xLocal k
    · exact a_mem_xLocal k)

theorem family_algebra_le_field : Algebra.adjoin k {familyH k,a k} ≤ (field k).toSubalgebra := by
  have ha : a k ∈ field k := IntermediateField.subset_adjoin k _ (by simp)
  have hb : b k ∈ field k := IntermediateField.subset_adjoin k _ (by simp)
  apply Algebra.adjoin_le
  intro q hq
  rcases (show q=familyH k ∨ q=a k by simpa using hq) with rfl | rfl
  · exact (field k).add_mem ha hb
  · exact ha

instance ratCharZero [CharZero k] : CharZero (Rat k) where
  cast_injective m n h := by
    apply Nat.cast_injective (R:=k)
    apply (algebraMap k (Rat k)).injective
    simpa only [map_natCast] using h

/-- Every member of Kuroda's family is a polynomial in the explicit field
intersection. `FamilyCoefficient` identifies its coefficient at index n as B³. -/
theorem exists_polynomial_family [CharZero k] :
    ∃ cs : ℕ → Rat k, cs 0=1 ∧ (∀ n, cs n∈Algebra.adjoin k {familyH k,a k}) ∧
      ∀ n, ∃ q : Poly k, q∈intersection k ∧
        embed k q = (Nat.factorial n:Rat k)*embed k (familyB k)^3*
          Family.dividedConvolution cs (c k) n := by
  have hp : familyH k^2-a k^3 ∈ regularLocal k := by
    rw [familyB_formula]
    exact embed_mem_regularLocal k _
  have hpf : (familyH k^2-a k^3)^3*familyH k ∈ regularLocal k := by
    rw [familyB_formula,familyB_cube_H]
    exact embed_mem_regularLocal k _
  rcases Family.exists_regular_family (regularLocal k) (familyH k) (a k) ((a k)⁻¹) (c k)
    (mul_inv_cancel₀ (a_ne_zero k)) hp (inverse_a_mem_regularLocal k) hpf
    (shifted_coordinate_mem_regularLocal k) with ⟨cs,hc0,hcR,hcD⟩
  refine ⟨cs,hc0,hcR,?_⟩
  intro n
  let Q := (Nat.factorial n:Rat k)*embed k (familyB k)^3*Family.dividedConvolution cs (c k) n
  have hx : Q∈xLocal k := (xLocal k).mul_mem
    ((xLocal k).mul_mem ((xLocal k).natCast_mem _) ((xLocal k).pow_mem (embed_mem_xLocal k _) 3))
    (Family.dividedConvolution_mem _ cs (fun i => family_algebra_le_xLocal k (hcR i))
      (c k) (c_mem_xLocal k) n)
  have hs : Q∈regularLocal k := by
    have hn := hcD n
    rw [familyB_formula] at hn
    dsimp [Q]
    rw [mul_assoc]
    exact (regularLocal k).mul_mem ((regularLocal k).natCast_mem _) hn
  obtain ⟨q,hq⟩ := regularDenominator_intersection k hx hs
  refine ⟨q,?_,hq⟩
  rw [mem_intersection,hq]
  have hB : embed k (familyB k)∈field k := by
    rw [← familyB_formula]
    have hf := family_algebra_le_field k (Algebra.subset_adjoin (show familyH k∈({familyH k,a k}:Set (Rat k)) by simp))
    have hg := family_algebra_le_field k (Algebra.subset_adjoin (show a k∈({familyH k,a k}:Set (Rat k)) by simp))
    exact (field k).sub_mem ((field k).pow_mem hf 2) ((field k).pow_mem hg 3)
  have ht : c k∈field k := IntermediateField.subset_adjoin k _ (by simp)
  exact (field k).mul_mem ((field k).mul_mem ((field k).natCast_mem _) ((field k).pow_mem hB 3))
    (Family.dividedConvolution_mem (field k).toSubalgebra cs
      (fun i => family_algebra_le_field k (hcR i)) (c k) ht n)

#print axioms exists_polynomial_family
#print axioms familyB_formula
#print axioms familyB_cube_H
#print axioms shifted_coordinate_formula

end
end Hilbert14
