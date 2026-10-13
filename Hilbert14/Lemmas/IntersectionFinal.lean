import Hilbert14.Lemmas.IntersectionFieldReduction
import Hilbert14.Lemmas.FractionCoordinates
import Mathlib.Tactic.FieldSimp

/-! Transport of the symmetric-field intersection under the
coordinate automorphism to Kuroda's explicit generated field. -/

namespace Hilbert14

variable (k : Type*) [Field k]

/-- The elementary symmetric sum maps to the first fixed target generator. -/
theorem theta_symmetric_sum : theta k (embed k (x k + v k)) = a k := by
  simp only [v, map_add, map_sub, map_pow, theta_x, theta_y, a]
  ring

/-- The elementary symmetric product maps to the second fixed target generator. -/
theorem theta_symmetric_product : theta k (embed k (x k * v k)) = b k := by
  simp only [v, map_mul, map_add, map_sub, map_pow, theta_x, theta_y, b]
  field_simp [embed_x_ne_zero k]

theorem theta_symmetric_z : theta k (embed k (z k)) = c k := theta_z k

/-- Every element of the actual x-localization has a power-of-x denominator. -/
theorem laurentToRat_powers_x (q : Laurent k) :
    ∃ a : Poly k, ∃ n : ℕ,
      laurentToRat k q = embed k a / embed k (x k) ^ n := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (x k) q
  change q * intoLaurent k (x k) ^ n = intoLaurent k a at ha
  refine ⟨a, n, (eq_div_iff (pow_ne_zero n (embed_x_ne_zero k))).mpr ?_⟩
  have hh := congrArg (laurentToRat k) ha
  simpa only [map_mul, map_pow, laurentToRat_embed] using hh

/-- The inverse coordinate modification sends every polynomial into P[1/x]. -/
theorem theta_inverse_embed_powers_x (p : Poly k) :
    ∃ a : Poly k, ∃ n : ℕ,
      (theta k).symm (embed k p) = embed k a / embed k (x k) ^ n := by
  change ∃ a : Poly k, ∃ n : ℕ,
    extendLaurent k (thetaEquiv k).symm (embed k p) =
      embed k a / embed k (x k) ^ n
  rw [extendLaurent_embed]
  exact laurentToRat_powers_x k _

/-- Arbitrary members of the target field pull back to the symmetric field. -/
theorem theta_inverse_mem_symmetricField {t : Rat k} (ht : t ∈ field k) :
    (theta k).symm t ∈ symmetricField k := by
  induction ht using IntermediateField.adjoin_induction with
  | mem t ht =>
    rcases ht with rfl | rfl | rfl
    · rw [← theta_symmetric_sum, AlgEquiv.symm_apply_apply]
      exact IntermediateField.subset_adjoin k _ (by simp)
    · rw [← theta_symmetric_product, AlgEquiv.symm_apply_apply]
      exact IntermediateField.subset_adjoin k _ (by simp)
    · rw [← theta_symmetric_z, AlgEquiv.symm_apply_apply]
      exact IntermediateField.subset_adjoin k _ (by simp)
  | algebraMap r => simpa only [AlgEquiv.commutes] using (symmetricField k).algebraMap_mem r
  | add p q _ _ hp hq => simpa only [map_add] using (symmetricField k).add_mem hp hq
  | inv p _ hp => simpa only [map_inv₀] using (symmetricField k).inv_mem hp
  | mul p q _ _ hp hq => simpa only [map_mul] using (symmetricField k).mul_mem hp hq

/-- The forward coordinate modification maps the full symmetric field to L. -/
theorem theta_mem_field {t : Rat k} (ht : t ∈ symmetricField k) :
    theta k t ∈ field k := by
  induction ht using IntermediateField.adjoin_induction with
  | mem t ht =>
    rcases ht with rfl | rfl | rfl
    · rw [theta_symmetric_sum]
      exact IntermediateField.subset_adjoin k _ (by simp)
    · rw [theta_symmetric_product]
      exact IntermediateField.subset_adjoin k _ (by simp)
    · rw [theta_symmetric_z]
      exact IntermediateField.subset_adjoin k _ (by simp)
  | algebraMap r => simpa only [AlgEquiv.commutes] using (field k).algebraMap_mem r
  | add p q _ _ hp hq => simpa only [map_add] using (field k).add_mem hp hq
  | inv p _ hp => simpa only [map_inv₀] using (field k).inv_mem hp
  | mul p q _ _ hp hq => simpa only [map_mul] using (field k).mul_mem hp hq

/-- Genuine field-intersection reduction for the exact fixed target:
A = theta(k[u+v,uv,z]) ∩ P. Since g=u+v and f=g+uv, this is theta(R[z]) ∩ P.
The forward implication applies to every element of L∩P. -/
theorem mem_intersection_iff_theta_symmetricAlgebra (p : Poly k) :
    p ∈ intersection k ↔ ∃ q : Poly k,
      q ∈ symmetricAlgebra k ∧ theta k (embed k q) = embed k p := by
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := symmetricField_inter_powers_x k
      (theta_inverse_mem_symmetricField k hp) (theta_inverse_embed_powers_x k p)
    refine ⟨q, hq, ?_⟩
    rw [heq, AlgEquiv.apply_symm_apply]
    rfl
  · rintro ⟨q, hq, heq⟩
    change embed k p ∈ field k
    rw [← heq]
    exact theta_mem_field k (embed_mem_symmetricField k hq)

/-- The same exact intersection reduction with the explicit g,f formulas. -/
theorem mem_intersection_iff_theta_Rz (p : Poly k) :
    p ∈ intersection k ↔ ∃ q : Poly k,
      q ∈ Algebra.adjoin k {y k + x k ^ 2, y k + x k * y k + x k ^ 3, z k} ∧
      theta k (embed k q) = embed k p := by
  rw [mem_intersection_iff_theta_symmetricAlgebra, symmetricAlgebra_eq_adjoin_g_f]

#print axioms mem_intersection_iff_theta_symmetricAlgebra
#print axioms mem_intersection_iff_theta_Rz

end Hilbert14
