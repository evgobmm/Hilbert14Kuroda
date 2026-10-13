import Hilbert14.Lemmas.IntersectionInvariants

/-! Intersection of the symmetric field with k[x,y,z][1/x],
using the swap to produce a second denominator representation. -/

namespace Hilbert14

variable (k : Type*) [Field k]

/-- The pre-modification field k(u+v,uv,z), with u=x, v=y-x+x². -/
noncomputable def symmetricField : IntermediateField k (Rat k) :=
  IntermediateField.adjoin k {embed k (x k + v k), embed k (x k * v k), embed k (z k)}

/-- The polynomial swap extended to the actual fraction field. -/
noncomputable def tauRat : Rat k ≃ₐ[k] Rat k :=
  IsFractionRing.algEquivOfAlgEquiv (tau k)

@[simp] theorem tauRat_embed (p : Poly k) : tauRat k (embed k p) = embed k (tau k p) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap (tau k) p

theorem tauRat_fixed_of_mem_symmetricField {t : Rat k} (ht : t ∈ symmetricField k) :
    tauRat k t = t := by
  induction ht using IntermediateField.adjoin_induction with
  | mem t ht =>
    rcases ht with rfl | rfl | rfl
    · simp [add_comm]
    · simp [mul_comm]
    · simp
  | algebraMap r => exact (tauRat k).commutes r
  | add p q _ _ hp hq => simp [hp, hq]
  | inv p _ hp => simp [hp]
  | mul p q _ _ hp hq => simp [hp, hq]

/-- The substantial pre-modification intersection reduction. Every element
of k(u+v,uv,z) with only a power-of-x denominator is an actual polynomial in
u+v, uv, and z. There is no assumption that the element began as a polynomial
expression in the field generators. -/
theorem symmetricField_inter_powers_x {t : Rat k} (ht : t ∈ symmetricField k)
    (hx : ∃ a : Poly k, ∃ n : ℕ, t = embed k a / embed k (x k) ^ n) :
    ∃ p : Poly k, p ∈ symmetricAlgebra k ∧ embed k p = t := by
  have hfix := tauRat_fixed_of_mem_symmetricField k ht
  have hv : ∃ b : Poly k, ∃ m : ℕ, t = embed k b / embed k (v k) ^ m := by
    obtain ⟨a, n, ha⟩ := hx
    refine ⟨tau k a, n, ?_⟩
    have he := congrArg (tauRat k) ha
    simpa [hfix] using he
  obtain ⟨p, hp⟩ := x_v_powers_intersection k hx hv
  refine ⟨p, mem_symmetricAlgebra_of_tau_fixed k ?_, hp⟩
  apply embed_injective k
  rw [← tauRat_embed, hp, hfix]

/-- The polynomial invariants embed into the genuine generated subfield. -/
theorem embed_mem_symmetricField {p : Poly k} (hp : p ∈ symmetricAlgebra k) :
    embed k p ∈ symmetricField k := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    apply IntermediateField.subset_adjoin
    rcases hp with rfl | rfl | rfl <;> simp
  | algebraMap r => simpa only [AlgHom.commutes] using (symmetricField k).algebraMap_mem r
  | add p q _ _ hp hq => simpa only [map_add] using (symmetricField k).add_mem hp hq
  | mul p q _ _ hp hq => simpa only [map_mul] using (symmetricField k).mul_mem hp hq

#print axioms symmetricField_inter_powers_x
#print axioms embed_mem_symmetricField

end Hilbert14
