import Hilbert14.Lemmas.IntersectionCoordinates

/-! The swap-invariant polynomial algebra k[u+v,uv,z],
with u=x and v=y−x+x². -/

namespace Hilbert14

variable (k : Type*) [Field k]

/-- k[u+v,uv,z], where u=x and v=y-x+x². -/
noncomputable def symmetricAlgebra : Subalgebra k (Poly k) :=
  Algebra.adjoin k {x k + v k, x k * v k, z k}

private theorem shear_C_mem_of_symmetric {p : Base k} (hp : p.IsSymmetric) :
    shear k (Polynomial.C p) ∈ symmetricAlgebra k := by
  have hm := symmetric_mem_adjoin_sum_product hp
  clear hp
  let φ : Base k →ₐ[k] Poly k :=
    (shear k).toAlgHom.comp Polynomial.CAlgHom
  change φ p ∈ symmetricAlgebra k
  induction hm using Algebra.adjoin_induction with
  | mem p hp =>
    rcases hp with rfl | rfl
    · change shear k (Polynomial.C (MvPolynomial.X 0 + MvPolynomial.X 1)) ∈ symmetricAlgebra k
      rw [map_add]
      change shear k (x k + y k) ∈ symmetricAlgebra k
      simp only [map_add, shear_x, shear_y]
      exact Algebra.subset_adjoin (by simp)
    · change shear k (Polynomial.C (MvPolynomial.X 0 * MvPolynomial.X 1)) ∈ symmetricAlgebra k
      rw [map_mul]
      change shear k (x k * y k) ∈ symmetricAlgebra k
      simp only [map_mul, shear_x, shear_y]
      exact Algebra.subset_adjoin (by simp)
  | algebraMap r => simpa only [AlgHom.commutes] using (symmetricAlgebra k).algebraMap_mem r
  | add p q _ _ hp hq => simpa only [map_add] using (symmetricAlgebra k).add_mem hp hq
  | mul p q _ _ hp hq => simpa only [map_mul] using (symmetricAlgebra k).mul_mem hp hq

private theorem shear_mem_of_swap_fixed {p : Poly k} (hp : coordinateSwap k p = p) :
    shear k p ∈ symmetricAlgebra k := by
  have hcoeff (i : ℕ) : (p.coeff i).IsSymmetric := by
    apply isSymmetric_of_swap_fixed
    have hc := congrArg (fun q : Poly k => q.coeff i) hp
    simpa [coordinateSwap, Polynomial.coe_mapAlgEquiv, MvPolynomial.renameEquiv] using hc
  rw [← Polynomial.sum_C_mul_X_pow_eq p, Polynomial.sum_def, map_sum]
  apply (symmetricAlgebra k).sum_mem
  intro i hi
  rw [map_mul, map_pow]
  apply (symmetricAlgebra k).mul_mem (shear_C_mem_of_symmetric k (hcoeff i))
  apply (symmetricAlgebra k).pow_mem
  change shear k (z k) ∈ symmetricAlgebra k
  rw [shear_z]
  exact Algebra.subset_adjoin (by simp)

/-- Every polynomial fixed by the actual Kuroda swap belongs to k[u+v,uv,z]. -/
theorem mem_symmetricAlgebra_of_tau_fixed {p : Poly k} (hp : tau k p = p) :
    p ∈ symmetricAlgebra k := by
  have hq : coordinateSwap k ((shear k).symm p) = (shear k).symm p := by
    apply (shear k).injective
    simpa [tau] using hp
  have h := shear_mem_of_swap_fixed k hq
  simpa using h

/-- Conversely, the three generators are fixed by the swap. -/
theorem tau_fixed_of_mem_symmetricAlgebra {p : Poly k} (hp : p ∈ symmetricAlgebra k) :
    tau k p = p := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    rcases hp with rfl | rfl | rfl
    · simp [add_comm]
    · simp [mul_comm]
    · simp
  | algebraMap r => exact (tau k).commutes r
  | add p q _ _ hp hq => simp [hp, hq]
  | mul p q _ _ hp hq => simp [hp, hq]

/-- The invariant algebra is exactly R[z], with generators
 g=y+x² and f=y+xy+x³. -/
theorem symmetricAlgebra_eq_adjoin_g_f : symmetricAlgebra k =
    Algebra.adjoin k {y k + x k ^ 2, y k + x k * y k + x k ^ 3, z k} := by
  have hg : x k + v k = y k + x k ^ 2 := by unfold v; ring
  have hf : x k * v k =
      (y k + x k * y k + x k ^ 3) - (y k + x k ^ 2) := by unfold v; ring
  unfold symmetricAlgebra
  rw [hg, hf]
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro p hp
    rcases hp with rfl | rfl | rfl
    · exact Algebra.subset_adjoin (by simp)
    · exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (by simp))
        (Algebra.subset_adjoin (by simp))
    · exact Algebra.subset_adjoin (by simp)
  · apply Algebra.adjoin_le
    intro p hp
    rcases hp with rfl | rfl | rfl
    · exact Algebra.subset_adjoin (by simp)
    · have h1 : y k + x k ^ 2 ∈ Algebra.adjoin k
          {y k + x k ^ 2, (y k + x k * y k + x k ^ 3) - (y k + x k ^ 2), z k} :=
        Algebra.subset_adjoin (by simp)
      have h2 : (y k + x k * y k + x k ^ 3) - (y k + x k ^ 2) ∈ Algebra.adjoin k
          {y k + x k ^ 2, (y k + x k * y k + x k ^ 3) - (y k + x k ^ 2), z k} :=
        Algebra.subset_adjoin (by simp)
      have h3 := Subalgebra.add_mem _ h2 h1
      rw [sub_add_cancel] at h3
      exact h3
    · exact Algebra.subset_adjoin (by simp)

#print axioms mem_symmetricAlgebra_of_tau_fixed
#print axioms tau_fixed_of_mem_symmetricAlgebra

end Hilbert14
