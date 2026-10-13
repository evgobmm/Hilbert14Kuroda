import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Tactic.FinCases

/-! The two-variable symmetric-polynomial step, over an arbitrary coefficient
ring. `IntersectionInvariants` applies these results to the coefficients
of a polynomial in z after the triangular coordinate change. -/
namespace Hilbert14

variable {R : Type*} [CommRing R]

/-- In two variables, invariance under the swap is full symmetry. -/
theorem isSymmetric_of_swap_fixed {p : MvPolynomial (Fin 2) R}
    (hp : MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) p = p) :
    p.IsSymmetric := by
  intro e
  have he : e = Equiv.refl (Fin 2) ∨ e = Equiv.swap 0 1 := by
    have hne : e 0 ≠ e 1 := e.injective.ne (by decide)
    have h0 := (e 0).isLt
    have h1 := (e 1).isLt
    generalize ha : e 0 = a at hne h0
    generalize hb : e 1 = b at hne h1
    fin_cases a <;> fin_cases b
    · exact (hne rfl).elim
    · left; ext i; fin_cases i <;> simp [ha, hb]
    · right; ext i; fin_cases i <;> simp [ha, hb]
    · exact (hne rfl).elim
  rcases he with rfl | rfl
  · exact MvPolynomial.rename_id_apply p
  · exact hp

/-- A symmetric polynomial in two variables is a polynomial expression in
 their sum and product. This holds over k[z] as well as over a field. -/
theorem exists_sum_product_expression {p : MvPolynomial (Fin 2) R}
    (hp : p.IsSymmetric) :
    ∃ q : MvPolynomial (Fin 2) R,
      MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then
        MvPolynomial.X 0 + MvPolynomial.X 1 else
        MvPolynomial.X 0 * MvPolynomial.X 1) q = p := by
  obtain ⟨q, hq⟩ := (MvPolynomial.esymmAlgHom_fin_bijective R 2).2 ⟨p, hp⟩
  refine ⟨q, ?_⟩
  have he : (fun i : Fin 2 => MvPolynomial.esymm (Fin 2) R (i + 1)) =
      (fun i : Fin 2 => if i = 0 then
        MvPolynomial.X 0 + MvPolynomial.X 1 else
        MvPolynomial.X 0 * MvPolynomial.X 1) := by
    funext i
    fin_cases i
    · simp [MvPolynomial.esymm_one, Fin.sum_univ_two]
    · change MvPolynomial.esymm (Fin 2) R 2 = _
      unfold MvPolynomial.esymm
      have hc : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
      have hs := Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
      rw [hc] at hs
      rw [hs]
      simp [Fin.prod_univ_two]
  have hval := congrArg Subtype.val hq
  rw [MvPolynomial.esymmAlgHom_apply, he] at hval
  exact hval

/-- Subalgebra form of the two-variable fundamental theorem. -/
theorem symmetric_mem_adjoin_sum_product {p : MvPolynomial (Fin 2) R}
    (hp : p.IsSymmetric) : p ∈ Algebra.adjoin R
      {MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 0 * MvPolynomial.X 1} := by
  obtain ⟨q, hq⟩ := exists_sum_product_expression hp
  rw [← hq]
  clear hp hq p
  induction q using MvPolynomial.induction_on with
  | C r =>
    simpa using (Algebra.adjoin R
      {(MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) R), MvPolynomial.X 0 * MvPolynomial.X 1}).algebraMap_mem r
  | add p q hp hq => simpa only [map_add] using Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.aeval_X]
    apply Subalgebra.mul_mem _ hp
    apply Algebra.subset_adjoin
    fin_cases i <;> simp

#print axioms isSymmetric_of_swap_fixed
#print axioms exists_sum_product_expression

end Hilbert14
