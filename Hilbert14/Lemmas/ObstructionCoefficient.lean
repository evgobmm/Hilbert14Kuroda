import Hilbert14.Definitions
import Hilbert14.Lemmas.Obstruction
import Mathlib.Tactic.Ring

/-! The coefficient B³ survives reduction modulo y⁴,
providing the nonzero coefficients used by the finite-generation obstruction. -/

namespace Hilbert14

variable (k : Type*) [Field k]

/-- The polynomial theta(f²-g³) in the coefficient ring k[x,y]. -/
noncomputable def bPoly : Base k :=
  (2 * MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0) * MvPolynomial.X 1 +
  (MvPolynomial.X 0 ^ 10 + 2 * MvPolynomial.X 0 ^ 9 -
    2 * MvPolynomial.X 0 ^ 8) * MvPolynomial.X 1 ^ 2 -
  MvPolynomial.X 0 ^ 15 * MvPolynomial.X 1 ^ 3

/-- Specialize x to one, retaining y as a genuine polynomial variable. -/
noncomputable def specializeXOne : Base k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 0 then 1 else Polynomial.X)

theorem specializeXOne_bPoly :
    specializeXOne k (bPoly k) = Polynomial.X + Polynomial.X ^ 2 - Polynomial.X ^ 3 := by
  simp [bPoly, specializeXOne]
  ring

/-- The family's fixed z-coefficient survives modulo y⁴. Evaluation x=1
reduces this to the nonzero y³ coefficient, so no domain assumption on the
quotient is needed. -/
theorem bPoly_cube_not_mem_yFourth :
    bPoly k ^ 3 ∉ Ideal.span {(MvPolynomial.X 1 : Base k) ^ 4} := by
  rw [Ideal.mem_span_singleton]
  rintro ⟨q, hq⟩
  have heq := congrArg (specializeXOne k) hq
  simp only [map_pow, map_mul, specializeXOne_bPoly] at heq
  have hy : specializeXOne k (MvPolynomial.X 1) = Polynomial.X := by
    simp [specializeXOne]
  rw [hy] at heq
  have hcube : (Polynomial.X + Polynomial.X ^ 2 - Polynomial.X ^ 3 : Polynomial k) ^ 3 =
      Polynomial.X ^ 3 + 3 * Polynomial.X ^ 4 - 5 * Polynomial.X ^ 6 +
      3 * Polynomial.X ^ 8 - Polynomial.X ^ 9 := by ring
  rw [hcube] at heq
  have hc := congrArg (fun p : Polynomial k => p.coeff 3) heq
  simp [Polynomial.coeff_X_pow_mul'] at hc

/-- The non-finite-generation criterion for the explicit field intersection,
given constant specialization at y=0 and a family with fixed coefficient B³.
`SpecializationBridge` and `FamilyCoefficient` prove these two hypotheses. -/
theorem not_finiteType_intersection_of_scalar_and_family
    (hscalar : ∀ p : intersection k, ∃ c : k, ∃ q : Poly k,
      (p : Poly k) = algebraMap k (Poly k) c + y k * q)
    (hfamily : ∀ n : ℕ, ∃ p : intersection k,
      (p : Poly k).coeff n = bPoly k ^ 3) :
    ¬ Algebra.FiniteType k (intersection k) := by
  apply not_finiteType_of_scalar_mod_and_coefficients
    (intersection k) (MvPolynomial.X 1) 4
    (Ideal.span {(MvPolynomial.X 1 : Base k) ^ 4})
  · exact Ideal.subset_span (Set.mem_singleton _)
  · exact hscalar
  · intro n
    obtain ⟨p, hp⟩ := hfamily n
    exact ⟨p, hp ▸ bPoly_cube_not_mem_yFourth k⟩

#print axioms bPoly_cube_not_mem_yFourth
#print axioms not_finiteType_intersection_of_scalar_and_family

end Hilbert14
