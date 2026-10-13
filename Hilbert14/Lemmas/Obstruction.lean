import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.Basic

/-! Non-finite-generation criteria from scalar-plus-nilpotent polynomial images.
Integrality and finite algebra generation imply finite module generation,
which bounds coefficient support even when the coefficient ring has zero divisors. -/
namespace Hilbert14

open Polynomial

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

/-- An element differing from a scalar by a nilpotent is integral. -/
theorem isIntegral_of_nilpotent_sub (a : S)
    (h : ∃ c : k, ∃ n : ℕ, (a - algebraMap k S c) ^ n = 0) :
    IsIntegral k a := by
  obtain ⟨c, n, hn⟩ := h
  refine ⟨(X - C c) ^ n, (monic_X_sub_C c).pow n, ?_⟩
  simpa using hn

/-- A finite-type algebra whose elements are scalar plus nilpotent is a finite module. -/
theorem finite_of_finiteType_nilpotent_sub [Algebra.FiniteType k S]
    (h : ∀ a : S, ∃ c : k, ∃ n : ℕ, (a - algebraMap k S c) ^ n = 0) :
    Module.Finite k S := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k S)
  exact ⟨by
    apply hs ▸ fg_adjoin_of_finite s.finite_toSet
    intro a _
    exact isIntegral_of_nilpotent_sub a (h a)⟩

/-- Finite scalar spans of polynomials have a uniform upper bound on support,
even when the coefficients have zero divisors. -/
theorem exists_coeff_bound_of_fg (M : Submodule k R[X]) (hM : M.FG) :
    ∃ n : ℕ, ∀ p ∈ M, ∀ i, n ≤ i → p.coeff i = 0 := by
  obtain ⟨s, hs⟩ := hM
  obtain ⟨n, hn⟩ := Polynomial.span_of_finite_le_degreeLT (R := R) s.finite_toSet
  have hle : M ≤ (Polynomial.degreeLT R n).restrictScalars k := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro p hp
    exact hn (Submodule.subset_span hp)
  refine ⟨n, fun p hp i hi => ?_⟩
  exact (Polynomial.degree_lt_iff_coeff_zero p n).mp
    (Polynomial.mem_degreeLT.mp (hle hp)) i hi

/-- The quotient-image obstruction: nilpotence bounds algebra generators, while
nonzero coefficients in arbitrarily high degrees prevent finite module generation. -/
theorem not_finiteType_of_nilpotent_sub_and_unbounded
    (A : Subalgebra k R[X])
    (hscalar : ∀ p : A, ∃ c : k, ∃ n : ℕ,
      ((p : R[X]) - algebraMap k R[X] c) ^ n = 0)
    (hunbounded : ∀ n : ℕ, ∃ p : A, (p : R[X]).coeff n ≠ 0) :
    ¬ Algebra.FiniteType k A := by
  intro hfinite
  let := hfinite
  have hnil : ∀ a : A, ∃ c : k, ∃ n : ℕ, (a - algebraMap k A c) ^ n = 0 := by
    intro a
    obtain ⟨c, n, hn⟩ := hscalar a
    exact ⟨c, n, Subtype.ext hn⟩
  let : Module.Finite k A := finite_of_finiteType_nilpotent_sub hnil
  have hfg : A.toSubmodule.FG := by
    exact Module.Finite.iff_fg.mp (inferInstance : Module.Finite k A.toSubmodule)
  obtain ⟨n, hn⟩ := exists_coeff_bound_of_fg A.toSubmodule hfg
  obtain ⟨p, hp⟩ := hunbounded n
  exact hp (hn p p.property n le_rfl)

/-- Convenient formulation for an algebra mapped into a polynomial quotient. -/
theorem not_finiteType_of_polynomial_image
    (φ : S →ₐ[k] R[X])
    (hscalar : ∀ a : S, ∃ c : k, ∃ n : ℕ,
      (φ a - algebraMap k R[X] c) ^ n = 0)
    (hunbounded : ∀ n : ℕ, ∃ a : S, (φ a).coeff n ≠ 0) :
    ¬ Algebra.FiniteType k S := by
  intro hfinite
  let := hfinite
  apply not_finiteType_of_nilpotent_sub_and_unbounded φ.range
  · intro p
    obtain ⟨a, ha⟩ := p.property
    rw [← ha]
    exact hscalar a
  · intro n
    obtain ⟨a, ha⟩ := hunbounded n
    exact ⟨φ.rangeRestrict a, ha⟩
  · exact Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective

/-- Direct coefficient-ideal form of the obstruction. For Kuroda, take `d = y`,
`m = 4`, and `I = (y⁴)`. The family need only have a coefficient outside `I`
at every index; a fixed surviving leading coefficient supplies this. -/
theorem not_finiteType_of_scalar_mod_and_coefficients
    (A : Subalgebra k R[X]) (d : R) (m : ℕ) (I : Ideal R)
    (hd : d ^ m ∈ I)
    (hscalar : ∀ p : A, ∃ c : k, ∃ q : R[X],
      (p : R[X]) = algebraMap k R[X] c + C d * q)
    (hcoeff : ∀ n : ℕ, ∃ p : A, (p : R[X]).coeff n ∉ I) :
    ¬ Algebra.FiniteType k A := by
  let ψ : R[X] →ₐ[k] (R ⧸ I)[X] := mapAlgHom (Ideal.Quotient.mkₐ k I)
  apply not_finiteType_of_polynomial_image (ψ.comp A.val)
  · intro a
    obtain ⟨c, q, hq⟩ := hscalar a
    refine ⟨c, m, ?_⟩
    change (ψ (a : R[X]) - algebraMap k (R ⧸ I)[X] c) ^ m = 0
    rw [hq, map_add, AlgHom.commutes, add_sub_cancel_left, map_mul, mul_pow]
    have hd' : ψ (C d) ^ m = 0 := by
      simp only [ψ, coe_mapAlgHom, Polynomial.map_C]
      change (C (Ideal.Quotient.mk I d)) ^ m = 0
      rw [← map_pow, ← map_pow]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hd, map_zero]
    rw [hd', zero_mul]
  · intro n
    obtain ⟨p, hp⟩ := hcoeff n
    refine ⟨p, ?_⟩
    change ((mapAlgHom (Ideal.Quotient.mkₐ k I)) (p : R[X])).coeff n ≠ 0
    rw [coeff_mapAlgHom_apply]
    exact fun h => hp (Ideal.Quotient.eq_zero_iff_mem.mp h)

#print axioms isIntegral_of_nilpotent_sub
#print axioms finite_of_finiteType_nilpotent_sub
#print axioms exists_coeff_bound_of_fg
#print axioms not_finiteType_of_nilpotent_sub_and_unbounded
#print axioms not_finiteType_of_polynomial_image
#print axioms not_finiteType_of_scalar_mod_and_coefficients

end Hilbert14
