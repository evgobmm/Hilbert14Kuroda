import Hilbert14.Lemmas.Specialization
import Hilbert14.Lemmas.Coordinates
import Hilbert14.Lemmas.IntersectionInvariants
import Hilbert14.Lemmas.IntersectionFinal
import Hilbert14.Lemmas.ObstructionCoefficient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Constant specialization at y=0 for the explicit intersection,
via the coordinate automorphism and the shifted-cusp obstruction. -/

namespace Hilbert14
noncomputable section

open Polynomial

variable (k : Type*) [Field k]

/-- Set y=0 and reorder the variables as k[z][x]. -/
def specializeYZero : Poly k →ₐ[k] (k[X])[X] := polyHom k X 0 (C X)

/-- Set y=0 in the coordinates before Laurent inversion. -/
def specializeShifted : Poly k →ₐ[k] (k[X])[X] := polyHom k X 0 (C X + X)

def specializationToLaurent : (k[X])[X] →ₐ[k] LaurentPolynomial k[X] :=
  (Polynomial.toLaurentAlg : (k[X])[X] →ₐ[k[X]] LaurentPolynomial k[X]).restrictScalars k

def specializedLaurentMap : Laurent k →ₐ[k] LaurentPolynomial k[X] :=
  IsLocalization.Away.liftAlgHom (x k)
    (show IsUnit ((specializationToLaurent k).comp (specializeYZero k) (x k)) by
      simpa [specializationToLaurent, specializeYZero] using
        (LaurentPolynomial.isUnit_T (R := k[X]) 1))

@[simp] theorem specializedLaurentMap_embed (p : Poly k) :
    specializedLaurentMap k (intoLaurent k p) = (specializeYZero k p).toLaurent := by
  exact IsLocalization.Away.lift_eq (x k)
    (show IsUnit ((specializationToLaurent k).comp (specializeYZero k) (x k)) by
      simpa [specializationToLaurent, specializeYZero] using
        (LaurentPolynomial.isUnit_T (R := k[X]) 1)) p

@[simp] theorem specializedLaurentMap_lx :
    specializedLaurentMap k (lx k) = LaurentPolynomial.T 1 := by
  simp [lx, specializeYZero]

@[simp] theorem specializedLaurentMap_ly :
    specializedLaurentMap k (ly k) = 0 := by
  simp [ly, specializeYZero]

@[simp] theorem specializedLaurentMap_lz :
    specializedLaurentMap k (lz k) = LaurentPolynomial.C X := by
  simp [lz, specializeYZero]

@[simp] theorem specializedLaurentMap_li :
    specializedLaurentMap k (li k) = LaurentPolynomial.T (-1) := by
  have h := congrArg (specializedLaurentMap k) (lx_mul_li k)
  rw [map_mul, map_one, specializedLaurentMap_lx] at h
  calc
    specializedLaurentMap k (li k) =
        (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) *
          specializedLaurentMap k (li k) := by
      rw [← LaurentPolynomial.T_add]
      simp only [neg_add_cancel, LaurentPolynomial.T_zero, one_mul]
    _ = LaurentPolynomial.T (-1) := by rw [mul_assoc, h, mul_one]

theorem specialize_thetaPoly (q : Poly k) :
    specializedLaurentMap k (thetaPoly k q) =
      LaurentPolynomial.invert (specializeShifted k q).toLaurent := by
  have heq : (specializedLaurentMap k).comp (thetaPoly k) =
      ((LaurentPolynomial.invert (R := k[X])).toAlgHom.restrictScalars k).comp
        ((specializationToLaurent k).comp (specializeShifted k)) := by
    apply polyHom_ext k
    · simp [thetaPoly, specializeShifted, specializationToLaurent]
    · simp [thetaPoly, specializeShifted, specializationToLaurent]
    · simp [thetaPoly, specializeShifted, specializationToLaurent]
  exact DFunLike.congr_fun heq q

theorem specializeShifted_mem_cusp {q : Poly k} (hq : q ∈ symmetricAlgebra k) :
    specializeShifted k q ∈ shiftedCusp := by
  change q ∈ Algebra.adjoin k {x k + v k, x k * v k, z k} at hq
  induction hq using Algebra.adjoin_induction with
  | mem p hp =>
    rcases hp with rfl | rfl | rfl
    · have heq : specializeShifted k (x k + v k) = (X : (k[X])[X]) ^ 2 := by
        simp [specializeShifted, v]
      rw [heq]
      exact Algebra.subset_adjoin (by simp)
    · have heq : specializeShifted k (x k * v k) =
          (X : (k[X])[X]) ^ 3 - X ^ 2 := by
        simp [specializeShifted, v]
        ring
      rw [heq]
      exact (shiftedCusp (k := k)).sub_mem
        (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp))
    · simp only [specializeShifted, polyHom_z]
      exact Algebra.subset_adjoin (by simp)
  | algebraMap r => simpa only [AlgHom.commutes] using (shiftedCusp (k := k)).algebraMap_mem r
  | add p q _ _ hp hq => simpa only [map_add] using (shiftedCusp (k := k)).add_mem hp hq
  | mul p q _ _ hp hq => simpa only [map_mul] using (shiftedCusp (k := k)).mul_mem hp hq

theorem specializeYZero_scalar_of_thetaPoly [CharZero k] {p q : Poly k}
    (hq : q ∈ symmetricAlgebra k) (hpq : thetaPoly k q = intoLaurent k p) :
    ∃ c : k, specializeYZero k p = C (C c) := by
  have h := congrArg (specializedLaurentMap k) hpq
  rw [specialize_thetaPoly, specializedLaurentMap_embed] at h
  exact ⟨_, eq_scalar_of_laurent_eq_shiftedCusp
    (specializeYZero k p) (specializeShifted k q) h.symm (specializeShifted_mem_cusp k hq)⟩

/-- Substitute the reordered x,z-polynomial back into the original ring. -/
def restoreSpecialization : (k[X])[X] →ₐ[k] Poly k :=
  Polynomial.eval₂AlgHom (Polynomial.aeval (z k)) (x k) (fun _ => Commute.all _ _)

def eraseY : Poly k →ₐ[k] Poly k := polyHom k (x k) 0 (z k)

theorem restore_specialization :
    (restoreSpecialization k).comp (specializeYZero k) = eraseY k := by
  apply polyHom_ext k <;> simp [restoreSpecialization, specializeYZero, eraseY]

theorem subtract_eraseY_mem (p : Poly k) :
    p - eraseY k p ∈ Ideal.span {y k} := by
  let I : Ideal (Poly k) := Ideal.span {y k}
  let π := Ideal.Quotient.mkₐ k I
  have hy : π (y k) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  have heq : π.comp (eraseY k) = π := by
    apply polyHom_ext k (T := Poly k ⧸ I) (f := π.comp (eraseY k)) (g := π)
    · simp [eraseY]
    · simp [eraseY, hy]
    · simp [eraseY]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (p - eraseY k p) = 0
  have hp : π (eraseY k p) = π p := DFunLike.congr_fun heq p
  rw [map_sub, hp, sub_self]

theorem scalar_plus_y_of_specializeYZero {p : Poly k} {c : k}
    (hp : specializeYZero k p = C (C c)) :
    ∃ q : Poly k, p = algebraMap k (Poly k) c + y k * q := by
  have h := congrArg (restoreSpecialization k) hp
  have heq : eraseY k p = algebraMap k (Poly k) c := by
    rw [← DFunLike.congr_fun (restore_specialization k) p]
    simpa [restoreSpecialization] using h
  have hmem := subtract_eraseY_mem k p
  rw [heq, Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, sub_eq_iff_eq_add.mp hq |>.trans (add_comm _ _)⟩

/-- Every element of the field intersection specializes to a scalar at y=0,
so it is a scalar plus a multiple of y in the polynomial ring. -/
theorem intersection_scalar_plus_y [CharZero k] (p : intersection k) :
    ∃ c : k, ∃ r : Poly k,
      (p : Poly k) = algebraMap k (Poly k) c + y k * r := by
  obtain ⟨q, hq, hpq⟩ := (mem_intersection_iff_theta_symmetricAlgebra k p).mp p.property
  have htheta : theta k (embed k q) = laurentToRat k (thetaPoly k q) := by
    change extendLaurent k (thetaEquiv k) (embed k q) = _
    rw [extendLaurent_embed]
    change laurentToRat k (thetaLaurent k (intoLaurent k q)) = _
    rw [thetaLaurent_embed]
  have hpq' : thetaPoly k q = intoLaurent k p := by
    apply laurentToRat_injective k
    rw [laurentToRat_embed, ← htheta]
    exact hpq
  obtain ⟨c, hc⟩ := specializeYZero_scalar_of_thetaPoly k hq hpq'
  exact ⟨c, scalar_plus_y_of_specializeYZero k hc⟩

/-- Constant specialization reduces non-finite-generation to the existence
of the family with fixed coefficient B³, supplied by `FamilyCoefficient`. -/
theorem not_finiteType_intersection_of_family [CharZero k]
    (hfamily : ∀ n : ℕ, ∃ p : intersection k,
      (p : Poly k).coeff n = bPoly k ^ 3) :
    ¬ Algebra.FiniteType k (intersection k) :=
  not_finiteType_intersection_of_scalar_and_family k (intersection_scalar_plus_y k) hfamily

#print axioms specializeYZero_scalar_of_thetaPoly
#print axioms scalar_plus_y_of_specializeYZero
#print axioms intersection_scalar_plus_y
#print axioms not_finiteType_intersection_of_family

end
end Hilbert14
