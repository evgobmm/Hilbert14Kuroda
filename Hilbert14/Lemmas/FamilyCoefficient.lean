import Hilbert14.Lemmas.FamilyConcrete
import Hilbert14.Lemmas.FamilyCoefficientBase
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.FinCases

/-! The fixed coefficient B³ of every family member, recovered
through the injective scalar extension k[x,y] → k(x,y). -/

namespace Hilbert14
noncomputable section
variable (k : Type*) [Field k]

abbrev CoeffField := FractionRing (Base k)
abbrev CoeffPoly := Polynomial (CoeffField k)
abbrev ExpandedRat := FractionRing (CoeffPoly k)

def expandPoly : Poly k →ₐ[k] CoeffPoly k :=
  Polynomial.mapAlgHom (IsScalarTower.toAlgHom k (Base k) (CoeffField k))

def expandedEmbed : CoeffPoly k →ₐ[k] ExpandedRat k :=
  IsScalarTower.toAlgHom k (CoeffPoly k) (ExpandedRat k)

def expandIntoRat : Poly k →ₐ[k] ExpandedRat k := (expandedEmbed k).comp (expandPoly k)

theorem expandIntoRat_injective : Function.Injective (expandIntoRat k) :=
  (IsFractionRing.injective (CoeffPoly k) (ExpandedRat k)).comp
    (Polynomial.map_injective _ (IsFractionRing.injective (Base k) (CoeffField k)))

def expandRat : Rat k →ₐ[k] ExpandedRat k :=
  IsFractionRing.liftAlgHom (expandIntoRat_injective k)

@[simp] theorem expandRat_embed (p : Poly k) :
    expandRat k (embed k p) = expandedEmbed k (expandPoly k p) :=
  IsFractionRing.lift_algebraMap (expandIntoRat_injective k) p

def expandedConstant : CoeffField k →ₐ[k] ExpandedRat k :=
  (expandedEmbed k).comp Polynomial.CAlgHom

theorem expandedConstant_injective : Function.Injective (expandedConstant k) :=
  (IsFractionRing.injective (CoeffPoly k) (ExpandedRat k)).comp Polynomial.C_injective

@[simp] theorem expandPoly_C (p : Base k) :
    expandPoly k (Polynomial.C p) = Polynomial.C (algebraMap (Base k) (CoeffField k) p) := by
  simp [expandPoly, Polynomial.coe_mapAlgHom]

@[simp] theorem expandPoly_z : expandPoly k (z k) = Polynomial.X := by
  simp [expandPoly, z, Polynomial.coe_mapAlgHom]

private theorem expand_x_constant : expandRat k (embed k (x k)) =
    expandedConstant k (algebraMap (Base k) (CoeffField k) (MvPolynomial.X 0)) := by
  simp [x, expandedConstant]

private theorem expand_y_constant : expandRat k (embed k (y k)) =
    expandedConstant k (algebraMap (Base k) (CoeffField k) (MvPolynomial.X 1)) := by
  simp [y, expandedConstant]

/-- Every recurrence coefficient is independent of the outer variable z. -/
theorem expand_family_coefficient_constant {t : Rat k}
    (ht : t ∈ Algebra.adjoin k {familyH k, a k}) :
    ∃ d : CoeffField k, expandRat k t = expandedConstant k d := by
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
    rcases ht with rfl | rfl
    · rw [familyH_formula]
      refine ⟨(algebraMap (Base k) (CoeffField k) (MvPolynomial.X 0))^5 *
          algebraMap (Base k) (CoeffField k) (MvPolynomial.X 1) +
          (algebraMap (Base k) (CoeffField k) (MvPolynomial.X 0))^4 *
          algebraMap (Base k) (CoeffField k) (MvPolynomial.X 1) +
          (algebraMap (Base k) (CoeffField k) (MvPolynomial.X 0))⁻¹^3, ?_⟩
      simp only [map_add, map_mul, map_pow, map_inv₀, expand_x_constant, expand_y_constant]
    · refine ⟨(algebraMap (Base k) (CoeffField k) (MvPolynomial.X 0))^5 *
          algebraMap (Base k) (CoeffField k) (MvPolynomial.X 1) +
          (algebraMap (Base k) (CoeffField k) (MvPolynomial.X 0))⁻¹^2, ?_⟩
      simp only [a, map_add, map_mul, map_pow, map_inv₀, expand_x_constant, expand_y_constant]
  | algebraMap r => exact ⟨algebraMap k (CoeffField k) r, by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨d, hd⟩ := hp
    obtain ⟨e, he⟩ := hq
    exact ⟨d+e, by simp [hd,he]⟩
  | mul p q _ _ hp hq =>
    obtain ⟨d, hd⟩ := hp
    obtain ⟨e, he⟩ := hq
    exact ⟨d*e, by simp [hd,he]⟩

/-- A shifted divided-power convolution has the expected top coefficient. -/
theorem dividedPolynomial_coeff {F : Type*} [Field F] (ds : ℕ → F) (u : F) (n : ℕ) :
    (∑ j : Fin (n+1), Polynomial.C (ds j / (Nat.factorial (n-j) : F)) *
      (Polynomial.X + Polynomial.C u) ^ (n-j)).coeff n = ds 0 / (Nat.factorial n : F) := by
  classical
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  rw [Finset.sum_eq_single (0 : Fin (n+1))]
  · simp
  · intro j _ hj
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun he => hj (Fin.ext he))
    have hjle : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    have hlt : n-j.val < n := Nat.sub_lt (lt_of_lt_of_le hjpos hjle) hjpos
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero, mul_zero]
  · simp


theorem expandedEmbed_dividedPolynomial (ds : ℕ → CoeffField k) (u : CoeffField k) (n : ℕ) :
    expandedEmbed k (∑ j : Fin (n+1), Polynomial.C (ds j / (Nat.factorial (n-j) : CoeffField k)) *
      (Polynomial.X + Polynomial.C u) ^ (n-j)) =
    Family.dividedConvolution (fun j => expandedConstant k (ds j))
      (expandedEmbed k (Polynomial.X + Polynomial.C u)) n := by
  unfold Family.dividedConvolution
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_pow]
  change expandedConstant k (ds j / (Nat.factorial (n-j) : CoeffField k)) *
    (expandedEmbed k (Polynomial.X + Polynomial.C u)) ^ (n-j) = _
  rw [map_div₀, map_natCast]
  ring

instance coeffFieldCharZero [CharZero k] : CharZero (CoeffField k) where
  cast_injective m n h := by
    apply Nat.cast_injective (R:=k)
    apply (algebraMap k (CoeffField k)).injective
    simpa only [map_natCast] using h

/-- Coefficients are preserved when the universally polynomial family is
viewed over the fraction field of k[x,y]. -/
theorem polynomial_family_coefficient [CharZero k]
    (cs : ℕ → Rat k) (hc0 : cs 0 = 1)
    (hcR : ∀ n, cs n ∈ Algebra.adjoin k {familyH k,a k})
    (n : ℕ) (q : Poly k)
    (hq : embed k q = (Nat.factorial n : Rat k) * embed k (familyB k)^3 *
      Family.dividedConvolution cs (c k) n) : q.coeff n = bPoly k ^ 3 := by
  classical
  choose ds hds using fun j => expand_family_coefficient_constant k (hcR j)
  have hd0 : ds 0 = 1 := by
    apply expandedConstant_injective k
    rw [← hds, hc0, map_one, map_one]
  let u : CoeffField k := (algebraMap (Base k) (CoeffField k) (MvPolynomial.X 0))⁻¹
  let β : CoeffField k := algebraMap (Base k) (CoeffField k) (bPoly k)
  let S : CoeffPoly k := ∑ j : Fin (n+1),
    Polynomial.C (ds j / (Nat.factorial (n-j) : CoeffField k)) *
      (Polynomial.X + Polynomial.C u) ^ (n-j)
  have hB : expandRat k (embed k (familyB k)) = expandedConstant k β := by
    rw [familyB_eq_C_bPoly, expandRat_embed, expandPoly_C]
    rfl
  have hc : expandRat k (c k) = expandedEmbed k (Polynomial.X + Polynomial.C u) := by
    simp only [c, map_add, map_inv₀, expandRat_embed, expandPoly_z]
    rw [← expandRat_embed, expand_x_constant]
    change expandedEmbed k Polynomial.X + (expandedConstant k
      (algebraMap (Base k) (CoeffField k) (MvPolynomial.X 0)))⁻¹ = _
    rw [← map_inv₀]
    rfl
  have hs : expandRat k (Family.dividedConvolution cs (c k) n) = expandedEmbed k S := by
    rw [expandedEmbed_dividedPolynomial]
    simp only [Family.dividedConvolution, map_sum, map_mul, map_div₀, map_pow, map_natCast,
      hds, hc]
  have heq : expandPoly k q = Polynomial.C ((Nat.factorial n : CoeffField k) * β^3) * S := by
    apply IsFractionRing.injective (CoeffPoly k) (ExpandedRat k)
    change expandedEmbed k (expandPoly k q) = expandedEmbed k _
    have hh := congrArg (expandRat k) hq
    simp only [map_mul, map_natCast, map_pow, expandRat_embed] at hh
    have hB' := hB
    rw [expandRat_embed] at hB'
    rw [hB', hs] at hh
    rw [map_mul]
    change expandedEmbed k (expandPoly k q) = expandedConstant k
      ((Nat.factorial n : CoeffField k) * β^3) * expandedEmbed k S
    simpa only [map_mul, map_natCast, map_pow] using hh
  have hn : (Nat.factorial n : CoeffField k) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hcoeff := congrArg (fun p : CoeffPoly k => p.coeff n) heq
  rw [Polynomial.coeff_C_mul, dividedPolynomial_coeff, hd0] at hcoeff
  have hcoeff' : algebraMap (Base k) (CoeffField k) (q.coeff n) = β^3 := by
    simpa [expandPoly, Polynomial.coeff_map, hn, mul_assoc, S, div_eq_mul_inv,
      mul_comm (β^3), mul_left_comm] using hcoeff
  apply IsFractionRing.injective (Base k) (CoeffField k)
  simpa only [map_pow] using hcoeff'

/-- The universally indexed family has the exact coefficient required by the
non-finite-generation argument in the genuine field intersection. -/
theorem exists_intersection_coefficient [CharZero k] (n : ℕ) :
    ∃ p : intersection k, (p : Poly k).coeff n = bPoly k ^ 3 := by
  obtain ⟨cs, hc0, hcR, hfamily⟩ := exists_polynomial_family k
  obtain ⟨q, hqA, hq⟩ := hfamily n
  exact ⟨⟨q,hqA⟩, polynomial_family_coefficient k cs hc0 hcR n q hq⟩

#print axioms polynomial_family_coefficient
#print axioms exists_intersection_coefficient

end
end Hilbert14
