import Hilbert14.Definitions
import Hilbert14.Lemmas.IntersectionDenominators
import Hilbert14.Lemmas.IntersectionSymmetry
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.Basic

/-! Denominator cancellation used in the genuine field-intersection argument.
No Bézout hypothesis is imposed: distinct polynomial variables are prime but
need not generate the unit ideal. `Hilbert14.Lemmas.IntersectionFinal` combines
this cancellation with symmetry and coordinate transport. -/
namespace Hilbert14

section Coordinates
variable (k : Type*) [Field k]

/-- The second coordinate exchanged with x by Kuroda's symmetry. -/
noncomputable def v : Poly k := y k - x k + x k ^ 2

theorem x_prime : Prime (x k) :=
  Polynomial.prime_C_iff.mpr (MvPolynomial.X_prime (i := 0))

private noncomputable def atZeroOne : Poly k →+* k :=
  (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 0 else 1)).comp
    (Polynomial.evalRingHom 0)

private theorem atZeroOne_x : atZeroOne k (x k) = 0 := by
  simp [atZeroOne, x]

private theorem atZeroOne_v : atZeroOne k (v k) = 1 := by
  simp [atZeroOne, v, x, y]

theorem x_not_dvd_v : ¬ x k ∣ v k := by
  intro h
  have hh := map_dvd (atZeroOne k) h
  rw [atZeroOne_x, atZeroOne_v] at hh
  exact zero_ne_one (zero_dvd_iff.mp hh).symm

theorem v_ne_zero : v k ≠ 0 := by
  intro h
  have hh := congrArg (atZeroOne k) h
  rw [atZeroOne_v, map_zero] at hh
  exact one_ne_zero hh

/-- The denominator-intersection step for the actual coordinates of the target.
This applies to arbitrary fractions, not just expressions in the field generators. -/
theorem x_v_powers_intersection {t : Rat k}
    (hx : ∃ a : Poly k, ∃ n : ℕ, t = embed k a / embed k (x k) ^ n)
    (hv : ∃ b : Poly k, ∃ m : ℕ, t = embed k b / embed k (v k) ^ m) :
    t ∈ Set.range (embed k) :=
  powers_fraction_intersection (embed k).toRingHom (embed_injective k)
    (x_prime k) (x_not_dvd_v k) (v_ne_zero k) hx hv

end Coordinates

#print axioms fraction_mem_range_of_prime_denominators
#print axioms powers_fraction_intersection
#print axioms x_v_powers_intersection

end Hilbert14
