import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Prime.Lemmas

/-! Prime-power denominator cancellation in an integral domain. -/

namespace Hilbert14

section Denominators
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
variable (ι : R →+* K) (hι : Function.Injective ι)
include hι

/-- A fraction with a prime-power denominator and a second denominator not
divisible by that prime is already in the original domain. -/
theorem fraction_mem_range_of_prime_denominators {p d a b : R} {n : ℕ}
    (hp : Prime p) (hd : ¬ p ∣ d) (hd0 : d ≠ 0)
    (h : ι a / ι p ^ n = ι b / ι d) :
    ∃ r : R, ι a / ι p ^ n = ι r := by
  have hp0 : ι p ≠ 0 := fun hz => hp.ne_zero (hι (hz.trans (map_zero ι).symm))
  have hd0' : ι d ≠ 0 := fun hz => hd0 (hι (hz.trans (map_zero ι).symm))
  have heq : a * d = b * p ^ n := by
    apply hι
    simpa only [map_mul, map_pow] using (div_eq_div_iff (pow_ne_zero n hp0) hd0').mp h
  have hdiv : p ^ n ∣ a := hp.pow_dvd_of_dvd_mul_right n hd
    (heq.symm ▸ dvd_mul_left (p ^ n) b)
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨r, ?_⟩
  rw [hr, map_mul, map_pow]
  exact mul_div_cancel_left₀ (ι r) (pow_ne_zero n hp0)

/-- Intersection of the two sets of prime-power-denominator fractions. -/
theorem powers_fraction_intersection {p q : R} (hp : Prime p)
    (hpq : ¬ p ∣ q) (hq0 : q ≠ 0) {t : K}
    (htp : ∃ a : R, ∃ n : ℕ, t = ι a / ι p ^ n)
    (htq : ∃ b : R, ∃ m : ℕ, t = ι b / ι q ^ m) :
    t ∈ Set.range ι := by
  obtain ⟨a, n, rfl⟩ := htp
  obtain ⟨b, m, heq⟩ := htq
  obtain ⟨r, hr⟩ := fraction_mem_range_of_prime_denominators ι hι hp
    (fun h => hpq (hp.dvd_of_dvd_pow h)) (pow_ne_zero m hq0)
    (by simpa only [map_pow] using heq)
  exact ⟨r, hr.symm⟩

end Denominators

#print axioms fraction_mem_range_of_prime_denominators
#print axioms powers_fraction_intersection

end Hilbert14
