import Hilbert14.Lemmas.Intersection

/-! Cancellation between powers of x and powers of 1+x⁷y. -/

namespace Hilbert14
variable (k : Type*) [Field k]

private noncomputable def origin : Poly k →+* k :=
  (MvPolynomial.eval (fun _ : Fin 2 => 0)).comp (Polynomial.evalRingHom 0)

private theorem origin_x : origin k (x k) = 0 := by simp [origin, x]

private theorem origin_regularDenominator : origin k (1 + x k ^ 7 * y k) = 1 := by
  simp [origin, x, y]

/-- The regular denominator used in G⁻¹ does not vanish identically. -/
theorem regularDenominator_ne_zero : (1 + x k ^ 7 * y k : Poly k) ≠ 0 := by
  intro h
  have hh := congrArg (origin k) h
  rw [origin_regularDenominator, map_zero] at hh
  exact one_ne_zero hh

/-- The regular denominator is not divisible by x, without a Bézout assumption. -/
theorem x_not_dvd_regularDenominator : ¬ x k ∣ (1 + x k ^ 7 * y k : Poly k) := by
  intro h
  have hh := map_dvd (origin k) h
  rw [origin_x, origin_regularDenominator] at hh
  exact zero_ne_one (zero_dvd_iff.mp hh).symm

/-- Simultaneous x-power and regular-denominator-power representations have no poles. -/
theorem regularDenominator_intersection {t : Rat k}
    (hx : ∃ a : Poly k, ∃ n : ℕ, t = embed k a / embed k (x k) ^ n)
    (hs : ∃ b : Poly k, ∃ m : ℕ,
      t = embed k b / embed k (1 + x k ^ 7 * y k) ^ m) :
    t ∈ Set.range (embed k) :=
  powers_fraction_intersection (embed k).toRingHom (embed_injective k)
    (x_prime k) (x_not_dvd_regularDenominator k) (regularDenominator_ne_zero k) hx hs

#print axioms regularDenominator_intersection
end Hilbert14
