import Hilbert14.Lemmas.FamilyTaylor
import Hilbert14.Lemmas.IntersectionDenominators
import Mathlib.Tactic.FieldSimp

/-! Subalgebras of fractions with powers of a fixed denominator
and their intersection criterion for polynomiality. -/

namespace Hilbert14.Family

variable {k R F : Type*} [Field k] [CommRing R] [Algebra k R] [Field F] [Algebra k F]

/-- The actual fractions whose denominator is a power of `p`. -/
def powersDenominator (ι : R →ₐ[k] F) (p : R) (hp : ι p ≠ 0) : Subalgebra k F where
  carrier := {q | ∃ a : R, ∃ n : ℕ, q=ι a/(ι p)^n}
  algebraMap_mem' c := ⟨algebraMap k R c,0,by simp⟩
  add_mem' := by
    rintro q r ⟨a,n,rfl⟩ ⟨b,m,rfl⟩
    refine ⟨a*p^m+b*p^n,n+m,?_⟩
    simp only [map_add,map_mul,map_pow,pow_add]
    field_simp
  mul_mem' := by
    rintro q r ⟨a,n,rfl⟩ ⟨b,m,rfl⟩
    refine ⟨a*b,n+m,?_⟩
    simp only [map_mul,pow_add,div_mul_div_comm]

theorem mem_powersDenominator (ι : R →ₐ[k] F) (p : R) (hp : ι p ≠ 0) (a : R) :
    ι a ∈ powersDenominator ι p hp := ⟨a,0,by simp⟩

theorem inv_mem_powersDenominator (ι : R →ₐ[k] F) (p : R) (hp : ι p ≠ 0) :
    (ι p)⁻¹ ∈ powersDenominator ι p hp := ⟨1,1,by simp⟩

/-- Polynomiality from membership in two explicit localizations. -/
theorem mem_range_of_two_powersDenominator [IsDomain R] (ι : R →ₐ[k] F)
    (hι : Function.Injective ι) (p s : R) (hp : Prime p) (hps : ¬ p∣s)
    (hp0 : ι p≠0) (hs0 : ι s≠0) {q : F}
    (hqp : q∈powersDenominator ι p hp0) (hqs : q∈powersDenominator ι s hs0) :
    q ∈ Set.range ι := by
  exact Hilbert14.powers_fraction_intersection ι.toRingHom hι hp hps
    (fun h => hs0 (by rw [h,map_zero])) hqp hqs

#print axioms mem_range_of_two_powersDenominator

end Hilbert14.Family
