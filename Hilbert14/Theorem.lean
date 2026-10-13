import Hilbert14.Specialization
import Hilbert14.Family

/-! Kuroda's counterexample to Hilbert's fourteenth problem.

The field and intersection are the explicit objects in `Hilbert14.Definitions`.
All mathematical inputs to the non-finite-generation criterion are discharged.
-/
namespace Hilbert14

/-- Kuroda's explicit polynomial intersection is not finitely generated over
any field of characteristic zero. -/
theorem kuroda_not_finiteType (k : Type*) [Field k] [CharZero k] :
    ¬ Algebra.FiniteType k (intersection k) :=
  not_finiteType_intersection_of_family k (exists_intersection_coefficient k)

/-- The complex-field counterexample. -/
theorem hilbert_fourteenth_counterexample :
    ¬ Algebra.FiniteType ℂ (intersection ℂ) :=
  kuroda_not_finiteType ℂ

/-- The non-finite-generation statement for the explicit field. -/
theorem main : MainTheorem := hilbert_fourteenth_counterexample

/-- An explicit negative answer in three polynomial variables over ℂ. -/
theorem hilbert_fourteenth_negative :
    ∃ L : IntermediateField ℂ (Rat ℂ),
      ¬ Algebra.FiniteType ℂ (L.toSubalgebra.comap (embed ℂ)) :=
  ⟨field ℂ, hilbert_fourteenth_counterexample⟩

end Hilbert14
