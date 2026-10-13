import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FiniteType

/-! The exact field intersection in Kuroda §4.1, with parameter t₂ = 5.
The outer polynomial variable is z; the two inner variables are x and y.
The non-finite-generation statement is proved in `Hilbert14.Theorem`. -/
namespace Hilbert14

noncomputable section

abbrev Base (k : Type*) [Field k] := MvPolynomial (Fin 2) k
abbrev Poly (k : Type*) [Field k] := Polynomial (Base k)
abbrev Rat (k : Type*) [Field k] := FractionRing (Poly k)

variable (k : Type*) [Field k]

noncomputable def embed : Poly k →ₐ[k] Rat k := IsScalarTower.toAlgHom k (Poly k) (Rat k)

def x : Poly k := Polynomial.C (MvPolynomial.X 0)
def y : Poly k := Polynomial.C (MvPolynomial.X 1)
def z : Poly k := Polynomial.X

noncomputable def a : Rat k := embed k (x k) ^ 5 * embed k (y k) + (embed k (x k))⁻¹ ^ 2
noncomputable def b : Rat k := embed k (x k) ^ 4 * embed k (y k) -
  (embed k (x k))⁻¹ ^ 2 + (embed k (x k))⁻¹ ^ 3
noncomputable def c : Rat k := embed k (z k) + (embed k (x k))⁻¹

noncomputable def field : IntermediateField k (Rat k) :=
  IntermediateField.adjoin k {a k, b k, c k}

noncomputable def intersection : Subalgebra k (Poly k) :=
  (field k).toSubalgebra.comap (embed k)

theorem mem_intersection (p : Poly k) : p ∈ intersection k ↔ embed k p ∈ field k := Iff.rfl

theorem embed_injective : Function.Injective (embed k) :=
  IsFractionRing.injective (Poly k) (Rat k)

/-- Kuroda’s explicit counterexample over the complex numbers. -/
def MainTheorem : Prop := ¬ Algebra.FiniteType ℂ (intersection ℂ)

end

end Hilbert14
