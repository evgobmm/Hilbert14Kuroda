import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FiniteType

/-!
# Kuroda's counterexample to Hilbert's fourteenth problem

The explicit example in §4.1 of
[Hilbert's fourteenth problem and field modifications](https://arxiv.org/abs/1803.08002v1),
with parameter t₂=5. All definitions depend only on Mathlib.
The outer polynomial variable is z; the inner variables are x and y.
-/
namespace Hilbert14.Paper

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

/-- Kuroda’s explicit counterexample over the complex numbers. -/
def CounterexampleStatement : Prop := ¬ Algebra.FiniteType ℂ (intersection ℂ)

end

end Hilbert14.Paper
