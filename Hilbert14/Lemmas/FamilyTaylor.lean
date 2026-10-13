import Hilbert14.Lemmas.Family
import Mathlib.RingTheory.PowerSeries.Exp

/-! The finite Taylor identity for the universal recurrence, obtained from the
coefficient identity of the formal exponential. No analytic convergence is involved. -/
namespace Hilbert14.Family

variable {F : Type*} [Field F] [CharZero F]

noncomputable def dividedConvolution (c : ℕ → F) (t : F) (n : ℕ) : F :=
  ∑ j : Fin (n+1), c j * (t^(n-j) / (Nat.factorial (n-j):F))

theorem coeff_exp_product (c : ℕ → F) (t : F) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk c * PowerSeries.rescale t (PowerSeries.exp F)) =
      dividedConvolution c t n := by
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, map_div₀, map_one, map_natCast]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [dividedConvolution, div_eq_mul_inv, one_mul]

/-- The all-index finite Taylor identity. Its right side is
`Σ_{j≤n} S_j(r) (z-r)^(n-j)/(n-j)!`. -/
theorem dividedConvolution_translate (c : ℕ → F) (r z : F) (n : ℕ) :
    dividedConvolution c z n = dividedConvolution (dividedConvolution c r) (z-r) n := by
  have he : PowerSeries.mk (dividedConvolution c r) =
      PowerSeries.mk c * PowerSeries.rescale r (PowerSeries.exp F) := by
    ext i
    simp only [PowerSeries.coeff_mk, coeff_exp_product]
  rw [← coeff_exp_product, ← coeff_exp_product, he, mul_assoc,
    PowerSeries.exp_mul_exp_eq_exp_add]
  rw [show r+(z-r)=z by ring]

section Regularity
variable {k : Type*} [Field k] [Algebra k F]

omit [CharZero F] in
/-- Multiplying the negative part by `p³` removes its only potentially singular factor `f`. -/
theorem cube_mul_negativePart_mem (D : Subalgebra k F) (f p h : F)
    (hp : p ∈ D) (hh : h ∈ D) (hpf : p^3*f ∈ D)
    {q : F} (hq : q ∈ negativePart (k:=k) f p h) : p^3*q ∈ D := by
  have hBD : Algebra.adjoin k ({p,h}:Set F) ≤ D := Algebra.adjoin_le (by
    intro x hx
    rcases (show x=p ∨ x=h by simpa using hx) with rfl | rfl
    · exact hp
    · exact hh)
  rcases hq with ⟨b,hb,c,hc,rfl⟩
  rw [mul_add, ← mul_assoc]
  exact D.add_mem (D.mul_mem (D.pow_mem hp 3) (hBD hb)) (D.mul_mem hpf (hBD hc))

/-- Taylor propagation of regularity to every member of the family. -/
theorem cube_mul_convolution_mem (D : Subalgebra k F) (f p h t : F)
    (hp : p ∈ D) (hh : h ∈ D) (hpf : p^3*f ∈ D) (ht : t-f*h ∈ D)
    (c : ℕ → F) (hc : ∀ n, dividedConvolution c (f*h) n ∈ negativePart (k:=k) f p h)
    (n : ℕ) : p^3*dividedConvolution c t n ∈ D := by
  rw [dividedConvolution_translate c (f*h) t n, dividedConvolution, Finset.mul_sum]
  apply D.sum_mem
  intro j _
  have hfac : ((Nat.factorial (n-j):F)⁻¹) ∈ D := by
    convert D.algebraMap_mem ((Nat.factorial (n-j):k)⁻¹) using 1
    simp only [map_inv₀, map_natCast]
  rw [← mul_assoc, div_eq_mul_inv]
  exact D.mul_mem (cube_mul_negativePart_mem D f p h hp hh hpf (hc j))
    (D.mul_mem (D.pow_mem ht _) hfac)

omit [CharZero F] in
/-- Convolutions stay in any coefficient subalgebra containing the parameter. -/
theorem dividedConvolution_mem (D : Subalgebra k F) (c : ℕ → F) (hc : ∀ n, c n ∈ D)
    (t : F) (ht : t ∈ D) (n : ℕ) : dividedConvolution c t n ∈ D := by
  apply D.sum_mem
  intro j _
  have hfac : ((Nat.factorial (n-j):F)⁻¹) ∈ D := by
    convert D.algebraMap_mem ((Nat.factorial (n-j):k)⁻¹) using 1
    simp only [map_inv₀, map_natCast]
  rw [div_eq_mul_inv]
  exact D.mul_mem (hc j) (D.mul_mem (D.pow_mem ht _) hfac)

/-- The universal regular family after field modification. `FamilyConcrete`
proves the four regularity hypotheses in the localization at 1+x⁷y. -/
theorem exists_regular_family (D : Subalgebra k F) (f g h t : F)
    (hgh : g*h=1) (hp : f^2-g^3 ∈ D) (hh : h ∈ D)
    (hpf : (f^2-g^3)^3*f ∈ D) (ht : t-f*h ∈ D) :
    ∃ c : ℕ → F, c 0=1 ∧ (∀ n, c n ∈ Algebra.adjoin k {f,g}) ∧
      ∀ n, (f^2-g^3)^3*dividedConvolution c t n ∈ D := by
  rcases exists_kuroda_coefficients (k:=k) f g h hgh with ⟨c,hc0,hcR,hcN⟩
  exact ⟨c,hc0,hcR,fun n => cube_mul_convolution_mem D f (f^2-g^3) h t hp hh hpf ht c hcN n⟩

end Regularity

#print axioms dividedConvolution_translate
#print axioms exists_regular_family

end Hilbert14.Family
