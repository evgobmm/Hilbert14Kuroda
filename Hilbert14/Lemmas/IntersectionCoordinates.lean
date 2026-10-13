import Hilbert14.Lemmas.Intersection
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring

/-! The triangular coordinate change and the swap of x and y−x+x². -/

namespace Hilbert14

variable (k : Type*) [Field k]

private noncomputable def shearForward : Base k →ₐ[k] Base k :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else
    MvPolynomial.X 1 - MvPolynomial.X 0 + MvPolynomial.X 0 ^ 2)

private noncomputable def shearBackward : Base k →ₐ[k] Base k :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else
    MvPolynomial.X 1 + MvPolynomial.X 0 - MvPolynomial.X 0 ^ 2)

/-- The triangular change (U,V) ↦ (x,y-x+x²). -/
noncomputable def baseShear : Base k ≃ₐ[k] Base k :=
  AlgEquiv.ofAlgHom (shearForward k) (shearBackward k)
    (by
      ext i
      fin_cases i <;> simp [shearForward, shearBackward]
      ring)
    (by
      ext i
      fin_cases i <;> simp [shearForward, shearBackward]
      ring)

noncomputable def shear : Poly k ≃ₐ[k] Poly k :=
  Polynomial.mapAlgEquiv (baseShear k)

@[simp] theorem baseShear_X_zero : baseShear k (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  change shearForward k (MvPolynomial.X 0) = _
  simp [shearForward]

@[simp] theorem baseShear_X_one : baseShear k (MvPolynomial.X 1) =
    MvPolynomial.X 1 - MvPolynomial.X 0 + MvPolynomial.X 0 ^ 2 := by
  change shearForward k (MvPolynomial.X 1) = _
  simp [shearForward]

@[simp] theorem baseShear_symm_X_zero : (baseShear k).symm (MvPolynomial.X 0) =
    MvPolynomial.X 0 := by
  change shearBackward k (MvPolynomial.X 0) = _
  simp [shearBackward]

@[simp] theorem baseShear_symm_X_one : (baseShear k).symm (MvPolynomial.X 1) =
    MvPolynomial.X 1 + MvPolynomial.X 0 - MvPolynomial.X 0 ^ 2 := by
  change shearBackward k (MvPolynomial.X 1) = _
  simp [shearBackward]

@[simp] theorem shear_x : shear k (x k) = x k := by
  simp [shear, x, Polynomial.coe_mapAlgEquiv]

@[simp] theorem shear_y : shear k (y k) = v k := by
  simp [shear, x, y, v, Polynomial.coe_mapAlgEquiv]

@[simp] theorem shear_z : shear k (z k) = z k := by
  simp [shear, z, Polynomial.coe_mapAlgEquiv]

/-- Exchange of the two original independent polynomial coordinates. -/
noncomputable def coordinateSwap : Poly k ≃ₐ[k] Poly k :=
  Polynomial.mapAlgEquiv (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1))

@[simp] theorem coordinateSwap_x : coordinateSwap k (x k) = y k := by
  simp [coordinateSwap, x, y, Polynomial.coe_mapAlgEquiv, MvPolynomial.renameEquiv]

@[simp] theorem coordinateSwap_y : coordinateSwap k (y k) = x k := by
  simp [coordinateSwap, x, y, Polynomial.coe_mapAlgEquiv, MvPolynomial.renameEquiv]

@[simp] theorem coordinateSwap_z : coordinateSwap k (z k) = z k := by
  simp [coordinateSwap, z, Polynomial.coe_mapAlgEquiv]

/-- Kuroda's polynomial symmetry, exchanging x and v=y-x+x². -/
noncomputable def tau : Poly k ≃ₐ[k] Poly k :=
  ((shear k).symm.trans (coordinateSwap k)).trans (shear k)

@[simp] theorem tau_x : tau k (x k) = v k := by
  have hx : (shear k).symm (x k) = x k := (AlgEquiv.symm_apply_eq _).mpr (shear_x k).symm
  simp [tau, hx]

@[simp] theorem tau_v : tau k (v k) = x k := by
  have hv : (shear k).symm (v k) = y k := (AlgEquiv.symm_apply_eq _).mpr (shear_y k).symm
  simp [tau, hv]

@[simp] theorem tau_z : tau k (z k) = z k := by
  have hz : (shear k).symm (z k) = z k := (AlgEquiv.symm_apply_eq _).mpr (shear_z k).symm
  simp [tau, hz]

#print axioms baseShear
#print axioms tau_x
#print axioms tau_v
#print axioms tau_z

end Hilbert14
