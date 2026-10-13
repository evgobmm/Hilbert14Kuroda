import Hilbert14.Definitions
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Polynomial substitutions and inverse automorphisms of k[x,y,z][1/x]. -/

namespace Hilbert14
noncomputable section

variable (k : Type*) [Field k]

/-- Simultaneous substitution of the three polynomial coordinates. -/
def polyHom {T : Type*} [CommRing T] [Algebra k T] (u v w : T) : Poly k →ₐ[k] T :=
  Polynomial.eval₂AlgHom (MvPolynomial.aeval ![u, v]) w (fun _ => Commute.all _ _)

@[simp] theorem polyHom_x {T : Type*} [CommRing T] [Algebra k T] (u v w : T) :
    polyHom k u v w (x k) = u := by simp [polyHom, x]

@[simp] theorem polyHom_y {T : Type*} [CommRing T] [Algebra k T] (u v w : T) :
    polyHom k u v w (y k) = v := by simp [polyHom, y]

@[simp] theorem polyHom_z {T : Type*} [CommRing T] [Algebra k T] (u v w : T) :
    polyHom k u v w (z k) = w := by simp [polyHom, z]

theorem polyHom_ext {T : Type*} [CommRing T] [Algebra k T]
    {f g : Poly k →ₐ[k] T} (hx : f (x k) = g (x k))
    (hy : f (y k) = g (y k)) (hz : f (z k) = g (z k)) : f = g := by
  apply Polynomial.algHom_ext'
  · apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · exact hx
    · exact hy
  · exact hz

theorem x_ne_zero : x k ≠ 0 := by
  simp [x, MvPolynomial.X_ne_zero]

abbrev Laurent := Localization.Away (x k)

def intoLaurent : Poly k →ₐ[k] Laurent k := IsScalarTower.toAlgHom k (Poly k) (Laurent k)
def lx : Laurent k := intoLaurent k (x k)
def ly : Laurent k := intoLaurent k (y k)
def lz : Laurent k := intoLaurent k (z k)
def li : Laurent k := IsLocalization.Away.invSelf (x k)

@[simp] theorem lx_mul_li : lx k * li k = 1 := IsLocalization.Away.mul_invSelf (x k)
@[simp] theorem li_mul_lx : li k * lx k = 1 := by rw [mul_comm, lx_mul_li]

theorem li_isUnit : IsUnit (li k) := isUnit_iff_exists_inv.mpr ⟨lx k, li_mul_lx k⟩

def thetaPoly : Poly k →ₐ[k] Laurent k := polyHom k (li k) (lx k ^ 5 * ly k) (lz k + li k)
def inversePoly : Poly k →ₐ[k] Laurent k := polyHom k (li k) (lx k ^ 5 * ly k) (lz k - lx k)

def thetaLaurent : Laurent k →ₐ[k] Laurent k :=
  IsLocalization.Away.liftAlgHom (x k) (show IsUnit (thetaPoly k (x k)) by
    simpa [thetaPoly] using li_isUnit k)

def inverseLaurent : Laurent k →ₐ[k] Laurent k :=
  IsLocalization.Away.liftAlgHom (x k) (show IsUnit (inversePoly k (x k)) by
    simpa [inversePoly] using li_isUnit k)

@[simp] theorem thetaLaurent_embed (p : Poly k) :
    thetaLaurent k (intoLaurent k p) = thetaPoly k p := by
  exact IsLocalization.Away.lift_eq (x k)
    (show IsUnit (thetaPoly k (x k)) by simpa [thetaPoly] using li_isUnit k) p

@[simp] theorem inverseLaurent_embed (p : Poly k) :
    inverseLaurent k (intoLaurent k p) = inversePoly k p := by
  exact IsLocalization.Away.lift_eq (x k)
    (show IsUnit (inversePoly k (x k)) by simpa [inversePoly] using li_isUnit k) p

@[simp] theorem thetaLaurent_x : thetaLaurent k (lx k) = li k := by
  simp [lx, thetaPoly]
@[simp] theorem thetaLaurent_y : thetaLaurent k (ly k) = lx k ^ 5 * ly k := by
  simp [ly, thetaPoly]
@[simp] theorem thetaLaurent_z : thetaLaurent k (lz k) = lz k + li k := by
  simp [lz, thetaPoly]
@[simp] theorem inverseLaurent_x : inverseLaurent k (lx k) = li k := by
  simp [lx, inversePoly]
@[simp] theorem inverseLaurent_y : inverseLaurent k (ly k) = lx k ^ 5 * ly k := by
  simp [ly, inversePoly]
@[simp] theorem inverseLaurent_z : inverseLaurent k (lz k) = lz k - lx k := by
  simp [lz, inversePoly]

theorem map_li {f : Laurent k →ₐ[k] Laurent k} (hf : f (lx k) = li k) : f (li k) = lx k := by
  have h := congrArg f (lx_mul_li k)
  rw [map_mul, map_one, hf] at h
  calc f (li k) = (lx k * li k) * f (li k) := by rw [lx_mul_li, one_mul]
       _ = lx k := by rw [mul_assoc, h, mul_one]

@[simp] theorem thetaLaurent_i : thetaLaurent k (li k) = lx k := map_li k (thetaLaurent_x k)
@[simp] theorem inverseLaurent_i : inverseLaurent k (li k) = lx k := map_li k (inverseLaurent_x k)

theorem theta_inverse : (thetaLaurent k).comp (inverseLaurent k) = AlgHom.id k (Laurent k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x k))
  apply polyHom_ext k
  · change thetaLaurent k (inverseLaurent k (lx k)) = lx k
    simp
  · change thetaLaurent k (inverseLaurent k (ly k)) = ly k
    simp only [inverseLaurent_y, map_mul, map_pow, thetaLaurent_x, thetaLaurent_y]
    rw [← mul_assoc, ← mul_pow, li_mul_lx, one_pow, one_mul]
  · change thetaLaurent k (inverseLaurent k (lz k)) = lz k
    simp

theorem inverse_theta : (inverseLaurent k).comp (thetaLaurent k) = AlgHom.id k (Laurent k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x k))
  apply polyHom_ext k
  · change inverseLaurent k (thetaLaurent k (lx k)) = lx k
    simp
  · change inverseLaurent k (thetaLaurent k (ly k)) = ly k
    simp only [thetaLaurent_y, map_mul, map_pow, inverseLaurent_x, inverseLaurent_y]
    rw [← mul_assoc, ← mul_pow, li_mul_lx, one_pow, one_mul]
  · change inverseLaurent k (thetaLaurent k (lz k)) = lz k
    simp

/-- Kuroda's automorphism of the polynomial ring with x inverted. -/
def thetaEquiv : Laurent k ≃ₐ[k] Laurent k :=
  AlgEquiv.ofAlgHom (thetaLaurent k) (inverseLaurent k) (theta_inverse k) (inverse_theta k)

end
end Hilbert14
