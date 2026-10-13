import Hilbert14.Lemmas.Coordinates

/-! Extension of the coordinate automorphism to k(x,y,z),
with injectivity and the images of the three variables. -/

namespace Hilbert14
noncomputable section
variable (k : Type*) [Field k]

theorem embed_x_ne_zero : embed k (x k) ≠ 0 := by
  exact fun h => x_ne_zero k (embed_injective k (by simpa using h))

def laurentToRat : Laurent k →ₐ[k] Rat k :=
  IsLocalization.Away.liftAlgHom (x k)
    (show IsUnit (embed k (x k)) from isUnit_iff_ne_zero.mpr (embed_x_ne_zero k))

@[simp] theorem laurentToRat_embed (p : Poly k) :
    laurentToRat k (intoLaurent k p) = embed k p := by
  exact IsLocalization.Away.lift_eq (x k)
    (show IsUnit (embed k (x k)) from isUnit_iff_ne_zero.mpr (embed_x_ne_zero k)) p

theorem intoLaurent_injective : Function.Injective (intoLaurent k) := by
  intro p q h
  apply embed_injective k
  simpa using congrArg (laurentToRat k) h

theorem laurentToRat_injective : Function.Injective (laurentToRat k) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (x k))
    (laurentToRat k).toRingHom).mpr
  intro p q
  change intoLaurent k p = intoLaurent k q ↔
    laurentToRat k (intoLaurent k p) = laurentToRat k (intoLaurent k q)
  simp only [laurentToRat_embed, (intoLaurent_injective k).eq_iff, (embed_injective k).eq_iff]

def transformedPoly (e : Laurent k ≃ₐ[k] Laurent k) : Poly k →ₐ[k] Rat k :=
  (laurentToRat k).comp (e.toAlgHom.comp (intoLaurent k))

theorem transformedPoly_injective (e : Laurent k ≃ₐ[k] Laurent k) :
    Function.Injective (transformedPoly k e) :=
  (laurentToRat_injective k).comp (e.injective.comp (intoLaurent_injective k))

def extendLaurent (e : Laurent k ≃ₐ[k] Laurent k) : Rat k →ₐ[k] Rat k :=
  IsFractionRing.liftAlgHom (transformedPoly_injective k e)

@[simp] theorem extendLaurent_embed (e : Laurent k ≃ₐ[k] Laurent k) (p : Poly k) :
    extendLaurent k e (embed k p) = laurentToRat k (e (intoLaurent k p)) := by
  exact IsFractionRing.lift_algebraMap (transformedPoly_injective k e) p

theorem extendLaurent_commutes (e : Laurent k ≃ₐ[k] Laurent k) (p : Laurent k) :
    extendLaurent k e (laurentToRat k p) = laurentToRat k (e p) := by
  have h : (extendLaurent k e).comp (laurentToRat k) = (laurentToRat k).comp e.toAlgHom := by
    apply IsLocalization.algHom_ext (Submonoid.powers (x k))
    apply AlgHom.ext
    intro q
    change extendLaurent k e (laurentToRat k (intoLaurent k q)) =
      laurentToRat k (e (intoLaurent k q))
    rw [laurentToRat_embed, extendLaurent_embed]
  exact DFunLike.congr_fun h p

theorem extendLaurent_comp_symm (e : Laurent k ≃ₐ[k] Laurent k) :
    (extendLaurent k e).comp (extendLaurent k e.symm) = AlgHom.id k (Rat k) := by
  apply IsLocalization.algHom_ext (nonZeroDivisors (Poly k))
  apply AlgHom.ext
  intro p
  change extendLaurent k e (extendLaurent k e.symm (embed k p)) = embed k p
  rw [extendLaurent_embed, extendLaurent_commutes, e.apply_symm_apply, laurentToRat_embed]

/-- The actual rational-function-field automorphism, with its proved inverse. -/
def theta : Rat k ≃ₐ[k] Rat k :=
  AlgEquiv.ofAlgHom (extendLaurent k (thetaEquiv k)) (extendLaurent k (thetaEquiv k).symm)
    (extendLaurent_comp_symm k (thetaEquiv k)) (extendLaurent_comp_symm k (thetaEquiv k).symm)

@[simp] theorem laurentToRat_li : laurentToRat k (li k) = (embed k (x k))⁻¹ := by
  have h := congrArg (laurentToRat k) (li_mul_lx k)
  have hm : laurentToRat k (li k) * embed k (x k) = 1 := by simpa [lx] using h
  calc laurentToRat k (li k) =
      (laurentToRat k (li k) * embed k (x k)) * (embed k (x k))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (embed_x_ne_zero k), mul_one]
    _ = (embed k (x k))⁻¹ := by rw [hm, one_mul]

@[simp] theorem theta_x : theta k (embed k (x k)) = (embed k (x k))⁻¹ := by
  change extendLaurent k (thetaEquiv k) (embed k (x k)) = _
  rw [extendLaurent_embed]
  change laurentToRat k (thetaLaurent k (lx k)) = _
  simp

@[simp] theorem theta_y : theta k (embed k (y k)) = embed k (x k)^5 * embed k (y k) := by
  change extendLaurent k (thetaEquiv k) (embed k (y k)) = _
  rw [extendLaurent_embed]
  change laurentToRat k (thetaLaurent k (ly k)) = _
  rw [thetaLaurent_y, map_mul, map_pow]
  simp only [lx, ly, laurentToRat_embed]

@[simp] theorem theta_z : theta k (embed k (z k)) = embed k (z k) + (embed k (x k))⁻¹ := by
  change extendLaurent k (thetaEquiv k) (embed k (z k)) = _
  rw [extendLaurent_embed]
  change laurentToRat k (thetaLaurent k (lz k)) = _
  rw [thetaLaurent_z, map_add, laurentToRat_li]
  simp only [lz, laurentToRat_embed]

end
end Hilbert14
