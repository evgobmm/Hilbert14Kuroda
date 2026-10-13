import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic

/-! Universal algebraic normal forms for Kuroda's family construction. -/
namespace Hilbert14.Family

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Every polynomial expression in `p,t` has a constant-in-`t` part and a `t`-multiple.
No algebraic independence or uniqueness is needed. -/
theorem split_adjoin_pair (p t : F) {q : F} (hq : q ∈ Algebra.adjoin k {p, t}) :
    ∃ a ∈ Algebra.adjoin k {p}, ∃ b ∈ Algebra.adjoin k {p, t}, q = a + t * b := by
  let R := Algebra.adjoin k ({p} : Set F)
  let S := Algebra.adjoin k ({p, t} : Set F)
  have hRS : R ≤ S := Algebra.adjoin_mono (by intro x hx; simp only [Set.mem_singleton_iff] at hx; simp [hx])
  have ht : t ∈ S := Algebra.subset_adjoin (by simp)
  induction hq using Algebra.adjoin_induction with
  | mem x hx =>
    rcases (show x = p ∨ x = t by simpa using hx) with rfl | rfl
    · exact ⟨x, Algebra.subset_adjoin (by simp), 0, S.zero_mem, by simp⟩
    · exact ⟨0, R.zero_mem, 1, S.one_mem, by simp⟩
  | algebraMap r => exact ⟨algebraMap k F r, R.algebraMap_mem r, 0, S.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases hy with ⟨c, hc, d, hd, rfl⟩
    exact ⟨a + c, R.add_mem ha hc, b + d, S.add_mem hb hd, by ring⟩
  | mul x y _ _ hx hy =>
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases hy with ⟨c, hc, d, hd, rfl⟩
    exact ⟨a*c, R.mul_mem ha hc, a*d + b*c + t*b*d,
      S.add_mem (S.add_mem (S.mul_mem (hRS ha) hd) (S.mul_mem hb (hRS hc)))
        (S.mul_mem (S.mul_mem ht hb) hd), by ring⟩

/-- A submodule containing 1 and stable under the generators contains their algebra. -/
theorem adjoin_le_of_mul_stable (s : Set F) (M : Submodule k F)
    (h1 : (1 : F) ∈ M) (hs : ∀ a ∈ s, ∀ b ∈ M, a*b ∈ M) :
    (Algebra.adjoin k s).toSubmodule ≤ M := by
  intro a ha
  have h : ∀ b ∈ M, a*b ∈ M := by
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact hs a ha
    | algebraMap r => intro b hb; simpa only [Algebra.smul_def] using M.smul_mem r hb
    | add a b _ _ ha hb => intro c hc; simpa only [add_mul] using M.add_mem (ha c hc) (hb c hc)
    | mul a b _ _ ha hb => intro c hc; simpa only [mul_assoc] using ha (b*c) (hb c hc)
  simpa using h 1 h1

/-- Laurent expressions in `g` split into the nonnegative and nonpositive parts,
with arbitrary polynomial coefficients in `p`. -/
theorem laurent_split (p g h : F) (hgh : g*h = 1) {q : F}
    (hq : q ∈ Algebra.adjoin k {p, g, h}) :
    ∃ a ∈ Algebra.adjoin k {p, g}, ∃ b ∈ Algebra.adjoin k {p, h}, q = a+b := by
  let R := Algebra.adjoin k ({p, g} : Set F)
  let S := Algebra.adjoin k ({p, h} : Set F)
  let M := R.toSubmodule ⊔ S.toSubmodule
  have hpR : p ∈ R := Algebra.subset_adjoin (by simp)
  have hpS : p ∈ S := Algebra.subset_adjoin (by simp)
  have hgR : g ∈ R := Algebra.subset_adjoin (by simp)
  have hhS : h ∈ S := Algebra.subset_adjoin (by simp)
  have hp0R : Algebra.adjoin k ({p} : Set F) ≤ R := Algebra.adjoin_mono (by intro x hx; simp_all)
  have hp0S : Algebra.adjoin k ({p} : Set F) ≤ S := Algebra.adjoin_mono (by intro x hx; simp_all)
  have left (a : F) (ha : a ∈ R) : a ∈ M := Submodule.mem_sup_left ha
  have right (a : F) (ha : a ∈ S) : a ∈ M := Submodule.mem_sup_right ha
  have hgS (b : F) (hb : b ∈ S) : g*b ∈ M := by
    rcases split_adjoin_pair p h hb with ⟨a, ha, c, hc, rfl⟩
    have he : g*(a+h*c) = g*a+c := by rw [mul_add, ← mul_assoc g h, hgh, one_mul]
    rw [he]
    exact M.add_mem (left _ (R.mul_mem hgR (hp0R ha))) (right _ hc)
  have hhR (a : F) (ha : a ∈ R) : h*a ∈ M := by
    rcases split_adjoin_pair p g ha with ⟨b, hb, c, hc, rfl⟩
    have he : h*(b+g*c) = h*b+c := by rw [mul_add, ← mul_assoc h g, mul_comm h g, hgh, one_mul]
    rw [he]
    exact M.add_mem (right _ (S.mul_mem hhS (hp0S hb))) (left _ hc)
  have hqM : q ∈ M := adjoin_le_of_mul_stable {p,g,h} M (left _ R.one_mem) (by
    intro a ha b hb
    rcases Submodule.mem_sup.mp hb with ⟨u, hu, v, hv, rfl⟩
    rcases (show a=p ∨ a=g ∨ a=h by simpa using ha) with rfl | rfl | rfl
    · simpa only [mul_add] using M.add_mem (left _ (R.mul_mem hpR hu)) (right _ (S.mul_mem hpS hv))
    · simpa only [mul_add] using M.add_mem (left _ (R.mul_mem hgR hu)) (hgS v hv)
    · simpa only [mul_add] using M.add_mem (hhR u hu) (right _ (S.mul_mem hhS hv))) hq
  rcases Submodule.mem_sup.mp hqM with ⟨a, ha, b, hb, he⟩
  exact ⟨a, ha, b, hb, he.symm⟩

/-- A quadratic element only needs powers zero and one over its coefficient algebra. -/
theorem quadratic_reduce (T : Subalgebra k F) (f : F) (hf : f^2 ∈ T)
    (s : Set F) (hs : ∀ x ∈ s, x ∈ T ∨ x = f) {q : F}
    (hq : q ∈ Algebra.adjoin k s) :
    ∃ a ∈ T, ∃ b ∈ T, q = a+f*b := by
  induction hq using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hs x hx with h | rfl
    · exact ⟨x, h, 0, T.zero_mem, by simp⟩
    · exact ⟨0, T.zero_mem, 1, T.one_mem, by simp⟩
  | algebraMap r => exact ⟨algebraMap k F r, T.algebraMap_mem r, 0, T.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases hy with ⟨c, hc, d, hd, rfl⟩
    exact ⟨a+c, T.add_mem ha hc, b+d, T.add_mem hb hd, by ring⟩
  | mul x y _ _ hx hy =>
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases hy with ⟨c, hc, d, hd, rfl⟩
    exact ⟨a*c+f^2*b*d, T.add_mem (T.mul_mem ha hc) (T.mul_mem (T.mul_mem hf hb) hd),
      a*d+b*c, T.add_mem (T.mul_mem ha hd) (T.mul_mem hb hc), by ring⟩

/-- The full normal-form decomposition used by the universal Kuroda recurrence.
It holds for arbitrary elements of the three-generator algebra, not just bounded monomials. -/
theorem kuroda_decomposition (f g h : F) (hgh : g*h = 1) {q : F}
    (hq : q ∈ Algebra.adjoin k {f,g,h}) :
    ∃ a ∈ Algebra.adjoin k {f,g},
    ∃ b ∈ Algebra.adjoin k {f^2-g^3,h},
    ∃ c ∈ Algebra.adjoin k {f^2-g^3,h}, q = a + (b+f*c) := by
  let p := f^2-g^3
  let T := Algebra.adjoin k ({p,g,h} : Set F)
  let R := Algebra.adjoin k ({f,g} : Set F)
  have hfR : f ∈ R := Algebra.subset_adjoin (by simp)
  have hgR : g ∈ R := Algebra.subset_adjoin (by simp)
  have hpR : p ∈ R := R.sub_mem (R.pow_mem hfR 2) (R.pow_mem hgR 3)
  have hRT : Algebra.adjoin k ({p,g} : Set F) ≤ R := Algebra.adjoin_le (by
    intro x hx
    rcases (show x=p ∨ x=g by simpa using hx) with rfl | rfl
    · exact hpR
    · exact hgR)
  have hgT : g ∈ T := Algebra.subset_adjoin (by simp)
  have hpT : p ∈ T := Algebra.subset_adjoin (by simp)
  have hf2 : f^2 ∈ T := by
    have he : f^2 = g^3+p := by dsimp [p]; ring
    rw [he]
    exact T.add_mem (T.pow_mem hgT 3) hpT
  rcases quadratic_reduce T f hf2 {f,g,h} (by
    intro x hx
    rcases (show x=f ∨ x=g ∨ x=h by simpa using hx) with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl hgT
    · exact Or.inl (Algebra.subset_adjoin (by simp))) hq with ⟨a, ha, b, hb, he⟩
  rcases laurent_split p g h hgh ha with ⟨a₀, ha₀, a₁, ha₁, rfl⟩
  rcases laurent_split p g h hgh hb with ⟨b₀, hb₀, b₁, hb₁, rfl⟩
  exact ⟨a₀+f*b₀, R.add_mem (hRT ha₀) (R.mul_mem hfR (hRT hb₀)),
    a₁, ha₁, b₁, hb₁, by rw [he]; ring⟩

/-- The negative part `k[p,h] + f k[p,h]`, as a vector subspace. -/
def negativePart (f p h : F) : Submodule k F where
  carrier := {q | ∃ b ∈ Algebra.adjoin k {p,h}, ∃ c ∈ Algebra.adjoin k {p,h}, q=b+f*c}
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  add_mem' := by
    rintro x y ⟨b,hb,c,hc,rfl⟩ ⟨d,hd,e,he,rfl⟩
    exact ⟨b+d, add_mem hb hd, c+e, add_mem hc he, by ring⟩
  smul_mem' := by
    rintro r x ⟨b,hb,c,hc,rfl⟩
    exact ⟨r • b, Subalgebra.smul_mem _ hb r, r • c, Subalgebra.smul_mem _ hc r,
      by simp only [Algebra.smul_def]; ring⟩

theorem one_mem_negativePart (f p h : F) : (1:F) ∈ negativePart (k:=k) f p h :=
  ⟨1, one_mem _, 0, zero_mem _, by simp⟩

/-- A chosen correction cancels the positive component of an arbitrary Laurent expression. -/
noncomputable def correction (R S : Subalgebra k F) (N : Submodule k F)
    (hsplit : ∀ q ∈ S, ∃ a ∈ R, ∃ b ∈ N, q=a+b) (q : F) : F := by
  classical
  exact if hq : q ∈ S then -Classical.choose (hsplit q hq) else 0

theorem correction_mem (R S : Subalgebra k F) (N : Submodule k F)
    (hsplit : ∀ q ∈ S, ∃ a ∈ R, ∃ b ∈ N, q=a+b) (q : F) :
    correction R S N hsplit q ∈ R := by
  unfold correction
  split_ifs with hq
  · exact R.neg_mem (Classical.choose_spec (hsplit q hq)).1
  · exact R.zero_mem

theorem add_correction_mem (R S : Subalgebra k F) (N : Submodule k F)
    (hsplit : ∀ q ∈ S, ∃ a ∈ R, ∃ b ∈ N, q=a+b) (q : F) (hq : q ∈ S) :
    q + correction R S N hsplit q ∈ N := by
  rw [correction, dite_eq_left hq]
  rcases (Classical.choose_spec (hsplit q hq)).2 with ⟨b,hb,he⟩
  have he' : q + -Classical.choose (hsplit q hq) = b := by
    calc
      _ = (Classical.choose (hsplit q hq) + b) + -Classical.choose (hsplit q hq) :=
        congrArg (fun x => x + -Classical.choose (hsplit q hq)) he
      _ = b := by ring
  exact he'.symm ▸ hb

/-- The recursive coefficients are defined for every natural index. The weight sequence
will be `r^j/j!`; the proof works for any weights in the ambient algebra with weight zero 1. -/
noncomputable def recurrence (R S : Subalgebra k F) (N : Submodule k F)
    (hsplit : ∀ q ∈ S, ∃ a ∈ R, ∃ b ∈ N, q=a+b) (w : ℕ → F) (n : ℕ) : F :=
  Nat.strongRecOn n fun n prev =>
    if n=0 then 1 else correction R S N hsplit (∑ j : Fin n, prev j j.isLt * w (n-j))

theorem recurrence_eq (R S : Subalgebra k F) (N : Submodule k F)
    (hsplit : ∀ q ∈ S, ∃ a ∈ R, ∃ b ∈ N, q=a+b) (w : ℕ → F) (n : ℕ) :
    recurrence R S N hsplit w n = if n=0 then 1 else
      correction R S N hsplit (∑ j : Fin n, recurrence R S N hsplit w j * w (n-j)) := by
  unfold recurrence
  rw [Nat.strongRecOn_eq]

theorem recurrence_zero (R S : Subalgebra k F) (N : Submodule k F)
    (hsplit : ∀ q ∈ S, ∃ a ∈ R, ∃ b ∈ N, q=a+b) (w : ℕ → F) :
    recurrence R S N hsplit w 0 = 1 := by rw [recurrence_eq]; simp

theorem recurrence_mem (R S : Subalgebra k F) (N : Submodule k F)
    (hsplit : ∀ q ∈ S, ∃ a ∈ R, ∃ b ∈ N, q=a+b) (w : ℕ → F) (n : ℕ) :
    recurrence R S N hsplit w n ∈ R := by
  rw [recurrence_eq]
  split_ifs
  · exact R.one_mem
  · exact correction_mem R S N hsplit _

/-- Universal cancellation: every normalized convolution lies in the negative part. -/
theorem recurrence_convolution_mem (R S : Subalgebra k F) (N : Submodule k F)
    (hRS : R ≤ S) (h1 : (1:F) ∈ N)
    (hsplit : ∀ q ∈ S, ∃ a ∈ R, ∃ b ∈ N, q=a+b)
    (w : ℕ → F) (hw : ∀ n, w n ∈ S) (hw0 : w 0 = 1) (n : ℕ) :
    (∑ j : Fin (n+1), recurrence R S N hsplit w j * w (n-j)) ∈ N := by
  by_cases hn : n=0
  · subst n
    simpa [recurrence_zero, hw0] using h1
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, hw0, mul_one]
    rw [recurrence_eq R S N hsplit w n, ite_eq_right hn]
    apply add_correction_mem
    exact S.sum_mem (fun j _ => S.mul_mem (hRS (recurrence_mem R S N hsplit w j)) (hw (n-j)))

/-- Universal coefficients from Kuroda's Lemma 2.2, with the decomposition proved above.
The specialization to characteristic zero is needed later for the leading coefficient. -/
theorem exists_kuroda_coefficients (f g h : F) (hgh : g*h=1) :
    ∃ c : ℕ → F, c 0=1 ∧
      (∀ n, c n ∈ Algebra.adjoin k {f,g}) ∧
      ∀ n, (∑ j : Fin (n+1), c j * ((f*h)^(n-j) / (Nat.factorial (n-j):F))) ∈
        negativePart (k:=k) f (f^2-g^3) h := by
  let R := Algebra.adjoin k ({f,g} : Set F)
  let S := Algebra.adjoin k ({f,g,h} : Set F)
  let N := negativePart (k:=k) f (f^2-g^3) h
  have hsplit : ∀ q ∈ S, ∃ a ∈ R, ∃ b ∈ N, q=a+b := by
    intro q hq
    rcases kuroda_decomposition f g h hgh hq with ⟨a,ha,b,hb,c,hc,he⟩
    exact ⟨a,ha,b+f*c,⟨b,hb,c,hc,rfl⟩,he⟩
  let w : ℕ → F := fun n => algebraMap k F ((Nat.factorial n : k)⁻¹) * (f*h)^n
  have hw : ∀ n, w n ∈ S := by
    intro n
    exact S.mul_mem (S.algebraMap_mem _) (S.pow_mem
      (S.mul_mem (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp))) n)
  have hw0 : w 0=1 := by simp [w]
  have hRS : R ≤ S := Algebra.adjoin_mono (by
    intro x hx
    rcases (show x=f ∨ x=g by simpa using hx) with rfl | rfl <;> simp)
  refine ⟨recurrence R S N hsplit w, recurrence_zero R S N hsplit w,
    recurrence_mem R S N hsplit w, ?_⟩
  intro n
  have hn := recurrence_convolution_mem R S N hRS (one_mem_negativePart _ _ _) hsplit w hw hw0 n
  simpa only [w, map_inv₀, map_natCast, div_eq_mul_inv, mul_comm ((f*h)^_)] using hn

#print axioms kuroda_decomposition
#print axioms exists_kuroda_coefficients
#print axioms recurrence_convolution_mem

end Hilbert14.Family
