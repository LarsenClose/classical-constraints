/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/PolymorphismCore.lean — Polymorphisms and polymorphism clones.

STATUS: 0 sorry, Classical.choice allowed (Side B).
-/

import ClassicalConstraints.Chain4_CSP.CSPInstanceCore
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Operations
-- ════════════════════════════════════════════════════════════

/-- An operation of arity k on a domain D. -/
def Operation (D : Type) (k : Nat) := (Fin k → D) → D

/-- A projection operation: returns the i-th argument. -/
def projection (D : Type) (k : Nat) (i : Fin k) : Operation D k :=
  fun args => args i

-- ════════════════════════════════════════════════════════════
-- Section 2: Preserving relations and polymorphisms
-- ════════════════════════════════════════════════════════════

/-- An operation f of arity k preserves a relation R of arity r if:
    given k tuples t_1,...,t_k all in R, applying f coordinatewise
    produces a tuple also in R.

    Input: rows : Fin k → Fin r → D where each ROW is in R.
    Output: the tuple (fun j => f (fun i => rows i j)) is in R. -/
def preservesRelation {D : Type} {deceq : DecidableEq D}
    {r : Nat} (R : FinRelation D deceq r) {k : Nat}
    (f : Operation D k) : Prop :=
  ∀ (rows : Fin k → Fin r → D),
    (∀ i : Fin k, R.mem (rows i) = true) →
    R.mem (fun j => f (fun i => rows i j)) = true

/-- A polymorphism of a constraint language: an operation that
    preserves ALL relations in the language. -/
def isPolymorphism {dom : CSPDomain}
    (lang : ConstraintLanguage dom) {k : Nat}
    (f : Operation dom.D k) : Prop :=
  ∀ (rel_idx : Fin lang.rels.length),
    preservesRelation (lang.rels[rel_idx]).2 f

/-- The polymorphism clone of a constraint language at arity k:
    all k-ary operations that preserve every relation. -/
def PolClone (dom : CSPDomain) (lang : ConstraintLanguage dom)
    (k : Nat) : Set (Operation dom.D k) :=
  { f | isPolymorphism lang f }

-- ════════════════════════════════════════════════════════════
-- Section 3: Special operations
-- ════════════════════════════════════════════════════════════

/-- A Weak Near-Unanimity (WNU) operation of arity k. -/
structure WNU (D : Type) (k : Nat) where
  op : Operation D k
  idempotent : ∀ x : D, op (fun _ => x) = x
  wnu_property : ∀ (x y : D) (i j : Fin k),
    op (Function.update (fun _ => x) i y) =
    op (Function.update (fun _ => x) j y)

/-- A majority operation (arity 3):
    f(x,x,y) = f(x,y,x) = f(y,x,x) = x. -/
structure MajorityOp (D : Type) where
  op : Operation D 3
  majority : ∀ (x y : D),
    op ![x, x, y] = x ∧
    op ![x, y, x] = x ∧
    op ![y, x, x] = x

/-- A Mal'cev operation (arity 3):
    f(x,y,y) = x and f(x,x,y) = y. -/
structure MalcevOp (D : Type) where
  op : Operation D 3
  left_identity : ∀ (x y : D), op ![x, y, y] = x
  right_identity : ∀ (x y : D), op ![x, x, y] = y

-- ════════════════════════════════════════════════════════════
-- Section 4: Clone closure theorems
-- ════════════════════════════════════════════════════════════

/-- Projections preserve all relations. -/
theorem projection_is_polymorphism (dom : CSPDomain)
    (lang : ConstraintLanguage dom) (k : Nat) (i : Fin k) :
    isPolymorphism lang (projection dom.D k i) := by
  intro rel_idx rows hrows
  have : (fun j => projection dom.D k i (fun m => rows m j)) = rows i := by
    funext j; simp [projection]
  rw [this]; exact hrows i

/-- Composition preserves polymorphism. -/
theorem compose_polymorphisms (dom : CSPDomain)
    (lang : ConstraintLanguage dom) (j k : Nat)
    (f : Operation dom.D k) (gs : Fin k → Operation dom.D j)
    (hf : isPolymorphism lang f)
    (hgs : ∀ i, isPolymorphism lang (gs i)) :
    isPolymorphism lang (fun args => f (fun i => gs i args)) := by
  intro rel_idx rows hrows
  exact hf rel_idx (fun i col => gs i (fun row => rows row col))
    (fun i => hgs i rel_idx rows hrows)

-- ════════════════════════════════════════════════════════════
-- Section 5: WNU properties
-- ════════════════════════════════════════════════════════════

-- Helper: ![x,x,x] = fun _ => x for Fin 3.
private lemma fin3_const (D : Type) (x : D) :
    (![x, x, x] : Fin 3 → D) = fun _ => x := by
  ext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [Matrix.cons_val_zero]
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · simp [Matrix.cons_val_one]
    · have hk : k = (0 : Fin 1) := Fin.fin_one_eq_zero k
      subst hk
      simp

-- Helper: evaluate ![v0, v1, v2] at each position.
private lemma mat3_zero (D : Type) (v0 v1 v2 : D) : (![v0, v1, v2] : Fin 3 → D) 0 = v0 := by
  simp [Matrix.cons_val_zero]
private lemma mat3_one (D : Type) (v0 v1 v2 : D) : (![v0, v1, v2] : Fin 3 → D) 1 = v1 := by
  simp [Matrix.cons_val_one]
private lemma mat3_two (D : Type) (v0 v1 v2 : D) : (![v0, v1, v2] : Fin 3 → D) 2 = v2 := by
  simp

-- Helper: Function.update f i y j = if j = i then y else f j, for Fin 3.
private lemma update_fin3_val (D : Type) (x y : D) (i j : Fin 3) :
    Function.update (fun _ => x) i y j = if j = i then y else x := by
  simp [Function.update]

-- Rewrite helpers for update at positions 0, 1, 2 of Fin 3.
private lemma fin3_update0 (D : Type) (x y : D) :
    Function.update (fun _ => x) (0 : Fin 3) y = ![y, x, x] := by
  ext i
  rw [update_fin3_val]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · simp
    · have hk : k = (0 : Fin 1) := Fin.fin_one_eq_zero k
      subst hk; simp [mat3_two, Fin.ext_iff]

private lemma fin3_update1 (D : Type) (x y : D) :
    Function.update (fun _ => x) (1 : Fin 3) y = ![x, y, x] := by
  ext i
  rw [update_fin3_val]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [Fin.ext_iff]
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · simp
    · have hk : k = (0 : Fin 1) := Fin.fin_one_eq_zero k
      subst hk; simp [mat3_two, Fin.ext_iff]

private lemma fin3_update2 (D : Type) (x y : D) :
    Function.update (fun _ => x) (2 : Fin 3) y = ![x, x, y] := by
  ext i
  rw [update_fin3_val]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [Fin.ext_iff]
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · simp [Fin.ext_iff]
    · have hk : k = (0 : Fin 1) := Fin.fin_one_eq_zero k
      subst hk; simp [mat3_two]

-- Helper needed before majority_is_wnu.
private lemma majority_single_change_val_aux (D : Type) (m : MajorityOp D) (x y : D)
    (i : Fin 3) : m.op (Function.update (fun _ => x) i y) = x := by
  have ha := m.majority x y
  -- i is a Fin 3 element; use decidability to case split.
  -- Method: rewrite i using the three update lemmas.
  -- We use the fact that every Fin 3 element is 0, 1, or 2.
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · -- i = 0
    rw [fin3_update0]; exact ha.2.2
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · -- i = 1 = Fin.succ 0
      rw [show (Fin.succ (0 : Fin 2) : Fin 3) = (1 : Fin 3) from rfl]
      rw [fin3_update1]; exact ha.2.1
    · -- i = 2 = Fin.succ (Fin.succ 0)
      -- k must be Fin 1 with k = 0, so k.succ = 1 : Fin 2, and j.succ = 2 : Fin 3.
      -- Need i = (2 : Fin 3).
      have hk : k = (0 : Fin 1) := Fin.fin_one_eq_zero k
      subst hk
      -- Now j = Fin.succ 0 : Fin 2, which is 1 : Fin 2? No: j : Fin 2, j = Fin.succ 0.
      -- And i = Fin.succ j = Fin.succ (Fin.succ 0) : Fin 3.
      -- Fin.succ (Fin.succ 0) : Fin 3 has val = 2.
      show m.op (Function.update (fun _ => x) (Fin.succ (Fin.succ (0 : Fin 1))) y) = x
      rw [show (Fin.succ (Fin.succ (0 : Fin 1)) : Fin 3) = (2 : Fin 3) from rfl]
      rw [fin3_update2]; exact ha.1

/-- A majority operation gives a WNU of arity 3. -/
theorem majority_is_wnu (D : Type) (m : MajorityOp D) :
    ∃ (w : WNU D 3), w.op = m.op := by
  refine ⟨⟨m.op, ?_, ?_⟩, rfl⟩
  · -- Idempotency: m.op (fun _ => x) = x.
    intro x
    have h := (m.majority x x).1
    rw [fin3_const] at h
    exact h
  · -- WNU property: all single-y-updates give the same result x.
    intro x y i j
    rw [majority_single_change_val_aux D m x y i,
        majority_single_change_val_aux D m x y j]

-- ════════════════════════════════════════════════════════════
-- Section 6: Boolean operations
-- ════════════════════════════════════════════════════════════

/-- The Boolean majority function: (a∧b) ∨ (b∧c) ∨ (a∧c). -/
def boolMaj : Operation Bool 3 :=
  fun args => (args 0 && args 1) || (args 1 && args 2) || (args 0 && args 2)

-- ════════════════════════════════════════════════════════════
-- Section 7: Antimonotonicity of PolClone
-- ════════════════════════════════════════════════════════════

/-- Polymorphism clones are antimonotone in the constraint language.
    If Γ₁ ⊆ Γ₂ (each relation of Γ₁ appears in Γ₂), then Pol(Γ₂) ⊆ Pol(Γ₁). -/
theorem pol_antimonotone (dom : CSPDomain)
    (lang₁ lang₂ : ConstraintLanguage dom)
    (hsub : ∀ (idx : Fin lang₁.rels.length),
      ∃ (idx₂ : Fin lang₂.rels.length),
        lang₁.rels[idx] = lang₂.rels[idx₂])
    (k : Nat)
    (f : Operation dom.D k)
    (hf : isPolymorphism lang₂ f) :
    isPolymorphism lang₁ f := by
  intro rel_idx rows hrows
  obtain ⟨idx₂, heq⟩ := hsub rel_idx
  -- heq : lang₁.rels[rel_idx] = lang₂.rels[idx₂]
  -- Use the Sigma equality to transfer: both have the same fst (arity) and snd (relation).
  -- Apply the suffices pattern: parametrize on s.
  suffices ∀ (s : Σ r : Nat, FinRelation dom.D dom.deceq r)
      (hs : s = lang₁.rels[rel_idx])
      (hs₂ : s = lang₂.rels[idx₂])
      (rows' : Fin k → Fin s.1 → dom.D)
      (hrows' : ∀ i, s.2.mem (rows' i) = true),
      s.2.mem (fun j => f (fun i => rows' i j)) = true by
    exact this _ rfl heq rows hrows
  intro s hs hs₂ rows' hrows'
  subst hs₂
  -- Now s = lang₂.rels[idx₂] definitionally.
  exact hf idx₂ rows' hrows'

-- ════════════════════════════════════════════════════════════
-- Section 8: WNU arity upward (for majority-type WNU)
-- ════════════════════════════════════════════════════════════

/-- Helper: majority single-change value is x. -/
private lemma majority_single_change_val (D : Type) (m : MajorityOp D) (x y : D)
    (i : Fin 3) : m.op (Function.update (fun _ => x) i y) = x :=
  majority_single_change_val_aux D m x y i

/-- A majority WNU satisfies: op(update(fun _ => x) i y) = x for all i.
    This is needed for the arity extension theorem. -/
theorem majority_wnu_single_change_eq (D : Type) (m : MajorityOp D) :
    let w := (majority_is_wnu D m).choose
    ∀ (x y : D) (i : Fin 3), w.op (Function.update (fun _ => x) i y) = x := by
  intro w x y i
  have hweq : w.op = m.op := (majority_is_wnu D m).choose_spec
  rw [hweq]
  exact majority_single_change_val D m x y i

/-- A WNU where single-y-updates evaluate to the background x.
    This is a stronger condition than plain WNU; majority satisfies it. -/
structure StrongWNU (D : Type) (k : Nat) extends WNU D k where
  single_change : ∀ (x y : D) (i : Fin k),
    op (Function.update (fun _ => x) i y) = x

/-- Majority gives a StrongWNU of arity 3. -/
theorem majority_is_strong_wnu (D : Type) (m : MajorityOp D) :
    ∃ (w : StrongWNU D 3), w.op = m.op := by
  obtain ⟨w, hweq⟩ := majority_is_wnu D m
  refine ⟨⟨w, ?_⟩, hweq⟩
  intro x y i
  rw [hweq]
  exact majority_single_change_val D m x y i

/-- Restriction of Function.update through a val-preserving embedding.
    When j.val >= m, embed i can never equal j, so the update is invisible. -/
private lemma update_through_val_embed_out_of_range {D : Type} {m n : Nat}
    (embed : Fin m → Fin n) (h_val : ∀ i, (embed i).val = i.val)
    (x y : D) (j : Fin n) (hj : ¬(j.val < m)) :
    (fun i_m : Fin m => Function.update (fun _ => x) j y (embed i_m)) = fun _ => x := by
  funext i_m
  simp only [Function.update, Fin.ext_iff, h_val]
  have : i_m.val ≠ j.val := by omega
  simp [this]

/-- Restriction of Function.update through a val-preserving embedding.
    When j.val < m, the update restricts to the corresponding inner index. -/
private lemma update_through_val_embed_in_range {D : Type} {m n : Nat}
    (embed : Fin m → Fin n) (h_val : ∀ i, (embed i).val = i.val)
    (x y : D) (j : Fin n) (hj : j.val < m) :
    (fun i_m : Fin m => Function.update (fun _ => x) j y (embed i_m)) =
    Function.update (fun _ => x) (⟨j.val, hj⟩ : Fin m) y := by
  funext i_m
  simp only [Function.update, Fin.ext_iff, h_val]
  by_cases h : i_m.val = j.val <;> simp [h]

/-- Extend a StrongWNU through a val-preserving embedding Fin m -> Fin n.
    The extended operation op'(args) = w.op(args . embed) is a WNU on Fin n.
    Used by strong_wnu_arity_upward (castSucc) and majority_gives_bounded_width (castLE). -/
theorem strong_wnu_via_val_embedding {D : Type} {m n : Nat}
    (w : StrongWNU D m) (embed : Fin m → Fin n)
    (h_val : ∀ i : Fin m, (embed i).val = i.val) :
    ∃ (w' : WNU D n), ∀ args : Fin n → D,
      w'.op args = w.op (fun i => args (embed i)) := by
  let op' : Operation D n := fun args => w.op (fun i => args (embed i))
  refine ⟨⟨op', ?_, ?_⟩, fun _ => rfl⟩
  · intro x; show w.op (fun i => (fun _ => x) (embed i)) = x
    simp only; exact w.idempotent x
  · intro x y i j
    show w.op (fun i_m => Function.update (fun _ => x) i y (embed i_m)) =
         w.op (fun i_m => Function.update (fun _ => x) j y (embed i_m))
    by_cases hi : i.val < m <;> by_cases hj : j.val < m
    · rw [update_through_val_embed_in_range embed h_val x y i hi,
          update_through_val_embed_in_range embed h_val x y j hj]
      exact w.wnu_property x y ⟨i.val, hi⟩ ⟨j.val, hj⟩
    · rw [update_through_val_embed_in_range embed h_val x y i hi,
          update_through_val_embed_out_of_range embed h_val x y j hj]
      rw [w.single_change x y ⟨i.val, hi⟩, w.idempotent]
    · rw [update_through_val_embed_out_of_range embed h_val x y i hi,
          update_through_val_embed_in_range embed h_val x y j hj]
      rw [w.idempotent, w.single_change x y ⟨j.val, hj⟩]
    · rw [update_through_val_embed_out_of_range embed h_val x y i hi,
          update_through_val_embed_out_of_range embed h_val x y j hj]

/-- A StrongWNU of arity k gives a WNU of arity k+1 by ignoring the last argument. -/
theorem strong_wnu_arity_upward (dom : CSPDomain) (k : Nat)
    (w : StrongWNU dom.D k) :
    ∃ (w' : WNU dom.D (k + 1)), ∀ (args : Fin (k + 1) → dom.D),
      w'.op args = w.op (fun i => args (Fin.castSucc i)) :=
  strong_wnu_via_val_embedding w Fin.castSucc (fun _ => rfl)

end ClassicalConstraints
