/-
  ClassicalConstraints/NonnegRankObstruction.lean
  Rectangle covers, fooling sets, and nonneg rank lower bounds.

  The two main techniques for nonneg rank lower bounds:
  1. Rectangle cover method: a nonneg factorization decomposes the support
     into at most r rectangles.
  2. Fooling set method: a fooling set of size s forces nonneg rank ≥ s.

  Classical.choice is allowed (Side B).
  No sorry.
-/

import ClassicalConstraints.Chain6_Extension.SlackMatrixCore
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: CombRectangle
-- ════════════════════════════════════════════════════════════

/-- A combinatorial rectangle in an m x n matrix: a product set R x C
    where R is a set of rows and C is a set of columns. -/
structure CombRectangle (m n : Nat) where
  rows : Finset (Fin m)
  cols : Finset (Fin n)
  h_rows_nonempty : rows.Nonempty
  h_cols_nonempty : cols.Nonempty

-- ════════════════════════════════════════════════════════════
-- Section 2: Rectangle cover as a Prop
-- ════════════════════════════════════════════════════════════

/-- Whether a matrix entry (i, j) is covered by a product set (rows, cols). -/
def inProductSet {m n : Nat} (rows : Finset (Fin m)) (cols : Finset (Fin n))
    (i : Fin m) (j : Fin n) : Prop :=
  i ∈ rows ∧ j ∈ cols

/-- A rectangle cover: the support of M is covered by r product sets.
    We use (Finset (Fin m) × Finset (Fin n)) rather than CombRectangle
    to avoid nonemptiness constraints in degenerate cases. -/
def HasRectangleCover {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) (r : Nat) : Prop :=
  ∃ (rects : Fin r → Finset (Fin m) × Finset (Fin n)),
    ∀ (i : Fin m) (j : Fin n),
      M i j > 0 →
      ∃ (k : Fin r), i ∈ (rects k).1 ∧ j ∈ (rects k).2

-- ════════════════════════════════════════════════════════════
-- Section 3: Monochromatic property (for completeness)
-- ════════════════════════════════════════════════════════════

/-- A rectangle (rows, cols) is monochromatic for a property P if P holds
    uniformly within the rectangle. -/
def ProductSetMonochromatic {m n : Nat} (rows : Finset (Fin m)) (cols : Finset (Fin n))
    (P : Fin m → Fin n → Prop) : Prop :=
  (∀ i, i ∈ rows → ∀ j, j ∈ cols → P i j) ∨
  (∀ i, i ∈ rows → ∀ j, j ∈ cols → ¬(P i j))

/-- CombRectangle is monochromatic if the underlying product set is. -/
def RectangleMonochromatic {m n : Nat} (rect : CombRectangle m n)
    (P : Fin m → Fin n → Prop) : Prop :=
  ProductSetMonochromatic rect.rows rect.cols P

-- ════════════════════════════════════════════════════════════
-- Section 4: NonnegRankLowerBound
-- ════════════════════════════════════════════════════════════

/-- A certificate that a matrix has nonneg rank > r.
    The certificate is a proof that no nonneg factorization of rank ≤ r exists. -/
structure NonnegRankLowerBound {m n : Nat}
    (M : Matrix (Fin m) (Fin n) ℝ) (r : Nat) where
  /-- The lower bound holds: no nonneg factorization of rank ≤ r exists. -/
  h_lower : ∀ r', r' ≤ r → ¬Nonempty (NonnegFactorization M r')

-- ════════════════════════════════════════════════════════════
-- Section 5: FoolingSet
-- ════════════════════════════════════════════════════════════

/-- A fooling set for a nonneg matrix M: a set of positions (i_k, j_k)
    such that M[i_k, j_k] > 0 for all k, but for any k ≠ l,
    M[i_k, j_l] = 0 or M[i_l, j_k] = 0.

    A fooling set of size s implies nonneg rank ≥ s. -/
structure FoolingSet {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) (s : Nat) where
  /-- Row indices of fooling positions. -/
  fool_rows : Fin s → Fin m
  /-- Column indices of fooling positions. -/
  fool_cols : Fin s → Fin n
  /-- Diagonal entries are positive. -/
  h_diagonal_pos : ∀ k, M (fool_rows k) (fool_cols k) > 0
  /-- Off-diagonal entries are zero in at least one direction. -/
  h_off_diagonal : ∀ k l, k ≠ l →
    M (fool_rows k) (fool_cols l) = 0 ∨ M (fool_rows l) (fool_cols k) = 0

-- ════════════════════════════════════════════════════════════
-- Section 6: Helper lemma: positive sum has a positive term
-- ════════════════════════════════════════════════════════════

/-- If a sum over a Finset is positive and all terms are nonneg,
    some term is positive. -/
theorem exists_pos_term_of_pos_sum {α : Type*} (s : Finset α)
    (f : α → ℝ) (_h_nonneg : ∀ x ∈ s, f x ≥ 0)
    (h_pos : s.sum f > 0) : ∃ x ∈ s, f x > 0 := by
  by_contra h
  push_neg at h
  have h_zero : s.sum f ≤ 0 := by
    apply Finset.sum_nonpos
    intro x hx
    linarith [h x hx]
  linarith

-- ════════════════════════════════════════════════════════════
-- Section 7: Theorem 1 — Nonneg factorization gives rectangle cover
-- ════════════════════════════════════════════════════════════

/-- A nonneg factorization of rank r implies a rectangle cover of the
    support by at most r product sets.

    For each k in Fin r:
    - rows_k = { i | fac.left[i,k] > 0 }
    - cols_k = { j | fac.right[k,j] > 0 }

    If M[i,j] > 0, some term fac.left[i,k] * fac.right[k,j] > 0 (nonneg + positive sum).
    That means i ∈ rows_k and j ∈ cols_k. -/
theorem nonneg_factorization_gives_rectangle_cover {m n : Nat}
    (M : Matrix (Fin m) (Fin n) ℝ)
    (_h_nonneg : ∀ i j, M i j ≥ 0)
    (r : Nat) (fac : NonnegFactorization M r) :
    HasRectangleCover M r := by
  classical
  -- Construct the product sets for each k : Fin r.
  by_cases hr : r = 0
  · -- r = 0: M is zero matrix (empty sum). No positive entries. Cover vacuously holds.
    subst hr
    exact ⟨Fin.elim0, fun i j h_pos => by
      have heq := congr_fun (congr_fun fac.h_eq i) j
      simp [Matrix.mul_apply] at heq
      linarith⟩
  · -- r > 0.
    -- Define rects : Fin r → (Finset (Fin m) × Finset (Fin n)).
    let rects : Fin r → Finset (Fin m) × Finset (Fin n) := fun k =>
      (Finset.univ.filter (fun i => decide (fac.left i k > 0) = true),
       Finset.univ.filter (fun j => decide (fac.right k j > 0) = true))
    refine ⟨rects, fun i j h_pos => ?_⟩
    -- h_pos : M i j > 0.
    -- From fac.h_eq: M i j = ∑ k, fac.left[i,k] * fac.right[k,j].
    have heq := congr_fun (congr_fun fac.h_eq i) j
    simp [Matrix.mul_apply] at heq
    -- h_pos : M i j > 0, heq : M i j = ∑ ..., so ∑ ... > 0
    have h_sum_pos : Finset.univ.sum (fun k => fac.left i k * fac.right k j) > 0 := by
      rw [← heq]; exact h_pos
    -- Some term in the sum is positive.
    obtain ⟨k, _, h_prod_pos⟩ := exists_pos_term_of_pos_sum Finset.univ
      (fun k => fac.left i k * fac.right k j)
      (fun k _ => mul_nonneg (fac.h_left_nonneg i k) (fac.h_right_nonneg k j))
      h_sum_pos
    refine ⟨k, ?_, ?_⟩
    · -- i ∈ (rects k).1
      simp only [rects, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [decide_eq_true_eq]
      have h := mul_pos_iff.mp h_prod_pos
      cases h with
      | inl h => exact h.1
      | inr h => linarith [fac.h_left_nonneg i k, h.1]
    · -- j ∈ (rects k).2
      simp only [rects, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [decide_eq_true_eq]
      have h := mul_pos_iff.mp h_prod_pos
      cases h with
      | inl h => exact h.2
      | inr h => linarith [fac.h_right_nonneg k j, h.2]

-- ════════════════════════════════════════════════════════════
-- Section 8: Theorem 2 — Fooling set lower bound
-- ════════════════════════════════════════════════════════════

/-- A fooling set of size s implies nonneg rank < s is impossible.

    Direct proof using the factorization structure:
    For each diagonal entry (fool_rows k, fool_cols k), find a column index t_of k
    such that fac.left[fool_rows k, t_of k] > 0 and fac.right[t_of k, fool_cols k] > 0.
    By pigeonhole (s > r), two indices k ≠ l share t_of k = t_of l =: t.
    Then M[fool_rows k, fool_cols l] ≥ left[k,t] * right[t, fool_cols l] > 0,
    and similarly M[fool_rows l, fool_cols k] > 0. But h_off_diagonal says one must be 0. -/
theorem fooling_set_lower_bound {m n : Nat}
    (M : Matrix (Fin m) (Fin n) ℝ)
    (_h_nonneg : ∀ i j, M i j ≥ 0)
    (s : Nat) (fs : FoolingSet M s) :
    ∀ r, r < s → ¬Nonempty (NonnegFactorization M r) := by
  intro r h_lt ⟨fac⟩
  classical
  -- For each diagonal position, find the factorization witness.
  have h_term_exists : ∀ k : Fin s, ∃ t : Fin r,
      fac.left (fs.fool_rows k) t > 0 ∧ fac.right t (fs.fool_cols k) > 0 := by
    intro k
    have h_sum : Finset.univ.sum (fun t : Fin r =>
        fac.left (fs.fool_rows k) t * fac.right t (fs.fool_cols k)) > 0 := by
      have heq := congr_fun (congr_fun fac.h_eq (fs.fool_rows k)) (fs.fool_cols k)
      simp [Matrix.mul_apply] at heq
      rw [← heq]
      exact fs.h_diagonal_pos k
    obtain ⟨t, _, h_prod_pos⟩ := exists_pos_term_of_pos_sum Finset.univ
      (fun t => fac.left (fs.fool_rows k) t * fac.right t (fs.fool_cols k))
      (fun t _ => mul_nonneg (fac.h_left_nonneg _ t) (fac.h_right_nonneg t _))
      h_sum
    have h_pos := mul_pos_iff.mp h_prod_pos
    cases h_pos with
    | inl h => exact ⟨t, h.1, h.2⟩
    | inr h => linarith [fac.h_left_nonneg (fs.fool_rows k) t, h.1]
  -- Choose the witness for each k.
  let t_of : Fin s → Fin r := fun k => Classical.choose (h_term_exists k)
  have t_of_spec : ∀ k : Fin s,
      fac.left (fs.fool_rows k) (t_of k) > 0 ∧ fac.right (t_of k) (fs.fool_cols k) > 0 :=
    fun k => Classical.choose_spec (h_term_exists k)
  -- Pigeonhole: s > r implies t_of is not injective.
  have h_not_inj : ∃ k l : Fin s, k ≠ l ∧ t_of k = t_of l := by
    by_contra h_all
    push_neg at h_all
    have h_inj : Function.Injective t_of := by
      intro k l h_eq
      by_contra h_ne
      exact h_all k l h_ne h_eq
    have h_card := Fintype.card_le_of_injective t_of h_inj
    simp [Fintype.card_fin] at h_card
    omega
  obtain ⟨k, l, h_neq, h_same⟩ := h_not_inj
  -- t_of k = t_of l; call it t_idx.
  set t_idx := t_of k with h_tidx
  have hk_left : fac.left (fs.fool_rows k) t_idx > 0 := (t_of_spec k).1
  have hk_right : fac.right t_idx (fs.fool_cols k) > 0 := (t_of_spec k).2
  have hl_left : fac.left (fs.fool_rows l) t_idx > 0 := by
    have := (t_of_spec l).1; rw [← h_same] at this; exact this
  have hl_right : fac.right t_idx (fs.fool_cols l) > 0 := by
    have := (t_of_spec l).2; rw [← h_same] at this; exact this
  -- M[fool_rows k, fool_cols l] > 0.
  have h_M_kl : M (fs.fool_rows k) (fs.fool_cols l) > 0 := by
    have heq := congr_fun (congr_fun fac.h_eq (fs.fool_rows k)) (fs.fool_cols l)
    simp [Matrix.mul_apply] at heq
    rw [heq]
    apply lt_of_lt_of_le (mul_pos hk_left hl_right)
    exact Finset.single_le_sum
      (f := fun j => fac.left (fs.fool_rows k) j * fac.right j (fs.fool_cols l))
      (fun t' _ => mul_nonneg (fac.h_left_nonneg _ t') (fac.h_right_nonneg t' _))
      (Finset.mem_univ t_idx)
  -- M[fool_rows l, fool_cols k] > 0.
  have h_M_lk : M (fs.fool_rows l) (fs.fool_cols k) > 0 := by
    have heq := congr_fun (congr_fun fac.h_eq (fs.fool_rows l)) (fs.fool_cols k)
    simp [Matrix.mul_apply] at heq
    rw [heq]
    apply lt_of_lt_of_le (mul_pos hl_left hk_right)
    exact Finset.single_le_sum
      (f := fun j => fac.left (fs.fool_rows l) j * fac.right j (fs.fool_cols k))
      (fun t' _ => mul_nonneg (fac.h_left_nonneg _ t') (fac.h_right_nonneg t' _))
      (Finset.mem_univ t_idx)
  -- h_off_diagonal says one of these must be 0. Contradiction.
  rcases fs.h_off_diagonal k l h_neq with h | h <;> linarith

-- ════════════════════════════════════════════════════════════
-- Section 9: Theorem 3 — No small cover implies high rank
-- ════════════════════════════════════════════════════════════

/-- If no rectangle cover of size r exists, then no nonneg factorization of rank r exists. -/
theorem no_small_cover_implies_high_rank {m n : Nat}
    (M : Matrix (Fin m) (Fin n) ℝ)
    (h_nonneg : ∀ i j, M i j ≥ 0)
    (r : Nat)
    (h_no_cover : ¬HasRectangleCover M r) :
    ¬Nonempty (NonnegFactorization M r) := by
  intro ⟨fac⟩
  exact h_no_cover (nonneg_factorization_gives_rectangle_cover M h_nonneg r fac)

end ClassicalConstraints
