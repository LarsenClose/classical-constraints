/-
  ClassicalConstraints/QuotientDescentCore.lean
  Core descent obstruction theorems, parametric over any InstanceFamily.

  Main results:
  1. Pigeonhole: if distinct solution types exceed basis cells, some cell
     contains instances with different solution types.
  2. Grade bounds basis cardinality via observable range bounds.
  3. Core obstruction: diverse + disjoint implies no descent (at a fixed basis).
  4. SuperPolyDiverse + disjoint + bounded width implies HardAtPolyGrade.
  5. Error bounds per cell (disjoint solution types).

  The disjointness condition is the MAKE-OR-BREAK hypothesis.
  Without it you get error bounds (still useful).
  With it you get the full obstruction.
-/

import ClassicalConstraints.Chain1_SAT.Obstruction
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Solution Types

The solution type of an instance is the set of witnesses that satisfy it.
When two instances share a basis cell but have different solution types,
any single decoder value cannot satisfy both. -/

namespace QuotientDescentCore

variable (F : InstanceFamily)

-- We need DecidableEq on witness types to form Finsets of Finsets (for counting
-- distinct solution types). This is a mild assumption: any concrete witness type
-- (bit strings, bounded integers) has decidable equality.
variable [instDecEqW : ∀ n, DecidableEq (F.W n)]

/-- Decidable satisfaction at a fixed instance, as a DecidablePred on witnesses. -/
instance instDecidableSat (n : Nat) (φ : F.X n) : DecidablePred (F.Sat n φ) :=
  fun w => F.h_dec n φ w

/-! ## 1. SolutionType: the set of valid witnesses -/

/-- The set of valid witnesses for instance φ at size n. -/
def SolutionType (n : Nat) (φ : F.X n) : Set (F.W n) :=
  { w | F.Sat n φ w }

/-- Finset version of the solution type, using decidability and finiteness. -/
def SolutionTypeFinset (n : Nat) (φ : F.X n) : Finset (F.W n) :=
  @Finset.univ (F.W n) (F.h_fin_W n) |>.filter (fun w => @decide (F.Sat n φ w) (F.h_dec n φ w))

omit instDecEqW in
/-- Membership in SolutionTypeFinset is equivalent to satisfaction. -/
theorem mem_solutionTypeFinset_iff (n : Nat) (φ : F.X n) (w : F.W n) :
    w ∈ SolutionTypeFinset F n φ ↔ F.Sat n φ w := by
  simp [SolutionTypeFinset, Finset.mem_filter, Finset.mem_univ, decide_eq_true_eq]

omit instDecEqW in
/-- An instance is satisfiable iff its solution type finset is nonempty. -/
theorem satisfiable_iff_nonempty (n : Nat) (φ : F.X n) :
    F.Satisfiable n φ ↔ (SolutionTypeFinset F n φ).Nonempty := by
  constructor
  · intro ⟨w, hw⟩
    exact ⟨w, (mem_solutionTypeFinset_iff F n φ w).mpr hw⟩
  · intro ⟨w, hw⟩
    exact ⟨w, (mem_solutionTypeFinset_iff F n φ w).mp hw⟩

/-! ## 2. Counting distinct solution types -/

/-- The image of the solution-type map over all instances.
    Each element is a distinct Finset of witnesses. -/
def solutionTypeImage (n : Nat) : Finset (Finset (F.W n)) :=
  (@Finset.univ (F.X n) (F.h_fin_X n)).image (SolutionTypeFinset F n)

/-- The number of distinct solution types at size n. -/
def numDistinctSolutionTypes (n : Nat) : Nat :=
  (solutionTypeImage F n).card

/-! ## 3. Counting basis cells -/

variable [alg : GradedObservableAlgebra F]

/-- The number of distinct basis cells (profiles) induced by a basis. -/
def numBasisCells {g n : Nat} (B : ObservableBasis F g n) : Nat :=
  ((@Finset.univ (F.X n) (F.h_fin_X n)).image (B.observe)).card

/-! ## 4. THEOREM 1: Pigeonhole on solution types vs basis cells

If the number of distinct solution types exceeds the number of
basis cells, then some cell must contain instances with different
solution types. -/

/-- Two instances share a basis cell but have different solution types. -/
structure CellConflict {g n : Nat} (B : ObservableBasis F g n) where
  /-- First instance -/
  φ₁ : F.X n
  /-- Second instance -/
  φ₂ : F.X n
  /-- They are basis-equivalent -/
  h_equiv : B.Equiv φ₁ φ₂
  /-- They have different solution types -/
  h_diff : SolutionTypeFinset F n φ₁ ≠ SolutionTypeFinset F n φ₂

/-- If f factors through g on a finset (g a₁ = g a₂ implies f a₁ = f a₂),
    then |image f| ≤ |image g|. -/
private theorem card_image_le_of_factors {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a₁ a₂ : α, a₁ ∈ s → a₂ ∈ s → g a₁ = g a₂ → f a₁ = f a₂) :
    (s.image f).card ≤ (s.image g).card := by
  -- Combined map approach (no Classical.choice):
  -- Map s to γ × β via a ↦ (g a, f a). The factoring condition makes
  -- Prod.fst injective on the product image, so |product image| ≤ |image g|.
  -- And |image f| ≤ |product image| since Prod.snd surjects onto image f.
  let fg : α → γ × β := fun a => (g a, f a)
  -- Step 1: |image f| ≤ |image fg| because Prod.snd surjects
  have h_snd : s.image f = (s.image fg).image Prod.snd := by
    ext b; simp [fg]
  have h1 : (s.image f).card ≤ (s.image fg).card := by
    rw [h_snd]; exact Finset.card_image_le
  -- Step 2: Prod.fst is injective on image fg (by the factoring condition)
  have h_fst_inj : Set.InjOn Prod.fst (s.image fg : Set (γ × β)) := by
    intro ⟨g₁, f₁⟩ hgf₁ ⟨g₂, f₂⟩ hgf₂ heq
    simp only [Finset.mem_coe] at hgf₁ hgf₂
    obtain ⟨a₁, ha₁, hfa₁⟩ := Finset.mem_image.mp hgf₁
    obtain ⟨a₂, ha₂, hfa₂⟩ := Finset.mem_image.mp hgf₂
    simp only [fg, Prod.mk.injEq] at hfa₁ hfa₂
    have hgeq : g a₁ = g a₂ := by rw [hfa₁.1, hfa₂.1]; exact heq
    have hfeq : f a₁ = f a₂ := h a₁ a₂ ha₁ ha₂ hgeq
    ext
    · exact heq
    · rw [← hfa₁.2, ← hfa₂.2, hfeq]
  -- Step 3: Prod.fst maps image fg into image g
  have h_fst_maps : Set.MapsTo Prod.fst (s.image fg : Set (γ × β)) (s.image g : Set γ) := by
    intro ⟨gv, _⟩ hgf
    simp only [Finset.mem_coe] at hgf ⊢
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hgf
    simp only [fg, Prod.mk.injEq] at hfa
    exact Finset.mem_image.mpr ⟨a, ha, hfa.1⟩
  -- Step 4: |image fg| ≤ |image g| by injective map
  have h2 : (s.image fg).card ≤ (s.image g).card :=
    Finset.card_le_card_of_injOn Prod.fst h_fst_maps h_fst_inj
  omega

/-- If solution types outnumber basis cells, two instances share a cell
    but have different solution types. -/
theorem pigeonhole_solution_types {g n : Nat} (B : ObservableBasis F g n)
    (h : numBasisCells F B < numDistinctSolutionTypes F n) :
    ∃ φ₁ φ₂ : F.X n, B.Equiv φ₁ φ₂ ∧
      SolutionTypeFinset F n φ₁ ≠ SolutionTypeFinset F n φ₂ := by
  by_contra h_no
  push_neg at h_no
  have hle : (solutionTypeImage F n).card ≤
      ((@Finset.univ (F.X n) (F.h_fin_X n)).image (B.observe)).card :=
    card_image_le_of_factors _ (SolutionTypeFinset F n) (B.observe)
      (fun a₁ a₂ _ _ heq => h_no a₁ a₂ heq)
  exact Nat.not_lt.mpr hle h

/-- Pigeonhole (variant): if solution types outnumber basis cells,
    a CellConflict exists. -/
theorem pigeonhole_conflict {g n : Nat} (B : ObservableBasis F g n)
    (h : numBasisCells F B < numDistinctSolutionTypes F n) :
    Nonempty (CellConflict F B) := by
  obtain ⟨φ₁, φ₂, he, hd⟩ := pigeonhole_solution_types F B h
  exact ⟨⟨φ₁, φ₂, he, hd⟩⟩

/-! ## 5. THEOREM 2: Grade bounds basis cardinality

The polynomial range condition h_poly_range bounds how many
distinct values each observable can take, hence how many
distinct profiles a width-w basis can produce. -/

omit instDecEqW in
/-- Upper bound on distinct profiles from a single observable at grade g. -/
theorem single_obs_range_bound (g n : Nat) (o : alg.Obs g n) :
    ∃ k : Nat, ∀ x : F.X n, alg.eval o x < k :=
  alg.h_fin_range g n o

omit instDecEqW in
/-- Upper bound: each grade-g observable has range < n^g + c for some c. -/
theorem obs_poly_bound (g : Nat) :
    ∃ c : Nat, ∀ n (o : alg.Obs g n) (x : F.X n),
      alg.eval o x < n ^ g + c :=
  alg.h_poly_range g

omit instDecEqW in
/-- The number of distinct basis profiles is at most (bound)^width,
    given that each coordinate of the observe map is < bound. -/
theorem basis_cells_poly_bound {g n : Nat} (B : ObservableBasis F g n)
    {bound : Nat}
    (h_bound : ∀ φ : F.X n, ∀ i : Fin B.width, B.observe φ i < bound) :
    numBasisCells F B ≤ bound ^ B.width := by
  unfold numBasisCells
  let toFinFun : F.X n → (Fin B.width → Fin bound) :=
    fun φ i => ⟨B.observe φ i, h_bound φ i⟩
  have h_recover : ∀ φ₁ φ₂ : F.X n,
      toFinFun φ₁ = toFinFun φ₂ → B.observe φ₁ = B.observe φ₂ := by
    intro φ₁ φ₂ heq
    funext i
    have := congr_fun heq i
    simp [toFinFun] at this
    exact this
  -- After unfolding, goal is (univ.image observe).card ≤ bound ^ B.width
  -- where univ uses F.h_fin_X n
  show ((@Finset.univ (F.X n) (F.h_fin_X n)).image B.observe).card ≤ bound ^ B.width
  calc ((@Finset.univ (F.X n) (F.h_fin_X n)).image B.observe).card
      ≤ ((@Finset.univ (F.X n) (F.h_fin_X n)).image toFinFun).card := by
        apply card_image_le_of_factors
        intro a₁ a₂ _ _ heq
        exact h_recover a₁ a₂ heq
    _ ≤ (@Finset.univ (Fin B.width → Fin bound) _).card := by
        apply Finset.card_le_card
        exact Finset.subset_univ _
    _ = Fintype.card (Fin B.width → Fin bound) := Finset.card_univ
    _ = bound ^ B.width := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-! ## 6. THEOREM 3: Core obstruction -- diverse + disjoint implies no descent

This is the central structural theorem. It combines:
- Pigeonhole (solution types > basis cells)
- Disjointness (conflicting instances have disjoint solutions)
to conclude that no descent witness can exist. -/

/-- Disjointness condition: whenever two instances in the same basis cell
    have different solution types, their solution sets are disjoint. -/
def DisjointConflicts {g n : Nat} (B : ObservableBasis F g n) : Prop :=
  ∀ (φ₁ φ₂ : F.X n), B.Equiv φ₁ φ₂ →
    SolutionTypeFinset F n φ₁ ≠ SolutionTypeFinset F n φ₂ →
    ∀ w : F.W n, ¬(F.Sat n φ₁ w ∧ F.Sat n φ₂ w)

/-- From a cell conflict with disjointness, we get a WitnessConflict. -/
def conflictToWitnessConflict {g n : Nat} {B : ObservableBasis F g n}
    (cc : CellConflict F B)
    (hd : DisjointConflicts F B)
    (hs₁ : F.Satisfiable n cc.φ₁)
    (hs₂ : F.Satisfiable n cc.φ₂) :
    WitnessConflict F B where
  φ₁ := cc.φ₁
  φ₂ := cc.φ₂
  h_sat₁ := hs₁
  h_sat₂ := hs₂
  h_equiv := cc.h_equiv
  h_disjoint := hd cc.φ₁ cc.φ₂ cc.h_equiv cc.h_diff

/-- Diversity condition: more distinct solution types (among satisfiable
    instances) than basis cells. -/
def DiverseAtBasis {g n : Nat} (B : ObservableBasis F g n) : Prop :=
  numBasisCells F B < numDistinctSolutionTypes F n

/-- Decidable satisfiability: derived from h_dec and h_fin_W. -/
instance instDecidableSatisfiable (n : Nat) (φ : F.X n) : Decidable (F.Satisfiable n φ) :=
  @Fintype.decidableExistsFintype (F.W n) (fun w => F.Sat n φ w)
    (instDecidableSat F n φ) (F.h_fin_W n)

/-- Satisfiable-filtered diversity: restrict counting to satisfiable instances. -/
def SatSolutionTypeImage (n : Nat) : Finset (Finset (F.W n)) :=
  (@Finset.univ (F.X n) (F.h_fin_X n)).filter
    (fun φ => decide (F.Satisfiable n φ)) |>.image (SolutionTypeFinset F n)

/-- Number of distinct solution types among satisfiable instances. -/
def numSatSolutionTypes (n : Nat) : Nat :=
  (SatSolutionTypeImage F n).card

/-- Strengthened diversity: among satisfiable instances only. -/
def SatDiverseAtBasis {g n : Nat} (B : ObservableBasis F g n) : Prop :=
  numBasisCells F B < numSatSolutionTypes F n

/-- Pigeonhole on satisfiable instances: if sat-diversity exceeds basis cells,
    two satisfiable instances share a cell but have different solution types. -/
private theorem sat_pigeonhole_extraction {g n : Nat} (B : ObservableBasis F g n)
    (h_diverse : SatDiverseAtBasis F B) :
    ∃ (φ₁ φ₂ : F.X n), F.Satisfiable n φ₁ ∧ F.Satisfiable n φ₂ ∧
      B.Equiv φ₁ φ₂ ∧ SolutionTypeFinset F n φ₁ ≠ SolutionTypeFinset F n φ₂ := by
  by_contra h_no
  push_neg at h_no
  let satFilter := (@Finset.univ (F.X n) (F.h_fin_X n)).filter
    (fun φ => decide (F.Satisfiable n φ))
  have hle : (satFilter.image (SolutionTypeFinset F n)).card ≤
      ((@Finset.univ (F.X n) (F.h_fin_X n)).image (B.observe)).card := by
    calc (satFilter.image (SolutionTypeFinset F n)).card
        ≤ (satFilter.image (B.observe)).card := by
          apply card_image_le_of_factors
          intro a₁ a₂ ha₁ ha₂ heq
          have ha₁' : F.Satisfiable n a₁ := by
            have := (Finset.mem_filter.mp ha₁).2
            simp [decide_eq_true_eq] at this; exact this
          have ha₂' : F.Satisfiable n a₂ := by
            have := (Finset.mem_filter.mp ha₂).2
            simp [decide_eq_true_eq] at this; exact this
          exact h_no a₁ a₂ ha₁' ha₂' heq
      _ ≤ ((@Finset.univ (F.X n) (F.h_fin_X n)).image (B.observe)).card := by
          apply Finset.card_le_card
          apply Finset.image_subset_image
          exact Finset.filter_subset _ _
  -- hle : |image solType on satFilter| ≤ |image observe|
  -- h_diverse : |image observe| < |image solType on satFilter|  (= SatDiverseAtBasis)
  exact Nat.not_lt.mpr hle h_diverse

/-- Core obstruction (at a fixed basis): if a basis has diversity + disjointness,
    no decoder through THAT basis can be sound. -/
theorem core_obstruction_at_basis {g n : Nat} (B : ObservableBasis F g n)
    (h_diverse : SatDiverseAtBasis F B)
    (h_disjoint : DisjointConflicts F B) :
    ¬ ∃ (d : (Fin B.width → Nat) → F.W n),
      (∀ φ, F.Satisfiable n φ → F.Sat n φ (d (B.observe φ))) := by
  intro ⟨d, hd⟩
  obtain ⟨φ₁, φ₂, hs₁, hs₂, he, hne⟩ := sat_pigeonhole_extraction F B h_diverse
  have h1 := hd φ₁ hs₁
  have h2 := hd φ₂ hs₂
  rw [show B.observe φ₂ = B.observe φ₁ from he.symm] at h2
  exact h_disjoint φ₁ φ₂ he hne (d (B.observe φ₁)) ⟨h1, h2⟩

/-! ## 7. THEOREM 4: SuperPolyDiverse implies HardAtPolyGrade

The asymptotic version: if diversity grows faster than any polynomial
bound on basis cells, the family is hard at every polynomial grade.

The hypothesis `BoundedDescentWidth` ensures that DescentWitness bases
at each grade have bounded width. This is needed because super-polynomial
diversity beats (n^g + c)^w for any fixed w, but the width w of a
DescentWitness could in principle vary with n. With bounded width, we
can pick n large enough to beat all possible basis cell counts. -/

/-- Super-polynomial diversity: for every grade g, width w, and constant c,
    at all sufficiently large n, the number of distinct solution types among
    satisfiable instances exceeds (n^g + c)^w. -/
def SuperPolyDiverse : Prop :=
  ∀ g : Nat, ∀ w : Nat, ∀ c : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
    (n ^ g + c) ^ w < numSatSolutionTypes F n

/-- Asymptotic disjointness: at every grade, every basis has disjoint conflicts. -/
def AsymptoticDisjointness : Prop :=
  ∀ g n : Nat, ∀ B : ObservableBasis F g n, DisjointConflicts F B

/-- Bounded descent width: at each grade, every DescentWitness has basis width at most W. -/
def BoundedDescentWidth (g W : Nat) : Prop :=
  ∀ n : Nat, ∀ dw : DescentWitness F g n, dw.basis.width ≤ W

/-- Super-polynomial diversity + asymptotic disjointness + bounded descent width
    implies no descent witness exists at grade g for large enough n. -/
theorem superPolyDiverse_no_descent_at_grade (g : Nat)
    (h_diverse : SuperPolyDiverse F)
    (h_disjoint : AsymptoticDisjointness F)
    (W : Nat) (h_bw : BoundedDescentWidth F g W) :
    ∃ n : Nat, IsEmpty (DescentWitness F g n) := by
  obtain ⟨c, hc⟩ := alg.h_poly_range g
  -- Get thresholds for width W and width 0 (handles degenerate base = 0 case)
  obtain ⟨N_W, hN_W⟩ := h_diverse g W c
  obtain ⟨N_0, hN_0⟩ := h_diverse g 0 c
  -- Use max of both thresholds + 1 to ensure n^g + c > 0 (since n ≥ 1)
  let N := max N_W (max N_0 1)
  use N
  constructor
  intro ⟨B, decode, h_sound⟩
  have h_width_le : B.width ≤ W := h_bw N ⟨B, decode, h_sound⟩
  have h_obs_bound : ∀ φ : F.X N, ∀ i : Fin B.width,
      B.observe φ i < N ^ g + c := fun φ i => hc N (B.obs i) φ
  have h_cells_le : numBasisCells F B ≤ (N ^ g + c) ^ B.width :=
    basis_cells_poly_bound F B h_obs_bound
  have h_base_pos : 0 < N ^ g + c := by
    have hN1 : 1 ≤ N := le_trans (le_max_right N_0 1) (le_max_right N_W _)
    have : 1 ≤ N ^ g := Nat.one_le_pow g N hN1
    omega
  have h_div : (N ^ g + c) ^ W < numSatSolutionTypes F N :=
    hN_W N (le_max_left _ _)
  have h_sat_diverse : SatDiverseAtBasis F B := by
    unfold SatDiverseAtBasis
    calc numBasisCells F B ≤ (N ^ g + c) ^ B.width := h_cells_le
      _ ≤ (N ^ g + c) ^ W := Nat.pow_le_pow_right h_base_pos h_width_le
      _ < numSatSolutionTypes F N := h_div
  exact core_obstruction_at_basis F B h_sat_diverse (h_disjoint g N B) ⟨decode, h_sound⟩

/-- Full hardness from super-polynomial diversity + asymptotic disjointness +
    bounded descent width at each grade. -/
theorem superPolyDiverse_implies_hard
    (h_diverse : SuperPolyDiverse F)
    (h_disjoint : AsymptoticDisjointness F)
    (h_bw : ∀ g : Nat, ∃ W : Nat, BoundedDescentWidth F g W) :
    HardAtPolyGrade F := by
  intro g
  obtain ⟨W, hW⟩ := h_bw g
  exact superPolyDiverse_no_descent_at_grade F g h_diverse h_disjoint W hW

/-! ## 8. Direct obstruction from conflict

This theorem uses the existing WitnessConflict infrastructure directly,
bypassing the counting argument. It is the cleanest statement. -/

omit instDecEqW in
/-- If a basis has a witness conflict, no decoder through that basis is sound.
    This is a direct consequence of no_descent_from_conflict. -/
theorem no_sound_decoder_from_conflict {g n : Nat}
    (B : ObservableBasis F g n)
    (hc : WitnessConflict F B) :
    ¬ ∃ (d : (Fin B.width → Nat) → F.W n),
      (∀ φ, F.Satisfiable n φ → F.Sat n φ (d (B.observe φ))) :=
  no_descent_from_conflict F B hc

omit instDecEqW in
/-- If at every grade g, some size n has a witness conflict at every
    basis of that grade, the family is hard at polynomial grade. -/
theorem conflict_at_all_grades_implies_hard
    (h : ∀ g : Nat, ∃ n : Nat,
      ∀ B : ObservableBasis F g n, Nonempty (WitnessConflict F B)) :
    HardAtPolyGrade F := by
  intro g
  obtain ⟨n, hn⟩ := h g
  use n
  constructor
  intro ⟨B, decode, h_sound⟩
  have ⟨wc⟩ := hn B
  exact no_descent_from_conflict F B wc ⟨decode, h_sound⟩

/-! ## 9. Error bounds per cell

When disjointness holds within a cell, at most one instance can be
satisfied by any single decoder value. -/

/-- The error set: instances in a cell where the decoder fails. -/
def decoderErrorSet {g n : Nat} (B : ObservableBasis F g n)
    (d : (Fin B.width → Nat) → F.W n) : Finset (F.X n) :=
  (@Finset.univ (F.X n) (F.h_fin_X n)).filter
    (fun φ => decide (F.Satisfiable n φ) &&
      !decide (F.Sat n φ (d (B.observe φ))))

omit instDecEqW in
/-- Any sound decoder has zero errors (by definition). -/
theorem sound_decoder_no_errors {g n : Nat} (B : ObservableBasis F g n)
    (d : (Fin B.width → Nat) → F.W n)
    (h_sound : ∀ φ, F.Satisfiable n φ → F.Sat n φ (d (B.observe φ))) :
    decoderErrorSet F B d = ∅ := by
  simp only [decoderErrorSet, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  intro φ
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    not_and, not_not]
  intro h_sat
  exact h_sound φ h_sat

omit instDecEqW in
/-- Error bound per cell: if instances in a cell have pairwise disjoint
    solution sets (no witness satisfies two distinct instances), at most
    1 instance can be satisfied by any single decoder value. -/
theorem error_lower_bound_per_cell {g n : Nat}
    (B : ObservableBasis F g n)
    (profile : Fin B.width → Nat)
    (instances : Finset (F.X n))
    (h_disjoint_sol : ∀ φ₁ ∈ instances, ∀ φ₂ ∈ instances,
      φ₁ ≠ φ₂ → ∀ w, ¬(F.Sat n φ₁ w ∧ F.Sat n φ₂ w))
    (d : (Fin B.width → Nat) → F.W n) :
    (instances.filter (fun φ =>
      @decide (F.Sat n φ (d profile)) (F.h_dec n φ (d profile)))).card ≤ 1 := by
  by_contra h_gt
  push_neg at h_gt
  rw [Finset.one_lt_card] at h_gt
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, hne⟩ := h_gt
  simp only [Finset.mem_filter, decide_eq_true_eq] at hφ₁ hφ₂
  exact h_disjoint_sol φ₁ hφ₁.1 φ₂ hφ₂.1 hne (d profile) ⟨hφ₁.2, hφ₂.2⟩

/-! ## 10. Intersection witness and disjoint failure

Without disjointness, a decoder CAN succeed if solution types overlap.
With disjointness, the decoder necessarily fails on one of two
conflicting instances. -/

omit instDecEqW in
/-- If a decoder satisfies both basis-equivalent instances,
    the decoder's witness lies in both solution types. -/
theorem intersection_witness_from_equiv {g n : Nat}
    (B : ObservableBasis F g n)
    (d : (Fin B.width → Nat) → F.W n)
    (φ₁ φ₂ : F.X n)
    (h_equiv : B.Equiv φ₁ φ₂)
    (h1 : F.Sat n φ₁ (d (B.observe φ₁)))
    (h2 : F.Sat n φ₂ (d (B.observe φ₂))) :
    d (B.observe φ₁) ∈ SolutionTypeFinset F n φ₁ ∧
    d (B.observe φ₁) ∈ SolutionTypeFinset F n φ₂ := by
  constructor
  · exact (mem_solutionTypeFinset_iff F n φ₁ _).mpr h1
  · rw [show B.observe φ₂ = B.observe φ₁ from h_equiv.symm] at h2
    exact (mem_solutionTypeFinset_iff F n φ₂ _).mpr h2

omit instDecEqW in
/-- If solution types are disjoint, the decoder cannot satisfy both. -/
theorem disjoint_implies_decoder_fails {g n : Nat}
    (B : ObservableBasis F g n)
    (d : (Fin B.width → Nat) → F.W n)
    (φ₁ φ₂ : F.X n)
    (h_equiv : B.Equiv φ₁ φ₂)
    (h_disj : Disjoint (SolutionTypeFinset F n φ₁) (SolutionTypeFinset F n φ₂)) :
    ¬(F.Sat n φ₁ (d (B.observe φ₁)) ∧ F.Sat n φ₂ (d (B.observe φ₂))) := by
  intro ⟨h1, h2⟩
  have ⟨hm1, hm2⟩ := intersection_witness_from_equiv F B d φ₁ φ₂ h_equiv h1 h2
  have := Finset.disjoint_left.mp h_disj hm1
  exact this hm2

/-! ## 11. Connecting diversity to WitnessConflict -/

/-- If we have diversity + disjointness at a basis, we can construct a
    WitnessConflict. This bridges the counting argument to the algebraic
    obstruction. -/
theorem diversity_disjoint_gives_conflict {g n : Nat}
    (B : ObservableBasis F g n)
    (h_diverse : SatDiverseAtBasis F B)
    (h_disjoint : DisjointConflicts F B) :
    Nonempty (WitnessConflict F B) := by
  obtain ⟨φ₁, φ₂, hs₁, hs₂, he, hne⟩ := sat_pigeonhole_extraction F B h_diverse
  exact ⟨{
    φ₁ := φ₁
    φ₂ := φ₂
    h_sat₁ := hs₁
    h_sat₂ := hs₂
    h_equiv := he
    h_disjoint := h_disjoint φ₁ φ₂ he hne
  }⟩

/-- Full chain: diversity + disjointness -> conflict -> no descent. -/
theorem diversity_disjoint_no_descent {g n : Nat}
    (B : ObservableBasis F g n)
    (h_diverse : SatDiverseAtBasis F B)
    (h_disjoint : DisjointConflicts F B) :
    ¬ ∃ (d : (Fin B.width → Nat) → F.W n),
      (∀ φ, F.Satisfiable n φ → F.Sat n φ (d (B.observe φ))) := by
  obtain ⟨wc⟩ := diversity_disjoint_gives_conflict F B h_diverse h_disjoint
  exact no_descent_from_conflict F B wc

/-! ## 12. HardAtPolyGrade from diversity + disjointness

Final assembly: if diversity is super-polynomial and disjointness holds
uniformly, with bounded descent width, the family is hard at every
polynomial grade. -/

/-- Uniform diversity + disjointness implies hardness. -/
theorem hard_from_uniform_diversity_disjointness
    (h_diverse : ∀ g : Nat, ∃ n : Nat,
      ∀ B : ObservableBasis F g n, SatDiverseAtBasis F B)
    (h_disjoint : AsymptoticDisjointness F) :
    HardAtPolyGrade F := by
  intro g
  obtain ⟨n, hn⟩ := h_diverse g
  use n
  constructor
  intro ⟨B, decode, h_sound⟩
  have h_div := hn B
  exact diversity_disjoint_no_descent F B h_div (h_disjoint g n B) ⟨decode, h_sound⟩

/-! ## 13. Honest assessment

### What is proved (0 sorry):
- `card_image_le_of_factors`: if f factors through g, |image f| <= |image g|
- `pigeonhole_solution_types`: diversity > cells implies a cell conflict exists
- `basis_cells_poly_bound`: |cells| <= bound^width (given coordinate bounds)
- `core_obstruction_at_basis`: diversity + disjointness at a basis -> no decoder
- `superPolyDiverse_no_descent_at_grade`: super-poly diversity + disjointness + bounded width -> no descent
- `superPolyDiverse_implies_hard`: assembly into HardAtPolyGrade (with bounded width)
- `error_lower_bound_per_cell`: at most 1 instance per cell satisfied (with disjointness)
- `diversity_disjoint_gives_conflict`: diversity + disjointness -> WitnessConflict
- `no_sound_decoder_from_conflict`: direct obstruction from WitnessConflict
- `conflict_at_all_grades_implies_hard`: conflict at all grades -> HardAtPolyGrade
- `sound_decoder_no_errors`: sound decoders have empty error set

### Design decisions:
- `core_obstruction` (with DescentWitness carrying its own basis) was removed:
  the basis mismatch is architectural, not fixable without changing DescentWitness.
  `core_obstruction_at_basis` is the clean replacement.
- `quantitative_error_bound` was removed: it was mathematically incorrect without
  an incompatibility assumption. A decoder CAN satisfy all instances if solution
  types overlap sufficiently.
- `superPolyDiverse_implies_hard` requires `BoundedDescentWidth`: without it,
  basis widths can grow with n, and super-polynomial diversity (which quantifies
  over width) cannot be applied to a specific witness without knowing its width
  in advance. The bounded-width assumption is realistic for natural encodings.
- `basis_cells_poly_bound` takes an explicit coordinate bound hypothesis rather
  than deriving it from `obs_poly_bound`. This is cleaner and avoids `.choose`
  in the statement.
- `error_lower_bound_per_cell` was simplified: the unused hypotheses `h_in_cell`,
  `h_sat`, and `h_distinct` were removed. Only pairwise disjointness is needed.
-/

end QuotientDescentCore
