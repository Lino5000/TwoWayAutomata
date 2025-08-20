import Mathlib.Computability.Language
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pigeonhole

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Configurations
import TwoWayAutomata.Kozen.Lemmas
import TwoWayAutomata.Kozen.Movement
import TwoWayAutomata.Kozen.Word

variable {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (x : Word α n) 

namespace TwoDFA

/--
After some number of steps, the machine m on input x will go from configuration start to the input configuration.
-/
inductive GoesTo (start : Config σ n) : Config σ n → Prop
  | refl : GoesTo start start
  | tail {mid stp : Config σ n} (head : GoesTo start mid) (tail : m.nextConfig x mid stp) : GoesTo start stp


namespace GoesTo

variable {m : TwoDFA α σ} {x : Word α n}

@[refl]
lemma reflexive {c : Config σ n} : m.GoesTo x c c := .refl

@[trans]
theorem trans {start mid stp : Config σ n} (ha : m.GoesTo x start mid) (hb : m.GoesTo x mid stp) : m.GoesTo x start stp := by
  induction hb with
  | refl => exact ha
  | tail _ htail ih => exact ih.tail htail

theorem single {start stp : Config σ n} (hstep : m.nextConfig x start stp) : m.GoesTo x start stp :=
  tail refl hstep

@[match_pattern]
theorem head {start mid stp : Config σ n} (hstep : m.nextConfig x start mid) (htail : m.GoesTo x mid stp) :
    m.GoesTo x start stp := trans (single hstep) htail

@[elab_as_elim]
theorem head_induction_on {stp : Config σ n} {motive : ∀ c : Config σ n, m.GoesTo x c stp → Prop} {strt : Config σ n} (h : m.GoesTo x strt stp)
  (refl : motive stp .refl) (head : ∀ {c1 c2 : Config σ n} (hnext : m.nextConfig x c1 c2) (hrest : m.GoesTo x c2 stp), motive c2 hrest → motive c1 (hrest.head hnext)) :
    motive strt h := by
  induction h with
  | refl => exact refl
  | @tail mid stp _ tl ih =>
    apply ih
    · exact head tl _ refl
    · exact fun h1 h2 ↦ head h1 (h2.tail tl)

end GoesTo



def reaches (c : Config σ n) : Prop :=
  m.GoesTo x ⟨ m.start, 0 ⟩ c

def accepts : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ .accept, i ⟩

def rejects : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ .reject, i ⟩

def language (m : TwoDFA α σ) : Language α :=
  {x : List α | m.accepts x.toWord }


theorem accept_preserve_state (i : Fin (n+2)) (cfg : Config σ n) (h : m.GoesTo x ⟨ .accept, i ⟩ cfg) : cfg.state = .accept := by
  induction h with
  | refl => simp
  | @tail mid stp hd tl ih =>
    have mid_def : mid = ⟨.accept, mid.idx⟩ := by rw [←ih]
    cases hget : x.get mid.idx; all_goals
      conv at tl =>
        rw [mid_def, ←m.stepConfig_gives_nextConfig]
        simp only [stepConfig, step, hget]
        rw [Config.ext_iff]
      exact tl.left.symm

theorem reject_preserve_state (i : Fin (n+2)) (cfg : Config σ n) (h : m.GoesTo x ⟨.reject, i ⟩ cfg) : cfg.state = .reject := by
  induction h with
  | refl => simp
  | @tail mid stp hd tl ih =>
    have mid_def : mid = ⟨.reject, mid.idx⟩ := by rw [←ih]
    cases hget : x.get mid.idx; all_goals
      conv at tl =>
        rw [mid_def, ←m.stepConfig_gives_nextConfig]
        simp only [stepConfig, step, hget]
        rw [Config.ext_iff]
      exact tl.left.symm

theorem accept_move_right (i : Fin (n+2)) (hi : i ≠ Fin.last _) (cfg : Config σ n) (h : m.GoesTo x ⟨ .accept, i⟩ cfg) : i ≤ cfg.idx := by
  induction h with
  | refl => simp
  | @tail mid stp hd tl ih =>
    have mid_def : mid = ⟨.accept, mid.idx⟩ := by
      have := m.accept_preserve_state x i mid hd
      rw [←this]
    cases hget : x.get mid.idx;
    all_goals
      conv at tl =>
        rw [mid_def, ←m.stepConfig_gives_nextConfig]
        simp only [stepConfig, step, hget]
        rw [Config.ext_iff]
    case left | symbol =>
      apply ih.trans
      simp [←tl.right, Movement.apply, Fin.le_iff_val_le_val]
    case right =>
      have hmid : mid.idx = Fin.last _ := x.eq_last_of_get_eq_right hget
      have mid_ne_zero : mid.idx ≠ 0 := by simp [hmid]
      have hlt : i < mid.idx := by
        rw [←hmid] at hi
        simp [Fin.lt_iff_le_and_ne, hi, ih]
      rw [←Fin.le_castSucc_pred_iff mid_ne_zero] at hlt
      suffices (mid.idx.pred mid_ne_zero).castSucc = stp.idx by simpa [this] using hlt
      simp [←tl.right, Movement.apply, ←Fin.val_inj]

theorem reject_move_right (i : Fin (n+2)) (hi : i ≠ Fin.last _) (cfg : Config σ n) (h : m.GoesTo x ⟨.reject, i⟩ cfg) : i ≤ cfg.idx := by
  induction h with
  | refl => simp
  | @tail mid stp hd tl ih =>
    have mid_def : mid = ⟨.reject, mid.idx⟩ := by
      have := m.reject_preserve_state x i mid hd
      ext <;> simp [this]
    cases hget : x.get mid.idx
    all_goals
      conv at tl =>
        rw [mid_def, ←m.stepConfig_gives_nextConfig]
        simp only [stepConfig, step, hget]
        rw [Config.ext_iff]
    case left | symbol =>
      apply ih.trans
      simp [←tl.right, Movement.apply, Fin.le_iff_val_le_val]
    case right =>
      have hmid : mid.idx = Fin.last _ := x.eq_last_of_get_eq_right hget
      have mid_ne_zero : mid.idx ≠ 0 := by simp [hmid]
      have hlt : i < mid.idx := by
        rw [←hmid] at hi
        simp [Fin.lt_iff_le_and_ne, hi, ih]
      rw [←Fin.le_castSucc_pred_iff mid_ne_zero] at hlt
      suffices (mid.idx.pred mid_ne_zero).castSucc = stp.idx by simpa [this] using hlt
      simp [←tl.right, Movement.apply, ←Fin.val_inj]

theorem accept_lt_accept (i j : Fin (n+2)) (h : i < j) : m.GoesTo x ⟨ .accept, i ⟩ ⟨ .accept, j ⟩ := by
  cases ha : x.get i with
  | right =>
    rw [Word.eq_last_of_get_eq_right ha] at h
    suffices ¬ Fin.last (n+1) < j by contradiction
    simp [j.le_last]
  | left | symbol a =>
    clear ha
    have j_ne_zero : j ≠ 0 := Fin.ne_zero_of_lt h
    have left_isValid_j : Movement.left.isValid j := by constructor <;> simp [j_ne_zero]
    let prevIdx := Movement.left.apply j left_isValid_j
    apply GoesTo.tail
    · suffices m.GoesTo x ⟨ .accept, i ⟩ ⟨ .accept, prevIdx ⟩ from this
      if heq : prevIdx = i
        then rw [heq]
        else
          apply accept_lt_accept i prevIdx
          have prev_def : prevIdx = j.predCast j_ne_zero := rfl
          suffices i ≤ prevIdx by simpa [Fin.lt_iff_le_and_ne, heq, Ne.symm]
          rw [Fin.lt_def] at h
          have one_le_j : 1 ≤ j.val := by simpa using Fin.one_le_of_ne_zero j_ne_zero
          simpa [prev_def, Fin.le_def, Nat.le_sub_iff_add_le one_le_j]
    · have prevIdx_ne_last : prevIdx ≠ Fin.last (n+1) := by
        apply Fin.ne_of_lt
        have : prevIdx < j := Movement.lt_of_apply_left j
        apply Fin.lt_of_lt_of_le this
        exact j.le_last
      right
      · simp only
        suffices x.get prevIdx ≠ .right from m.accept_not_at_rightEnd this
        exact Word.get_neq_right_of_neq_last prevIdx_ne_last
      · exact Movement.left.opp_cancel_of_valid j left_isValid_j
  termination_by j
  decreasing_by all_goals {
    simp only [Fin.val_fin_lt]
    exact Movement.lt_of_apply_left j
  }

theorem reject_lt_reject (i j : Fin (n+2)) (h : i < j) : m.GoesTo x ⟨ .reject, i ⟩ ⟨ .reject, j ⟩ := by
  cases ha : x.get i with
  | right =>
    rw [Word.eq_last_of_get_eq_right ha] at h
    suffices ¬ Fin.last (n+1) < j by contradiction
    simp [j.le_last]
  | left | symbol a =>
    clear ha
    have j_ne_zero : j ≠ 0 := Fin.ne_zero_of_lt h
    have left_isValid_j : Movement.left.isValid j := by constructor <;> simp [j_ne_zero]
    let prevIdx := Movement.left.apply j left_isValid_j
    apply GoesTo.tail
    · suffices m.GoesTo x ⟨ .reject, i ⟩ ⟨ .reject, prevIdx ⟩ from this
      if heq : prevIdx = i
        then rw [heq]
        else
          apply reject_lt_reject i prevIdx
          have prev_def : prevIdx = j.predCast j_ne_zero := rfl
          suffices i ≤ prevIdx by simpa [Fin.lt_iff_le_and_ne, heq, Ne.symm]
          rw [Fin.lt_def] at h
          have one_le_j : 1 ≤ j.val := by
            suffices 1 ≤ j by simpa
            exact Fin.one_le_of_ne_zero j_ne_zero
          simpa [prev_def, Fin.le_def, Nat.le_sub_iff_add_le one_le_j]
    · have prevIdx_ne_last : prevIdx ≠ Fin.last (n+1) := by
        apply Fin.ne_of_lt
        have : prevIdx < j := Movement.lt_of_apply_left j
        apply Fin.lt_of_lt_of_le this
        exact j.le_last
      right
      · simp only
        suffices x.get prevIdx ≠ .right from m.reject_not_at_rightEnd this
        exact Word.get_neq_right_of_neq_last prevIdx_ne_last
      · exact Movement.left.opp_cancel_of_valid j left_isValid_j
  termination_by j
  decreasing_by all_goals {
    simp only [Fin.val_fin_lt]
    exact Movement.lt_of_apply_left j
  }


theorem reaches_accept_last_of_accepts (haccept : m.accepts x) : m.reaches x ⟨ .accept, Fin.last (n+1) ⟩ := by
  rcases haccept with ⟨idx, hidx⟩
  if h : idx = Fin.last (n+1)
    then rwa [← h]
    else
      unfold reaches
      trans
      · exact hidx
      · apply m.accept_lt_accept x idx (Fin.last _)
        exact Fin.lt_last_iff_ne_last.mpr h

theorem reaches_reject_last_of_rejects (hreject : m.rejects x) : m.reaches x ⟨ .reject, Fin.last (n+1) ⟩ := by
  rcases hreject with ⟨idx, hidx⟩
  if h : idx = Fin.last (n+1)
    then rwa [← h]
    else
      unfold reaches
      trans
      · exact hidx
      · apply m.reject_lt_reject x idx (Fin.last _)
        exact Fin.lt_last_iff_ne_last.mpr h


theorem single_path {strt stp1 stp2 : Config σ n} (h1 : m.GoesTo x strt stp1) (h2 : m.GoesTo x strt stp2) : m.GoesTo x stp1 stp2 ∨ m.GoesTo x stp2 stp1 := by
  induction h1 using GoesTo.head_induction_on with
  | refl => left; exact h2
  | @head strt1 mid1 hnext1 hrest1 ih1 =>
    induction h2 using GoesTo.head_induction_on with
    | refl => right; exact hrest1.head hnext1
    | @head strt2 mid2 hnext2 hrest2 _ =>
      suffices mid1 = mid2 by apply ih1; rwa [this]
      exact nextConfig_right_unique hnext1 hnext2

theorem not_accept_and_reject : ¬ (m.reaches x ⟨.accept, Fin.last _⟩ ∧ m.reaches x ⟨.reject, Fin.last _⟩) := by
  by_contra h
  cases m.single_path x h.left h.right with
  | inl h =>
    clear * - h
    have := m.accept_preserve_state x (Fin.last _) ⟨.reject, Fin.last _⟩ h
    simp at this
  | inr h =>
    clear * - h
    have := m.reject_preserve_state x (Fin.last _) ⟨.accept, Fin.last _⟩ h
    simp at this


def CyclesAt (c : Config σ n) : Prop :=
  ∃ last, m.GoesTo x c last ∧ m.nextConfig x last c

namespace CyclesAt

variable {m : TwoDFA α σ} {x : Word α n}

theorem as_head {c : Config σ n} (h : m.CyclesAt x c) : ∃ next, m.nextConfig x c next ∧ m.GoesTo x next c := by
  obtain ⟨last, path, link⟩ := h
  cases path using GoesTo.head_induction_on with
  | refl =>
    have := nextConfig.irrefl m x c
    contradiction  -- this ∧ link
  | @head _ c' hd tl ih =>
    clear ih
    use c'
    constructor
    · exact hd
    · exact tl.tail link

theorem step {c1 c2 : Config σ n} (cyc : m.CyclesAt x c1) (h : m.nextConfig x c1 c2) : m.CyclesAt x c2 := by
  obtain ⟨last, ⟨path, link⟩⟩ := cyc
  use c1
  constructor; swap
  · assumption
  · induction path using GoesTo.head_induction_on with
    | refl =>
      have := nextConfig.irrefl m x last
      contradiction
    | head hf tl _ =>
      rw [nextConfig_right_unique hf h] at tl
      exact tl.tail link

theorem transfer {c1 c2 : Config σ n} (cyc : m.CyclesAt x c1) (h : m.GoesTo x c1 c2) : m.CyclesAt x c2 := by
  induction h with
  | refl => assumption
  | tail _ tl ih => exact ih.step tl

theorem split {c1 c2 : Config σ n} (cyc : m.CyclesAt x c1) (h : m.GoesTo x c1 c2) : m.GoesTo x c2 c1 := by
  induction h using GoesTo.head_induction_on with
  | refl => exact .refl
  | head hd tl ih =>
    apply ih (cyc.step hd) |>.trans
    obtain ⟨_, link, path⟩ := cyc.as_head
    rwa [nextConfig_right_unique link hd] at path

end CyclesAt

abbrev diverges : Prop := ∃ q i, m.reaches x ⟨.other q, i⟩ ∧ m.CyclesAt x ⟨.other q, i⟩

theorem accept_all_cycles (hacc : m.accepts x) {c : Config σ n} (hreach : m.reaches x c) (hcyc : m.CyclesAt x c) : c.state = .accept := by
  obtain ⟨_, hacc⟩ := hacc
  rcases m.single_path x hacc hreach with h | h
  case' intro.inr => have h := hcyc.split h
  all_goals exact accept_preserve_state _ _ _ _ h

theorem reject_all_cycles (hrej : m.rejects x) {c : Config σ n} (hreach : m.reaches x c) (hcyc : m.CyclesAt x c) : c.state = .reject := by
  obtain ⟨_, hrej⟩ := hrej
  rcases m.single_path x hrej hreach with h | h
  case' intro.inr => have h := hcyc.split h
  all_goals exact reject_preserve_state _ _ _ _ h


section Runs

def Run : Type _ := Nat → Config σ n

def runOn : Run (σ := σ) (n := n)
  | 0 => m.init
  | n + 1 => m.stepConfig x <| runOn n

theorem runOn_step (k : Nat) : m.nextConfig x (m.runOn x k) (m.runOn x (k+1)) := by
  rw [←stepConfig_gives_nextConfig]
  conv => rhs; simp only [runOn]

theorem runOn_GoesTo (i k : Nat) : m.GoesTo x (m.runOn x i) (m.runOn x (i+k)) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    apply ih.tail
    apply runOn_step

theorem reaches_runOn (i : Nat) : m.reaches x (m.runOn x i) := by
  have := m.runOn_GoesTo x 0 i
  conv at this =>
    rw [zero_add]
    arg 3; simp only [runOn, init]
  assumption

theorem runOn_of_reaches (c : Config σ n) (h : m.reaches x c) : ∃ k, m.runOn x k = c := by
  induction h with
  | refl => exists 0
  | tail _ tl ih =>
    obtain ⟨k, hrun⟩ := ih
    use k+1
    apply nextConfig_right_unique _ tl
    rw [←hrun]
    apply runOn_step

theorem cycle_of_run_repeats (i k : Nat) (h1 : k ≠ 0) (h2 : m.runOn x i = m.runOn x (i+k)) : m.CyclesAt x (m.runOn x i) := by
  cases k with
  | zero => contradiction
  | succ k =>
    clear h1
    rw [←Nat.add_assoc] at h2
    use m.runOn x (i + k)
    constructor
    · apply runOn_GoesTo
    · rw [h2]
      apply runOn_step

theorem run_repeats_offset {step1 step2 off : Nat} (h : m.runOn x step1 = m.runOn x step2) : m.runOn x (step1 + off) = m.runOn x (step2 + off) := by
  induction off with
  | zero => exact h
  | succ off ih => simp [runOn, ih]

theorem run_repeats [fin_card : Fintype (Config σ n)] : ∃ i k : Nat, k ≠ 0 ∧ m.runOn x i = m.runOn x (i + k) := by
  obtain ⟨u, v, hne, hrep⟩ := Finite.exists_ne_map_eq_of_infinite (m.runOn x)
  rcases em (u < v) with hlt | hlt
  case' inl =>
    let a := u
    let b := v
    have hlt : a < b := hlt
    have hrep : m.runOn x a = m.runOn x b := hrep
  case' inr =>
    let a := v
    let b := u
    have hlt : a < b := by
      rcases Nat.lt_trichotomy u v with _ | _ | _
      · contradiction
      · contradiction
      · assumption
    have hrep : m.runOn x a = m.runOn x b := hrep.symm
  all_goals
    clear * - hlt hrep
    obtain ⟨k, hadd⟩ := Nat.exists_eq_add_of_lt hlt
    use a, (k+1)
    constructor
    · simp
    · simpa [hadd] using hrep

--- Every 2DFA will end up in a cycle on every input. The "halting" behaviour is actually entering the `accept_cycle` or the `reject_cycle`
theorem will_cycle [Fintype σ] : ∃ c, m.reaches x c ∧ m.CyclesAt x c := by
  obtain ⟨i, k, hne, hrep⟩ := m.run_repeats x
  use m.runOn x i
  constructor
  · apply reaches_runOn
  · exact m.cycle_of_run_repeats x _ _ hne hrep

end Runs

theorem divergence_iff [Fintype σ] : m.diverges x ↔ (¬m.accepts x ∧ ¬m.rejects x) where
  mp := by
    intro hdiv
    by_contra hterm
    rw [←not_or, not_not] at hterm
    obtain ⟨q, i, hreach, cyc⟩ := hdiv
    cases hterm with
    | inl hacc =>
      have := m.accept_all_cycles x hacc hreach cyc
      contradiction
    | inr hrej =>
      have := m.reject_all_cycles x hrej hreach cyc
      contradiction
  mpr := by
    rintro ⟨hacc, hrej⟩
    obtain ⟨⟨q, i⟩, hreach, hcyc⟩ := m.will_cycle x
    cases q with
    | other q => exact ⟨q, i, hreach, hcyc⟩
    | accept =>
      unfold TwoDFA.accepts at hacc
      absurd hacc; use i
    | reject =>
      unfold TwoDFA.rejects at hrej
      absurd hrej; use i

end TwoDFA
