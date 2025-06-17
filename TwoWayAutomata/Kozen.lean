/-
# Kozen 2DFAs

An implementation of Two-way Deterministic Finite Automata ready to follow the proof of their regularity due to Kozen.
-/ -- TODO: add reference.
import Mathlib.Logic.Relation
import Mathlib.Computability.Language

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Word

universe u v

abbrev Fin.predCast {n : Nat} (i : Fin (n + 1)) (h : i ≠ 0) : Fin (n + 1) := 
  have prf : (i.pred h).val < n + 1 := by
    simp
    suffices i.val - 1 < i.val from Nat.lt_trans this i.is_lt
    apply Nat.sub_lt_of_pos_le <| by simp
    suffices 0 < i.val from this
    cases hv : i.val with
    | zero => rw [← Fin.val_ne_iff, Fin.val_zero] at h
              contradiction
    | succ n => exact Nat.succ_pos n
  i.pred h |>.castLT prf


theorem TwoDFA.accept_at_leftEnd {α : Type u} {σ : Type v} (m : TwoDFA α σ) : m.step .left m.accept = (m.accept, .right) := by
  have hinBounds := m.in_bounds_left m.accept
  have hpreserve := m.halt_preserve_state .left
  cases hinBounds with
  | intro wBounds hBounds => cases hpreserve.left with
                             | intro wPres hPres => rw [hBounds, Prod.ext_iff] at hPres
                                                    simp only at hPres
                                                    rw [hPres.left] at hBounds
                                                    exact hBounds

theorem TwoDFA.accept_not_at_rightEnd {α : Type u} {σ : Type v} (m : TwoDFA α σ) {a : TapeSymbol α} (h : a ≠ .right) : m.step a m.accept = (m.accept, .right) := by
  cases a with
  | left => exact m.accept_at_leftEnd
  | right => contradiction
  | symbol a => exact m.halt_move_right a |>.left

theorem TwoDFA.reject_at_leftEnd {α : Type u} {σ : Type v} (m : TwoDFA α σ) : m.step .left m.reject = (m.reject, .right) := by
  have hinBounds := m.in_bounds_left m.reject
  have hpreserve := m.halt_preserve_state .left
  cases hinBounds with
  | intro wBounds hBounds => cases hpreserve.right with
                             | intro wPres hPres => rw [hBounds, Prod.ext_iff] at hPres
                                                    simp only at hPres
                                                    rw [hPres.left] at hBounds
                                                    exact hBounds

theorem TwoDFA.reject_not_at_rightEnd {α : Type u} {σ : Type v} (m : TwoDFA α σ) {a : TapeSymbol α} (h : a ≠ .right) : m.step a m.reject = (m.reject, .right) := by
  cases a with
  | left => exact m.reject_at_leftEnd
  | right => contradiction
  | symbol a => exact m.halt_move_right a |>.right

section Evaluation

section ValidMovement

structure Movement.isValid {n : Nat} (move : Movement) (i : Fin (n+2)) : Prop where
  hleft : ¬ (i = 0 ∧ move = .left)
  hright : ¬ (i = Fin.last (n+1) ∧ move = .right)

theorem Movement.one_le_of_left_isValid {n : Nat} (i : Fin (n+2)) (h : Movement.left.isValid i) : 1 ≤ i := by
  have := h.hleft
  apply i.one_le_of_ne_zero
  simp at this
  exact this

def Movement.apply {n : Nat} (move : Movement) (i : Fin (n+2)) (hvalid : move.isValid i) : Fin (n+2) :=
  match hm : move with
  | .left => i.predCast <| by
               have h := hvalid.hleft
               simp at h
               assumption
  | .right => let j := i.succ
              j.castLT <| by
                rw [Fin.val_succ i]
                have : i.val < n+1 := by 
                  apply Fin.val_lt_last
                  have h := hvalid.hright
                  simp at h
                  assumption
                simp [this]

theorem Movement.isValid_castLE {n m : Nat} (move : Movement) (i : Fin (n+2)) {valid : move.isValid i} (h : n+2 ≤ m+2) :
    move.isValid (i.castLE h) := by
  constructor
  · rw [← Fin.castLE_zero h, Fin.castLE_inj]
    exact valid.hleft
  · cases move
    · simp only [reduceCtorEq, and_false, not_false_eq_true]
    · simp only [and_true]
      rw [Fin.ext_iff]
      simp only [Fin.coe_castLE, Fin.val_last, ne_eq]
      rw [add_le_add_iff_right] at h
      apply Nat.ne_of_lt
      apply Nat.lt_of_lt_of_le
      · have ne_last_n := valid.hright
        simp only [and_true] at ne_last_n
        exact Fin.val_lt_last ne_last_n
      · rwa [add_le_add_iff_right]

theorem Movement.isValid_castLE_of_lt_of_ne_0 {n m : Nat} (move : Movement) (i : Fin (n+2)) (hlt : n+2 < m+2) (hne : i ≠ 0) :
    move.isValid (i.castLE <| le_of_lt hlt) := by
  have hle := le_of_lt hlt
  constructor
  · rw [← Fin.castLE_zero hle, Fin.castLE_inj]
    simp only [hne, false_and, not_false_eq_true]
  · suffices (i.castLE hle) ≠ Fin.last (m+1) by simp only [this, false_and, not_false_eq_true]
    rw [← Fin.val_ne_iff]
    simp only [Fin.coe_castLE, Fin.val_last, ne_eq]
    apply Nat.ne_of_lt
    apply Nat.lt_of_le_of_lt
    · exact i.le_last
    · rw [add_lt_add_iff_right] at hlt
      simpa

theorem Movement.isValid_of_apply {n : Nat} (move : Movement) (i j : Fin (n+2)) {valid : move.isValid i} (_ : move.apply i valid = j) :
    move.isValid i := valid

theorem Movement.apply_left_ne_last {n : Nat} (i : Fin (n+2)) {valid : Movement.left.isValid i} : Movement.left.apply i valid ≠ Fin.last (n+1) := by
  apply Fin.ne_of_lt
  simp [Movement.apply, Fin.lt_def]
  have : n + 1 = (n + 2) - 1 := by simp
  conv => rhs; rw [this, Nat.sub_one]
  rw [Nat.sub_one]
  apply Nat.pred_lt_pred
  · have := valid.hleft
    simp at this
    rw [Fin.ext_iff, Fin.val_zero] at this
    assumption
  · exact i.is_lt

theorem Movement.apply_right_ne_zero {n : Nat} (i : Fin (n+2)) {valid : Movement.right.isValid i} : Movement.right.apply i valid ≠ 0 := by
  apply Fin.ne_of_gt
  simp only [Movement.apply, Fin.lt_def, Fin.castLT, Fin.val_succ]
  simp

theorem Movement.isValid_opp_apply_of_isValid {n : Nat} (move : Movement) (i : Fin (n+2)) (valid : move.isValid i) :
    move.opp.isValid (move.apply i valid) := by
  unfold Movement.opp
  constructor
  · cases move
    · simp
    · simp
      exact Movement.apply_right_ne_zero i
  · cases move
    · simp
      exact Movement.apply_left_ne_last i
    · simp

theorem Movement.opp_cancel_of_valid {n : Nat} (i : Fin (n+2)) (move : Movement) (valid : move.isValid i) :
    move.opp.apply (move.apply i valid) (move.isValid_opp_apply_of_isValid i valid) = i := by
  unfold Movement.apply
  unfold Movement.opp
  cases move
  <;> simp only [Fin.ext_iff, Fin.coe_castLT, Fin.val_succ, Fin.coe_pred]
  · rw [Nat.add_comm]
    apply Nat.add_sub_cancel'
    cases h : i.val with
    | zero => have := valid.hleft
              simp at this
              rw [Fin.ext_iff, Fin.val_zero] at this
              contradiction
    | succ n => apply Nat.succ_le_succ
                exact Nat.zero_le n
  · apply Nat.add_one_sub_one

theorem Movement.ne_zero_of_left_isValid {n : Nat} (i : Fin (n+2)) (valid : Movement.left.isValid i) : i ≠ 0 := by
  have := valid.hleft
  simp at this
  assumption

theorem Movement.lt_of_apply_left {n : Nat} (i : Fin (n+2)) {valid : Movement.left.isValid i} :
    Movement.left.apply i valid < i := by
  unfold Movement.apply
  simp [Fin.lt_def]
  apply Nat.sub_lt_of_pos_le <| by simp
  exact Movement.one_le_of_left_isValid i valid


theorem TwoDFA.step_move_always_valid {α : Type u} {σ : Type v} (m : TwoDFA α σ) {n : Nat} {x : Word α n}
     {i : Fin (n+2)} {move : Movement} {s t : σ} (h : m.step (x.get i) s = ⟨ t, move ⟩) : move.isValid i := by
  constructor
  · if hz : i = 0
      then
        simp [hz]
        rw [← x.get_eq_left_iff_eq_0] at hz
        rw [hz] at h
        cases m.in_bounds_left s with
        | intro a ha => have : move = .right := by
                          simp [h, Prod.ext_iff] at ha
                          exact ha.right
                        simp [this]
      else simp [hz]
  · if hl : i = Fin.last (n+1)
      then
        simp [hl]
        rw [x.get_eq_right_iff_eq_last] at hl
        rw [hl] at h
        cases m.in_bounds_right s with
        | intro a ha => have : move = .left := by
                          simp [h, Prod.ext_iff] at ha
                          exact ha.right
                        simp [this]
      else simp [hl]
      
end ValidMovement

section Configurations

variable {α : Type u} {σ : Type v} (m : TwoDFA α σ)

@[ext]
structure TwoDFA.Config (σ : Type v) (n : Nat) where
  state : σ
  idx : Fin (n + 2)

deriving instance DecidableEq for TwoDFA.Config

@[simp]
def TwoDFA.Config.castLE {σ : Type v} {n m : Nat} (h : n ≤ m) (c : Config σ n) : Config σ m where
  state := c.state
  idx := c.idx.castLE <| by rw [add_le_add_iff_right]; exact h

variable {n : Nat} (x : Word α n) 

def TwoDFA.stepConfig : Config σ n → Config σ n
  | ⟨ state, idx ⟩ => match hstep : m.step (x.get idx) state with
                      | ⟨ nextState, move ⟩ =>
                        let hvalid : move.isValid idx := m.step_move_always_valid hstep
                        ⟨ nextState, move.apply idx hvalid ⟩

inductive TwoDFA.nextConfig (c1 c2 : Config σ n) : Prop where
  | stepLeft : m.step (x.get c1.idx) c1.state = (c2.state, .left) →
               (hvalid : Movement.left.isValid c1.idx) →
               (happly : Movement.left.apply c1.idx hvalid = c2.idx) →
             nextConfig c1 c2
  | stepRight : m.step (x.get c1.idx) c1.state = (c2.state, .right) →
                (hvalid : Movement.right.isValid c1.idx) →
                (happly : Movement.right.apply c1.idx hvalid = c2.idx) →
              nextConfig c1 c2

theorem TwoDFA.stepConfig_gives_nextConfig (c1 c2 : Config σ n) : m.stepConfig x c1 = c2 ↔ m.nextConfig x c1 c2 where
  mp := by
    intro h 
    cases hstep : m.step (x.get c1.idx) c1.state with
    | mk t move => simp [hstep, stepConfig, Config.ext_iff] at h
                   cases hmove : move
                   · left
                     · rw [← h.left, ← hmove]
                       assumption
                     · rw [← h.right]
                       ext
                       simp only [hmove]
                     · rw [← hmove]
                       exact move.isValid_of_apply c1.idx c2.idx h.right
                   · right
                     · rw [← h.left, ← hmove]
                       assumption
                     · rw [← h.right]
                       ext
                       simp only [hmove]
                     · rw [← hmove]
                       exact move.isValid_of_apply c1.idx c2.idx h.right
  mpr := by
    intro h
    cases h with
    | stepLeft hstep hvalid happly => simp [stepConfig, hstep, hvalid]
                                      ext
                                      · simp only
                                      · simp only [happly]
    | stepRight hstep hvalid happly => simp [stepConfig, hstep, hvalid]
                                       ext
                                       · simp only
                                       · simp only [happly]

theorem TwoDFA.nextConfig.push_lt {c1 c2 : Config σ n} (a : α) (hnext : m.nextConfig x c1 c2) (hlt : c1.idx < Fin.last (n+1)) :
    m.nextConfig (x.push a) (c1.castLE <| by simp) (c2.castLE <| by simp) := by
  have get_same : x.get c1.idx = (x.push a).get (c1.castLE <| by simp).idx := by
    have := x.get_push_lt a c1.idx hlt
    rw [this]
    simp only [Config.castLE]
  cases hnext with
  | stepLeft hstep hvalid happly =>
    left
    · rw [← get_same]
      simp only [Config.castLE]
      exact hstep
    · simp [Movement.apply, Fin.predCast, Fin.ext_iff] at *
      exact happly
    · apply Movement.isValid_castLE (valid := hvalid)
      simp
  | stepRight hstep hvalid happly =>
    right
    · rw [← get_same]
      simp only [Config.castLE]
      exact hstep
    · simp [Movement.apply, Fin.predCast, Fin.ext_iff] at *
      exact happly
    · apply Movement.isValid_castLE (valid := hvalid)
      simp

theorem TwoDFA.nextConfig.push_eq (c1 : Config σ n) (c2 : Config σ (n+1)) {move : Movement} (a : α) (heq : c1.idx = Fin.last (n+1)) 
    (hstep : m.step a c1.state = ⟨c2.state, move⟩)
    (hmove : move.apply
               (c1.idx.castLE <| by simp)
               (move.isValid_castLE_of_lt_of_ne_0 c1.idx (by simp) (by simp [heq]))
             = c2.idx) :
    m.nextConfig (x.push a) (c1.castLE <| by simp) c2 := by
  have get_pushed : (x.push a).get (c1.castLE <| by simp).idx = a := x.get_push_eq a c1.idx heq
  have hvalid := move.isValid_castLE_of_lt_of_ne_0 c1.idx (by simp : n + 2 < n+3) (by simp [heq])
  cases move
  · left
    · rw [get_pushed]
      simpa only [Config.castLE]
    · suffices Movement.left.apply (c1.castLE <| by simp).idx hvalid = c2.idx from this
      exact hmove
  · right
    · rw [get_pushed]
      simpa only [Config.castLE]
    · suffices Movement.right.apply (c1.castLE <| by simp).idx hvalid = c2.idx from this
      exact hmove

end Configurations

section Runs

variable {α : Type u} {σ : Type v} (m : TwoDFA α σ) {n : Nat} (x : Word α n) 

inductive TwoDFA.Run (start : Config σ n) : Config σ n → Type v
  | start : Run start start
  | step : (current next : Config σ n) → (head : Run start current) → (hstep : m.nextConfig x current next) → Run start next

inductive TwoDFA.RunLeftOf (k : Fin (n+2)) (start : Config σ n) : Config σ n → Type v
  | start : (hleft : start.idx ≤ k) → RunLeftOf k start start
  | step : (current next : Config σ n) → (head : RunLeftOf k start current) → (hstep : m.nextConfig x current next) → (hleft : next.idx ≤ k) → RunLeftOf k start next

/--
Extract the prefix of a run which only uses configurations left of index `k`
-/
def TwoDFA.Run.leftOf [DecidableEq σ] {start current : Config σ n} (k : Fin (n+2)) (h : start.idx ≤ k) : m.Run x start current → Σ stop : Config σ n, m.RunLeftOf x k start stop 
  | .start => ⟨start, TwoDFA.RunLeftOf.start h⟩
  | .step current next head hstep => 
    let newHead := head.leftOf k h
    if can_continue : newHead.1 = current ∧ next.idx ≤ k
      then 
        have ⟨hcont, hleft⟩ := can_continue
        ⟨next, TwoDFA.RunLeftOf.step current next (by rw [←hcont]; exact newHead.2) hstep hleft⟩
      else newHead

def TwoDFA.RunLeftOf.forget {start current : Config σ n} {k : Fin (n+2)} : m.RunLeftOf x k start current → m.Run x start current
  | .start _ => .start
  | .step current next head hstep _ => .step current next (head.forget) hstep

end Runs


variable {α : Type u} {σ : Type v} (m : TwoDFA α σ) {n : Nat} (x : Word α n) 

/--
After some number of steps, the machine m on input x will go from configuration start to the input configuration.
-/
inductive TwoDFA.GoesTo (start : Config σ n) : Config σ n → Prop
  | refl : GoesTo start start
  | tail {mid stop : Config σ n} (head : GoesTo start mid) (tail : m.nextConfig x mid stop) : GoesTo start stop

theorem TwoDFA.GoesTo.trans {start mid stop : Config σ n} (ha : m.GoesTo x start mid) (hb : m.GoesTo x mid stop) : m.GoesTo x start stop := by
  induction hb with
  | refl => exact ha
  | tail _ htail ih => exact ih.tail htail

def TwoDFA.GoesTo.single {start stop : Config σ n} (hstep : m.nextConfig x start stop) : m.GoesTo x start stop :=
  .tail .refl hstep

def TwoDFA.GoesTo.head {start mid stop : Config σ n} (hstep : m.nextConfig x start mid) (htail : m.GoesTo x mid stop) :
    m.GoesTo x start stop := .trans m x (.single m x hstep) htail

/--
After some number of steps *which stay to the left of stop.idx*, the machine m on input x will go from configuration start to stop.
-/
inductive TwoDFA.GoesToFromLeft (start : Config σ n) : Config σ n → Prop
  | refl : GoesToFromLeft start start
  | tail {mid stop : Config σ n} (head : GoesToFromLeft start mid) (tail : m.nextConfig x mid stop) (h : mid.idx < stop.idx) : GoesToFromLeft start stop

def TwoDFA.GoesToFromLeft.cast {start stop : Config σ n} (h : m.GoesToFromLeft x start stop) : m.GoesTo x start stop := by
  induction h with
  | refl => exact .refl
  | tail _ htail h ih => exact ih.tail htail

def TwoDFA.GoesToFromLeft.trans {start mid stop : Config σ n} (ha : m.GoesToFromLeft x start mid) (hb : m.GoesToFromLeft x mid stop) : m.GoesToFromLeft x start stop := by
  induction hb with
  | refl => exact ha
  | tail _ htail h ih => exact ih.tail htail h

def TwoDFA.GoesToFromLeft.single {start stop : Config σ n} (hstep : m.nextConfig x start stop) (h : start.idx < stop.idx) : m.GoesToFromLeft x start stop :=
  .tail .refl hstep h

theorem TwoDFA.GoesToFromLeft.push {start stop : Config σ n} (a : α) (h : m.GoesToFromLeft x start stop) :
    m.GoesToFromLeft (x.push a) (start.castLE <| by simp) (stop.castLE <| by simp) := by
  induction h with
  | refl => exact .refl
  | tail _ htail h ih =>
    rename Config σ n => stop2
    apply ih.tail
    · apply TwoDFA.nextConfig.push_lt m x a htail 
      apply Fin.lt_of_lt_of_le
      · exact h
      · exact stop2.idx.le_last
    · simp only [Config.castLE, Fin.castLE_lt_castLE_iff]
      exact h


def TwoDFA.reaches (c : Config σ n) : Prop :=
  m.GoesTo x ⟨ m.start, 0 ⟩ c

def TwoDFA.accepts : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ m.accept, i ⟩

def TwoDFA.rejects : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ m.reject, i ⟩
            
def TwoDFA.language (m : TwoDFA α σ) : Language α :=
  {x : List α | m.accepts x.toWord }

theorem TwoDFA.accept_lt_accept (i j : Fin (n+2)) (h : i < j) : m.GoesTo x ⟨ m.accept, i ⟩ ⟨ m.accept, j ⟩ := by
  have j_ne_zero : j ≠ 0 := by
    apply Fin.ne_of_gt
    apply Fin.lt_of_le_of_lt
    · exact Fin.zero_le i
    · exact h
  have one_le_j : 1 ≤ j.val := by
    suffices 1 ≤ j by simp [Fin.le_def] at this; assumption
    exact j.one_le_of_ne_zero j_ne_zero
  cases ha : x.get i with
  | right =>
    have := Word.eq_last_of_get_eq_right ha
    rw [this] at h
    suffices ¬ Fin.last (n+1) < j by contradiction
    rw [Fin.not_lt]
    exact j.le_last
  | left | symbol a =>
    clear ha
    have left_isValid_j : Movement.left.isValid j := by constructor <;> simp [j_ne_zero]
    let prevIdx := Movement.left.apply j left_isValid_j
    apply GoesTo.tail
    · suffices m.GoesTo x ⟨ m.accept, i ⟩ ⟨ m.accept, prevIdx ⟩ from this
      if heq : prevIdx = i
        then
          rw [heq]
          exact .refl
        else
          apply accept_lt_accept i prevIdx
          have prev_def : prevIdx = j.predCast j_ne_zero := by rfl
          suffices i ≤ prevIdx by simp [Fin.lt_iff_le_and_ne, this, heq, Ne.intro, Ne.symm]
          rw [Fin.lt_def] at h
          simp [prev_def, Fin.le_def, Nat.le_sub_iff_add_le one_le_j]
          assumption
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


theorem TwoDFA.reaches_accept_last_of_accepts (haccept : m.accepts x) : m.reaches x ⟨ m.accept, Fin.last (n+1) ⟩ := by
  cases haccept with
  | intro idx hidx =>
    if h : idx = Fin.last (n+1)
      then rw [← h]; assumption
      else
        apply GoesTo.trans m x hidx
        apply m.accept_lt_accept x idx (Fin.last (n+1))
        cases Fin.lt_or_eq_of_le <| Fin.le_last idx
        · assumption
        · contradiction

end Evaluation

section example2DFA

def tripleZeros (x : List (Fin 2)) : Prop := (x.count 0) % 3 = 0
def evenOnes (x : List (Fin 2)) : Prop := (x.count 1) % 2 = 0

def exampleLanguage : Language (Fin 2) := 
  { x : List (Fin 2) | tripleZeros x ∧ evenOnes x }


inductive ExampleState : Type where
  | q : Fin 3 → ExampleState
  | p : Fin 2 → ExampleState
  | t : ExampleState
  | r : ExampleState

theorem fin2_lt_2 (j : Fin 2) : j = 0 ∨ j = 1 := by
  cases h : j.val with
  | zero => left
            apply Fin.ext
            exact h
  | succ n => right
              apply Fin.ext
              suffices h2 : n = 0 by simp [h, h2]
              have : n + 1 < 2 := by
                have isLt := j.isLt
                rw [h] at isLt
                exact isLt
              cases this with
              | refl => rfl
              | step hlt => simp at hlt

theorem fin3_lt_3 (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := 
  match j with
  | ⟨ val, isLt ⟩ => by
    cases isLt with
    | refl => right; right; simp
    | step hp => simp at hp
                 cases hp with
                 | refl => right; left; simp
                 | step hp => have : val = 0 := Nat.eq_zero_of_le_zero hp
                              left
                              simp [this]

def exampleStep (a : TapeSymbol <| Fin 2) (s : ExampleState) : ExampleState × Movement :=
  match s, a with
  | .t, .right => (ExampleState.t, Movement.left)
  | .t, _ => (ExampleState.t, Movement.right)
  | .r, .right => (ExampleState.r, Movement.left)
  | .r, _ => (ExampleState.r, Movement.right)
  | .q i, .symbol 0 => (ExampleState.q (i+1), Movement.right)
  | .q 0, .right => (ExampleState.p 0, Movement.left)
  | .q _, .right => (ExampleState.r, Movement.left)
  | .q i, _ => (ExampleState.q i, Movement.right)
  | .p j, .symbol 1 => (ExampleState.p (j+1), Movement.left)
  | .p 0, .left => (ExampleState.t, Movement.right)
  | .p 1, .left => (ExampleState.r, Movement.right)
  | .p j, _ => (ExampleState.p j, Movement.left)

/-- A 2DFA which identifies strings of {0, 1} where the number of 0s is divisible by 3 and the number of 1s is divisible by 2 -/
def example2DFA : TwoDFA (Fin 2) ExampleState where
  start := ExampleState.q 0
  accept := ExampleState.t
  reject := ExampleState.r
  distinct_tr := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  step := exampleStep
  in_bounds_left := by
    intro q
    cases q with
    | p j => apply Or.elim (fin2_lt_2 j)
             · intro h
               simp [h, exampleStep]
             · intro h
               simp [h, exampleStep]
    | _ => simp [exampleStep]
  in_bounds_right := by
    intro q
    cases q with
    | q j => apply Or.elim (fin3_lt_3 j)
             · intro h
               simp [h, exampleStep]
             · intro h
               apply Or.elim h
               · intro h
                 simp [h, exampleStep]
               · intro h
                 simp [h, exampleStep]
    | _ => simp [exampleStep]
  halt_move_right := by
    intro a
    simp only [exampleStep, and_self]
  halt_preserve_state := by
    intro a
    cases a with
    | right => apply And.intro <;>
                 apply Exists.intro Movement.left <;>
                   rfl
    | _ => apply And.intro <;>
             apply Exists.intro Movement.right <;>
               rfl

def Word.count {α : Type u} [BEq α] {n : Nat} (w : Word α n) (x : α) : Nat := w.val.count x

theorem word_count_eq_list_count {α : Type u} [BEq α] (w : List α) (x : α) : w.toWord.count x = w.count x := by
  simp [Word.count, List.toWord]

theorem Word.count_nil {α : Type u} [BEq α] (x : α) : Word.nil.count x = 0 := by
  simp only [count, nil, Vector.count_mk, List.count_toArray, List.count_nil]

theorem Word.count_push_eq {α : Type u} [BEq α] [ReflBEq α] {n : Nat} (w : Word α n) (x : α) : (w.push x).count x = (w.count x) + 1 := by
  simp only [count, push, Vector.count_push, BEq.refl, ite_true]

theorem Word.count_push_ne {α : Type u} [BEq α] [LawfulBEq α] {n : Nat} (w : Word α n) (x y : α) (h : x ≠ y) : (w.push y).count x = w.count x := by
  simp only [count, push]
  exact Vector.count_push_of_ne h.symm

theorem example_zeros_count {n : Nat} (w : Word (Fin 2) n) (i : Fin 3) :
    example2DFA.GoesToFromLeft w ⟨ .q i, 0 ⟩ ⟨ .q (i + w.count 0), Fin.last (n + 1) ⟩ := by
  induction w using Word.inductionPush with
  | hnil =>
    rw [Word.count_nil]
    have : i + ↑(0 : Nat) = i := by
      simp only [Nat.cast, Fin.isValue, Fin.natCast_eq_zero, Nat.dvd_zero]
      exact Fin.add_zero i
    simp only [Fin.isValue, Nat.reduceAdd, Fin.reduceLast, this]
    clear this
    apply TwoDFA.GoesToFromLeft.single example2DFA Word.nil
    · suffices example2DFA.step (Word.nil.get 0) (.q i) = (.q i, .right) by
        right
        · exact this
        · simp [Movement.apply]
        · exact example2DFA.step_move_always_valid this
      have : Word.nil.get 0 = .left (α := Fin 2) := Word.get_eq_left_of_eq_zero <| .refl 0
      simp only [example2DFA, Fin.isValue, exampleStep, this]
    · simp
  | hpush a w hind =>
    rename Nat => k  -- Implicit argument renamed separately
    apply TwoDFA.GoesToFromLeft.tail
    · have := TwoDFA.GoesToFromLeft.push example2DFA w a hind
      simp at this
      exact this
    · let c1 : TwoDFA.Config ExampleState k := ⟨ .q (i + w.count 0), Fin.last (k+1) ⟩
      let c2 : TwoDFA.Config ExampleState (k+1) := ⟨ .q (i + (w.push a).count 0), Fin.last (k+2) ⟩
      have heq : c1.idx = Fin.last (k+1) := .refl c1.idx
      have hstep : example2DFA.step a c1.state = ⟨c2.state, .right⟩ := by
        cases a using Fin.cases with
        | zero => simp [example2DFA, exampleStep, c1, c2, Word.count_push_eq, Fin.ext_iff, Fin.val_add, add_assoc]
        | succ i' => simp [Fin.fin_one_eq_zero i', example2DFA, exampleStep, c1, c2, Word.count_push_ne]
      have hmove : Movement.right.apply (c1.idx.castLE <| by simp) (Movement.right.isValid_castLE_of_lt_of_ne_0 c1.idx (by simp) (by simp [heq])) = c2.idx := by
        simp [c1, c2, Movement.apply, Fin.castLE, Fin.last]
      exact TwoDFA.nextConfig.push_eq example2DFA w c1 c2 a heq hstep hmove
    · simp [Fin.lt_def]

theorem example_ones_count {n : Nat} (w : Word (Fin 2) n) (i : Fin 2) :
    example2DFA.GoesTo w ⟨ .p i, n ⟩ ⟨ .p (i + w.count 1), 0 ⟩ := by
  induction w using Word.inductionPush with
  | hnil =>
    rw [Word.count_nil]
    have : i + ↑(0 : Nat) = i := by
      simp only [Nat.cast, Fin.isValue, Fin.natCast_eq_zero, Nat.dvd_zero]
      exact Fin.add_zero i
    simp only [Nat.reduceAdd, this, Fin.isValue]
    exact .refl
  | hpush a w hind =>
    rename Nat => k
    cases a using Fin.cases with
    | zero =>
      sorry
    | succ a =>
      have a_eq_0 : a = 0 := Fin.fin_one_eq_zero a
      simp [a_eq_0, Word.count_push_eq]
      sorry

theorem Fin.mod_n_of_ofNat' (n k : Nat) [neZero : NeZero n] :
    Fin.ofNat' n k = ⟨ k % n, Nat.mod_lt k neZero.pos ⟩ := by rfl

theorem example_on_triple_zeros {w : List (Fin 2)} (h : tripleZeros w) :
    example2DFA.GoesToFromLeft w.toWord ⟨ .q 0, 0 ⟩ ⟨ .q 0, Fin.last (w.length + 1) ⟩ := by
  have h2 := example_zeros_count w.toWord 0
  have : (w.toWord.count 0 : Fin 3) = ⟨ (w.toWord.count 0) % 3, _ ⟩ := Fin.mod_n_of_ofNat' 3 <| w.toWord.count 0
  rw [this] at h2; clear this
  have : w.toWord.count 0 = w.count 0 := word_count_eq_list_count w 0
  rw [this] at h2; clear this
  conv at h2 =>
    pattern List.count 0 w % 3
    rw [h]
  exact h2

theorem example_on_even_ones {w : List (Fin 2)} (h : evenOnes w) :
    example2DFA.GoesTo w.toWord ⟨ .p 0, w.length ⟩ ⟨ .p 0, 0 ⟩ := by
  have h2 := example_ones_count w.toWord 0
  have : (w.toWord.count 1 : Fin 2) = ⟨ (w.toWord.count 1) % 2, _ ⟩ := Fin.mod_n_of_ofNat' 2 <| w.toWord.count 1
  rw [this] at h2; clear this
  have : w.toWord.count 1 = w.count 1 := word_count_eq_list_count w 1
  rw [this] at h2; clear this
  conv at h2 =>
    pattern List.count 1 w % 2
    rw [h]
  exact h2

theorem exampleAcceptsLanguage : example2DFA.language = exampleLanguage := by
  ext
  rename List (Fin 2) => w
  unfold exampleLanguage
  unfold TwoDFA.language
  rw [Set.mem_def, Set.mem_def, Set.setOf_app_iff, Set.setOf_app_iff]
  constructor

  -- example2DFA.accepts w → w ∈ exampleLanguage
  · intro h
    sorry

  -- w ∈ exampleLanguage → example2DFA.accepts w
  · intro h
    have ⟨ hzeros, hones ⟩ := h

    have zeros_pass := example_on_triple_zeros hzeros |>.cast

    have turn_around : example2DFA.GoesTo w.toWord ⟨ .q 0, Fin.last (w.length + 1) ⟩ ⟨ .p 0, w.length ⟩ := by
      apply TwoDFA.GoesTo.single example2DFA w.toWord
      have hvalid : Movement.left.isValid <| Fin.last (w.length + 1) := by constructor <;> simp
      left
      · have := w.toWord.get_eq_right_of_eq_last (i := Fin.last (w.length + 1)) <| by rfl
        simp [this, example2DFA, exampleStep]
      · suffices Movement.left.apply (Fin.last (w.length + 1)) hvalid = w.length from this
        simp [Movement.apply, Fin.predCast, Fin.pred_last, Fin.ext_iff]
        symm
        apply Nat.mod_eq_of_lt
        apply Nat.lt_add_right 1
        simp

    have ones_pass := example_on_even_ones hones

    have accept_at_left : example2DFA.nextConfig w.toWord ⟨ .p 0, 0 ⟩ ⟨ .t, 1 ⟩ := by
      have hvalid : Movement.right.isValid (0 : Fin (w.length + 2)) := by constructor <;> simp
      right
      · have := w.toWord.get_eq_left_of_eq_zero <| by rfl
        simp [this, example2DFA, exampleStep]
      · suffices Movement.right.apply 0 hvalid = 1 from this
        simp [Movement.apply, Fin.castLT]

    apply Exists.intro 1
    apply TwoDFA.GoesTo.trans example2DFA w.toWord zeros_pass
    apply TwoDFA.GoesTo.trans example2DFA w.toWord turn_around
    apply TwoDFA.GoesTo.trans example2DFA w.toWord ones_pass
    exact TwoDFA.GoesTo.single example2DFA w.toWord accept_at_left

end example2DFA
