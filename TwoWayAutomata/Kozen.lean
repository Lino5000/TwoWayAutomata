/-
# Kozen 2DFAs

An implementation of Two-way Deterministic Finite Automata ready to follow the proof of their regularity due to Kozen.
-/ -- TODO: add reference.
import Mathlib.Logic.Relation
import Mathlib.Computability.Language
import Mathlib.Algebra.Group.Fin.Basic

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Word

universe u v

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

theorem exampleZerosPass_ofCount {n : Nat} (hn : n ≠ 0) (i : Fin (n+2)) (h : i ≠ 0) (w : Word (Fin 2) n) (j : Fin 3) (hcount : (w.split i h).fst.count 0 % 3 = j) :
    example2DFA.GoesTo w ⟨example2DFA.start, 0⟩ ⟨.q j, i.castLE <| by simp⟩ := by
  let pi := i.pred h
  let piCast : Fin (n+2) := pi.castLE <| by simp
  cases ha : w.get piCast with
  | left =>
    simp only [Fin.castLE, Word.get_eq_left_iff_eq_0, Fin.mk_eq_zero] at ha
    have : pi.succ = 1 := by
      conv at ha =>
        unfold piCast
        rw [←Fin.val_inj]
        simp only [Fin.coe_castLE, Fin.val_zero, Fin.val_eq_zero_iff]
      simp [ha]
    simp only [Fin.castLE, this, Fin.val_one']
    have hi : i = 1 := by simp [pi] at this; assumption
    simp only [hi, Fin.val_one, Fin.mk_one]
    have hj : j = 0 := by
      simp [w.split_one i hi] at hcount
      symm; rwa [←Fin.val_inj, Fin.val_zero]
    rw [hj]
    conv in example2DFA.start => simp [example2DFA]
    apply TwoDFA.GoesTo.single
    have hvalid : Movement.right.isValid (0 : Fin (n+2)) := by constructor <;> simp
    right -- TwoDFA.nextConfig x y = ⟨step x = (y, .right)⟩
    · simp only [example2DFA, Fin.isValue, pi, Word.get_eq_left_of_eq_zero rfl, exampleStep]
    · suffices Movement.right.apply 0 hvalid = 1 by assumption
      simp [Movement.apply, ←Fin.val_inj]
  | right =>
    simp only [← Word.get_eq_right_iff_eq_last, ← Fin.val_eq_val, Fin.coe_castLE,
      Fin.val_last, piCast] at ha
    have := pi.is_lt
    rw [ha, lt_self_iff_false] at this
    contradiction
  | symbol a =>
    have piInternal : piCast.internal := w.internal_of_get_eq_symbol <| by use a
    have piCast_ne_zero : piCast ≠ 0 := by simp [piInternal.left]
    have := w.split_pred i <| by
      rw [←Fin.val_fin_lt, Fin.val_one]
      have := Nat.succ_lt_of_lt_pred <| by
        have := Fin.pos_of_ne_zero piCast_ne_zero
        simp only [←Fin.val_fin_lt, Fin.val_zero, Fin.coe_castLE, Fin.coe_pred, piCast, pi] at this
        exact this
      simpa
    simp [this, Vector.count_push] at hcount
    have piCast_eq_predCast : i.predCast h = piCast := rfl
    have : w.getInternal (i.predCast h) piInternal = a := by
      simp [this, Word.getInternal, Fin.internal.val]
      have pi_ne_zero : pi ≠ 0 := by
        unfold piCast at piCast_ne_zero
        rw [←Fin.val_ne_iff] at piCast_ne_zero
        simpa using piCast_ne_zero
      have piCast_pred_lt_n : piCast.pred piCast_ne_zero < n := by
        suffices (pi : Nat) - 1 < n by simp only [Fin.coe_pred, Fin.coe_castLE, piCast, this]
        apply Nat.sub_one_lt_of_le
        · apply Nat.pos_of_ne_zero
          rwa [←Fin.val_ne_iff] at pi_ne_zero
        · exact pi.is_le
      have : (piCast.pred piCast_ne_zero).castLT piCast_pred_lt_n = pi.pred pi_ne_zero := by
        rw [←Fin.val_eq_val]
        simp [piCast]
      rw [this]
      have piCast_pred_ne_last : piCast.pred piCast_ne_zero ≠ Fin.last n := by 
        suffices piCast.pred piCast_ne_zero < pi from Fin.ne_last_of_lt this
        rw [←Fin.val_fin_lt]
        suffices (pi : Nat) - 1 < pi by simpa [piCast]
        apply Nat.pred_lt_self
        simp only [Nat.sub_eq, tsub_zero, Fin.val_pos_iff]
        exact Fin.pos_of_ne_zero pi_ne_zero
      have : pi.pred pi_ne_zero = (piCast.pred piCast_ne_zero).castPred piCast_pred_ne_last := by
        rw [←Fin.val_inj]
        simp [piCast]
      rw [this]
      simpa [Word.get, piCast_ne_zero, piCast_pred_ne_last] using ha
    rw [this] at hcount
    have : w.split (i.predCast h) (by rwa [piCast_eq_predCast]) = w.split piCast piCast_ne_zero := by simp [Word.split, piCast, pi]
    rw [this] at hcount
    let countFin : Fin 3 := Fin.ofNat 3 <| (w.split piCast piCast_ne_zero).1.count 0
    have hcountFin : (w.split piCast piCast_ne_zero).1.count 0 % 3 = countFin.val := rfl
    have move_right_valid_from_piCast : Movement.right.isValid piCast := by
      constructor
      · simp
      · simp [piInternal.right]
    have move_right_from_piCast : Movement.right.apply piCast move_right_valid_from_piCast = i := by
      simp only [Movement.apply]
      rw [←Fin.val_inj]
      simp [piCast, pi, Nat.sub_one_add_one <| Fin.val_ne_of_ne h]
    if hazero : a = 0
      then
        have prev_count : (w.split piCast piCast_ne_zero).1.count 0 % 3 = ↑(j - 1) := by
          simp [hazero] at hcount 
          rw [hcountFin, Fin.val_eq_val]
          suffices countFin + 1 = j by rw [←this]; simp
          unfold countFin
          rw [Fin.ofNat_add, ←Fin.val_eq_val]
          simp [hcount]
        let prev : TwoDFA.Config ExampleState n := ⟨ .q (j-1), piCast ⟩
        have hind : example2DFA.GoesTo w ⟨example2DFA.start, 0⟩ prev := exampleZerosPass_ofCount hn piCast piCast_ne_zero w (j-1) prev_count
        constructor
        · exact hind
        · rw [←TwoDFA.stepConfig_gives_nextConfig]
          simp only [TwoDFA.stepConfig, example2DFA, Fin.isValue, Fin.castLE_refl,
            TwoDFA.Config.mk.injEq, prev]
          rw [hazero] at ha
          constructor
          · simp [ha, exampleStep]
          · simp [ha, exampleStep, move_right_from_piCast]
      else
        have prev_count : (w.split piCast piCast_ne_zero).1.count 0 % 3 = ↑j := by
          simpa [hazero] using hcount
        let prev : TwoDFA.Config ExampleState n := ⟨ .q j, piCast ⟩
        have hind : example2DFA.GoesTo w ⟨example2DFA.start, 0⟩ prev := exampleZerosPass_ofCount hn piCast piCast_ne_zero w j prev_count
        constructor
        · exact hind
        · rw [←TwoDFA.stepConfig_gives_nextConfig]
          simp only [TwoDFA.stepConfig, example2DFA, Fin.isValue, Fin.castLE_refl,
            TwoDFA.Config.mk.injEq, prev]
          have : a = 1 := by
            apply Or.elim <| fin2_lt_2 a
            · intro; contradiction
            · intro; trivial
          rw [this] at ha
          constructor
          · simp [ha, exampleStep]
          · simp [ha, exampleStep, move_right_from_piCast]
  termination_by sizeOf i
  decreasing_by all_goals {
    suffices (i : Nat) - 1 < i by simp [this]
    have : i.val ≠ 0 := Fin.val_ne_of_ne h
    exact Nat.sub_one_lt this
  }


/- #check (x.split i).fst.count 0 % 3 = 0 -/
theorem exampleZerosPass {n : Nat} (i : Fin (n+2)) (h : i ≠ 0) (w : Word (Fin 2) n) (j : Fin 3) :
    (w.split i h).fst.count 0 % 3 = j ↔ example2DFA.GoesTo w ⟨example2DFA.start, 0⟩ ⟨.q j, i.castLE <| by simp⟩ := by
  if hn : n = 0
    then
      have : i = 1 := by
        have := i.is_le
        conv at this =>
          simp only [hn, zero_add]
          rw [Nat.le_iff_lt_or_eq]
        rw [←Fin.val_inj, Fin.val_one]
        apply Or.resolve_left this
        simpa
      have split_empty := w.split_one i this
      simp [split_empty, this]
      have w_get_zero := w.get_eq_left_of_eq_zero (i := 0) <| by trivial
      constructor
      · intro hj
        have hj := Eq.symm hj
        rw [Fin.val_eq_zero_iff] at hj
        rw [hj]
        apply TwoDFA.GoesTo.single
        rw [←TwoDFA.stepConfig_gives_nextConfig]
        simp only [TwoDFA.stepConfig, example2DFA, TwoDFA.Config.mk.injEq, w_get_zero, exampleStep]
        constructor
        · trivial
        · simp only [Movement.apply]
          rw [←Fin.val_inj]
          simp
      · intro hgoes
        by_contra hj
        apply Or.elim <| fin3_lt_3 j
        · intro h2
          rw [←Fin.val_inj, Fin.val_zero] at h2
          have := h2.symm
          contradiction
        · intro hj
          apply Or.elim hj
          · intro hj
            rw [hj] at hgoes
            sorry
          · intro hj
            rw [hj] at hgoes
            sorry
    else
      constructor
      · exact exampleZerosPass_ofCount hn i h w j
      · intro h
        sorry

theorem list_count_eq_vector_count {α : Type u} [BEq α] (w : List α) (a : α) : List.count a w = Vector.count a w.toWord.val := by
  simp only [List.toWord, Vector.count, List.count_toArray]

theorem exampleAcceptsLanguage : example2DFA.language = exampleLanguage := by
  unfold exampleLanguage
  unfold TwoDFA.language
  rw [Set.setOf_inj]
  ext
  rename List (Fin 2) => w
  constructor

  -- example2DFA.accepts w → w ∈ exampleLanguage
  · intro h
    sorry

  -- w ∈ exampleLanguage → example2DFA.accepts w
  · intro h
    have ⟨ hzeros, hones ⟩ := h
    conv at hzeros =>
      unfold tripleZeros
      rw [list_count_eq_vector_count]

    let n := w.length
    have zerosPass := exampleZerosPass_ofCount sorry (Fin.last (n+1)) sorry (w.toWord) 0 sorry
    sorry

end example2DFA
