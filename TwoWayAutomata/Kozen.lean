/-
# Kozen 2DFAs

An implementation of Two-way Deterministic Finite Automata ready to follow the proof of their regularity due to Kozen.
-/ -- TODO: add reference.
import Mathlib.Logic.Relation

universe u v

inductive TapeSymbol (α : Type u) : Type u where
  | left : TapeSymbol α
  | right : TapeSymbol α
  | symbol : α → TapeSymbol α

instance {α : Type u} : Coe α (TapeSymbol α) where
  coe := TapeSymbol.symbol

inductive Movement : Type where
  | left : Movement
  | right : Movement

def Movement.opp : Movement → Movement
  | .left => .right
  | .right => .left

structure TwoDFA (α : Type u) (σ : Type v) : Type (max u v) where
  step : TapeSymbol α → σ → σ × Movement
  start : σ
  accept : σ
  reject : σ
  distinct_tr : accept ≠ reject
  in_bounds_left : ∀ q : σ, ∃ u : σ, step TapeSymbol.left q = (u, Movement.right)
  in_bounds_right : ∀ q : σ, ∃ u : σ, step TapeSymbol.right q = (u, Movement.left)
  halt_move_right : ∀ a : α, step a accept = (accept, Movement.right) ∧ step a reject = (reject, Movement.right)
  halt_preserve_state : ∀ a : TapeSymbol α, (∃ m : Movement, step a accept = (accept, m)) ∧ (∃ m : Movement, step a reject = (reject, m))

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

section String

structure Word (α : Type u) (n : Nat) : Type u where
  val : Vector α n

--def Word.get {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) : TapeSymbol α :=
--  match i with
--  | ⟨ val, isLt ⟩ => match val with
--                     | 0 => .left
--                     | k + 1 => let kFin : Fin (n+1) := ⟨ k, Nat.lt_of_succ_lt_succ isLt ⟩
--                                if h : kFin = Fin.last n
--                                  then .right
--                                  else let ltN := Fin.val_lt_last h
--                                       w.val.get ⟨ k, ltN ⟩
def Word.get {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) : TapeSymbol α :=
  if h : i = 0
    then .left
    else
      let k := i.pred h
      if h : k = Fin.last n
        then .right
        else
          let ltN := Fin.val_lt_last h
          w.val.get <| k.castLT ltN


theorem Word.get_eq_left_of_eq_zero {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i = 0 → w.get i = .left := by
  intro h
  simp only [↓reduceDIte, Word.get, h]

theorem Word.get_neq_left_of_neq_zero {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i ≠ 0 → w.get i ≠ .left := by
  intro h1
  if h2 : i.pred h1 = Fin.last n
    then simp [Word.get, h1, h2]
    else simp [Word.get, h1, h2]

theorem Word.eq_zero_of_get_eq_left {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : w.get i = .left → i = 0 := by
  false_or_by_contra
  have : w.get i ≠ .left := Word.get_neq_left_of_neq_zero <| by assumption
  contradiction

theorem Word.get_eq_left_iff_eq_0 {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : w.get i = .left ↔ i = 0 where
  mpr := Word.get_eq_left_of_eq_zero
  mp := Word.eq_zero_of_get_eq_left


theorem Word.get_eq_right_of_eq_last {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i = Fin.last (n+1) → w.get i = .right := by
  intro h
  simp [h, Word.get, Fin.pred, Fin.subNat, Fin.last]

theorem Word.get_neq_right_of_neq_last {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i ≠ Fin.last (n+1) → w.get i ≠ .right := by
  intro h1
  if h2 : i = 0
    then simp [Word.get, h2]
    else if h3 : i.pred h2 = Fin.last n
      then
        have : i = Fin.last (n+1) := by 
          simp [Fin.pred, Fin.subNat, Fin.last] at h3
          simp [Fin.last, Fin.ext_iff]
          rw [Nat.sub_one] at h3
          suffices i = n.succ by assumption
          cases h4 : i.val
          · simp [Nat.pred, h4] at h3
            rw [← h3]
            have : (i : Nat) ≠ 0 := Fin.val_ne_of_ne h2
            contradiction
          · rw [h4, ← Nat.sub_one, Nat.add_sub_cancel_right] at h3
            rw [h3]
        have : w.get i = .right := Word.get_eq_right_of_eq_last this
        contradiction
      else simp [Word.get, h2, h3]

theorem Word.eq_last_of_get_eq_right {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : w.get i = .right → i = Fin.last (n+1) := by
  false_or_by_contra
  have : w.get i ≠ .right := Word.get_neq_right_of_neq_last <| by assumption
  contradiction

theorem Word.get_eq_right_iff_eq_last {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i = Fin.last (n+1) ↔ w.get i = .right where
  mp := Word.get_eq_right_of_eq_last
  mpr := Word.eq_last_of_get_eq_right

end String

section ValidMovement

structure Movement.isValid {n : Nat} (move : Movement) (i : Fin (n+2)) : Prop where
  hleft : ¬ (i = 0 ∧ move = .left)
  hright : ¬ (i = Fin.last (n+1) ∧ move = .right)

theorem Fin.one_le_of_ne_zero {n : Nat} (i : Fin (n+2)) (h : i ≠ 0) : 1 ≤ i := by
  rw [← Fin.not_lt, Fin.lt_def, Fin.val_one]
  simp [Fin.ext_iff] at h
  cases h : i.val
  · contradiction
  · simp

theorem Movement.one_le_of_left_isValid {n : Nat} (i : Fin (n+2)) (h : Movement.left.isValid i) : 1 ≤ i := by
  have := h.hleft
  apply i.one_le_of_ne_zero
  simp at this
  exact this

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

def Movement.apply {n : Nat} (move : Movement) (i : Fin (n+2)) (hvalid : move.isValid i) : Fin (n+2) :=
  match hm : move with
  | .left => i.predCast <| by
               have h := hvalid.hleft
               simp at h
               assumption
  | .right => let j := i.succ
              j.castLT <| by
                rw [Fin.val_succ i]
                have : i < n+1 := by 
                  apply Fin.val_lt_last
                  have h := hvalid.hright
                  simp at h
                  assumption
                simp [this]

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
  simp [Movement.apply, Fin.lt_def]

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
  <;> simp [Fin.ext_iff]
  -- move = .right solved by simp
  rw [Nat.add_comm]
  apply Nat.add_sub_cancel'
  cases h : i.val with
  | zero => have := valid.hleft
            simp at this
            rw [Fin.ext_iff, Fin.val_zero] at this
            contradiction
  | succ n => apply Nat.succ_le_succ
              exact Nat.zero_le n

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

end ValidMovement

variable {α : Type u} {σ : Type v} (m : TwoDFA α σ)

theorem TwoDFA.step_move_always_valid {n : Nat} {x : Word α n} {i : Fin (n+2)} {move : Movement} {s t : σ} (h : m.step (x.get i) s = ⟨ t, move ⟩):
     move.isValid i := by
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
      

@[ext]
structure TwoDFA.Config (σ : Type v) (n : Nat) where
  state : σ
  idx : Fin (n + 2)

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

def TwoDFA.manyStepConfig : Config σ n → Config σ n → Prop :=
  Relation.ReflTransGen <| m.nextConfig x

def TwoDFA.reaches (c : Config σ n) : Prop :=
  m.manyStepConfig x ⟨ m.start, 0 ⟩ c

def TwoDFA.accepts : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ m.accept, i ⟩

def TwoDFA.rejects : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ m.reject, i ⟩
            

theorem TwoDFA.accept_lt_accept (i j : Fin (n+2)) (h : i < j) : m.manyStepConfig x ⟨ m.accept, i ⟩ ⟨ m.accept, j ⟩ := by
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
    apply Relation.ReflTransGen.tail
    · suffices m.manyStepConfig x ⟨ m.accept, i ⟩ ⟨ m.accept, prevIdx ⟩ from this
      if heq : prevIdx = i
        then
          rw [heq]
          exact Relation.ReflTransGen.refl
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
    simp
    rw [← Fin.lt_def]
    exact Movement.lt_of_apply_left j
  }


theorem TwoDFA.reaches_accept_last_of_accepts (haccept : m.accepts x) : m.reaches x ⟨ m.accept, Fin.last (n+1) ⟩ := by
  cases haccept with
  | intro idx hidx =>
    if h : idx = Fin.last (n+1)
      then rw [← h]; assumption
      else
        apply Relation.ReflTransGen.trans hidx
        apply m.accept_lt_accept x idx (Fin.last (n+1))
        cases Fin.lt_or_eq_of_le <| Fin.le_last idx
        · assumption
        · contradiction

end Evaluation

section example2DFA

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

end example2DFA
