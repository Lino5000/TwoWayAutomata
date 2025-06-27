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
deriving instance Fintype for TwoDFA.Config

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

/--
After the input number of steps, the machine m on input x can reach configuration stp from the input configuration
Morally the same as GoesTo, but pulling off the start of the run rather than the end.
-/
inductive TwoDFA.ReachesIn (stp : Config σ n) : Nat → Config σ n → Prop
  | refl : ReachesIn stp 0 stp
  | step {start mid : Config σ n} {l : Nat} (head : m.nextConfig x start mid) (tail : ReachesIn stp l mid) : ReachesIn stp l.succ start

theorem TwoDFA.ReachesIn.trans {start mid stp : Config σ n} {la lb : Nat} (ha : m.ReachesIn x mid la start) (hb : m.ReachesIn x stp lb mid) : m.ReachesIn x stp (la + lb) start := by
  induction ha with
  | refl => simp [hb]
  | step hhead _ ih => 
    have := ih.step hhead
    simpa [Nat.add_comm]

def TwoDFA.ReachesIn.single {start stp : Config σ n} (hstep : m.nextConfig x start stp) : m.ReachesIn x stp 1 start :=
  .step hstep .refl

def TwoDFA.ReachesIn.tail {start mid stp : Config σ n} {l : Nat} (hstep : m.nextConfig x mid stp) (hhead : m.ReachesIn x mid l start) : m.ReachesIn x stp l.succ start :=
  .trans m x hhead <| .single m x hstep

theorem TwoDFA.ReachesIn.config_eq_of_len_0 {strt stp : Config σ n} {l : Nat} (hreach : m.ReachesIn x stp l strt) (hl : l = 0) : strt = stp := by
  rw [hl] at hreach
  cases hreach with
  | refl => rfl

theorem TwoDFA.ReachesIn_of_GoesTo {start stp : Config σ n} (h : m.GoesTo x start stp) : ∃ l : Nat, m.ReachesIn x stp l start := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | tail _ htail hind =>
    have ⟨headl, hind⟩ := hind
    use headl.succ
    exact .tail m x htail hind

theorem TwoDFA.GoesTo_of_ReachesIn {start stp : Config σ n} {l : Nat} (h : m.ReachesIn x stp l start) : m.GoesTo x start stp := by
  induction h with
  | refl => exact .refl
  | step hhead _ hind => exact GoesTo.head m x hhead hind

theorem TwoDFA.GoesTo_iff_ReachesIn {start stp : Config σ n} : m.GoesTo x start stp ↔ ∃ l : Nat, m.ReachesIn x stp l start where
  mp := ReachesIn_of_GoesTo m x
  mpr := by rintro ⟨l, h⟩; exact GoesTo_of_ReachesIn m x h

def TwoDFA.reaches (c : Config σ n) : Prop :=
  m.GoesTo x ⟨ m.start, 0 ⟩ c

def TwoDFA.reachesIn (nsteps : Nat) (c : Config σ n) : Prop :=
  m.ReachesIn x c nsteps ⟨ m.start, 0 ⟩

def TwoDFA.accepts : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ m.accept, i ⟩

def TwoDFA.rejects : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ m.reject, i ⟩

def TwoDFA.acceptsFrom (c : Config σ n) (nsteps : Nat) : Prop :=
  ∃ i : Fin (n+2), m.ReachesIn x ⟨ m.accept, i⟩ nsteps c

def TwoDFA.language (m : TwoDFA α σ) : Language α :=
  {x : List α | m.accepts x.toWord }

def TwoDFA.cyclesAt (c : Config σ n) (len : Nat) : Prop :=
  m.ReachesIn x c len.succ c

theorem TwoDFA.cyclesAt_of_cyclesAt_step (c : Config σ n) (len : Nat) (h : m.cyclesAt x c len) :
    m.cyclesAt x (m.stepConfig x c) len := by
  cases h with
  | @step _ mid _ head tail =>
    have : m.ReachesIn x mid len.succ mid := TwoDFA.ReachesIn.tail m x head tail
    rw [←stepConfig_gives_nextConfig] at head
    rwa [head]

def TwoDFA.stepBack (c : Config σ n) : Set (Config σ n) := { cprev : Config σ n | m.nextConfig x cprev c }

theorem TwoDFA.stepBack_Nonempty_of_notStart_of_GoesTo (c : Config σ n) (hc : c ≠ ⟨m.start, 0⟩) (hgoes : m.GoesTo x ⟨m.start, 0⟩ c) : m.stepBack x c |>.Nonempty := by
  induction hgoes with
  | refl => contradiction
  | @tail mid _ _ tail _ =>
    simp only [Set.Nonempty]
    use mid
    simpa [stepBack]

theorem TwoDFA.ReachesIn.split_last {strt stp : Config σ n} {len : Nat} (h : m.ReachesIn x stp len strt) (hlen : len ≠ 0) :
    ∃ mid : Config σ n, m.nextConfig x mid stp ∧ m.ReachesIn x mid len.pred strt := by
  induction h with
  | refl => contradiction -- hlen : 0 ≠ 0
  | @step strt' _ l head tail ih =>
    if hl : l = 0
      then
        use strt'
        constructor
        · rwa [←tail.config_eq_of_len_0 m x hl]
        · simp [hl, TwoDFA.ReachesIn.refl]
      else
        obtain ⟨mid', hnext, hreach⟩ := ih hl
        use mid'
        constructor
        · exact hnext
        · have := hreach.step head
          rw [Nat.succ_pred_eq_of_ne_zero hl] at this
          simpa

theorem TwoDFA.ReachesIn.split_trans {m : TwoDFA α σ} {x : Word α n} {strt mid stp : Config σ n} {l1 l2 : Nat} (h1 : m.ReachesIn x stp (l1 + l2) strt) (h2 : m.ReachesIn x mid l1 strt) :
    m.ReachesIn x stp l2 mid := by
  sorry

theorem TwoDFA.cyclesAt_stepBack_of_cyclesAt (c : Config σ n) (len : Nat) (h : m.cyclesAt x c len) :
    ∃ prev ∈ m.stepBack x c, m.cyclesAt x prev len := by
  obtain ⟨mid, hnext, hreach⟩ := h.split_last (hlen := by simp)
  use mid
  constructor
  · simp [stepBack, hnext]
  · exact hreach.step hnext

theorem TwoDFA.config_eq_of_cycles_of_ReachesIn {m : TwoDFA α σ} {x : Word α n} (c1 c2 : Config σ n) {len : Nat} (hcycles : m.cyclesAt x c1 len) (hreaches : m.ReachesIn x c2 len.succ c1) : c1 = c2 :=
  sorry

theorem TwoDFA.ReachesIn.remove_initial_cycle {m : TwoDFA α σ} {x : Word α n} {start c : Config σ n} {len k : Nat} (hk : len ≤ k) (hcycle : m.cyclesAt x start len) (hreaches : m.ReachesIn x c k start) :
    m.ReachesIn x c (k - len) start := by
  sorry

theorem TwoDFA.reachesIn_maxSteps_of_reaches [fin_cfgs : Fintype (Config σ n)] (c : Config σ n) (h : m.reaches x c) :
    ∃ k ≤ fin_cfgs.card, m.reachesIn x k c := by
  sorry

theorem TwoDFA.reaches_iff_reachesIn_maxSteps [fin_cfgs : Fintype (Config σ n)] (c : Config σ n) : m.reaches x c ↔ ∃ k ≤ fin_cfgs.card, m.reachesIn x k c where
  mp := m.reachesIn_maxSteps_of_reaches x c
  mpr := by
    rintro ⟨k, hk, hreachesIn⟩
    exact m.GoesTo_of_ReachesIn x hreachesIn

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

section Proving

variable {n : Nat} {α : Type u} {σ : Type v}

def SplitPredicate (n : Nat) (α : Type u) : Type _ :=
  (i : Fin (n+2)) → (h : i ≠ 0) → (Vector α (min (↑(i.pred h)) n) × Vector α (n - ↑(i.pred h))) → Prop

def SplitPredicate.apply (sp : SplitPredicate n α) (w : Word α n) (i : Fin (n+2)) (h : i ≠ 0) : Prop :=
  sp i h <| w.split i h

structure TwoDFA.ConfigMeaning (n : Nat) (α : Type u) (σ : Type v) : Type _ where
  --- Meaning of being in the given state at the left end marker
  atLeft : σ → Vector α n → Prop
  --- Meaning of being in the given state at the given position in the input after the left endmarker
  inWord : σ → SplitPredicate n α 

def TwoDFA.ConfigMeaning.apply (cm : ConfigMeaning n α σ) (w : Word α n) (cfg : Config σ n) : Prop :=
  if hcfg : cfg.idx = 0
    then
      cm.atLeft cfg.state w.val
    else
      cm.inWord cfg.state |>.apply w cfg.idx hcfg

theorem TwoDFA.ConfigMeaning.apply_of_reachable (motive : ConfigMeaning n α σ) (m : TwoDFA α σ) (w : Word α n)
  (base : motive.apply w ⟨m.start, 0⟩) (ind : ∀ cfg : Config σ n, motive.apply w cfg → motive.apply w (m.stepConfig w cfg))
  (cfg : Config σ n) (hgoes : m.reaches w cfg) :
    motive.apply w cfg := by
  induction hgoes with
  | refl => exact base
  | @tail mid stp head tail head_ih =>
    have hind := ind mid head_ih
    have : m.stepConfig w mid = stp := by rwa [m.stepConfig_gives_nextConfig w mid stp]
    rwa [this] at hind

/- theorem TwoDFA.ConfigMeaning.reachable_of_apply (motive : ConfigMeaning n α σ) (m : TwoDFA α σ) (w : Word α n) -/
/-   (base : motive.apply w ⟨m.start, 0⟩) (ind : ∀ cfg : Config σ n, motive.apply w cfg → motive.apply w (m.stepConfig w cfg)) -/
/-   (cfg : Config σ n) (happly : motive.apply w cfg) : -/
/-     m.reaches w cfg := by -/
/-   sorry -/

def TwoDFA.stepBackTimes (m : TwoDFA α σ) (w : Word α n) (k : Nat) (cfg : Config σ n) : Set (Config σ n) :=
  match k with
  | 0 => {cfg}
  | k + 1 =>
    let prevs := m.stepBack w cfg
    ⋃₀ prevs.image (m.stepBackTimes w k)

theorem TwoDFA.reachesIn_of_start_mem_stepBackTimes (m : TwoDFA α σ) (w : Word α n) (k : Nat) (cfg : Config σ n)
  (h : ⟨m.start, 0⟩ ∈ m.stepBackTimes w k cfg) : m.reachesIn w k cfg := by
  match k with
  | 0 =>
    conv at h =>
      simp [TwoDFA.stepBackTimes]
    rw [←h]
    exact .refl
  | k + 1 =>
    conv at h =>
      simp [stepBackTimes]
    rcases h with ⟨prev, ⟨hstepBack, hind⟩⟩
    apply TwoDFA.ReachesIn.tail m w
    · simpa using hstepBack
    · exact m.reachesIn_of_start_mem_stepBackTimes w k prev hind

end Proving
