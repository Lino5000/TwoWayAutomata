import Mathlib.Algebra.Group.Fin.Basic

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Word  -- TODO move utilities/extensions out to their own file, rather than in here

theorem Movement.card_eq_2 : Fintype.card Movement = 2 := by
  unfold Fintype.card
  unfold Finset.univ
  unfold Fintype.elems
  unfold instFintypeMovement
  unfold Movement.enumList
  simp

def Movement.opp : Movement → Movement
  | .left => .right
  | .right => .left

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

theorem Movement.lt_apply_right {n : Nat} (i : Fin (n+2)) {valid : Movement.right.isValid i} :
    i < Movement.right.apply i valid := by
  unfold Movement.apply
  simp [Fin.lt_def]

theorem Movement.apply_ne_self {n : Nat} (i : Fin (n+2)) (mov : Movement) (valid : mov.isValid i) : mov.apply i valid ≠ i := by
  by_contra heq
  cases mov
  all_goals simp [apply, ←Fin.val_inj] at heq
  -- move right is discharged by simp, just need a little more for left
  suffices i.val ≠ 0 by
    have := Nat.sub_one_ne_self (a := i.val) this
    contradiction
  have := valid.hleft
  simp only [and_true, ←ne_eq] at this
  rwa [Fin.ne_iff_vne, Fin.val_zero] at this

theorem TwoDFA.step_move_always_valid {α : Type _} {σ : Type _} (m : TwoDFA α σ) {n : Nat} {x : Word α n}
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
