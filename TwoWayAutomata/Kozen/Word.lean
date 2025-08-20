import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic

import TwoWayAutomata.Kozen.Basics

universe u v

namespace Word

@[simp]
theorem get_eq_left_of_eq_zero {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i = 0 → w.get i = .left := by
  intro h
  simp only [↓reduceDIte, Word.get, h]

theorem get_neq_left_of_neq_zero {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i ≠ 0 → w.get i ≠ .left := by
  intro h1
  if h2 : i.pred h1 = Fin.last n
    then simp [Word.get, h1, h2]
    else simp [Word.get, h1, h2]

theorem eq_zero_of_get_eq_left {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : w.get i = .left → i = 0 := by
  false_or_by_contra
  have : w.get i ≠ .left := Word.get_neq_left_of_neq_zero <| by assumption
  contradiction

theorem get_eq_left_iff_eq_0 {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : w.get i = .left ↔ i = 0 where
  mpr := Word.get_eq_left_of_eq_zero
  mp := Word.eq_zero_of_get_eq_left

@[simp]
theorem get_eq_right_of_eq_last {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i = Fin.last (n+1) → w.get i = .right := by
  intro h
  simp [h, Word.get, Fin.pred, Fin.subNat, Fin.last]

theorem get_neq_right_of_neq_last {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i ≠ Fin.last (n+1) → w.get i ≠ .right := by
  intro h1
  if h2 : i = 0
    then simp [Word.get, h2]
    else if h3 : i.pred h2 = Fin.last n
      then
        have : i = Fin.last (n+1) := by 
          simp [Fin.pred, Fin.subNat, Fin.last] at h3
          simp [Fin.last, Fin.ext_iff]
          rw [Nat.sub_one] at h3
          suffices i = n.succ by simp only [this, Nat.succ_eq_add_one, Fin.natCast_eq_last,
            Fin.val_last, Nat.add_left_inj]
          cases h4 : i.val with
          | zero =>
            simp only [Nat.pred, h4] at h3
            have : (i : Nat) ≠ 0 := Fin.val_ne_of_ne h2
            contradiction
          | succ k =>
            rw [h4, ← Nat.sub_one, Nat.add_sub_cancel_right] at h3
            simp only [Nat.succ_eq_add_one, Fin.natCast_eq_last, Fin.val_last]
            rw [h3]
        have : w.get i = .right := Word.get_eq_right_of_eq_last this
        contradiction
      else simp [Word.get, h2, h3]

theorem eq_last_of_get_eq_right {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : w.get i = .right → i = Fin.last (n+1) := by
  false_or_by_contra
  have : w.get i ≠ .right := Word.get_neq_right_of_neq_last <| by assumption
  contradiction

theorem get_eq_right_iff_eq_last {α : Type u} {n : Nat} {w : Word α n} {i : Fin (n+2)} : i = Fin.last (n+1) ↔ w.get i = .right where
  mp := Word.get_eq_right_of_eq_last
  mpr := Word.eq_last_of_get_eq_right

end Word

@[reducible]
def Fin.internal {n : Nat} (i : Fin (n+2)) : Prop :=
  i ≠ 0 ∧ i ≠ Fin.last (n+1)

def Fin.internal.val {n : Nat} {i : Fin (n+2)} (h : i.internal) : Fin n :=
  let p := i.pred h.left 
  have hp : p.val < n := by
    unfold p
    rw [Fin.coe_pred]
    have val_lt : i.val < n+1 := by
      apply Nat.lt_of_le_of_ne <| Fin.le_last i
      exact Fin.val_ne_of_ne h.right
    have val_ne : i.val ≠ 0 := Fin.val_ne_of_ne h.left
    have := Nat.pred_lt_pred val_ne val_lt
    simp only [Nat.pred_eq_sub_one, add_tsub_cancel_right] at this
    exact this
  p.castLT hp

@[simp]
theorem Fin.internal.val_eq_pred {n : Nat} {i : Fin (n+2)} (int : i.internal) : int.val = i.val - 1 := by
  simp only [val, coe_castLT, coe_pred]

@[simp]
theorem Fin.internal.i_val_ne_last {n : Nat} {i : Fin (n+2)} (int : i.internal) : i.val ≠ n+1 := by
  have := int.right
  simpa [Fin.ne_iff_vne] using this

@[simp]
theorem Fin.internal.i_val_ne_zero {n : Nat} {i : Fin (n+2)} (int : i.internal) : i.val ≠ 0 := by
  simp [int.left]

@[simp]
theorem Fin.internal.pred_ne_last {n : Nat} {i : Fin (n+2)} (int : i.internal) : i.pred int.left ≠ Fin.last n := by
  simp only [ne_iff_vne, coe_pred, val_last]
  rw [←Nat.add_one_ne_add_one_iff, Nat.sub_one_add_one]
  · exact int.i_val_ne_last
  · exact int.i_val_ne_zero

@[simp]
theorem Fin.internal.val_succ_lt {n : Nat} {i : Fin (n+2)} (int : i.internal) : i.val.succ < n + 2 := by
  have := int.right
  rw [←Fin.lt_last_iff_ne_last, Fin.lt_iff_val_lt_val] at this
  simpa

@[simp]
def Word.get_eq_symbol_of_internal {α : Type u} {n : Nat} (w : Word α n) {i : Fin (n+2)} (int : i.internal) :
    w.get i = .symbol (w.val.get int.val) := by
  have not_left : w.get i ≠ .left := Word.get_neq_left_of_neq_zero int.left
  have not_right : w.get i ≠ .right := Word.get_neq_right_of_neq_last int.right
  cases h : w.get i with
  | left | right => contradiction
  | symbol a =>
    rw [TapeSymbol.symbol.injEq]
    have i_not_last : i.pred int.left ≠ Fin.last n := by
      false_or_by_contra
      rename i.pred int.left = Fin.last n => assump
      have : (i.pred int.left).succ = (Fin.last n).succ := by rw [Fin.succ_inj]; exact assump
      simp at this
      have := int.right
      contradiction
    have : (i.pred int.left).castPred i_not_last = int.val := by
      simp [Fin.castPred, int.val_eq_pred, Fin.ext_iff]
    simp [Word.get, int.left, int.right, i_not_last, this] at h
    exact h.symm

def Word.internal_of_get_eq_symbol {α : Type u} {n : Nat} (w : Word α n) {i : Fin (n+2)} (h : ∃ a : α, w.get i = .symbol a) :
    i.internal := by
  constructor
  · rw [ne_eq, ←Word.get_eq_left_iff_eq_0 (w:=w)]
    have ⟨ a, ha ⟩ := h
    simp [ha]
  · rw [ne_eq, Word.get_eq_right_iff_eq_last (w:=w)]
    have ⟨ a, ha ⟩ := h
    simp [ha]

theorem Word.get_eq_symbol_iff_internal {α : Type u} {n : Nat} (w : Word α n) {i : Fin (n+2)} : i.internal ↔ ∃ a : α, w.get i = .symbol a := by
  constructor
  · intro hint
    have := w.get_eq_symbol_of_internal hint
    exists (w.val.get hint.val)
  · exact w.internal_of_get_eq_symbol

def Word.getInternal {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) (int : i.internal) : α :=
  w.val.get int.val

@[simp]
theorem Word.getInternal_eq_getElem {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) (int : i.internal) :
    w.getInternal i int = w.val[int.val] := by
  simp [getInternal, Vector.get]

@[simp]
theorem Word.getInternal_eq_get {α : Type _} {n : Nat} (w : Word α n) (i : Fin (n+2)) (int : i.internal) :
    w.getInternal i int = w.get i := by
  simp [getInternal, get, int.left, int.pred_ne_last, Fin.internal.val]

-- Extract from the word ⊢ w₁ ... wₙ ⊣ the list of symbols wᵢ... wⱼ₋₁ with i=start and j=stop
def Word.extract {α : Type u} {n : Nat} (w : Word α n) (start stop : Fin (n+2)) (h1 : start.internal) (h2 : stop ≠ 0) :
    Vector α (min stop.val.pred n - start.val.pred) :=
  let vectStart := start.pred h1.left
  let vectStop := stop.pred h2
  have size_eq : min vectStop.val n - vectStart.val = min stop.val.pred n - start.val.pred := by
    simp only [Fin.coe_pred, Nat.pred_eq_sub_one, vectStop, vectStart]
  by rw [← size_eq]
     exact w.val.extract vectStart vectStop


theorem split_lens_add_to_n (n : Nat) (i : Fin (n+2)) (h : i ≠ 0) : min ↑(i.pred h) n + (n - ↑(i.pred h)) = n := by
  simp only [h, ↓reduceDIte, Fin.coe_pred]
  suffices i-1 ≤ n by simp [this]
  rw [Nat.sub_one, Nat.pred_le_iff]
  exact i.is_le

abbrev split_spec {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) (h : i ≠ 0) : Prop :=
  let ⟨ l, r ⟩ := w.split i h
  Vector.cast (split_lens_add_to_n n i h) (l ++ r) = w.val

theorem Word.split_meets_spec {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) (h : i ≠ 0) : split_spec w i h := by
  simp [split_spec, split, h, Vector.cast]

@[simp]
theorem Word.split_append {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) (h : i ≠ 0) :
    (w.split i h).1 ++ (w.split i h).2 = Vector.cast (split_lens_add_to_n n i h).symm w.val := by
  simp [Word.split, Vector.cast]

theorem Word.split_one {n : Nat} {α : Type u} (w : Word α n) (i : Fin (n+2)) (hi : i = 1) :
    w.split i (by simp [hi]) = ((⟨#[], by simp [hi]⟩, Vector.cast (by simp [hi]) w.val) : split_type α i (by simp [hi])) := by
  simp only [split, Fin.coe_pred, Vector.take_eq_extract, Vector.cast_rfl,
    Vector.drop_eq_cast_extract]
  rw [Prod.mk_inj]
  constructor
  · simp [←Vector.toArray_inj, hi]
  · simp [Vector.cast_eq_cast, ←Vector.toArray_inj, Vector.toArray_extract, Vector.toArray_cast, hi]

theorem Word.split_last {n : Nat} {α : Type u} (w : Word α n) (i : Fin (n+2)) (hi : i = Fin.last _) :
    w.split i (by simp [hi]) = ((Vector.cast (by simp [hi]) w.val, ⟨#[], by simp [hi]⟩) : split_type α i (by simp [hi])) := by
  simp only [split, Fin.coe_pred, Vector.take_eq_extract, Vector.cast_rfl, Vector.drop_eq_cast_extract]
  rw [Prod.mk_inj]
  constructor
  · simp [←Vector.toArray_inj, hi]
  · simp [←Vector.toArray_inj, Vector.toArray_extract, Vector.toArray_cast, hi]

@[reducible]
def Fin.predCast {n : Nat} (i : Fin (n+1)) (h : i ≠ 0) : Fin (n+1) := (i.pred h).castLE <| by simp

@[reducible]
def Fin.succCast {n : Nat} (i : Fin (n+1)) (h : i ≠ Fin.last n) : Fin (n+1) := i.succ.castLT <| by
  rw [Fin.val_succ, Nat.add_one_lt_add_one_iff]
  exact i.val_lt_last h

theorem Fin.predCast_lt_predCast {n : Nat} (a b : Fin (n+1)) (ha : a ≠ 0) (hlt : a < b) : a.predCast ha < b.predCast (Fin.ne_zero_of_lt hlt) := by
  rwa [castLE_lt_castLE_iff, pred_lt_pred_iff]

theorem Fin.predCast_lt {n : Nat} (i : Fin (n+1)) (h : i ≠ 0) : i.predCast h < i := by
  rw [lt_iff_val_lt_val]
  simp [h, Nat.sub_one_lt]

theorem split_pred_idx_eq {n : Nat} (i : Fin (n+2)) (hi : 1 < i) : min (↑((i.predCast <| Fin.ne_zero_of_lt hi).pred <| Fin.ne_zero_of_lt (Fin.predCast_lt_predCast 1 i (by simp) hi))) n + 1 = min (↑(i.pred <| Fin.ne_zero_of_lt hi)) n := by
  have : ↑i - 1 ≤ n := by
    rw [←Nat.succ_le_succ_iff]
    simp [hi, i.is_le]
  simp only [Fin.coe_pred, Fin.coe_castLE, tsub_le_iff_right, Fin.is_le', inf_of_le_left, this]
  apply Nat.sub_add_cancel
  rw [←Nat.succ_le_succ_iff, Nat.succ_eq_add_one, Nat.succ_eq_add_one]
  suffices (i : Nat) - 1 + 1 = ↑i by rwa [this]
  apply Nat.sub_add_cancel
  apply Nat.le_of_lt
  rwa [Fin.lt_iff_val_lt_val, Fin.val_one] at hi

theorem split_pred_i_internal {n : Nat} (i : Fin (n+2)) (hi : 1 < i) : (i.predCast <| Fin.ne_zero_of_lt hi).internal := by
  constructor
  · exact Fin.ne_zero_of_lt (Fin.predCast_lt_predCast 1 i (by simp) hi)
  · apply Fin.ne_of_lt
    apply Fin.lt_of_lt_of_le
    · exact Fin.predCast_lt i <| Fin.ne_zero_of_lt hi
    · exact i.le_last

theorem Word.split_pred {n : Nat} {α : Type u} (w : Word α n) (i : Fin (n+2)) (hi : 1 < i) :
    (w.split i <| Fin.ne_zero_of_lt hi).1 = Vector.cast (split_pred_idx_eq i hi) ((w.split (i.predCast <| Fin.ne_zero_of_lt hi) <| Fin.ne_zero_of_lt (Fin.predCast_lt_predCast 1 i (by simp) hi)).1.push (w.getInternal (i.predCast <| Fin.ne_zero_of_lt hi) (split_pred_i_internal i hi))) := by
  have l1 : (i : Nat) - 1 - 1 + 1 = (i : Nat) - 1 := by
    suffices 1 ≤ (i : Nat) - 1 from Nat.sub_add_cancel this
    have : (i : Nat) ≠ 0 := Nat.ne_zero_of_lt hi
    rwa [←Nat.succ_le_succ_iff, ←Nat.add_one, ←Nat.add_one, Nat.sub_one_add_one this]
  unfold Vector.cast
  simp [split, getInternal_eq_getElem, Fin.internal.val, l1]

lemma split_pred2_lens {n : Nat} (i : Fin (n+2)) (hi : 1 < i) : n - ↑((i.predCast <| Fin.ne_zero_of_lt hi).pred <| Fin.ne_zero_of_lt (Fin.predCast_lt_predCast 1 i (by simp) hi)) - 1 = n - ↑(i.pred <| Fin.ne_zero_of_lt hi) := by
  suffices n - (↑i - 1 - 1) - 1 = n - (↑i - 1) by simpa
  suffices (i : Nat) - 1 ≠ 0 by rw [Nat.sub_sub, Nat.sub_one_add_one this]
  apply Nat.ne_of_gt
  rw [←Nat.succ_lt_succ_iff]
  have : (i : Nat) ≠ 0 := Nat.ne_zero_of_lt hi
  conv =>
    rhs
    rw [←Nat.add_one, Nat.sub_one_add_one this]
  exact hi

theorem Word.split_pred2 {n : Nat} {α : Type u} (w : Word α n) (i : Fin (n+2)) (hi : 1 < i) :
    Vector.cast (split_pred2_lens i hi).symm (w.split i <| Fin.ne_zero_of_lt hi).2 = (w.split (i.predCast <| Fin.ne_zero_of_lt hi) <| Fin.ne_zero_of_lt (Fin.predCast_lt_predCast 1 i (by simp) hi)).2.tail := by
  have : (i : Nat) - 1 - 1 + 1 = (i : Nat) - 1 := by
    apply Nat.sub_one_add_one
    rw [Fin.lt_iff_val_lt_val, Fin.val_one] at hi
    have : (i : Nat) ≠ 0 := Nat.ne_zero_of_lt hi
    exact Nat.ne_of_gt <| Nat.zero_lt_sub_of_lt hi
  simp [Word.split, Vector.cast, this]

lemma split_pred2_lens' {n : Nat} (i j : Fin (n+2)) (hi : 1 < i) (hj : j = i.predCast (Fin.ne_zero_of_lt hi)) :
    n - ↑(j.pred <| by rw [hj]; exact Fin.ne_zero_of_lt (Fin.predCast_lt_predCast 1 i (by simp) hi)) - 1 = n - ↑(i.pred <| Fin.ne_zero_of_lt hi) := by
  conv in j => rw [hj]
  exact split_pred2_lens i hi

theorem Word.split_pred2' {n : Nat} {α : Type u} (w : Word α n) (i j : Fin (n+2)) (hi : 1 < i) (hj : j = i.predCast (Fin.ne_zero_of_lt hi)) :
    Vector.cast (split_pred2_lens' i j hi hj).symm (w.split i <| Fin.ne_zero_of_lt hi).2 =
      (w.split j <| by rw [hj]; exact Fin.ne_zero_of_lt (Fin.predCast_lt_predCast 1 i (by simp) hi)).2.tail := by
  have jval : j.val = i.val - 1 := by simp [hj]
  have : (i : Nat) - 1 - 1 + 1 = (i : Nat) - 1 := by
    apply Nat.sub_one_add_one
    rw [Fin.lt_iff_val_lt_val, Fin.val_one] at hi
    have : (i : Nat) ≠ 0 := Nat.ne_zero_of_lt hi
    exact Nat.ne_of_gt <| Nat.zero_lt_sub_of_lt hi
  simp [Word.split, Vector.cast, jval, this]

theorem Fin.succCast_ne_zero {n : Nat} (i : Fin (n+1)) (hilast : i ≠ Fin.last n) : i.succCast hilast ≠ 0 := by
  simp [←Fin.val_ne_iff]

theorem split_succ_idx_eq {n : Nat} (i : Fin (n+2)) (hi : i ≠ 0) (hilast : i ≠ Fin.last (n+1)) : min (↑((i.succCast hilast).pred (i.succCast_ne_zero hilast))) n = min (↑(i.pred hi)) n + 1 := by
  have l1 : (i : Nat) ≤ n := by
    rw [←Nat.add_one_le_add_one_iff]
    exact Fin.val_lt_last hilast
  have l2 : (i : Nat) - 1 ≤ n := by
    rw [tsub_le_iff_right]
    exact Nat.le_succ_of_le l1
  have l3 : (i : Nat) ≠ 0 := Fin.val_ne_of_ne hi
  simp [l1, l2, Nat.sub_one_add_one l3]

theorem Word.split_succ {n : Nat} {α : Type u} (w : Word α n) (i : Fin (n+2)) (hi : i ≠ 0) (hilast : i ≠ Fin.last (n+1)) :
    Vector.cast (split_succ_idx_eq i hi hilast).symm ((w.split i hi).1.push (w.getInternal i ⟨hi, hilast⟩)) = (w.split (i.succCast hilast) (i.succCast_ne_zero hilast)).1 := by
  have l1 : (i : Nat) - 1 + 1 = i := Nat.sub_one_add_one <| by rwa [←Fin.val_ne_iff] at hi
  unfold Vector.cast
  simp [split, getInternal_eq_getElem, Fin.internal.val, l1]

theorem split_succ2_lens {n : Nat} {i : Fin (n + 2)} (hi : i ≠ 0) (hilast : i ≠ Fin.last _) :
    n - ↑(i.pred hi) - 1 = n - ↑((i.succCast hilast).pred <| Fin.succCast_ne_zero i hilast) := by
  have : i.val ≠ 0 := by rwa [Fin.ne_iff_vne, Fin.val_zero] at hi
  simp [Nat.sub_sub, Nat.sub_one_add_one this]

theorem Word.split_succ2 {n : Nat} {α : Type u} (w : Word α n) (i : Fin (n+2)) (hi : i ≠ 0) (hilast : i ≠ Fin.last (n+1)) :
    Vector.cast (split_succ2_lens hi hilast) (w.split i hi).2.tail = (w.split (i.succCast hilast) <| Fin.succCast_ne_zero i hilast).2 := by
  have l1 : i.val - 1 + 1 = i := Nat.sub_one_add_one <| by rwa [←Fin.val_ne_iff] at hi
  have l2 : i.val - 1 + (n - (i.val - 1)) = n := by
    rw [←Nat.add_sub_assoc]
    apply Nat.add_sub_self_left
    rw [←Nat.add_one_le_add_one_iff, l1]
    exact i.is_le
  unfold Vector.cast
  simp [split, getInternal_eq_getElem, Fin.internal.val, l1, l2]

theorem split_2_idx_valid_of_internal {n : Nat} {i : Fin (n+2)} (h : i.internal) : 0 < n - ↑(i.pred h.left) := by
  simp only [Fin.coe_pred, Nat.sub_pos_iff_lt]
  rw [←Nat.add_one_lt_add_one_iff, Nat.sub_one_add_one <| by simp [h.left]]
  have := Fin.lt_last_iff_ne_last.mpr h.right
  simpa

theorem Word.split_2_getElem {n : Nat} {α : Type u} (w : Word α n) (i : Fin (n+2)) (int : i.internal) :
    (w.split i int.left).2[0]'(split_2_idx_valid_of_internal int) = w.getInternal i int := by
  simp [Word.split, Word.getInternal, Fin.internal.val, Vector.get]

@[simp]
lemma Fin.internal.val_pred_lt {n : Nat} {i : Fin (n+1)} (int : i.succ.internal) : i.val < n := by
  have := int.right
  rw [←Fin.lt_last_iff_ne_last, Fin.lt_iff_val_lt_val] at this
  simpa

lemma List.toWord_val_getElem_eq_getElem {α : Type u} (w : List α) (i : Fin w.length) : w.toWord.val[i] = w[i.val] := by
  have : w = w.toWord.val.toList := by simp [toWord]
  conv =>
    rhs; pattern w
    rw [this]
  simp only [Vector.getElem_toList, Fin.getElem_fin]

@[simp]
theorem Word.toWord_get_internal {α : Type u} (w : List α) (i : Fin (w.length + 1)) (int : i.succ.internal) :
    w.toWord.get i.succ = w[i.val]'(int.val_pred_lt) := by
  apply w.toWord.getInternal_eq_get _ int |>.symm.trans
  rw [w.toWord.getInternal_eq_getElem _ int, TapeSymbol.symbol.injEq, List.toWord_val_getElem_eq_getElem]
  have : int.val.val = i.val := by simp [Fin.internal.val]
  conv in int.val.val =>
    rw [this]
