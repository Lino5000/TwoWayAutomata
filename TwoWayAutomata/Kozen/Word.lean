import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.Fin.Basic

import TwoWayAutomata.Kozen.Basics

universe u v

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
          suffices i = n.succ by simp only [this, Nat.succ_eq_add_one, Fin.natCast_eq_last,
            Fin.val_last, Nat.add_left_inj]
          cases h4 : i.val
          · simp only [Nat.pred, h4] at h3
            have : (i : Nat) ≠ 0 := Fin.val_ne_of_ne h2
            contradiction
          · rw [h4, ← Nat.sub_one, Nat.add_sub_cancel_right] at h3
            rw [h3] at h4
            rw [Fin.ext_iff]
            simp only [Nat.succ_eq_add_one, Fin.natCast_eq_last, Fin.val_last]
            exact h4
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

@[match_pattern]
def Word.nil {α : Type u} : Word α 0 := ⟨ { toList := [], size_toArray := by simp } ⟩

@[match_pattern]
def Word.cons {α : Type u} {n : Nat} (w : Word α n) (a : α) : Word α (n+1) :=
  ⟨ w.val.insertIdx 0 a ⟩

theorem Word.cons_as_list {α : Type u} {n : Nat} (xs : List α) (hxs : xs.length = n) (a : α) :
    (⟨⟨xs⟩, hxs⟩ : Word α n).cons a = ⟨⟨a :: xs⟩, by rw [←hxs]; exact List.length_cons⟩ := by
  simp [Word.cons]

theorem Word.cons_toList {α : Type u} {n : Nat} (w : Word α n) (a : α) :
    (w.cons a).val.toList = a :: w.val.toList := by
  simp [Word.cons]

def Word.push {α : Type u} {n : Nat} (w : Word α n) (a : α) : Word α (n+1) :=
  ⟨ w.val.push a ⟩

theorem Word.get_push_lt {α : Type u} {n : Nat} (w : Word α n) (a : α) (i : Fin (n+2)) (h : i < Fin.last (n+1)) :
    w.get i = (w.push a).get (i.castLE <| by simp) := by
  cases i using Fin.cases with
  | zero =>
    simp only [Fin.castLE_zero]
    rw [Word.get_eq_left_of_eq_zero, Word.get_eq_left_of_eq_zero]
    <;> rfl
  | succ i =>
    unfold Word.get
    simp only [Fin.pred_succ, Fin.castLE_succ, Nat.succ_eq_add_one]
    have not_zero : i.succ ≠ 0 := Fin.succ_ne_zero i
    have not_last : i ≠ Fin.last n := by
      apply Fin.ne_of_lt
      rwa [← Fin.succ_lt_succ_iff, Fin.succ_last]
    simp [not_zero, not_last]

    let j : Fin (n+2) := i.castLE <| by simp
    have cast_not_zero : j.succ ≠ 0 := Fin.succ_ne_zero j
    have cast_not_last : j ≠ Fin.last (n+1) := by
      rw [← Fin.val_ne_iff]
      simp only [Fin.coe_castLE, Fin.val_last, j]
      exact  Nat.ne_of_lt i.is_lt
    simp [j, cast_not_zero, cast_not_last]

    unfold Vector.get
    unfold Word.push
    simp only [Fin.coe_cast, Fin.coe_castPred, Fin.coe_castLE, j]
    symm
    apply Vector.getElem_push_lt
    apply Nat.lt_of_le_of_ne
    · have le_n := Fin.le_last i
      simp only [Fin.le_def, Fin.val_last, j] at le_n
      assumption
    · rwa [← Fin.val_ne_iff, Fin.val_last] at not_last

theorem Word.get_push_eq {α : Type u} {n : Nat} (w : Word α n) (a : α) (i : Fin (n+2)) (h : i = Fin.last (n+1)) :
    (w.push a).get (i.castLE <| by simp) = a := by
  have not_zero : (i.castLE <| by simp) ≠ (0 : Fin (n+3)) := by simp [h, Fin.castLE]
  have pred_not_last : (i.castLE <| by simp).pred not_zero ≠ Fin.last (n+1) := by simp [h, Fin.castLE, Fin.last]
  simp [get, push, not_zero, pred_not_last]
  simp [Vector.get, h]
  exact Vector.getElem_push_eq

def Word.reverse {α : Type u} {n : Nat} (w : Word α n) : Word α n :=
  ⟨ w.val.reverse ⟩

@[simp]
theorem Word.push_eq_reverse_cons {α : Type u} {n : Nat} (w : Word α n) (a : α) : w.cons a = (w.reverse.push a).reverse := by
  unfold Word.push
  unfold Word.reverse
  unfold Word.cons
  simp only [Vector.insertIdx_zero, Vector.reverse_push, Vector.reverse_reverse]

@[simp]
theorem Word.reverse_reverse {α : Type u} {n : Nat} (w : Word α n) : w.reverse.reverse = w := by
  unfold Word.reverse
  simp only [Vector.reverse_reverse]

theorem Word.reverse_nil {α : Type u} : Word.nil.reverse = (Word.nil : Word α 0) := by
  simp only [reverse, nil, Vector.reverse_mk, List.reverse_toArray, List.reverse_nil]

@[elab_as_elim]
def Word.induction {α : Type u} {motive : ∀ {n : Nat}, Word α n → Sort _} (hnil : motive .nil)
    (hcons : ∀ {n : Nat}, ∀ a : α, ∀ w : Word α n, motive w → motive (w.cons a)) :
    ∀ {n : Nat}, ∀ w : Word α n, motive w 
  | n, ⟨ wval ⟩ => wval.elimAsList go
  where
    go : {n : Nat} → (xs : List α) → (ha : xs.length = n) → motive ⟨⟨xs⟩, ha⟩
    | 0, .nil, ha => by
      have : ⟨⟨.nil⟩, ha⟩ = Word.nil := by rfl
      rw [this]
      exact hnil
    | k+1, .cons x xs, ha => by
      have hxs_len : xs.length = k := by
        rw [List.length_cons, Nat.add_left_inj] at ha
        exact ha
      let w : Word α k := ⟨⟨xs⟩, hxs_len⟩
      have hind : motive w := go xs hxs_len
      have := hcons x w hind
      rw [Word.cons_as_list] at this
      exact this

@[elab_as_elim]
def Word.inductionPush {α : Type u} {motive : ∀ {n : Nat}, Word α n → Sort _} (hnil : motive .nil)
    (hpush : ∀ {n : Nat}, ∀ a : α, ∀ w : Word α n, motive w → motive (w.push a)) {n : Nat} (w : Word α n) :
    motive w := by
  let revMotive := fun {k : Nat} => fun (w : Word α k) => motive w.reverse
  have hrevNil : revMotive .nil := hnil
  have hrevCons : ∀ {k : Nat}, ∀ a : α, ∀ w : Word α k, revMotive w → revMotive (w.cons a) := by
    intro k a w hind
    unfold revMotive
    rw [push_eq_reverse_cons, reverse_reverse]
    exact hpush a w.reverse hind
  have := Word.induction (motive := revMotive) hrevNil hrevCons w.reverse
  unfold revMotive at this
  rw [Word.reverse_reverse] at this
  exact this



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

theorem Fin.internal.val_eq_pred {n : Nat} {i : Fin (n+2)} (int : i.internal) : int.val = i.val - 1 := by
  simp only [val, coe_castLT, coe_pred]

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

def Word.getInternal {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) (int : i.internal) : α := by
  have ha := w.get_eq_symbol_of_internal int
  match hget : w.get i with
  | .left | .right => rw [hget] at ha; contradiction
  | .symbol a => exact a

-- Extract from the word ⊢ w₁ ... wₙ ⊣ the list of symbols wᵢ... wⱼ₋₁ with i=start and j=stop
def Word.extract {α : Type u} {n : Nat} (w : Word α n) (start stop : Fin (n+2)) (h1 : start.internal) (h2 : stop ≠ 0) :
    Vector α (min stop.val.pred n - start.val.pred) :=
  let vectStart := start.pred h1.left
  let vectStop := stop.pred h2
  have size_eq : min vectStop.val n - vectStart.val = min stop.val.pred n - start.val.pred := by
    simp only [Fin.coe_pred, Nat.pred_eq_sub_one, vectStop, vectStart]
  by rw [← size_eq]
     exact w.val.extract vectStart vectStop

