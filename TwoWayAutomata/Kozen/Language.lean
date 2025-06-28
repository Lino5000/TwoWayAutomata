import Mathlib.Computability.Language
import Mathlib.Data.Fin.Basic

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Word
import TwoWayAutomata.Kozen.Movement
import TwoWayAutomata.Kozen.Configurations

variable {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (x : Word α n) 

namespace TwoDFA

/--
After some number of steps, the machine m on input x will go from configuration start to the input configuration.
-/
inductive GoesTo (start : Config σ n) : Config σ n → Prop
  | refl : GoesTo start start
  | tail {mid stp : Config σ n} (head : GoesTo start mid) (tail : m.nextConfig x mid stp) : GoesTo start stp

namespace GoesTo

@[trans]
theorem trans {start mid stp : Config σ n} (ha : m.GoesTo x start mid) (hb : m.GoesTo x mid stp) : m.GoesTo x start stp := by
  induction hb with
  | refl => exact ha
  | tail _ htail ih => exact ih.tail htail

def single {start stp : Config σ n} (hstep : m.nextConfig x start stp) : m.GoesTo x start stp :=
  tail refl hstep

def head {start mid stp : Config σ n} (hstep : m.nextConfig x start mid) (htail : m.GoesTo x mid stp) :
    m.GoesTo x start stp := trans m x (single m x hstep) htail

end GoesTo



def reaches (c : Config σ n) : Prop :=
  m.GoesTo x ⟨ m.start, 0 ⟩ c

def accepts : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ m.accept, i ⟩

def rejects : Prop :=
  ∃ i : Fin (n+2), m.reaches x ⟨ m.reject, i ⟩

def language (m : TwoDFA α σ) : Language α :=
  {x : List α | m.accepts x.toWord }

theorem accept_lt_accept (i j : Fin (n+2)) (h : i < j) : m.GoesTo x ⟨ m.accept, i ⟩ ⟨ m.accept, j ⟩ := by
  have j_ne_zero : j ≠ 0 := Fin.ne_zero_of_lt h
  have one_le_j : 1 ≤ j.val := by
    suffices 1 ≤ j by simpa
    exact Fin.one_le_of_ne_zero j_ne_zero
  cases ha : x.get i with
  | right =>
    rw [Word.eq_last_of_get_eq_right ha] at h
    suffices ¬ Fin.last (n+1) < j by contradiction
    simp [j.le_last]
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
          have prev_def : prevIdx = j.predCast j_ne_zero := rfl
          suffices i ≤ prevIdx by simp [Fin.lt_iff_le_and_ne, this, heq, Ne.symm]
          rw [Fin.lt_def] at h
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


theorem reaches_accept_last_of_accepts (haccept : m.accepts x) : m.reaches x ⟨ m.accept, Fin.last (n+1) ⟩ := by
  rcases haccept with ⟨idx, hidx⟩
  if h : idx = Fin.last (n+1)
    then rwa [← h]
    else
      unfold reaches
      trans
      · exact hidx
      · apply m.accept_lt_accept x idx (Fin.last _)
        exact Fin.lt_last_iff_ne_last.mpr h

end TwoDFA
