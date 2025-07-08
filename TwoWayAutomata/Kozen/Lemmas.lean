import Mathlib.Data.Fintype.Fin

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Configurations

namespace TwoDFA

theorem accept_at_leftEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .left m.accept = (m.accept, .right) := by
  have hinBounds := m.in_bounds_left m.accept
  have hpreserve := m.halt_preserve_state .left
  cases hinBounds with
  | intro wBounds hBounds => cases hpreserve.left with
                             | intro wPres hPres => rw [hBounds, Prod.ext_iff] at hPres
                                                    simp only at hPres
                                                    rw [hPres.left] at hBounds
                                                    exact hBounds

theorem accept_not_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) {a : TapeSymbol α} (h : a ≠ .right) : m.step a m.accept = (m.accept, .right) := by
  cases a with
  | left => exact m.accept_at_leftEnd
  | right => contradiction
  | symbol a => exact m.halt_move_right a |>.left

theorem reject_at_leftEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .left m.reject = (m.reject, .right) := by
  have hinBounds := m.in_bounds_left m.reject
  have hpreserve := m.halt_preserve_state .left
  cases hinBounds with
  | intro wBounds hBounds => cases hpreserve.right with
                             | intro wPres hPres => rw [hBounds, Prod.ext_iff] at hPres
                                                    simp only at hPres
                                                    rw [hPres.left] at hBounds
                                                    exact hBounds

theorem reject_not_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) {a : TapeSymbol α} (h : a ≠ .right) : m.step a m.reject = (m.reject, .right) := by
  cases a with
  | left => exact m.reject_at_leftEnd
  | right => contradiction
  | symbol a => exact m.halt_move_right a |>.right

theorem config_accept_at_leftEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) :
    m.nextConfig w ⟨m.accept, 0⟩ ⟨m.accept, 1⟩ := by
  have get_left := w.get_eq_left_of_eq_zero rfl
  have step_accept := m.accept_at_leftEnd
  right
  · simpa [get_left]
  · simp [Movement.apply, Fin.castLT]
  · constructor <;> simp

theorem config_accept_not_at_rightEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) (idx : Fin (n+2)) (h : idx ≠ Fin.last _) :
    m.nextConfig w ⟨m.accept, idx⟩ ⟨m.accept, idx.succCast h⟩ := by
  have get_nright := w.get_neq_right_of_neq_last h
  have step_accept := m.accept_not_at_rightEnd get_nright
  right
  · simpa
  · simp [Movement.apply, Fin.castLT]
  · constructor <;> simp [h]

theorem config_reject_at_leftEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) :
    m.nextConfig w ⟨m.reject, 0⟩ ⟨m.reject, 1⟩ := by
  have get_left := w.get_eq_left_of_eq_zero rfl
  have step_reject := m.reject_at_leftEnd
  right
  · simpa [get_left]
  · simp [Movement.apply, Fin.castLT]
  · constructor <;> simp

theorem config_reject_not_at_rightEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) (idx : Fin (n+2)) (h : idx ≠ Fin.last _) :
    m.nextConfig w ⟨m.reject, idx⟩ ⟨m.reject, idx.succCast h⟩ := by
  have get_nright := w.get_neq_right_of_neq_last h
  have step_reject := m.reject_not_at_rightEnd get_nright
  right
  · simpa
  · simp [Movement.apply, Fin.castLT]
  · constructor <;> simp [h]

end TwoDFA
