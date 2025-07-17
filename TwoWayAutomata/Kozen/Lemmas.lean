import Mathlib.Data.Fintype.Fin

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Configurations

namespace TwoDFA

theorem accept_at_leftEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .left m.accept = (m.accept, .right) := by
  obtain ⟨_, hBounds⟩ := m.in_bounds_left m.accept
  obtain ⟨⟨_, hPres⟩, _⟩ := m.halt_preserve_state .left
  rw [hBounds, Prod.ext_iff] at hPres
  simp only at hPres
  rwa [hPres.left] at hBounds

theorem accept_not_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) {a : TapeSymbol α} (h : a ≠ .right) : m.step a m.accept = (m.accept, .right) := by
  cases a with
  | left => exact m.accept_at_leftEnd
  | right => contradiction
  | symbol a => exact m.halt_move_right a |>.left

theorem accept_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .right m.accept = (m.accept, .left) := by
  obtain ⟨_, hBounds⟩ := m.in_bounds_right m.accept
  obtain ⟨⟨_, hPres⟩, _⟩ := m.halt_preserve_state .right
  rw [hBounds, Prod.ext_iff] at hPres
  simp only at hPres
  rwa [hPres.left] at hBounds

theorem reject_at_leftEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .left m.reject = (m.reject, .right) := by
  obtain ⟨_, hBounds⟩ := m.in_bounds_left m.reject
  obtain ⟨_, ⟨_, hPres⟩⟩ := m.halt_preserve_state .left
  rw [hBounds, Prod.ext_iff] at hPres
  simp only at hPres
  rwa [hPres.left] at hBounds

theorem reject_not_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) {a : TapeSymbol α} (h : a ≠ .right) : m.step a m.reject = (m.reject, .right) := by
  cases a with
  | left => exact m.reject_at_leftEnd
  | right => contradiction
  | symbol a => exact m.halt_move_right a |>.right

theorem reject_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .right m.reject = (m.reject, .left) := by
  obtain ⟨_, hBounds⟩ := m.in_bounds_right m.reject
  obtain ⟨_, ⟨_, hPres⟩⟩ := m.halt_preserve_state .right
  rw [hBounds, Prod.ext_iff] at hPres
  simp only at hPres
  rwa [hPres.left] at hBounds

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

theorem config_accept_at_rightEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) :
    m.nextConfig w ⟨m.accept, Fin.last _⟩ ⟨m.accept, (Fin.last _).predCast <| by simp⟩ := by
  have get_right := w.get_eq_right_of_eq_last rfl
  have step_accept := m.accept_at_rightEnd
  left
  · simpa [get_right]
  · simp [Movement.apply, Fin.castLT]
  · constructor <;> simp

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

theorem config_reject_at_rightEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) :
    m.nextConfig w ⟨m.reject, Fin.last _⟩ ⟨m.reject, (Fin.last _).predCast <| by simp⟩ := by
  have get_right := w.get_eq_right_of_eq_last rfl
  have step_reject := m.reject_at_rightEnd
  left
  · simpa [get_right]
  · simp [Movement.apply, Fin.castLT]
  · constructor <;> simp

@[simp]
theorem nextConfig.irrefl {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) (c : Config σ n) : ¬m.nextConfig w c c := by
  by_contra h
  rcases h with ⟨_, hval, _⟩ | ⟨_, hval, _⟩
  all_goals
    have := Movement.apply_ne_self _ _ hval
    contradiction

@[simp]
theorem nextConfig.halt_preserve_state {α σ : Type*} {n : Nat} {m : TwoDFA α σ} {w : Word α n} {c1 c2 : Config σ n}
  (hnext : m.nextConfig w c1 c2) (hlt : c1.state = m.accept ∨ c1.state = m.reject) :
    c2.state = c1.state := by
  rcases hlt with hlt | hlt
  case' inl =>
    have c1_def : c1 = ⟨m.accept, c1.idx⟩ := by rw [←hlt]
    obtain ⟨mv, hstep⟩ := m.halt_preserve_state (w.get c1.idx) |>.left
  case' inr =>
    have c1_def : c1 = ⟨m.reject, c1.idx⟩ := by rw [←hlt]
    obtain ⟨mv, hstep⟩ := m.halt_preserve_state (w.get c1.idx) |>.right
  all_goals
    rw [hlt]
    conv at hnext =>
      rw [←stepConfig_gives_nextConfig, c1_def]
      simp only [stepConfig, Config.ext_iff]
    unfold step at hstep
    have := hnext.left.symm
    rw [hstep] at this
    simpa

end TwoDFA
