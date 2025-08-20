import Mathlib.Data.Fintype.Fin

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Configurations

namespace TwoDFA

theorem accept_at_leftEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .left .accept = (.accept, .right) := by
  simp [step]

theorem accept_not_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) {a : TapeSymbol α} (h : a ≠ .right) : m.step a .accept = (.accept, .right) := by
  cases a with
  | right => contradiction
  | left | symbol a => simp [step]

theorem accept_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .right .accept = (.accept, .left) := by
  simp [step]

theorem reject_at_leftEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .left .reject = (.reject, .right) := by
  simp [step]

theorem reject_not_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) {a : TapeSymbol α} (h : a ≠ .right) : m.step a .reject = (.reject, .right) := by
  cases a with
  | right => contradiction
  | left | symbol a => simp [step]

theorem reject_at_rightEnd {α σ : Type*} (m : TwoDFA α σ) : m.step .right .reject = (.reject, .left) := by
  simp [step]

theorem config_accept_at_leftEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) :
    m.nextConfig w ⟨.accept, 0⟩ ⟨.accept, 1⟩ := by
  rw [←stepConfig_gives_nextConfig]
  simp only [stepConfig, step, Word.get_eq_left_of_eq_zero, Config.mk.injEq, true_and]
  simp [Movement.apply, ←Fin.val_inj]

theorem config_accept_not_at_rightEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) (idx : Fin (n+2)) (h : idx ≠ Fin.last _) :
    m.nextConfig w ⟨.accept, idx⟩ ⟨.accept, idx.succCast h⟩ := by
  rw [←stepConfig_gives_nextConfig]
  simp only [stepConfig, step, w.get_neq_right_of_neq_last h, imp_self, Config.mk.injEq, true_and]
  simp [Movement.apply, ←Fin.val_inj]

theorem config_accept_at_rightEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) :
    m.nextConfig w ⟨.accept, Fin.last _⟩ ⟨.accept, (Fin.last _).predCast <| by simp⟩ := by
  rw [←stepConfig_gives_nextConfig]
  simp only [stepConfig, step, Word.get_eq_right_of_eq_last, Config.mk.injEq, true_and]
  simp [Movement.apply, ←Fin.val_inj]

theorem config_reject_at_leftEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) :
    m.nextConfig w ⟨.reject, 0⟩ ⟨.reject, 1⟩ := by
  rw [←stepConfig_gives_nextConfig]
  simp only [stepConfig, step, Word.get_eq_left_of_eq_zero, Config.mk.injEq, true_and]
  simp [Movement.apply, ←Fin.val_inj]

theorem config_reject_not_at_rightEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) (idx : Fin (n+2)) (h : idx ≠ Fin.last _) :
    m.nextConfig w ⟨.reject, idx⟩ ⟨.reject, idx.succCast h⟩ := by
  rw [←stepConfig_gives_nextConfig]
  simp only [stepConfig, step, w.get_neq_right_of_neq_last h, imp_self, Config.mk.injEq, true_and]
  simp [Movement.apply, ←Fin.val_inj]

theorem config_reject_at_rightEnd {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) :
    m.nextConfig w ⟨.reject, Fin.last _⟩ ⟨.reject, (Fin.last _).predCast <| by simp⟩ := by
  rw [←stepConfig_gives_nextConfig]
  simp only [stepConfig, step, Word.get_eq_right_of_eq_last, Config.mk.injEq, true_and]
  simp [Movement.apply, ←Fin.val_inj]

@[simp]
theorem nextConfig.irrefl {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) (c : Config σ n) : ¬m.nextConfig w c c := by
  by_contra h
  rcases h with ⟨_, hval, _⟩ | ⟨_, hval, _⟩
  all_goals
    have := Movement.apply_ne_self _ _ hval
    contradiction

@[simp]
theorem nextConfig.must_move {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) (c1 c2 : Config σ n) (h : c1.idx = c2.idx) : ¬m.nextConfig w c1 c2 := by
  rintro (⟨_, hvalid, hmv⟩ | ⟨_, _, hmv⟩)
  all_goals simp [h, Movement.apply, ←Fin.val_inj] at hmv
  -- Just a little more to do in the stepLeft case
  suffices c2.idx.val - 1 ≠ c2.idx.val by contradiction
  apply Nat.sub_one_ne_self
  simpa [h] using hvalid.hleft

@[simp]
theorem nextConfig.halt_preserve_state {α σ : Type*} {n : Nat} {m : TwoDFA α σ} {w : Word α n} {c1 c2 : Config σ n}
  (hnext : m.nextConfig w c1 c2) (hlt : c1.state = .accept ∨ c1.state = .reject) :
    c2.state = c1.state := by
  rcases hlt with hlt | hlt
  case' inl =>
    have c1_def : c1 = ⟨.accept, c1.idx⟩ := by rw [←hlt]
  case' inr =>
    have c1_def : c1 = ⟨.reject, c1.idx⟩ := by rw [←hlt]
  all_goals
    cases hget : w.get c1.idx; all_goals
      conv at hnext =>
        rw [←stepConfig_gives_nextConfig, c1_def]
        simp only [stepConfig, step, hget]
      rw [c1_def, ←hnext]

end TwoDFA
