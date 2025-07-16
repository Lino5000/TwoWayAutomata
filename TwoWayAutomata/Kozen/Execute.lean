import Mathlib.Data.Fintype.Defs

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Configurations
import TwoWayAutomata.Kozen.Language
import TwoWayAutomata.Kozen.Lemmas
import TwoWayAutomata.Kozen.Movement
import TwoWayAutomata.Kozen.Word

inductive RunResult : Type
  | accept : RunResult
  | reject : RunResult
  | cycle : RunResult

namespace TwoDFA

variable {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) 

def execute [DecidableEq σ] [fin_cfgs : Fintype (Config σ n)] : RunResult :=
  let last_config := m.runOn w fin_cfgs.card
  if last_config.state = m.accept
    then .accept
    else if last_config.state = m.reject
      then .reject
      -- We step as many times as there are unique configurations; if we haven't terminated yet we never will
      else .cycle

theorem execute_accept_iff_runOn_state_eq_accept [DecidableEq σ] [fin_cfgs : Fintype (Config σ n)] :
    m.execute w = .accept ↔ (m.runOn w fin_cfgs.card).state = m.accept where
  mp := by
    intro hexec
    by_contra hne
    simp [execute, hne] at hexec
    if h : (m.runOn w (Fintype.card (Config σ n))).state = m.reject
      then simp [h] at hexec
      else simp [h] at hexec
  mpr := by
    intro heq
    simp [execute, heq]

-- If steps > card, the same config must appear earlier in the run, and we can repeat that logic until we get steps' ≤ card
theorem runOn_max_steps [Fintype σ] (steps : Nat) (cfg : Config σ n) (h : m.runOn w steps = cfg) :
    ∃ steps' ≤ Fintype.card (Config σ n), m.runOn w steps' = cfg := by
  sorry

theorem accepts_iff_runOn_max_eq_accept [Fintype σ] : m.accepts w ↔ ∃ i, m.runOn w (Fintype.card (Config σ n)) = ⟨m.accept, i⟩ where
  mp := by
    rintro ⟨pos, hreach⟩
    obtain ⟨steps, hrun⟩ := runOn_of_reaches (h := hreach)
    rcases em (steps ≤ Fintype.card (Config σ n)) with hsteps | _
    case' inr =>
      -- In the steps > card case, we use runOn_max_steps to get an early-enough point in the run that is the same configuration
      obtain ⟨steps, hsteps, hrun⟩ := runOn_max_steps (h := hrun)
    all_goals
      clear * - hsteps hrun
      let remaining := Fintype.card (Config σ n) - steps
      have : steps + remaining = Fintype.card (Config σ n) := by simp [remaining, hsteps]
      rw [←this]; clear this
      use (m.runOn w (steps + remaining)).idx
      ext : 1 <;> simp only
      apply m.accept_preserve_state w pos (m.runOn w (steps + remaining))
      rw [←hrun]
      apply runOn_GoesTo
  mpr := by
    rintro ⟨i, hrun⟩
    use i
    rw [←hrun]
    apply reaches_runOn

theorem accepts_iff_execute_eq_accept [DecidableEq σ] [Fintype σ] : m.accepts w ↔ m.execute w = .accept := by
  rw [execute_accept_iff_runOn_state_eq_accept, accepts_iff_runOn_max_eq_accept]
  constructor
  -- m.accepts w → m.execute w = .accept
  · rintro ⟨_, hrun⟩
    rw [hrun]
  -- m.execute w = .accept → m.accepts w
  · intro h
    use (m.runOn w (Fintype.card (Config σ n))).idx
    ext : 1
    · exact h
    · rfl

end TwoDFA
