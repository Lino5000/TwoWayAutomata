import Mathlib.Data.Fintype.Defs

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Configurations
import TwoWayAutomata.Kozen.Movement
import TwoWayAutomata.Kozen.Word

inductive RunResult : Type
  | accept : RunResult
  | reject : RunResult
  | cycle : RunResult


namespace TwoDFA

variable {α σ : Type*} {n : Nat} (m : TwoDFA α σ) (w : Word α n) 

def stepConfig : Config σ n → Config σ n
  | ⟨ state, idx ⟩ => match hstep : m.step (w.get idx) state with
                      | ⟨ nextState, move ⟩ =>
                        let hvalid : move.isValid idx := m.step_move_always_valid hstep
                        ⟨ nextState, move.apply idx hvalid ⟩

theorem stepConfig_gives_nextConfig (c1 c2 : Config σ n) : m.stepConfig w c1 = c2 ↔ m.nextConfig w c1 c2 where
  mp := by
    intro h 
    rcases hstep : m.step (w.get c1.idx) c1.state with ⟨t, move⟩
    simp [hstep, stepConfig, Config.ext_iff] at h
    cases hmove : move
    · left
      · rwa [← h.left, ← hmove]
      · rw [← h.right]
        simp only [hmove]
      · rw [← hmove]
        exact move.isValid_of_apply _ _ h.right
    · right
      · rwa [← h.left, ← hmove]
      · rw [← h.right]
        simp only [hmove]
      · rw [← hmove]
        exact move.isValid_of_apply _ _ h.right
  mpr := by
    rintro (⟨hstep, _, happly⟩ | ⟨hstep, _, happly⟩)
    all_goals
      simp only [stepConfig, hstep]
      ext
      · simp only
      · simp only [happly]

def stepTimes (steps : Nat) (strt : Config σ n) : Config σ n :=
  match steps with
  | 0 => strt
  | n + 1 => m.stepConfig w <| stepTimes n strt

def execute [DecidableEq σ] [fin_cfgs : Fintype (Config σ n)] : RunResult :=
  let last_config := m.stepTimes w fin_cfgs.card m.init
  if last_config.state = m.accept
    then .accept
    else if last_config.state = m.reject
      then .reject
      -- We step as many times as there are unique configurations; if we haven't terminated yet we never will
      else .cycle

end TwoDFA
