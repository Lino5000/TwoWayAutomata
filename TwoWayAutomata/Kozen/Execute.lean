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

abbrev NatUpTo (n : Nat) : Type _ := Finset.range (n+1)

lemma NatUpTo.card_eq {n : Nat} : Fintype.card (NatUpTo n) = n + 1 := by simp

theorem runOn_earlier_of_runOn_card [Fintype σ] : ∃ steps ≤ Fintype.card (Config σ n), m.runOn w steps = m.runOn w (Fintype.card (Config σ n) + 1) := by
  let cfgcard := Fintype.card (Config σ n)
  let runOn' : NatUpTo cfgcard → Config σ n := fun n' ↦ m.runOn w n'
  obtain ⟨e1, e2, hne, hrun'⟩ := Fintype.exists_ne_map_eq_of_card_lt runOn' <| by
    suffices Fintype.card (NatUpTo cfgcard) = Fintype.card (Config σ n) + 1 by simp [this]
    apply NatUpTo.card_eq
  have val_ne : e1.val ≠ e2.val := by rw [Subtype.coe_ne_coe]; exact hne
  have hrep : m.runOn w e1.val = m.runOn w e2.val := by unfold runOn' at hrun'; exact hrun'
  have hle1 : e1.val ≤ cfgcard := by rw [←Finset.mem_range_succ_iff]; exact e1.property
  have hle2 : e2.val ≤ cfgcard := by rw [←Finset.mem_range_succ_iff]; exact e2.property
  rcases Nat.lt_or_lt_of_ne val_ne with hlt | hlt
  case' inl => -- e1 < e2
    let a := e1.val; let b := e2.val
    have ha : a = e1 := rfl; have hb : b = e2 := rfl
    have hlea : a ≤ cfgcard := by rw [ha]; exact hle1
    have hleb : b ≤ cfgcard := by rw [hb]; exact hle2
  case' inr => -- e1 > e2
    let a := e2.val; let b := e1.val
    have ha : a = e2 := rfl; have hb : b = e1 := rfl
    have hlea : a ≤ cfgcard := by rw [ha]; exact hle2
    have hleb : b ≤ cfgcard := by rw [hb]; exact hle1
    have hrep := hrep.symm
  all_goals
    rw [←ha, ←hb] at hlt hrep
    clear * - hlea hleb hlt hrep
    let k := b - a
    have hadd : b = a + k := by symm; exact Nat.add_sub_of_le <| Nat.le_of_lt hlt
    have hkpos : 0 < k := Nat.sub_pos_of_lt hlt
    rw [hadd] at hrep hleb
    let off := (cfgcard + 1) - b
    have hadd2 : cfgcard + 1 = a + k + off := by
      unfold off; rw [hadd]
      symm
      apply Nat.add_sub_of_le
      apply Nat.le_trans hleb
      simp
    use a + off
    constructor
    -- a + off ≤ cfgcard
    · omega -- Automated proof of Nat and Int linear arithmetic, which is sufficient here
    -- runOn (a+off) = runOn (cfgcard+1)
    · rw [hadd2]
      apply run_repeats_offset (h := hrep)


-- If steps > card, the same config must appear earlier in the run, and we can repeat that logic until we get steps' ≤ card
theorem runOn_max_steps_of_reachable [Fintype σ] (cfg : Config σ n) (h : m.reaches w cfg) :
    ∃ steps ≤ Fintype.card (Config σ n), m.runOn w steps = cfg := by
  induction h with
  | refl => use 0; simp [runOn]
  | tail hd tl ih =>
    obtain ⟨steps, hle, hrun⟩ := ih
    have runOn_steps_succ_eq_stp := by
      have := m.runOn_step w steps
      rw [hrun] at this
      exact nextConfig_right_unique this tl
    if heq : steps = Fintype.card (Config σ n)
      then
        obtain ⟨steps', hsteps', hrun'⟩ := m.runOn_earlier_of_runOn_card w
        rw [←runOn_steps_succ_eq_stp]
        exists steps'
        simp [hsteps', hrun', heq]
      else
        use steps + 1
        constructor
        · exact Nat.lt_of_le_of_ne hle heq
        · exact runOn_steps_succ_eq_stp

theorem accepts_iff_runOn_max_eq_accept [Fintype σ] : m.accepts w ↔ ∃ i, m.runOn w (Fintype.card (Config σ n)) = ⟨m.accept, i⟩ where
  mp := by
    rintro ⟨pos, hreach⟩
    obtain ⟨steps, hsteps, hrun⟩ := runOn_max_steps_of_reachable (h := hreach)
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
