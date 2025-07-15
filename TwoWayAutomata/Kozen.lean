/-
# Kozen 2DFAs

An implementation of Two-way Deterministic Finite Automata ready to follow the proof of their regularity due to Kozen.
-/ -- TODO: add reference.
import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Word
import TwoWayAutomata.Kozen.Movement
import TwoWayAutomata.Kozen.Configurations
import TwoWayAutomata.Kozen.Language
import TwoWayAutomata.Kozen.Correctness

section Evaluation

variable {α σ : Type*} (m : TwoDFA α σ) {n : Nat} (x : Word α n) 

/--
After the input number of steps, the machine m on input x can reach configuration stp from the input configuration
Morally the same as GoesTo, but pulling off the start of the run rather than the end.
-/
inductive TwoDFA.ReachesIn (stp : Config σ n) : Nat → Config σ n → Prop
  | refl : ReachesIn stp 0 stp
  | step {start mid : Config σ n} {l : Nat} (head : m.nextConfig x start mid) (tail : ReachesIn stp l mid) : ReachesIn stp l.succ start

theorem TwoDFA.ReachesIn.trans {start mid stp : Config σ n} {la lb : Nat} (ha : m.ReachesIn x mid la start) (hb : m.ReachesIn x stp lb mid) : m.ReachesIn x stp (la + lb) start := by
  induction ha with
  | refl => simp [hb]
  | step hhead _ ih => 
    have := ih.step hhead
    simpa [Nat.add_comm]

def TwoDFA.ReachesIn.single {start stp : Config σ n} (hstep : m.nextConfig x start stp) : m.ReachesIn x stp 1 start :=
  .step hstep .refl

def TwoDFA.ReachesIn.tail {start mid stp : Config σ n} {l : Nat} (hstep : m.nextConfig x mid stp) (hhead : m.ReachesIn x mid l start) : m.ReachesIn x stp l.succ start :=
  .trans m x hhead <| .single m x hstep

theorem TwoDFA.ReachesIn.config_eq_of_len_0 {strt stp : Config σ n} {l : Nat} (hreach : m.ReachesIn x stp l strt) (hl : l = 0) : strt = stp := by
  rw [hl] at hreach
  cases hreach with
  | refl => rfl

theorem TwoDFA.ReachesIn_of_GoesTo {start stp : Config σ n} (h : m.GoesTo x start stp) : ∃ l : Nat, m.ReachesIn x stp l start := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | tail _ htail hind =>
    have ⟨headl, hind⟩ := hind
    use headl.succ
    exact .tail m x htail hind

theorem TwoDFA.GoesTo_of_ReachesIn {start stp : Config σ n} {l : Nat} (h : m.ReachesIn x stp l start) : m.GoesTo x start stp := by
  induction h with
  | refl => exact .refl
  | step hhead _ hind => exact GoesTo.head hhead hind

theorem TwoDFA.GoesTo_iff_ReachesIn {start stp : Config σ n} : m.GoesTo x start stp ↔ ∃ l : Nat, m.ReachesIn x stp l start where
  mp := ReachesIn_of_GoesTo m x
  mpr := by rintro ⟨l, h⟩; exact GoesTo_of_ReachesIn m x h

def TwoDFA.reachesIn (nsteps : Nat) (c : Config σ n) : Prop :=
  m.ReachesIn x c nsteps ⟨ m.start, 0 ⟩

def TwoDFA.acceptsFrom (c : Config σ n) (nsteps : Nat) : Prop :=
  ∃ i : Fin (n+2), m.ReachesIn x ⟨ m.accept, i⟩ nsteps c

def TwoDFA.cyclesAt (c : Config σ n) (len : Nat) : Prop :=
  m.ReachesIn x c len.succ c

theorem TwoDFA.cyclesAt_of_cyclesAt_step (c : Config σ n) (len : Nat) (h : m.cyclesAt x c len) :
    m.cyclesAt x (m.stepConfig x c) len := by
  cases h with
  | @step _ mid _ head tail =>
    have : m.ReachesIn x mid len.succ mid := TwoDFA.ReachesIn.tail m x head tail
    rw [←stepConfig_gives_nextConfig] at head
    rwa [head]

def TwoDFA.stepBack (c : Config σ n) : Set (Config σ n) := { cprev : Config σ n | m.nextConfig x cprev c }

theorem TwoDFA.stepBack_Nonempty_of_notStart_of_GoesTo (c : Config σ n) (hc : c ≠ ⟨m.start, 0⟩) (hgoes : m.GoesTo x ⟨m.start, 0⟩ c) : m.stepBack x c |>.Nonempty := by
  induction hgoes with
  | refl => contradiction
  | @tail mid _ _ tail _ =>
    simp only [Set.Nonempty]
    use mid
    simpa [stepBack]

theorem TwoDFA.ReachesIn.split_last {strt stp : Config σ n} {len : Nat} (h : m.ReachesIn x stp len strt) (hlen : len ≠ 0) :
    ∃ mid : Config σ n, m.nextConfig x mid stp ∧ m.ReachesIn x mid len.pred strt := by
  induction h with
  | refl => contradiction -- hlen : 0 ≠ 0
  | @step strt' _ l head tail ih =>
    if hl : l = 0
      then
        use strt'
        constructor
        · rwa [←tail.config_eq_of_len_0 m x hl]
        · simp [hl, TwoDFA.ReachesIn.refl]
      else
        obtain ⟨mid', hnext, hreach⟩ := ih hl
        use mid'
        constructor
        · exact hnext
        · have := hreach.step head
          rw [Nat.succ_pred_eq_of_ne_zero hl] at this
          simpa

theorem TwoDFA.ReachesIn.split_trans {m : TwoDFA α σ} {x : Word α n} {strt mid stp : Config σ n} {l1 l2 : Nat} (h1 : m.ReachesIn x stp (l1 + l2) strt) (h2 : m.ReachesIn x mid l1 strt) :
    m.ReachesIn x stp l2 mid := by
  sorry

theorem TwoDFA.cyclesAt_stepBack_of_cyclesAt (c : Config σ n) (len : Nat) (h : m.cyclesAt x c len) :
    ∃ prev ∈ m.stepBack x c, m.cyclesAt x prev len := by
  obtain ⟨mid, hnext, hreach⟩ := h.split_last (hlen := by simp)
  use mid
  constructor
  · simp [stepBack, hnext]
  · exact hreach.step hnext

theorem TwoDFA.config_eq_of_cycles_of_ReachesIn {m : TwoDFA α σ} {x : Word α n} (c1 c2 : Config σ n) {len : Nat} (hcycles : m.cyclesAt x c1 len) (hreaches : m.ReachesIn x c2 len.succ c1) : c1 = c2 :=
  sorry

theorem TwoDFA.ReachesIn.remove_initial_cycle {m : TwoDFA α σ} {x : Word α n} {start c : Config σ n} {len k : Nat} (hk : len ≤ k) (hcycle : m.cyclesAt x start len) (hreaches : m.ReachesIn x c k start) :
    m.ReachesIn x c (k - len) start := by
  sorry

theorem TwoDFA.reachesIn_maxSteps_of_reaches [fin_cfgs : Fintype (Config σ n)] (c : Config σ n) (h : m.reaches x c) :
    ∃ k ≤ fin_cfgs.card, m.reachesIn x k c := by
  sorry

theorem TwoDFA.reaches_iff_reachesIn_maxSteps [fin_cfgs : Fintype (Config σ n)] (c : Config σ n) : m.reaches x c ↔ ∃ k ≤ fin_cfgs.card, m.reachesIn x k c where
  mp := m.reachesIn_maxSteps_of_reaches x c
  mpr := by
    rintro ⟨k, hk, hreachesIn⟩
    exact m.GoesTo_of_ReachesIn x hreachesIn

end Evaluation

section Proving

variable {n : Nat} {α σ : Type*}

/- theorem TwoDFA.ConfigMeaning.reachable_of_apply (motive : ConfigMeaning n α σ) (m : TwoDFA α σ) (w : Word α n) -/
/-   (base : motive.apply w ⟨m.start, 0⟩) (ind : ∀ cfg : Config σ n, motive.apply w cfg → motive.apply w (m.stepConfig w cfg)) -/
/-   (cfg : Config σ n) (happly : motive.apply w cfg) : -/
/-     m.reaches w cfg := by -/
/-   sorry -/

def TwoDFA.stepBackTimes (m : TwoDFA α σ) (w : Word α n) (k : Nat) (cfg : Config σ n) : Set (Config σ n) :=
  match k with
  | 0 => {cfg}
  | k + 1 =>
    let prevs := m.stepBack w cfg
    ⋃₀ prevs.image (m.stepBackTimes w k)

theorem TwoDFA.reachesIn_of_start_mem_stepBackTimes (m : TwoDFA α σ) (w : Word α n) (k : Nat) (cfg : Config σ n)
  (h : ⟨m.start, 0⟩ ∈ m.stepBackTimes w k cfg) : m.reachesIn w k cfg := by
  match k with
  | 0 =>
    conv at h =>
      simp [TwoDFA.stepBackTimes]
    rw [←h]
    exact .refl
  | k + 1 =>
    conv at h =>
      simp [stepBackTimes]
    rcases h with ⟨prev, ⟨hstepBack, hind⟩⟩
    apply TwoDFA.ReachesIn.tail m w
    · simpa using hstepBack
    · exact m.reachesIn_of_start_mem_stepBackTimes w k prev hind

end Proving
