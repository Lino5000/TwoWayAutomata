import TwoWayAutomata.Kozen.Correctness
import TwoWayAutomata.Kozen.Termination

import TwoWayAutomata.Visualise.TwoDFA

abbrev allOnes (x : List (Fin 2)) : Prop := x.all (· == 1)

def exampleLanguage : Language (Fin 2) := { x | allOnes x}


inductive ExampleState : Type where
  | q : ExampleState
  deriving Fintype

def exampleStep (a : TapeSymbol (Fin 2)) (s : ExampleState) : State ExampleState × Movement :=
  match s, a with
  | .q, .right => (.accept, .left)
  | .q, .symbol 0 => (.other .q, .left)
  | .q, _ => (.other .q, .right)

/-- A 2DFA that recognises strings consisting of entirely 1's, diverging on any string that contains a 0 -/
def example2DFA : TwoDFA (Fin 2) ExampleState where
  start := .q
  stepOther := exampleStep
  stay_in_bounds p := by
    cases p
    simp [exampleStep]

def exampleConfigMeaning {n : Nat} : TwoDFA.ConfigMeaning n (Fin 2) ExampleState where
  accept w := w.all (· == 1)
  reject w := w.any (· != 1)
  atLeft | .q, _ => True
  inWord | .q, _ => fun ⟨wl, _⟩ ↦ wl.all (· == 1)

theorem exampleCMInductive {n : Nat} : exampleConfigMeaning.Inductive (n := n) example2DFA where
  base := by simp [exampleConfigMeaning, example2DFA]
  ind := by
    rintro w s i hind
    let get_res := w.get i
    match hs : s, hget : get_res with
    | .q, .right =>
      have hright : i = Fin.last _ := w.eq_last_of_get_eq_right hget
      rw [hright]; rw [hright] at hind
      conv at hget => unfold get_res; rw [hright]
      simp only [TwoDFA.stepConfig, example2DFA, hget, exampleStep]
      simp only [Movement.apply, Fin.predCast, Fin.castLE, Fin.coe_pred, Fin.val_last, add_tsub_cancel_right]
      have last_ne_zero : Fin.last (n+1) ≠ 0 := by symm; simp
      conv at hind =>
        simp only [TwoDFA.ConfigMeaning.apply, last_ne_zero, ↓reduceDIte]
        simp only [SplitPredicate.apply, exampleConfigMeaning, Word.split_append, Word.split_last, Vector.all_cast, Vector.any_cast]
      if hn : n = 0
        then simp [TwoDFA.ConfigMeaning.apply, hn, exampleConfigMeaning]
        else
          have : ⟨n, by simp⟩ ≠ (0 : Fin (n+2)) := by
            rw [←Fin.zero_eta, Fin.ne_iff_vne]
            simp [hn]
          simpa only [TwoDFA.ConfigMeaning.apply, this, ↓reduceDIte, exampleConfigMeaning]
    | .q, .left =>
      have hleft : i = 0 := w.eq_zero_of_get_eq_left hget
      rw [hleft]; rw [hleft] at hind
      conv at hget => unfold get_res; rw [hleft]
      simp only [TwoDFA.stepConfig, example2DFA, hget, exampleStep]
      simp only [Movement.apply, Fin.castLT, Fin.succ_zero_eq_one, Fin.coe_ofNat_eq_mod, Nat.one_mod, Fin.mk_one]
      conv at hind =>
        simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, one_ne_zero, ↓reduceDIte]
        simp only [SplitPredicate.apply, Word.split_append]
      simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, one_ne_zero, ↓reduceDIte]
      simp [SplitPredicate.apply, Word.split_one]
    | .q, .symbol 0 =>
      unfold get_res at hget
      have hint : i.internal := w.internal_of_get_eq_symbol ⟨_, hget⟩
      simp only [TwoDFA.stepConfig, example2DFA, hget, exampleStep]
      simp only [Movement.apply]
      conv at hind =>
        simp only [TwoDFA.ConfigMeaning.apply, hint.left, ↓reduceDIte]
        simp only [SplitPredicate.apply, exampleConfigMeaning, Word.split_append, Vector.all_cast, Vector.any_cast]
      if hpred : i.predCast hint.left = 0 
        then simp [hpred, exampleConfigMeaning]
        else
          simp only [TwoDFA.ConfigMeaning.apply, hpred, ↓reduceDIte]
          simp only [SplitPredicate.apply, exampleConfigMeaning]
          have : 1 < i := by 
            simp [Fin.predCast, Fin.castLE] at hpred
            rw [Fin.lt_iff_val_lt_val, Fin.val_one]
            exact Nat.lt_of_sub_ne_zero hpred
          conv at hind =>
            rw [w.split_pred _ this]
            simp only [Vector.all_cast, Vector.all_push, Bool.and_eq_true]
          exact hind.left
    | .q, .symbol 1 =>
      unfold get_res at hget
      have hint : i.internal := w.internal_of_get_eq_symbol ⟨_, hget⟩
      simp only [TwoDFA.stepConfig, example2DFA, hget, exampleStep]
      simp only [Movement.apply]
      conv at hind =>
        simp only [TwoDFA.ConfigMeaning.apply, hint.left, ↓reduceDIte]
        simp only [SplitPredicate.apply, exampleConfigMeaning, Word.split_append, Vector.all_cast, Vector.any_cast]
      have : i.succ.castLT hint.val_succ_lt ≠ 0 := by
        rw [←Fin.zero_eta, Fin.ne_iff_vne]
        simp
      simp only [TwoDFA.ConfigMeaning.apply, this, ↓reduceDIte]
      simp only [SplitPredicate.apply, exampleConfigMeaning]
      rw [←w.split_succ _ hint.left hint.right]
      simp only [Vector.all_cast, Vector.all_push, Bool.and_eq_true]
      constructor
      · assumption
      · simpa using w.getInternal_eq_get _ hint |>.trans hget

def cfg_encoding : TwoDFA.WellFoundedEncoding ExampleState where
  E := fun n ↦ Fin (n+2)
  wfrel := {
    rel := LT.lt,
    wf := IsWellFounded.wf
  }
  encode c := c.snd

lemma get_eq_one_of_allOnes (w : List (Fin 2)) (h : allOnes w) {i : Fin (w.length)} : w.get i = 1 := by
  conv at h =>
    unfold allOnes
    rw [List.all_eq_true]
  have := h (w.get i) <| w.get_mem _
  simpa

lemma eq_one_of_allOnes_of_get_eq_symbol {w : List (Fin 2)} {p : Fin (w.length + 2)} (hones : allOnes w) {a : Fin 2} (hget : w.toWord.get p = .symbol a) :
    w.toWord.get p = .symbol 1 := by
  have int : p.internal := w.toWord.internal_of_get_eq_symbol ⟨_, hget⟩
  simp only [← w.toWord.getInternal_eq_get _ int, TapeSymbol.symbol.injEq]
  rw [w.toWord.getInternal_eq_getElem]
  simp only [List.toWord, Array.toVector, getElem, Vector.get, Array.getInternal]
  exact get_eq_one_of_allOnes w hones

theorem example_halts_of_allOnes {w : List (Fin 2)} (h : allOnes w) : ¬example2DFA.diverges w.toWord := by
  apply TwoDFA.halts_of_next_except_halt_WF
  apply TwoDFA.next_except_halt_WF_of_encoding _ cfg_encoding
  rintro ⟨q⟩ p1 ⟨q⟩ p2 hnext
  simp only [cfg_encoding, TwoDFA.WellFoundedEncoding.rel]
  simp only [example2DFA, ← TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, TwoDFA.Config.mk.injEq] at hnext
  obtain ⟨hstate, hpos⟩ := hnext
  cases hget : w.toWord.get p1 with
  | right => simp [hget, exampleStep] at hstate  -- Contradiction; .q at .right always steps to .t, not .q
  | left =>
    simp only [exampleStep, hget] at hpos
    unfold Movement.apply at hpos
    simp [←hpos, Fin.lt_iff_val_lt_val]
  | symbol a =>
    have hget : w.toWord.get p1 = .symbol 1 := eq_one_of_allOnes_of_get_eq_symbol h hget
    simp only [exampleStep, hget] at hpos
    unfold Movement.apply at hpos
    simp [←hpos, Fin.lt_iff_val_lt_val]

theorem exampleAcceptsLanguage : example2DFA.language = exampleLanguage := by
  apply example2DFA.language_eq_of_inductive (hind := exampleCMInductive)
  case hacc | hrej =>
    intro w h
    unfold exampleLanguage
    rw [Set.mem_setOf]
    have : Fin.last (w.length + 1) ≠ 0 := by simp
    conv at h =>
      simp only [example2DFA, exampleConfigMeaning, TwoDFA.ConfigMeaning.apply, this, ↓reduceDIte]
      simp only [SplitPredicate.apply, Word.split_append, Vector.all_cast, Vector.any_cast]
    simpa using h
  case hdiv =>
    intro w hdiv h
    conv at h =>
      unfold exampleLanguage
      rw [Set.mem_setOf]
    absurd hdiv
    apply example_halts_of_allOnes h

section Visualise

instance : ToString ExampleState where
  toString | .q => "q"

instance : LinearOrder ExampleState := by
  apply LinearOrder.lift' (fun _ ↦ (0 : Nat))
  intro x y _
  cases x
  cases y
  rfl

def main := IO.println example2DFA.asDotGraph

end Visualise
