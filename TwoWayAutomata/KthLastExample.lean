import TwoWayAutomata

section Helpers

def List.kth_last {α : Type _} (l : List α) (k : Nat) [knz : NeZero k] : Option α :=
  if hk : k ≤ l.length
    then
      have : l.length - k < l.length := by have := knz.pos; omega
      some l[l.length - k]
    else
      none

end Helpers

section Example

--- The family of languages in this example is parametrised by a position 'k' and a symbol 'a' from the alphabet 'α'
variable {α : Type _} [DecidableEq α] (k : Nat) [knz : NeZero k] (a : α)

--- The family of languages, each of the form "strings where the kth last symbol is 'a'"
def language : Language α := {w | w.kth_last k = some a}


/--
The states our machines will use; 'pass' will move to the right end-marker,
then 'count' will count back k steps to get to the kth last symbol.
--/
inductive ExState : Type _ where
  | pass : ExState
  | count (j : Fin (k.pred + 1)) : ExState
  deriving Fintype

--- The family of 2DFAs that recognise the previous family of languages
def machine : TwoDFA α (ExState k) where
  start := .pass
  stepOther
    | .right, .pass => (.other <| .count <| Fin.last _, .left)
    | _, .pass => (.other .pass, .right)
    -- If we run out of space while counting back, reject
    | .left, .count j => (.reject, .right)
    -- Makes some proofs easier to have this be explicit,
    -- This case is impossible to reach so we choose the returned state to make other proofs easier
    | .right, .count j => (.other <| .count j, .left)
    | .symbol sym, .count j => 
      if j = 0
        then
          if sym = a
            then (.accept, .right)
            else (.reject, .right)
        else
          (.other <| .count (j-1), .left)
  stay_in_bounds q := by cases q <;> simp

def cfg_meaning (n : Nat) : TwoDFA.ConfigMeaning n α (ExState k) where
  accept w := ∃ hk : k ≤ n, w.get ⟨n - k, by have := knz.ne; omega⟩ = a
  reject w := ∀ hk : k ≤ n, w.get ⟨n - k, by have := knz.ne; omega⟩ ≠ a
  atLeft
    | .pass, _ => True              -- pass states tell us nothing
    | .count j, _ => n = k - 1 - j.val  -- if we reach the left end while counting, the string is too short
  inWord 
    | .pass, _ => fun _ ↦ True      -- pass states tell us nothing
    | .count j, i => fun _ ↦        -- count states tell us about our position
      if i = Fin.last _
        then False  -- It is impossible to be in a count state at the right end-marker
        else i = n - (k - 1 - j.val) ∧ (k - 1 - j.val) ≤ n

theorem meaning_inductive {n : Nat} : (cfg_meaning k a n).Inductive (machine k a) where
  base w := by simp [machine, cfg_meaning]
  ind w q i ih := by
    cases hget : w.get i
    case' left =>
      have hzero : i = 0 := w.eq_zero_of_get_eq_left hget
    case' right | symbol =>
      have hzero : i ≠ 0 := by simp [←w.get_eq_left_iff_eq_0, hget]
    all_goals
      cases q
      <;> simp only [TwoDFA.stepConfig, hget, machine, Nat.pred_eq_sub_one]
    case symbol.pass | left.pass =>
      simp [cfg_meaning, SplitPredicate.apply]
    case right.pass =>
      have hlast := w.eq_last_of_get_eq_right hget
      by_cases hn : n = 0
      · suffices if n = 0 then n = k - 1 - (k - 1) else n = n - (k - 1 - (k - 1)) ∧ k ≤ n + (k - 1) + 1 by
          simpa [hlast, Fin.predCast, cfg_meaning, TwoDFA.ConfigMeaning.apply, SplitPredicate.apply, ←Fin.val_inj, Movement.apply]
        simp [hn]
      · suffices if n = 0 then n = k - 1 - (k - 1) else n = n - (k - 1 - (k - 1)) ∧ k ≤ n + (k - 1) + 1 by
          simpa [hlast, Fin.predCast, cfg_meaning, TwoDFA.ConfigMeaning.apply, SplitPredicate.apply, ←Fin.val_inj, Movement.apply]
        simp only [hn, ↓reduceIte]
        constructor <;> omega
    case right.count j =>
      have := w.eq_last_of_get_eq_right hget
      simp [TwoDFA.ConfigMeaning.apply, Movement.apply, ←Fin.val_inj, cfg_meaning, SplitPredicate.apply, this] at ih
    case left.count j =>
      simp only [TwoDFA.ConfigMeaning.apply, cfg_meaning, Nat.pred_eq_sub_one, ne_eq, Fin.coe_pred]
      intro hklt; exfalso
      apply Nat.not_le_of_gt ?hkgt hklt
      have ih : n = k - 1 - j.val := by simpa [cfg_meaning, TwoDFA.ConfigMeaning.apply, hzero] using ih
      have := knz.pos
      omega
    case symbol.count sym j =>
      have hjlt : j.val < k := by 
        have : k = k.pred + 1 := by
          rw [Nat.pred_eq_sub_one]
          symm
          exact Nat.sub_add_cancel knz.pos
        conv => rhs; rw [this]
        exact j.is_lt
      by_cases hj : j = 0
      <;> simp only [hj, ↓reduceIte, cfg_meaning, TwoDFA.ConfigMeaning.apply]
      -- j = 0
      · obtain ⟨ieq, hkles⟩ : i.val = n - (k - 1) ∧ k ≤ n + 1 := by
          have : ¬i = Fin.last _ := by simp [w.get_eq_right_iff_eq_last, hget]
          simpa [cfg_meaning, hzero, TwoDFA.ConfigMeaning.apply, SplitPredicate.apply, hj, this] using ih
        clear ih
        have hkne : k ≠ n + 1 := by
          by_contra hkeq
          simp [hkeq] at ieq
          contradiction  -- i = 0 ∧ i ≠ 0
        have hkle : k ≤ n := by omega
        clear hkles hkne
        have hget : w.val.get ⟨n - k, by omega⟩ = sym := by
          have hlast : i.pred hzero ≠ Fin.last _ := by
            rw [Fin.ne_iff_vne]
            simp only [Fin.coe_pred, Fin.val_last, ne_eq]
            have := knz.pos
            omega
          suffices ((i.pred hzero).castPred hlast) = ⟨n - k, by omega⟩ by
            simpa [this, Word.get, hzero, hlast] using hget
          simp only [← Fin.val_inj, Fin.coe_castPred, Fin.coe_pred]
          omega
        by_cases ha : sym = a
        <;> simp only [ha, ↓reduceIte, ne_eq]
        -- j = 0 ∧ sym = a
        · exists hkle
          rwa [ha] at hget
        -- j = 0 ∧ sym ≠ a
        · intro -- no name because it's redundant
          simpa [hget]
      -- j ≠ 0
      · obtain ⟨i_val, k_le⟩ : i.val = n - (k - 1 - j.val) ∧ k ≤ n + j.val + 1 := by
          have : ¬i = Fin.last _ := by simp [w.get_eq_right_iff_eq_last, hget]
          simpa [cfg_meaning, TwoDFA.ConfigMeaning.apply, hzero, SplitPredicate.apply, this] using ih
        have hj' := hj
        rw [←Fin.val_inj, Fin.val_zero] at hj
        split
        next heq => -- i - 1 = 0
          have _ : n - (k - 1 - j.val) - 1 = 0 := by
            simpa [Movement.apply, ←Fin.val_inj, i_val] using heq
          rw [Fin.val_sub_one_of_ne_zero hj']
          have _ := knz.pos
          obtain ⟨i_ne_zero, _⟩ := Movement.left.isValid_of_apply i 0 heq
          simp only [and_true, Fin.ne_iff_vne, Fin.val_zero] at i_ne_zero
          omega
        next hne => -- i - 1 ≠ 0
          simp only [SplitPredicate.apply, Movement.apply, Fin.coe_castLE, Fin.coe_pred, Nat.pred_eq_sub_one]
          rw [Fin.val_sub_one_of_ne_zero hj']
          have := i.predCast_ne_last hzero
          simp only [this, ↓reduceIte]
          constructor
          · rw [i_val]; omega
          · have : k - 1 - j.val ≤ n := by omega
            suffices k - 1 - j.val ≠ n by omega
            by_contra heq
            suffices i = 0 by contradiction
            simpa [heq] using i_val

def encoding : TwoDFA.WellFoundedEncoding (ExState k) where
  E {n} := Fin (k+1) × Fin (n+2)
  wfrel := {
    rel := Prod.Lex GT.gt LT.lt,
    wf := IsWellFounded.wf
  }
  encode 
    | (.pass, i) => (Fin.last _, i)
    | (.count j, i) => (
        j.castLT <| by
          apply j.is_lt.trans
          simp [Nat.sub_add_cancel knz.pos]
        , i.rev)

theorem machine_halts {w : List α} : ¬(machine k a).diverges w.toWord := by
  apply TwoDFA.halts_of_next_except_halt_WF
  apply TwoDFA.next_except_halt_WF_of_encoding _ (encoding k)
  intro q1 i1 q2 i2 hnext
  simp [encoding, TwoDFA.WellFoundedEncoding.rel]
  match q1, q2 with
  | .pass, .pass =>
    apply Prod.Lex.right
    cases hget : w.toWord.get i1
    case right => -- Finds a contradiction at hnext
      simp [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget] at hnext
    case left | symbol =>
      have : i2.val = i1.val + 1 := by
        simp only [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget] at hnext
        simpa [Movement.apply, ←Fin.val_inj] using hnext.symm
      rw [Fin.lt_iff_val_lt_val]
      omega
  | .pass, .count j =>
    cases hget : w.toWord.get i1
    case left | symbol =>
      simp [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget] at hnext
    case right =>
      obtain ⟨j_val, happly⟩ : Fin.last (k - 1) = j ∧ Movement.left.apply i1 ?_ = i2 := by
        simpa [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget] using hnext
      rw [←j_val]
      apply Prod.Lex.left
      simpa [Fin.lt_iff_val_lt_val] using knz.pos
  | .count j1, .count j2 =>
    cases hget : w.toWord.get i1
    case left =>
      simp [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget] at hnext
    case right =>
      obtain ⟨jeq, happly⟩ : j1 = j2 ∧ Movement.left.apply i1 ?_ = i2 := by
        simpa [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget] using hnext
      rw [jeq]
      apply Prod.Lex.right
      rw [Fin.rev_lt_rev, ←happly, Fin.lt_iff_val_lt_val]
      have := w.toWord.eq_last_of_get_eq_right hget
      simp [Movement.apply, this]
    case symbol sym =>
      by_cases hj1 : j1 = 0
      case pos =>
        by_cases hsym : sym = a
        <;> simp [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget, hj1, hsym] at hnext
      case neg =>
        obtain ⟨j_val, happly⟩ : j1 - 1 = j2 ∧ Movement.left.apply i1 ?_ = i2 := by
          simpa [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget, hj1] using hnext
        rw [←j_val]
        apply Prod.Lex.left
        rw [GT.gt, Fin.lt_iff_val_lt_val]
        simp [Fin.sub_one_lt_iff, Fin.pos_of_ne_zero hj1]
  | .count j, .pass =>
    cases hget : w.toWord.get i1
    case left =>
      simp [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget] at hnext
    case symbol sym =>
      -- All the following cases find contradictions with the resulting state
      by_cases hj : j = 0
      <;> by_cases hsym : sym = a
      <;> simp [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget, hj, hsym] at hnext
    case right =>
      have : i1 = Fin.last _ := Word.eq_last_of_get_eq_right hget
      -- We get a different contradiction here, but a contradiction none-the-less
      simp [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, machine, hget, this] at hnext

theorem machine_correct : (machine k a).language = language k a := by
  apply TwoDFA.language_eq_of_inductive _ _ _ (meaning_inductive k a)
  case hrej =>
    intro w h
    unfold language
    rw [Set.mem_setOf]
    simp only [machine, cfg_meaning, TwoDFA.ConfigMeaning.apply, ↓reduceDIte, Vector.get, List.getElem_toArray, Fin.coe_cast] at h
    by_contra hkth_last
    obtain ⟨hkle, _⟩ : ∃ hk : k ≤ w.length, _ := by simpa [List.kth_last] using hkth_last
    have := h hkle
    contradiction
  case hacc =>
    intro w h
    unfold language
    rw [Set.mem_setOf]
    simp only [machine, cfg_meaning, TwoDFA.ConfigMeaning.apply, ↓reduceDIte, Vector.get, List.getElem_toArray, Fin.coe_cast] at h
    obtain ⟨hkle, hget⟩ := h
    simp [List.kth_last, hkle, hget]
  case hdiv =>
    intro _ hdiv
    by_contra
    apply machine_halts _ _ hdiv

end Example
