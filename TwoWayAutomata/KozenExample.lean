import TwoWayAutomata.Kozen.Correctness
import TwoWayAutomata.Kozen.Termination

import TwoWayAutomata.Visualise.TwoDFA

theorem Vector.count_tail {α : Type _} [BEq α] (n : Nat) (w : Vector α (n+1)) (a : α) : Vector.count a w = Vector.count a w.tail + if w[0] == a then 1 else 0 := by
  have eq_push_front : w = w.tail.insertIdx 0 w[0] := by
    suffices #[w[0]] = w.toArray.extract 0 1 by simp [insertIdx, this, Array.extract_eq_self_of_le]
    rw [Array.extract_succ_right (by simp) (by simp)]
    simp
  conv =>
    lhs
    rw [eq_push_front]
    simp only [Nat.add_one_sub_one, insertIdx_zero, count_cast, count_append, count_mk, List.count_toArray, List.count_singleton]
    rw [Nat.add_comm]

theorem Vector.tail_cast {α : Type _} {n m : Nat} (w : Vector α n) (h : n = m) : (Vector.cast h w).tail = Vector.cast (by simp [h]) w.tail := by
  simp [extract, h]


abbrev tripleZeros (x : List (Fin 2)) : Prop := (x.count 0) % 3 = 0
abbrev evenOnes (x : List (Fin 2)) : Prop := (x.count 1) % 2 = 0

def exampleLanguage : Language (Fin 2) := { x | tripleZeros x ∧ evenOnes x }


section example2DFA

inductive ExampleState : Type where
  | q : Fin 3 → ExampleState
  | p : Fin 2 → ExampleState
  deriving Fintype

theorem fin2_lt_2 (j : Fin 2) : j = 0 ∨ j = 1 := by
  rcases j with ⟨val, refl | h⟩
  all_goals simp
  -- Just val = 0 case left
  have := Nat.eq_zero_of_le_zero <| by simpa using h
  simp [this]

theorem fin3_lt_3 (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  rcases j with ⟨val, refl | ⟨refl | h⟩⟩
  all_goals simp
  -- Just val = 0 case left
  have := Nat.eq_zero_of_le_zero <| by simpa using h
  simp [this]

def exampleStep (a : TapeSymbol <| Fin 2) (s : ExampleState) : State ExampleState × Movement :=
  match s, a with
  | .q i, .symbol 0 => (ExampleState.q (i+1), Movement.right)
  | .q 0, .right => (ExampleState.p 0, Movement.left)
  | .q _, .right => (.reject, Movement.left)
  | .q i, _ => (ExampleState.q i, Movement.right)
  | .p j, .symbol 1 => (ExampleState.p (j+1), Movement.left)
  | .p 0, .left => (.accept, Movement.right)
  | .p 1, .left => (.reject, Movement.right)
  | .p j, _ => (ExampleState.p j, Movement.left)

/-- A 2DFA which identifies strings of {0, 1} where the number of 0s is divisible by 3 and the number of 1s is divisible by 2 -/
def example2DFA : TwoDFA (Fin 2) ExampleState where
  start := ExampleState.q 0
  stepOther := exampleStep
  stay_in_bounds p := by
    cases p
    case' p j => rcases fin2_lt_2 j with hj | hj
    case' q j => rcases fin3_lt_3 j with hj | hj | hj
    all_goals simp [hj, exampleStep]

def exampleConfigMeaning {n : Nat} : TwoDFA.ConfigMeaning n (Fin 2) ExampleState where
  accept word := (word.count 0) % 3 = 0 ∧ (word.count 1) % 2 = 0
  reject word := (word.count 0) % 3 ≠ 0 ∨ (word.count 1) % 2 = 1
  atLeft
    | .p j, word => (word.count 0) % 3 = 0 ∧ (word.count 1) % 2 = ↑j
    | .q j, _    => 0 = ↑j
  inWord
    | .q j, _ => fun ⟨wleft, _⟩ ↦ wleft.count 0 % 3 = ↑j
    | .p j, _ => fun ⟨wleft, wright⟩ ↦ (wleft ++ wright).count 0 % 3 = 0 ∧ wright.tail.count 1 % 2 = ↑j


theorem exampleCMInductive {n : Nat} : exampleConfigMeaning.Inductive (n := n) example2DFA where
  base := by simp [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, example2DFA]
  ind := by
    rintro w state idx hind
    let get_res := w.get idx
    match hstate : state, hget : get_res with
    | .q j, .left =>
      unfold get_res at hget
      have idx_zero : idx = 0 := Word.eq_zero_of_get_eq_left hget
      rw [idx_zero]
      conv at hind =>
        rw [idx_zero]
        simp only [TwoDFA.ConfigMeaning.apply, ↓reduceDIte, exampleConfigMeaning]
      have hget' : w.get 0 = .left := by rw [←idx_zero]; exact hget
      have right_valid : Movement.right.isValid (n := n) 0 := by constructor <;> simp
      have right_apply : Movement.right.apply 0 right_valid = 1 := by rw [←Fin.val_inj]; simp [Movement.apply]
      simpa [example2DFA, exampleConfigMeaning, TwoDFA.ConfigMeaning.apply, TwoDFA.stepConfig, exampleStep, hget', right_apply, SplitPredicate.apply, Word.split_one]
    | .p j, .left => cases fin2_lt_2 j; all_goals
      rename j = _ => hj
      unfold get_res at hget
      have idx_zero : idx = 0 := Word.eq_zero_of_get_eq_left hget
      rw [idx_zero]
      rw [hj]
      conv at hind =>
        rw [idx_zero, hj]
        simp only [TwoDFA.ConfigMeaning.apply, ↓reduceDIte, exampleConfigMeaning, Fin.val_zero, Fin.val_one]
      have : w.get 0 = .left := by rw [←idx_zero]; exact hget
      have right_valid : Movement.right.isValid (n := n) 0 := ⟨by simp, by simp⟩
      have right_apply : Movement.right.apply 0 right_valid = 1 := by unfold Movement.apply; rw [←Fin.val_inj]; simp
      simp [TwoDFA.ConfigMeaning.apply, TwoDFA.stepConfig, example2DFA, exampleStep, right_apply, exampleConfigMeaning, hind]
    | .q j, .right =>
      cases fin3_lt_3 j; case' inr => rename j = _ ∨ _ => hj'; cases hj'
      all_goals
        rename j = _ => hj
        unfold get_res at hget
        have idx_last := Word.eq_last_of_get_eq_right hget
        rw [idx_last]
        rw [idx_last] at hget
        have left_valid : Movement.left.isValid (Fin.last (n+1)) := ⟨by simp, by simp⟩
        have left_apply : Movement.left.apply (Fin.last (n+1)) left_valid = (@Nat.cast _ (Fin.NatCast.instNatCast (n+2)) n) := by
          unfold Movement.apply
          simp only
          rw [←Fin.val_inj]
          simp only [Fin.coe_castLE, Fin.coe_pred, Fin.val_last, add_tsub_cancel_right, Fin.val_natCast]
          symm; rw [Nat.mod_eq_iff_lt]
          · exact Nat.lt_succ_of_lt <| Nat.lt_succ_self n
          · simp
        conv in TwoDFA.stepConfig _ _ _ =>
          simp [TwoDFA.stepConfig, example2DFA, exampleStep, hj, hget, left_apply]
        conv at hind =>
          rw [hj, idx_last]
          simp [exampleConfigMeaning, TwoDFA.ConfigMeaning.apply, SplitPredicate.apply, Word.split]
      case inl =>  -- j = 0
        if hn : (@Nat.cast _ (Fin.NatCast.instNatCast (n+2)) n) = 0
          then
            have hn' : n = 0 := by simpa [←Fin.val_inj, Nat.mod_eq_of_lt] using hn
            have w_empty : w.val = ⟨#[], by simp [hn']⟩ := w.val.eq_empty_of_size_eq_zero hn'
            simp [exampleConfigMeaning, TwoDFA.ConfigMeaning.apply, hn, ↓reduceDIte, w_empty]
          else
            simp only [exampleConfigMeaning, TwoDFA.ConfigMeaning.apply, hn, ↓reduceDIte, Fin.val_zero, SplitPredicate.apply]
            have n_mod_n_plus_2 : n % (n + 2) = n := Nat.mod_eq_of_lt <| by simp
            have hn' : n ≠ 0 := by simpa only [←ne_eq, Fin.ne_iff_vne, Fin.val_natCast, Fin.val_zero, n_mod_n_plus_2] using hn
            have n_mod_n_plus_2' : n % (n + 1 + 1) = n := by simp [n_mod_n_plus_2]
            have hlen : n - ↑((@Nat.cast _ (Fin.NatCast.instNatCast (n+2)) n).pred hn) - 1 = 0 := by
              simp [n_mod_n_plus_2', Nat.sub_sub_self <| Nat.pos_of_ne_zero hn']
            have : (w.split (@Nat.cast _ (Fin.NatCast.instNatCast (n+2)) n) hn).2.tail = ⟨#[], by rw [hlen]; simp⟩ := by
              simp [Word.split, Vector.tail, n_mod_n_plus_2', Nat.sub_one_add_one hn']
            rw [Word.split_append, Vector.count_cast, this]
            simp [hind]
      all_goals  -- j = 1 ∨ j = 2
        by_cases hn : (@Nat.cast _ (Fin.NatCast.instNatCast (n+2)) n) = 0
        <;> simp [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, hind]
    | .p j, .right =>
      unfold get_res at hget
      have idx_last := Word.eq_last_of_get_eq_right hget
      rw [idx_last]
      rw [idx_last] at hget
      have split_last_len : n - ↑((Fin.last (n + 1)).pred <| by simp) - 1 = 0 := by simp
      have split_last_tail_empty : (w.split (Fin.last _) <| by simp).2.tail = ⟨#[], by simp⟩ := by simp [Word.split]
      conv at hind =>
        rw [idx_last]
        simp only [TwoDFA.ConfigMeaning.apply, Fin.last_eq_zero_iff, Nat.add_eq_zero, one_ne_zero,
          and_false, ↓reduceDIte, SplitPredicate.apply, exampleConfigMeaning, Fin.isValue, ne_eq,
          Fin.coe_pred, Vector.count_cast, not_and,
          Nat.mod_two_not_eq_zero, Fin.val_last, Nat.add_one_sub_one]
        rw [Word.split_append, Vector.count_cast, split_last_tail_empty]
        simp only [Fin.isValue, Fin.coe_pred, Fin.val_last, Nat.add_one_sub_one, Vector.count_mk,
          List.count_toArray, List.nodup_nil, List.count_nil, Nat.zero_mod]
      have n_mod_n_plus_2 : n = n % (n + 2) := by symm; apply Nat.mod_eq_of_lt; simp
      have left_valid : Movement.left.isValid (Fin.last (n+1)) := ⟨by simp, by simp⟩
      have left_apply : Movement.left.apply (Fin.last (n+1)) left_valid = (@Nat.cast _ (Fin.NatCast.instNatCast (n+2)) n) := by
        rw [←Fin.val_inj]
        simp [Movement.apply]
        exact n_mod_n_plus_2
      conv in example2DFA.stepConfig _ _ =>
        simp only [TwoDFA.stepConfig, example2DFA, Fin.isValue, hget, exampleStep, left_apply]
      if hn : n = 0
        then
          have w_empty : w.val = ⟨#[], by simp [hn]⟩ := w.val.eq_empty_of_size_eq_zero hn
          simp [TwoDFA.ConfigMeaning.apply, hn, exampleConfigMeaning, w_empty]
          exact hind.right
        else
          have hn2 : (@Nat.cast _ (Fin.NatCast.instNatCast (n+2)) n) ≠ 0 := by
            rwa [Fin.ne_iff_vne, Fin.val_natCast, Fin.val_zero, ←n_mod_n_plus_2]
          simp only [TwoDFA.ConfigMeaning.apply, hn2, ↓reduceDIte, exampleConfigMeaning, SplitPredicate.apply]
          rw [Word.split_append, Vector.count_cast]
          have : n = n % (n + 1 + 1) := n_mod_n_plus_2
          have split_n_tail_size : 0 = n - ↑((@Nat.cast _ (Fin.NatCast.instNatCast (n+2)) n).pred hn2) - 1 := by
            simp only [Fin.coe_pred, Fin.val_natCast, ← this]
            rw [Nat.sub_sub_self]
            exact Nat.pos_of_ne_zero hn
          have split_n_tail_empty : (w.split (@Nat.cast _ (Fin.NatCast.instNatCast (n+2)) n) hn2).2.tail = ⟨#[], by rw [Array.size_empty]; exact split_n_tail_size⟩ := by
            have h' : n ≤ 1 + (n - 1) := by rw [Nat.add_comm, Nat.sub_add_cancel <| Nat.pos_of_ne_zero hn]
            simp [←this, h']
          rw [split_n_tail_empty]
          simp [hind]
    | .q j, .symbol a =>
      cases fin3_lt_3 j; case' inr => rename j = _ ∨ _ => hj'; cases hj'
      all_goals
        rename j = _ => hj
        unfold get_res at hget
        have idx_int : idx.internal := w.internal_of_get_eq_symbol <| by use a
        rw [hj]
        cases fin2_lt_2 a; all_goals
          rename a = _ => ha
          conv in example2DFA.stepConfig _ _ =>
            simp only [TwoDFA.stepConfig, example2DFA, Fin.isValue, hget, ha, exampleStep, Fin.reduceAdd]
          conv at hind =>
            rw [hj]
            simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, idx_int.left, ↓reduceDIte]
            simp only [SplitPredicate.apply, Fin.val_zero, Fin.val_one, Fin.val_two]
          have move_right_valid : Movement.right.isValid idx := by constructor <;> simp [idx_int.right]
          have move_right : Movement.right.apply idx move_right_valid = idx.succCast idx_int.right := by simp [Movement.apply]
          have idx_succ_ne_zero : idx.succCast idx_int.right ≠ 0 := by rw [Fin.ne_iff_vne]; simp
          simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, idx_succ_ne_zero, ↓reduceDIte, move_right]
          simp only [SplitPredicate.apply, Fin.val_zero, Fin.val_one, Fin.val_two]
          rw [←w.split_succ idx idx_int.left idx_int.right]
          simp only [Vector.count_cast, Vector.count_push]
          have : w.getInternal idx idx_int = a := by
            suffices idx.pred idx_int.left ≠ Fin.last n by
              simpa [Word.get, Word.getInternal, Fin.internal.val, idx_int.left, this] using hget
            conv in Fin.last n => rw [←Fin.pred_last]
            rw [ne_eq, Fin.pred_inj]
            exact idx_int.right
          rw [Nat.add_mod, hind, this]
          simp [ha]
    | .p j, .symbol a =>
      cases fin2_lt_2 j; all_goals
        rename j = _ => hj
        unfold get_res at hget
        have idx_int : idx.internal := w.internal_of_get_eq_symbol <| by use a
        rw [hj]
        cases fin2_lt_2 a; all_goals
          rename a = _ => ha
          conv in example2DFA.stepConfig _ _ =>
            simp only [TwoDFA.stepConfig, example2DFA, Fin.isValue, hget, ha, exampleStep, Fin.reduceAdd]
          conv at hind =>
            rw [hj]
            simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, idx_int.left, ↓reduceDIte]
            simp only [SplitPredicate.apply, Fin.val_zero, Fin.val_one]
            rw [Word.split_append, Vector.count_cast]
          have move_left_valid : Movement.left.isValid idx := by constructor <;> simp [idx_int.left]
          have move_left : Movement.left.apply idx move_left_valid = idx.predCast idx_int.left := by simp [Movement.apply]
          simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, Fin.val_zero, Fin.val_one, move_left]
          if hidx : idx.predCast idx_int.left = 0
            then
              simp only [↓reduceDIte, hidx]
              have idx_one : idx = 1 := by
                rw [←Fin.pred_inj (ha := idx_int.left) (hb := by simp)]
                simpa [Fin.predCast, ←Fin.val_inj] using hidx
              conv at hind =>
                pattern w.split idx _
                rw [w.split_one idx idx_one]
              simp only [Vector.tail_cast, Vector.count_cast] at hind
              constructor
              · exact hind.left
              · if hn : n = 0
                  then
                    conv at hget =>  -- if n=0, then w.get 1 = .right ≠ .symbol a
                      simp [idx_one, Word.get, hn]
                    contradiction
                  else
                    have count_tail := Vector.count_tail (n-1) (Vector.cast (Nat.sub_one_add_one hn).symm w.val)
                    conv at count_tail =>
                      enter [a]
                      rw [Vector.tail_cast, Vector.count_cast, Vector.count_cast, Vector.getElem_cast]
                    have : w.val[0] = a := by simpa [Word.get, idx_one, getElem, hn] using hget
                    rw [count_tail, Nat.add_mod, hind.right, this]
                    simp [ha]
            else
              simp only [↓reduceDIte, hidx]
              simp only [SplitPredicate.apply]
              rw [Word.split_append, Vector.count_cast]
              have one_lt_idx : 1 < idx := by
                rw [←Fin.pred_lt_pred_iff]
                · simp only [Fin.pred_one]
                  apply Fin.pos_of_ne_zero
                  rw [←Fin.val_inj] at hidx
                  rw [Fin.ne_iff_vne]
                  simpa [Fin.pred] using hidx
                · simp
                · exact idx_int.left
              have := w.split_pred2 idx one_lt_idx
              rw [←this, Vector.count_cast]
              constructor
              · exact hind.left
              · have split2_size : (n - ↑(idx.pred idx_int.left)) ≠ 0 := by
                  simp only [Fin.coe_pred, ne_eq, Nat.sub_eq_zero_iff_le, not_le]
                  rw [←Nat.add_one_lt_add_one_iff, Nat.sub_one_add_one <| by simp [idx_int.left]]
                  simpa [←Fin.lt_last_iff_ne_last] using idx_int.right
                let k := (n - ↑(idx.pred idx_int.left)).pred
                have : n - (↑idx - 1) ≠ 0 := by simpa using split2_size
                have count_tail := Vector.count_tail k (Vector.cast (by simp [k, Nat.sub_one_add_one this]) (w.split idx idx_int.left).2)
                conv at count_tail =>
                  enter [a]
                  rw [Vector.tail_cast, Vector.count_cast, Vector.count_cast, Vector.getElem_cast]
                have : w.getInternal idx idx_int = a := by
                  suffices idx.pred idx_int.left ≠ Fin.last n by
                    simpa [Word.getInternal, Fin.internal.val, Word.get, idx_int.left, this] using hget
                  conv in Fin.last n => rw [←Fin.pred_last]
                  rw [ne_eq, Fin.pred_inj]
                  exact idx_int.right
                rw [count_tail, Nat.add_mod, hind.right, Word.split_2_getElem, this]
                simp [ha]

def cfg_encoding : TwoDFA.WellFoundedEncoding ExampleState where
  E := fun n ↦ Nat × Fin (n+2)
  wfrel := {
    rel := Prod.Lex LT.lt LT.lt,
    wf := IsWellFounded.wf
  }
  encode
  | ⟨.q _, pos⟩ => (0, pos)
  | ⟨.p _, pos⟩ => (1, pos.rev)

lemma example_never_p_to_q {n : Nat} {w : Word (Fin 2) n} : ∀ i, ∀ j, ∀ p1 p2, ¬ example2DFA.nextConfig w ⟨.other (.p i), p1⟩ ⟨.other (.q j), p2⟩
  | i, j, p1, p2 => by
    simp only [example2DFA, Fin.isValue, ← TwoDFA.stepConfig_gives_nextConfig,
      TwoDFA.stepConfig, TwoDFA.Config.mk.injEq, not_and]
    rcases fin2_lt_2 i with h | h
    all_goals
      intro hstep
      absurd hstep; clear hstep
      cases w.get p1 with
      | left | right => simp [h, exampleStep]
      | symbol a => rcases fin2_lt_2 a with ha | ha <;> simp [ha, exampleStep]

lemma example_q_to_q_right {j1 j2 : Fin 3} {a : TapeSymbol (Fin 2)} (h : (exampleStep a (.q j1)).1 = .other (.q j2)) : (exampleStep a (.q j1)).2 = .right := by
  rcases a with left | right | a
  case' symbol => -- Split the symbol case by what the symbol is
    rcases fin2_lt_2 a with ha | ha
    all_goals
      rw [ha]
      rw [ha] at h
      clear ha
  all_goals -- Split all cases by which .q state they start in
    rcases fin3_lt_3 j1 with hj | hj | hj
    all_goals
      rw [hj]
      rw [hj] at h
      clear hj
  all_goals simp [exampleStep] at h  -- Clear cases where it wouldn't end up in a .q state
  all_goals simp [exampleStep]  -- Work through the rest of the cases and see that they all move right

lemma example_p_to_p_left {j1 j2 : Fin 2} {a : TapeSymbol (Fin 2)} (h : (exampleStep a (.p j1)).1 = .other (.p j2)) : (exampleStep a (.p j1)).2 = .left := by
  rcases a with left | right | a
  case' symbol => -- Split symbol case by what the symbol is
    rcases fin2_lt_2 a with ha | ha
    all_goals
      rw [ha]
      rw [ha] at h
      clear ha
  all_goals -- Split all cases by which .p state they start in
    rcases fin2_lt_2 j1 with hj | hj
    all_goals
      rw [hj]
      rw [hj] at h
      clear hj
  all_goals simp [exampleStep] at h  -- Clear cases where it wouldn't end up in a .p state
  all_goals simp [exampleStep]  -- Work through the rest of the cases and see that they all move left

theorem example_never_diverges {n : Nat} (w : Word (Fin 2) n) : ¬ example2DFA.diverges w := by
  apply TwoDFA.halts_of_next_except_halt_WF
  apply TwoDFA.next_except_halt_WF_of_encoding _ cfg_encoding
  rintro q1 p1 q2 p2 hnext
  simp only [cfg_encoding, TwoDFA.WellFoundedEncoding.rel]
  match q1, q2 with
  | .q j1, .q j2 => 
    simp only
    apply Prod.Lex.right
    conv at hnext =>
      simp only [example2DFA, Fin.isValue, ← TwoDFA.stepConfig_gives_nextConfig,
        TwoDFA.stepConfig, TwoDFA.Config.mk.injEq, not_and]
    obtain ⟨hnextstate, hnextmove⟩ := hnext
    suffices p2 = Movement.right.apply p1 ?_ by rw [this]; apply Movement.lt_apply_right
    conv at hnextmove =>
      lhs; arg 1; rw [example_q_to_q_right hnextstate]
    exact hnextmove.symm
  | .q _, .p _ => apply Prod.Lex.left; simp
  | .p j1, .p j2 => 
    simp only
    apply Prod.Lex.right
    rw [Fin.rev_lt_rev]
    conv at hnext =>
      simp only [example2DFA, Fin.isValue, ← TwoDFA.stepConfig_gives_nextConfig,
        TwoDFA.stepConfig, TwoDFA.Config.mk.injEq, not_and]
    obtain ⟨hnextstate, hnextmove⟩ := hnext
    suffices p2 = Movement.left.apply p1 ?_ by rw [this]; apply Movement.lt_of_apply_left
    conv at hnextmove =>
      lhs; arg 1; rw [example_p_to_p_left hnextstate]
    exact hnextmove.symm
  | .p _, .q _ => absurd hnext; apply example_never_p_to_q

theorem exampleAcceptsLanguage : example2DFA.language = exampleLanguage := by
  apply example2DFA.language_eq_of_inductive _ _ exampleCMInductive
  case hacc | hrej => 
    intro w h
    unfold exampleLanguage
    rw [Set.mem_setOf]
    have : Fin.last (w.length + 1) ≠ 0 := by simp
    conv at h =>
      simp only [example2DFA, exampleConfigMeaning, TwoDFA.ConfigMeaning.apply, this, ↓reduceDIte]
      simp only [SplitPredicate.apply, Word.split_append, Vector.count_cast]
    simpa [imp_iff_not_or, List.toWord] using h
  case hdiv =>
    intro _ hdiv
    absurd hdiv
    apply example_never_diverges

end example2DFA

section Visualise

instance : ToString ExampleState where
  toString
  | .q j => s! "q{j}"
  | .p j => s! "p{j}"

def state_val : ExampleState → Nat 
  | .q j => j.val
  | .p j => 10 + j.val

instance : LinearOrder ExampleState := by
  apply LinearOrder.lift' state_val
  intro x y heq
  cases x
  <;> cases y
  case q.q | p.p =>
    simpa [state_val, Fin.val_inj] using heq
  case q.p jq jp | p.q jp jq =>
    exfalso
    suffices jq.val ≠ 10 + jp.val by
      simp only [state_val] at heq
      rw [heq] at this
      contradiction
    clear heq
    have := jp.is_lt
    have := jq.is_lt
    omega

def main := IO.println example2DFA.asDotGraph

end Visualise
