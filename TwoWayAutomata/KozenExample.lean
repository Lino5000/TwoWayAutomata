import TwoWayAutomata.Kozen

section example2DFA

def tripleZeros (x : List (Fin 2)) : Prop := (x.count 0) % 3 = 0
def evenOnes (x : List (Fin 2)) : Prop := (x.count 1) % 2 = 0

def exampleLanguage : Language (Fin 2) := 
  { x : List (Fin 2) | tripleZeros x ∧ evenOnes x }


inductive ExampleState : Type where
  | q : Fin 3 → ExampleState
  | p : Fin 2 → ExampleState
  | t : ExampleState
  | r : ExampleState

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

def exampleStep (a : TapeSymbol <| Fin 2) (s : ExampleState) : ExampleState × Movement :=
  match s, a with
  | .t, .right => (ExampleState.t, Movement.left)
  | .t, _ => (ExampleState.t, Movement.right)
  | .r, .right => (ExampleState.r, Movement.left)
  | .r, _ => (ExampleState.r, Movement.right)
  | .q i, .symbol 0 => (ExampleState.q (i+1), Movement.right)
  | .q 0, .right => (ExampleState.p 0, Movement.left)
  | .q _, .right => (ExampleState.r, Movement.left)
  | .q i, _ => (ExampleState.q i, Movement.right)
  | .p j, .symbol 1 => (ExampleState.p (j+1), Movement.left)
  | .p 0, .left => (ExampleState.t, Movement.right)
  | .p 1, .left => (ExampleState.r, Movement.right)
  | .p j, _ => (ExampleState.p j, Movement.left)

/-- A 2DFA which identifies strings of {0, 1} where the number of 0s is divisible by 3 and the number of 1s is divisible by 2 -/
def example2DFA : TwoDFA (Fin 2) ExampleState where
  start := ExampleState.q 0
  accept := ExampleState.t
  reject := ExampleState.r
  distinct_tr := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  step := exampleStep
  in_bounds_left := by
    intro q
    cases q with
    | p j =>
      rcases fin2_lt_2 j with hj | hj
      <;> simp [hj, exampleStep]
    | _ => simp [exampleStep]
  in_bounds_right := by
    intro q
    cases q with
    | q j =>
      rcases fin3_lt_3 j with hj | hj | hj
      <;> simp [hj, exampleStep]
    | _ => simp [exampleStep]
  halt_move_right := by
    intro a
    simp only [exampleStep, and_self]
  halt_preserve_state := by
    intro a
    cases a with
    | right => constructor <;> exists Movement.left
    | _ => constructor <;> exists Movement.right

theorem exampleZerosPass_ofCount {n : Nat} (hn : n ≠ 0) (i : Fin (n+2)) (h : i ≠ 0) (w : Word (Fin 2) n) (j : Fin 3) (hcount : (w.split i h).fst.count 0 % 3 = j) :
    example2DFA.GoesTo w ⟨example2DFA.start, 0⟩ ⟨.q j, i.castLE <| by simp⟩ := by
  let pi := i.pred h
  let piCast : Fin (n+2) := pi.castLE <| by simp
  cases ha : w.get piCast with
  | left =>
    simp only [Fin.castLE, Word.get_eq_left_iff_eq_0, Fin.mk_eq_zero] at ha
    have : pi.succ = 1 := by
      conv at ha =>
        unfold piCast
        rw [←Fin.val_inj]
        simp only [Fin.coe_castLE, Fin.val_zero, Fin.val_eq_zero_iff]
      simp [ha]
    simp only [Fin.castLE, this, Fin.val_one']
    have hi : i = 1 := by simp [pi] at this; assumption
    simp only [hi, Fin.val_one, Fin.mk_one]
    have hj : j = 0 := by
      simp [w.split_one i hi] at hcount
      symm; rwa [←Fin.val_inj, Fin.val_zero]
    rw [hj]
    conv in example2DFA.start => simp [example2DFA]
    apply TwoDFA.GoesTo.single
    have hvalid : Movement.right.isValid (0 : Fin (n+2)) := by constructor <;> simp
    right -- TwoDFA.nextConfig x y = ⟨step x = (y, .right)⟩
    · simp only [example2DFA, Fin.isValue, pi, Word.get_eq_left_of_eq_zero rfl, exampleStep]
    · suffices Movement.right.apply 0 hvalid = 1 by assumption
      simp [Movement.apply, ←Fin.val_inj]
  | right =>
    simp only [← Word.get_eq_right_iff_eq_last, ← Fin.val_eq_val, Fin.coe_castLE,
      Fin.val_last, piCast] at ha
    have := pi.is_lt
    rw [ha, lt_self_iff_false] at this
    contradiction
  | symbol a =>
    have piInternal : piCast.internal := w.internal_of_get_eq_symbol <| by use a
    have piCast_ne_zero : piCast ≠ 0 := by simp [piInternal.left]
    have := w.split_pred i <| by
      rw [←Fin.val_fin_lt, Fin.val_one]
      have := Nat.succ_lt_of_lt_pred <| by
        have := Fin.pos_of_ne_zero piCast_ne_zero
        simp only [←Fin.val_fin_lt, Fin.val_zero, Fin.coe_castLE, Fin.coe_pred, piCast, pi] at this
        exact this
      simpa
    simp [this, Vector.count_push] at hcount
    have piCast_eq_predCast : i.predCast h = piCast := rfl
    have : w.getInternal (i.predCast h) piInternal = a := by
      simp [this, Word.getInternal, Fin.internal.val]
      have pi_ne_zero : pi ≠ 0 := by
        unfold piCast at piCast_ne_zero
        rw [←Fin.val_ne_iff] at piCast_ne_zero
        simpa using piCast_ne_zero
      have piCast_pred_lt_n : piCast.pred piCast_ne_zero < n := by
        suffices (pi : Nat) - 1 < n by simp only [Fin.coe_pred, Fin.coe_castLE, piCast, this]
        apply Nat.sub_one_lt_of_le
        · apply Nat.pos_of_ne_zero
          rwa [←Fin.val_ne_iff] at pi_ne_zero
        · exact pi.is_le
      have : (piCast.pred piCast_ne_zero).castLT piCast_pred_lt_n = pi.pred pi_ne_zero := by
        rw [←Fin.val_eq_val]
        simp [piCast]
      rw [this]
      have piCast_pred_ne_last : piCast.pred piCast_ne_zero ≠ Fin.last n := by 
        suffices piCast.pred piCast_ne_zero < pi from Fin.ne_last_of_lt this
        rw [←Fin.val_fin_lt]
        suffices (pi : Nat) - 1 < pi by simpa [piCast]
        apply Nat.pred_lt_self
        simp only [Nat.sub_eq, tsub_zero, Fin.val_pos_iff]
        exact Fin.pos_of_ne_zero pi_ne_zero
      have : pi.pred pi_ne_zero = (piCast.pred piCast_ne_zero).castPred piCast_pred_ne_last := by
        rw [←Fin.val_inj]
        simp [piCast]
      rw [this]
      simpa [Word.get, piCast_ne_zero, piCast_pred_ne_last] using ha
    rw [this] at hcount
    have : w.split (i.predCast h) (by rwa [piCast_eq_predCast]) = w.split piCast piCast_ne_zero := by simp [Word.split, piCast, pi]
    rw [this] at hcount
    let countFin : Fin 3 := Fin.ofNat 3 <| (w.split piCast piCast_ne_zero).1.count 0
    have hcountFin : (w.split piCast piCast_ne_zero).1.count 0 % 3 = countFin.val := rfl
    have move_right_valid_from_piCast : Movement.right.isValid piCast := by
      constructor
      · simp
      · simp [piInternal.right]
    have move_right_from_piCast : Movement.right.apply piCast move_right_valid_from_piCast = i := by
      simp only [Movement.apply]
      rw [←Fin.val_inj]
      simp [piCast, pi, Nat.sub_one_add_one <| Fin.val_ne_of_ne h]
    if hazero : a = 0
      then
        have prev_count : (w.split piCast piCast_ne_zero).1.count 0 % 3 = ↑(j - 1) := by
          simp [hazero] at hcount 
          rw [hcountFin, Fin.val_eq_val]
          suffices countFin + 1 = j by rw [←this]; simp
          unfold countFin
          rw [Fin.ofNat_add, ←Fin.val_eq_val]
          simp [hcount]
        let prev : TwoDFA.Config ExampleState n := ⟨ .q (j-1), piCast ⟩
        have hind : example2DFA.GoesTo w ⟨example2DFA.start, 0⟩ prev := exampleZerosPass_ofCount hn piCast piCast_ne_zero w (j-1) prev_count
        constructor
        · exact hind
        · rw [hazero] at ha
          rw [←TwoDFA.stepConfig_gives_nextConfig]
          simp only [TwoDFA.stepConfig, example2DFA, Fin.isValue, Fin.castLE_refl,
            TwoDFA.Config.mk.injEq, prev]
          constructor
          · simp [ha, exampleStep]
          · simp [ha, exampleStep, move_right_from_piCast]
      else
        have prev_count : (w.split piCast piCast_ne_zero).1.count 0 % 3 = ↑j := by
          simpa [hazero] using hcount
        let prev : TwoDFA.Config ExampleState n := ⟨ .q j, piCast ⟩
        have hind : example2DFA.GoesTo w ⟨example2DFA.start, 0⟩ prev := exampleZerosPass_ofCount hn piCast piCast_ne_zero w j prev_count
        constructor
        · exact hind
        · rw [Fin.eq_one_of_ne_zero a hazero] at ha
          rw [←TwoDFA.stepConfig_gives_nextConfig]
          simp only [TwoDFA.stepConfig, example2DFA, Fin.isValue, Fin.castLE_refl,
            TwoDFA.Config.mk.injEq, prev]
          constructor
          · simp [ha, exampleStep]
          · simp [ha, exampleStep, move_right_from_piCast]
  termination_by sizeOf i
  decreasing_by all_goals {
    suffices (i : Nat) - 1 < i by simp [this]
    have : i.val ≠ 0 := Fin.val_ne_of_ne h
    exact Nat.sub_one_lt this
  }

theorem exampleOnesPass_ofCount {n : Nat} (hn : n ≠ 0) (i : Fin (n+2)) (h : i ≠ Fin.last _) (w : Word (Fin 2) n) (j : Fin 2) (hcount : (w.split (i.succCast h) (i.succCast_ne_zero h)).snd.count 1 % 2 = j) :
    example2DFA.GoesTo w ⟨.q 0, Fin.last _⟩ ⟨.p j, i⟩ := by
  cases hget : w.get i with
  | left =>
    have i_eq_zero := w.eq_zero_of_get_eq_left hget
    have i_succ_eq_one : i.succCast h = 1 := by simp [i_eq_zero, Fin.succCast, Fin.castLT]
    conv at hcount =>
      simp [w.split_one _ i_succ_eq_one]
    rw [i_eq_zero]
    let prev : TwoDFA.Config ExampleState n := ⟨.p j, 1⟩
    have prev_count : Vector.count 1 (w.split (Fin.succCast 0 (by simp)) <| Fin.succCast_ne_zero 0 (by simp)).2 % 2 = j.val := by
      have : Fin.succCast 0 (by simp) = (1 : Fin (n+2)) := by simp [Fin.succCast, Fin.castLT]
      simp [w.split_one _ this, hcount]
    exact exampleOnesPass_ofCount hn 0 (by simp) w j prev_count
  | right =>
    have := w.eq_last_of_get_eq_right hget
    contradiction
  | symbol a =>
    have i_int := w.internal_of_get_eq_symbol ⟨_, hget⟩
    conv at hcount =>
      rw [←w.split_succ2 i i_int.left h, Vector.count_cast]
    let prev_idx := i.succCast h
    by_cases hprev : prev_idx = Fin.last _
    case' pos => -- prev_idx = .last _
      have get_prev := w.get_eq_right_of_eq_last hprev
      let get_sym := a
    case' neg => -- prev_idx ≠ .last _
      obtain ⟨a', get_prev⟩ : ∃ x, w.get prev_idx = .symbol x := by
        sorry
      let get_sym := a'
    all_goals
      rcases fin2_lt_2 get_sym with ha | ha
      focus -- a = 0
        let prev : TwoDFA.Config ExampleState n := ⟨.p j, prev_idx⟩
      rotate_left; focus -- a = 1
        let prev : TwoDFA.Config ExampleState n := ⟨.p (j-1), prev_idx⟩
      all_goals
        unfold get_sym at ha
        let hind : example2DFA.GoesTo w ⟨.q 0, Fin.last _⟩ prev := sorry
        constructor
        · exact hind
        · simp only [example2DFA, ← TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, TwoDFA.Config.mk.injEq]
          simp [prev, get_prev, ha]
          simp only [exampleStep, Fin.zero_eq_one_iff]
          sorry
  termination_by sizeOf (Fin.last _ - i)
  decreasing_by all_goals {
    simp
    sorry
  }

theorem exampleZerosPass {n : Nat} (w : Word (Fin 2) n) (j : Fin 3) (hcount : w.val.count 0 % 3 = j) :
    example2DFA.GoesTo w ⟨example2DFA.start, 0⟩ ⟨.q j, Fin.last _⟩ := by
  if hn : n = 0
    then
      have w_empty := w.val.eq_empty_of_size_eq_zero hn
      conv at hcount =>
        simp [w_empty]
        rw [←Fin.val_zero (n := 3), Fin.val_inj]
      rw [←hcount]
      have last_one : Fin.last (n+1) = 1 := by simp [hn, ←Fin.val_inj]
      conv in Fin.last _ => rw [last_one]
      apply TwoDFA.GoesTo.single
      have := w.get_eq_left_of_eq_zero rfl
      simp [example2DFA, ←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, this, exampleStep]
      simp [Movement.apply, Fin.castLT]
    else
      apply exampleZerosPass_ofCount hn (i := Fin.last _) (h := by simp)
      simp [Word.split, hcount]

universe u
theorem Vector.count_tail {α : Type u} [BEq α] (n : Nat) (w : Vector α (n+1)) (a : α) : Vector.count a w = Vector.count a w.tail + if w[0] == a then 1 else 0 := by
  have eq_push_front : w = w.tail.insertIdx 0 w[0] := by
    suffices #[w[0]] = w.toArray.extract 0 1 by simp [insertIdx, this, Array.extract_eq_self_of_le]
    rw [Array.extract_succ_right (by simp) (by simp)]
    simp
  conv =>
    lhs
    rw [eq_push_front]
    simp only [Nat.add_one_sub_one, insertIdx_zero, count_cast, count_append, count_mk, List.count_toArray, List.count_singleton]
    rw [Nat.add_comm]

theorem Vector.tail_cast {α : Type u} {n m : Nat} (w : Vector α n) (h : n = m) : (Vector.cast h w).tail = Vector.cast (by simp [h]) w.tail := by
  simp [extract, h]

theorem exampleOnesPass {n : Nat} (w : Word (Fin 2) n) (j : Fin 2) (hcount : w.val.count 1 % 2 = j) :
    example2DFA.GoesTo w ⟨.q 0, Fin.last _⟩ ⟨.p j, 0⟩ := by
  if hn : n = 0
    then
      have w_empty := w.val.eq_empty_of_size_eq_zero hn
      conv at hcount =>
        simp [w_empty]
        rw [←Fin.val_zero (n := 2), Fin.val_inj]
      rw [←hcount]
      apply TwoDFA.GoesTo.single
      have := w.get_eq_right_of_eq_last rfl
      simp [example2DFA, TwoDFA.stepConfig, ←TwoDFA.stepConfig_gives_nextConfig, this, exampleStep]
      have last_one : Fin.last (n+1) = 1 := by simp [hn, ←Fin.val_inj]
      conv in Fin.last _ => rw [last_one]
      simp [Movement.apply, Fin.predCast]
    else
      apply exampleOnesPass_ofCount hn (i := 0) (h := by simp) (j := j)
      simp [Word.split, hcount]

theorem list_count_eq_vector_count {α : Type u} [BEq α] (w : List α) (a : α) : List.count a w = Vector.count a w.toWord.val := by
  simp only [List.toWord, Vector.count, List.count_toArray]

def exampleConfigMeaning {n : Nat} : TwoDFA.ConfigMeaning n (Fin 2) ExampleState where
  atLeft
    | .p j, word => (word.count 0) % 3 = 0 ∧ (word.count 1) % 2 = ↑j
    | .q j, _    => 0 = ↑j
    | .t  , word => (word.count 0) % 3 = 0 ∧ (word.count 1) % 2 = 0
    | .r  , word => (word.count 0) % 3 ≠ 0 ∨ (word.count 1) % 2 = 1
  inWord
    | .q j, _, _ => fun ⟨wleft, _⟩ ↦ wleft.count 0 % 3 = ↑j
    | .p j, idx, _ => fun ⟨wleft, wright⟩ ↦ (wleft ++ wright).count 0 % 3 = 0 ∧ wright.tail.count 1 % 2 = ↑j
    | .t  , _, _ => fun ⟨wleft, wright⟩ ↦ (wleft ++ wright).count 0 % 3 = 0 ∧ (wleft ++ wright).count 1 % 2 = 0
    | .r  , _, _ => fun ⟨wleft, wright⟩ ↦ ¬((wleft ++ wright).count 0 % 3 = 0 ∧ (wleft ++ wright).count 1 % 2 = 0)

theorem exampleCMBase {n : Nat} (w : Word (Fin 2) n) : exampleConfigMeaning.apply w ⟨example2DFA.start, 0⟩ := by
  simp [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, example2DFA]

theorem dite_eq_of_same_branch {α : Sort _} (c : Prop) [h : Decidable c] (b : α) : dite c (fun _ ↦ b) (fun _ ↦ b) = b := by
  if x : c then simp else simp

theorem exampleCMInd {n : Nat} (w : Word (Fin 2) n) (cfg : TwoDFA.Config ExampleState n) (hind : exampleConfigMeaning.apply w cfg) :
    exampleConfigMeaning.apply w (example2DFA.stepConfig w cfg) := by
  let ⟨state, idx⟩ := cfg
  let get_res := w.get idx
  match hstate : state, hget : get_res with
  | .t, .left | .t, .symbol a
  | .r, .left | .r, .symbol a =>
    unfold get_res at hget
    conv in example2DFA.stepConfig _ _ =>
      simp only [TwoDFA.stepConfig, example2DFA, exampleStep, hget]
    simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, Movement.apply_right_ne_zero, ↓reduceDIte]
    simp only [SplitPredicate.apply]
    rw [Word.split_append, Vector.count_cast, Vector.count_cast]
    conv at hind =>
      simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, ↓reduceDIte]
      simp only [SplitPredicate.apply]
      enter [3, h]
      rw [Word.split_append, Vector.count_cast, Vector.count_cast]
    if h : idx = 0
      then simpa [h, or_iff_not_and_not] using hind
      else simpa [h, or_iff_not_and_not] using hind
  | .t, .right =>
    unfold get_res at hget
    conv in example2DFA.stepConfig _ _ =>
      simp only [TwoDFA.stepConfig, example2DFA, exampleStep, hget]
    have last_idx := Word.eq_last_of_get_eq_right hget
    have move_left_valid : Movement.left.isValid idx := by
      rw [last_idx]
      constructor <;> simp
    if hn : n = 0
      then
        have move_left : Movement.left.apply idx move_left_valid = 0 := by
          simp [last_idx, Movement.apply, ←Fin.val_inj, hn]
        simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, move_left, ↓reduceDIte]
        have w_empty : w.val = ⟨#[], by simp [hn]⟩ := w.val.eq_empty_of_size_eq_zero hn
        simp [w_empty]
      else
        have idx_ne_zero : idx ≠ 0 := by simp [last_idx]
        conv at hind =>
          simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, idx_ne_zero, ↓reduceDIte]
          simp only [SplitPredicate.apply]
          rw [Word.split_append, Vector.count_cast, Vector.count_cast]
        have move_left : Movement.left.apply idx move_left_valid ≠ 0 := by
          simp [last_idx, Movement.apply, Fin.ne_iff_vne, hn]
        simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, move_left, ↓reduceDIte]
        simp only [SplitPredicate.apply]
        rwa [Word.split_append, Vector.count_cast, Vector.count_cast]
  | .r, .right =>
    unfold get_res at hget
    have last_idx := Word.eq_last_of_get_eq_right hget
    have idx_ne_zero : idx ≠ 0 := by simp [last_idx, ←Fin.val_inj]
    if hn : n = 0
      then
        have w_empty : w.val = ⟨#[], by simp [hn]⟩ := w.val.eq_empty_of_size_eq_zero hn
        conv at hind =>
          simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, idx_ne_zero, ↓reduceDIte]
          simp only [SplitPredicate.apply]
          rw [Word.split_append, Vector.count_cast, Vector.count_cast]
          simp [w_empty]
        contradiction
      else
        conv at hind =>
          simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, idx_ne_zero, ↓reduceDIte]
          simp only [SplitPredicate.apply]
          rw [Word.split_append, Vector.count_cast, Vector.count_cast]
        conv in example2DFA.stepConfig _ _ =>
          simp only [TwoDFA.stepConfig, example2DFA, exampleStep, hget]
        have move_left_valid : Movement.left.isValid idx := by
          rw [last_idx]
          constructor <;> simp
        have move_left : Movement.left.apply idx move_left_valid ≠ 0 := by
          simp [last_idx, Movement.apply, Fin.ne_iff_vne, hn]
        simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, move_left, ↓reduceDIte]
        simp only [SplitPredicate.apply]
        rwa [Word.split_append, Vector.count_cast, Vector.count_cast]
  | .q j, .left =>
    unfold get_res at hget
    have idx_zero : idx = 0 := Word.eq_zero_of_get_eq_left hget
    rw [idx_zero]
    conv at hind =>
      rw [idx_zero]
      simp only [TwoDFA.ConfigMeaning.apply, ↓reduceDIte, exampleConfigMeaning]
    have : w.get 0 = .left := by rw [←idx_zero]; exact hget
    simp only [TwoDFA.ConfigMeaning.apply, TwoDFA.stepConfig, example2DFA, Fin.isValue, this,
      exampleStep, exampleConfigMeaning, ne_eq, Fin.coe_pred, Vector.count_append, not_and,
      Nat.mod_two_not_eq_zero]
    have right_valid : Movement.right.isValid (n := n) 0 := ⟨by simp, by simp⟩
    have right_apply : Movement.right.apply 0 right_valid = 1 := by unfold Movement.apply; rw [←Fin.val_inj]; simp
    have sizes_eq : 0 = min (↑((Movement.right.apply 0 right_valid).pred (by simp [right_apply]))) n := by simp [right_apply]
    have : (w.split (Movement.right.apply 0 right_valid) (by simp [right_apply])).1 = ⟨#[], by simp [sizes_eq]⟩ := by
      simp [right_apply]
    simp [this, right_apply, SplitPredicate.apply, ←hind]
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
    simp only [TwoDFA.ConfigMeaning.apply, TwoDFA.stepConfig, example2DFA, Fin.isValue, this,
      exampleStep, right_apply, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceDIte,
      exampleConfigMeaning, SplitPredicate.apply, Word.split_append, Vector.count_cast, Vector.count_cast]
    simp [hind]
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
        simp only [Fin.coe_castLE, Fin.coe_pred, Fin.val_last, add_tsub_cancel_right,
          Fin.ofNat_eq_cast, Fin.val_natCast]
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
          simp [exampleConfigMeaning, TwoDFA.ConfigMeaning.apply, hn, ↓reduceDIte, Fin.val_zero, w_empty]
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
      all_goals simp only [TwoDFA.ConfigMeaning.apply, exampleConfigMeaning, hn, ↓reduceDIte]
      case pos =>  -- n = 0
        simp [hind]
      case neg =>  -- n ≠ 0
        simp only [SplitPredicate.apply]
        rw [Word.split_append, Vector.count_cast]
        simp [hind]
  | .p j, .right =>
    unfold get_res at hget
    have idx_last := Word.eq_last_of_get_eq_right hget
    rw [idx_last]
    rw [idx_last] at hget
    have split_last_len : n - ↑((Fin.last (n + 1)).pred <| by simp) - 1 = 0 := by simp
    have split_last_tail_empty : (w.split (Fin.last _) <| by simp).2.tail = ⟨#[], by simp [split_last_len]⟩ := by simp [Word.split]
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
        simp only [TwoDFA.ConfigMeaning.apply, hn2, ↓reduceDIte, exampleConfigMeaning, Nat.mod_two_not_eq_zero, SplitPredicate.apply]
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

theorem exampleCMAlways {n : Nat} (w : Word (Fin 2) n) : ∀ cfg : TwoDFA.Config ExampleState n, example2DFA.reaches w cfg → exampleConfigMeaning.apply w cfg :=
  exampleConfigMeaning.apply_of_reachable example2DFA w (exampleCMBase w) (exampleCMInd w)

theorem exampleAcceptsLanguage : example2DFA.language = exampleLanguage := by
  unfold exampleLanguage
  unfold TwoDFA.language
  rw [Set.setOf_inj]
  ext
  rename List (Fin 2) => w
  constructor

  -- example2DFA.accepts w → w ∈ exampleLanguage
  · intro h
    have := exampleCMAlways w.toWord _ <| example2DFA.reaches_accept_last_of_accepts w.toWord h
    conv at this =>
      simp only [TwoDFA.ConfigMeaning.apply, Fin.last_eq_zero_iff, Nat.add_eq_zero,
        List.length_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, exampleConfigMeaning,
        example2DFA]
      simp only [SplitPredicate.apply, Word.split_append, Vector.count_cast, ←list_count_eq_vector_count]
    exact this

  -- w ∈ exampleLanguage → example2DFA.accepts w
  · rintro ⟨ hzeros, hones ⟩
    conv at hzeros =>
      unfold tripleZeros
      rw [list_count_eq_vector_count]
    conv at hones =>
      unfold evenOnes
      rw [list_count_eq_vector_count]

    have zerosPass := exampleZerosPass w.toWord 0 hzeros
    have onesPass := exampleOnesPass w.toWord 0 hones

    use 1
    constructor
    · exact TwoDFA.GoesTo.trans example2DFA w.toWord zerosPass onesPass
    · simp [←TwoDFA.stepConfig_gives_nextConfig, TwoDFA.stepConfig, example2DFA, Word.get_eq_left_of_eq_zero rfl, exampleStep]
      simp [Movement.apply, Fin.castLT]

end example2DFA
