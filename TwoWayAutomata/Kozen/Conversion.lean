import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Computability.DFA

import TwoWayAutomata.Kozen.Language
import TwoWayAutomata.Kozen.Correctness

theorem Option.ne_some {α : Type _} (o : Option α) {a : α} (h : o ≠ some a) : o = none ∨ ∃ b : α, b ≠ a ∧ o = some b := by
  cases o with
  | none => simp
  | some b => right; use b; simpa using h

lemma List.length_takeWhile_le {α : Sort _} {l : List α} {p : α → Bool} : (l.takeWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih => 
    unfold List.takeWhile
    cases _ : p hd with
    | true => simpa
    | false => simp

lemma List.length_takeWhile {α : Sort _} {l : List α} {p : α → Bool} {n : Nat} (hat : ∀ hn : n < l.length, p l[n] = false)
  (hprev : ∀ k (hk : k < min n l.length), p (l[k]'((Nat.lt_min.mp hk).right)) = true) :
    (l.takeWhile p).length = min n l.length := by
  if hn : n < l.length
    then
      induction l generalizing n with
      | nil => simp at hn -- hn : n < 0
      | cons hd tl ih => 
        cases n with
        | zero => 
          have hd_false : p hd = false := by simpa using hat
          simp [takeWhile, hd_false]
        | succ n => 
          have hd_true : p hd = true := hprev 0 <| by simp
          simp [takeWhile, hd_true]
          apply ih 
          · simpa using hat
          · intro k hk
            have := hprev (k+1) <| by omega
            simpa
          · simpa using hn
    else
      have min_eq : min n l.length = l.length := by simpa using hn
      rw [min_eq]
      suffices l.takeWhile p = l by rw [this]
      rw [List.takeWhile_eq_self_iff]
      intro e he
      obtain ⟨_, _, heq⟩ := List.mem_iff_getElem.mp he
      rw [←heq]
      apply hprev
      rwa [min_eq]

lemma List.getElem_takeWhile {α : Sort _} {l : List α} {i : Nat} {p : α → Bool} {hi : i < (l.takeWhile p).length} :
    (l.takeWhile p)[i] = l[i]'(Nat.lt_of_lt_of_le hi List.length_takeWhile_le) := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    if hp : p hd
      then
        unfold List.takeWhile
        conv => lhs; arg 1; rw [hp]
        cases i <;> simp [ih]
      else
        have hp : p hd = false := by simp [hp]
        conv at hi =>
          rhs; arg 1; unfold List.takeWhile
          simp only [hp]
        simp at hi -- contradiction, hi : i < [].length

namespace TwoDFA

variable {α σ : Type*}

inductive GoesLeftOf {n : Nat} (m : TwoDFA α σ) (w : Word α n) (i : Fin (n+2)) : Config σ n → Config σ n → Prop where
  | refl {cfg : Config σ n} : m.GoesLeftOf w i cfg cfg
  | tail {strt mid stp : Config σ n} (hlt : mid.idx ≤ i) (head : m.GoesLeftOf w i strt mid) (tail : m.nextConfig w mid stp) : m.GoesLeftOf w i strt stp

namespace GoesLeftOf

variable {n : Nat} (m : TwoDFA α σ) (w : Word α n) (i : Fin (n+2)) 

@[refl]
theorem reflexive (cfg : Config σ n) : m.GoesLeftOf w i cfg cfg := .refl

theorem forget {cfg1 cfg2 : Config σ n} (h : m.GoesLeftOf w i cfg1 cfg2) : m.GoesTo w cfg1 cfg2 := by
  induction h with
  | refl => rfl
  | tail _ _ tl ih => apply ih.tail tl

theorem single {strt stp : Config σ n} {i : Fin _} (hlt : strt.idx ≤ i) (hnext : m.nextConfig w strt stp) : m.GoesLeftOf w i strt stp := 
  .tail hlt .refl hnext

theorem head {strt mid stp : Config σ n} (head : m.nextConfig w strt mid) (tail : m.GoesLeftOf w strt.idx mid stp) {i : Fin _} (hidx : i = strt.idx) : m.GoesLeftOf w i strt stp := by
  induction tail with
  | refl => exact .tail (by rw [hidx]) .refl head
  | tail hlt _ tl ih =>
    rw [←hidx] at hlt
    exact ih.tail hlt tl

@[trans]
theorem trans {strt mid stp : Config σ n} {i : Fin _} (ha : m.GoesLeftOf w i strt mid) (hb : m.GoesLeftOf w i mid stp) : m.GoesLeftOf w i strt stp := by
  induction hb with
  | refl => exact ha
  | tail hlt _ tl ih => exact ih.tail hlt tl

theorem castSucc {cfg1 cfg2 : Config σ n} {i : Fin _} (h : m.GoesLeftOf w i.castSucc cfg1 cfg2) : m.GoesLeftOf w i.succ cfg1 cfg2 := by
  induction h with
  | refl => rfl
  | tail hlt _ tl ih =>
    refine .tail ?_ ih tl
    apply hlt.trans
    simp [Fin.le_iff_val_le_val]

theorem castLE {cfg1 cfg2 : Config σ n} {i j : Fin _} (hgoes : m.GoesLeftOf w i cfg1 cfg2) (hle : i ≤ j) : m.GoesLeftOf w j cfg1 cfg2 := by
  induction hgoes with
  | refl => rfl
  | tail hlt _ tl ih => exact ih.tail (hlt.trans hle) tl

theorem attach {cfg1 cfg2 : Config σ n} (h : m.GoesTo w cfg1 cfg2) : m.GoesLeftOf w (Fin.last _) cfg1 cfg2 := by
  induction h with
  | refl => rfl
  | tail _ tl ih => exact ih.tail (Fin.le_last _) tl


lemma step_mpr_go {m : TwoDFA α σ} {w : Word α n} {i : Fin _} (j : Nat) (psqs : List (σ × σ)) (hj : j < psqs.length.pred)
  (hmap : ∀ (j : ℕ) (hj : j < psqs.length.pred),
      m.nextConfig w { state := (psqs[j]'(Nat.lt_of_lt_pred hj)).1, idx := i.succ } { state := (psqs[j]'(Nat.lt_of_lt_pred hj)).2, idx := i.castSucc } ∧
      m.GoesLeftOf w i.castSucc { state := (psqs[j]'(Nat.lt_of_lt_pred hj)).2, idx := i.castSucc } { state := (psqs[j+1]'(Nat.succ_lt_of_lt_pred hj)).1, idx := i.succ }) :
    m.GoesLeftOf w i.succ { state := (psqs[0]'(Nat.lt_of_le_of_lt (by simp : 0 ≤ j) (Nat.lt_of_lt_pred hj))).fst, idx := i.succ } { state := (psqs[j+1]'(Nat.succ_lt_of_lt_pred hj)).fst, idx := i.succ } := by
  induction j with
  | zero => 
    obtain ⟨hstep, hgoes⟩ := hmap 0 (Nat.lt_of_le_of_lt (by rfl) hj)
    apply head
    · exact hstep
    · apply castLE
      · exact hgoes
      · simp only [Fin.castSucc_le_succ]
    · simp
  | succ j ih =>
    have hlt : j < psqs.length.pred := j.lt_add_one.trans hj
    have hgoes := ih hlt
    obtain ⟨hstep, hgoes'⟩ := hmap _ hj
    apply hgoes.trans
    apply head
    · exact hstep
    · apply castLE
      · exact hgoes'
      · simp only [Fin.castSucc_le_succ]
    · simp

end GoesLeftOf

--- A "table" that stores all the information needed to completely reconstruct the behaviour of a given 2DFA on a fixed input prefix.
structure BackTable (σ : Type _) : Type _ where
  --- The state the 2DFA is in the first time it exits the prefix.
  init : Option σ
  --- What state the 2DFA will be in when it exits the prefix, based on what state it re-entered (from the right) in.
  map : σ → Option σ

-- TODO: Find some way to not need the [DecidableEq σ] constraint
instance [DecidableEq σ] [Fintype σ] : Fintype (BackTable σ) := derive_fintype% _

--- The table for this 2DFA when the prefix is empty (just the left endmarker)
def first_table (m : TwoDFA α σ) : BackTable σ where
  -- The movements in both of these steps are always going to be "go right", so we don't need to repeat at all
  init := some <| (m.step .left m.start).1
  map q := some <| (m.step .left q).1

/--
Repeatedly apply the step function and the mapping for the prefix to
determine where a state should map in the table for appending `a` to the
prefix.
-/
def step_right [Fintype σ] (m : TwoDFA α σ) (t : BackTable σ) (a : α) (q : σ) : Option σ := 
  -- Fuel counts down each time we go into the prefix (by querying the table) so that we can guarantee termination
  -- The initial value needs to be large enough to ensure that we only run out if we are actually in a cycle
  go q <| Fintype.card σ + 1
  where
    go (q : σ) : Nat → Option σ
    | 0 => none
    | fuel + 1 =>
      match m.step a q with
      | ⟨p, .right⟩ => some p
      | ⟨p, .left⟩ => 
        -- We've stepped back into the prefix, where do we end up?
        let q' := t.map p
        -- If we got stuck, return none, otherwise try taking another step
        q' >>= (go · fuel)


def step_table [Fintype σ] (m : TwoDFA α σ) (t : BackTable σ) (a : α) : BackTable σ where
  init := t.init >>= m.step_right t a  -- Only step if t.init ≠ none
  map := m.step_right t a

/--
An accepting table is one where if we start with it's initial state and trace
it as the machine takes it between the table's prefix and the right endmarker,
it eventually ends up in the machine's accept state.
-/
def accepting_table [Fintype σ] (m : TwoDFA α σ) (t : BackTable σ) : Prop :=
  -- This absolutely will get stuck in a loop of some form; even the accept and reject states sit in a loop at the right endmarker forever
  -- What we want to do is go into the prefix enough times to ensure we reach that loop, then check if the resulting looping state is m.accept
  t.init >>= (go · (Fintype.card σ + 1)) = some m.accept
  where
    go (q : σ) : Nat → Option σ
    | 0 => some q  -- When we run out of fuel return the current state, rather than reporting the inevitable cycle
    | fuel + 1 =>
      let p' := (m.step .right q).1
      -- We've stepped back into the prefix, where do we end up?
      let q' := t.map p'
      -- If we got stuck, return none, otherwise try taking another step
      q' >>= (go · fuel)

--- Convert a TwoDFA into an equivalent (accepting the same language) One-Way DFA
def to_one_way [Fintype σ] (m : TwoDFA α σ) : DFA α (BackTable σ) where
  step := m.step_table
  start := m.first_table
  accept := {t | m.accepting_table t}

section RunTable 

-- The sequence of pᵢ, qᵢ pairs that step_right goes through, as a function from Nat. run_table n will return none if an earlier step moved right
def run_table' (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ) : Nat → Option (σ × σ × Movement)
  | 0 => (p, m.step a p)
  | k + 1 =>
    match m.run_table' t a p k with
    | .none => none  -- Something earlier moved right
    | .some (_, _, .right) => none  -- Previous step moved right
    | .some (_, qₖ, .left) => (t.map qₖ).map <| fun pₛₖ ↦ (pₛₖ, m.step a pₛₖ)

lemma run_table'_no_holes {m : TwoDFA α σ} {t : BackTable σ} {a : TapeSymbol α} {p p' q : σ} {mv : Movement} {k : Nat} (h : m.run_table' t a p k = some (p', q, mv)) :
    ∀ k' ≤ k, ∃ p' q mv, m.run_table' t a p k' = some (p', q, mv) := by
  intro k' hk
  cases hk with
  | refl => exists p', q, mv
  | step hk' =>
    rename Nat => k -- now hk' : k' ≤ k
    match hprev : m.run_table' t a p k with
    | .none | .some (_, _, .right) => simp [run_table', hprev] at h  -- impossible, these cases would return none not some (...) after the new step
    | .some (p'', q'', .left) =>
      apply run_table'_no_holes (h := hprev)
      exact hk'

lemma run_table'_prefix_only_left {m : TwoDFA α σ} {t : BackTable σ} {a : TapeSymbol α} {p p' q : σ} {mv : Movement} {k : Nat} (h : m.run_table' t a p k = some (p', q, mv)) :
    ∀ k' < k, ∃ p' q, m.run_table' t a p k' = some (p', q, .left) := by
  intro k' hk'
  obtain ⟨p'', q', mv', heq⟩ := run_table'_no_holes h k' <| Nat.le_of_lt hk'
  suffices mv' = .left by simp [this, heq]
  cases mv' with
  | left => rfl
  | right =>
    induction hk' generalizing p' q mv with
    | refl =>
      conv at h =>
        unfold run_table'
        rw [heq]
        simp only
      contradiction  -- h : none = some (...)
    | step _ ih => 
      rename Nat => k''
      match hrun : m.run_table' t a p k'' with
      | .some _ => apply ih hrun
      | .none =>
        conv at h =>
          unfold run_table'
          rw [hrun]
          simp only
        contradiction  -- h : none = some (...)

lemma run_table'_rep_offset {m : TwoDFA α σ} {t : BackTable σ} {a : TapeSymbol α} {p : σ} {step1 step2 off : Nat} (h : m.run_table' t a p step1 = m.run_table' t a p step2) :
    m.run_table' t a p (step1 + off) = m.run_table' t a p (step2 + off) := by
  induction off with
  | zero => assumption
  | succ _ ih => simp [run_table', ih]

variable [fin_states : Fintype σ]

lemma run_table'_max_len_some {m : TwoDFA α σ} {t : BackTable σ} {s : TapeSymbol α} {p p' q : σ} {mv : Movement} {k : Nat} (h : m.run_table' t s p k = some (p', q, mv)) :
    ∃ k' < Fintype.card (σ × σ × Movement), m.run_table' t s p k' = some (p', q, mv) := by
  if hk : k < Fintype.card (σ × σ × Movement)
    then exists k
    else
      let outcard := Fintype.card (σ × σ × Movement)
      have all_eq_some : ∀ k' ≤ outcard, _ := fun k' hk' ↦ m.run_table'_no_holes h k' <| by omega
      let run_table'' : NatUpTo outcard → (σ × σ × Movement) := fun n' ↦ m.run_table' t s p n' |>.get <| by
        obtain ⟨_, _, _, hsome⟩ := all_eq_some n'.val <| by rw [←Finset.mem_range_succ_iff]; exact n'.property
        simp [hsome]
      obtain ⟨e1, e2, hne, h'⟩ := Fintype.exists_ne_map_eq_of_card_lt run_table'' <| by simp [NatUpTo.card_eq, outcard]
      have val_ne : e1.val ≠ e2.val := by rwa [Subtype.coe_ne_coe]
      have hrep : m.run_table' t s p e1.val = m.run_table' t s p e2.val := by
        unfold run_table'' at h'
        rwa [Option.get_inj] at h'
      have hle1 : e1.val ≤ outcard := by rw [←Finset.mem_range_succ_iff]; exact e1.property
      have hle2 : e2.val ≤ outcard := by rw [←Finset.mem_range_succ_iff]; exact e2.property
      rcases Nat.lt_or_lt_of_ne val_ne with hlt | hlt
      case' inl => -- e1 < e2
        let a := e1.val; let b := e2.val
        have ha : a = e1 := rfl; have hb : b = e2 := rfl
        have hlea : a ≤ outcard := by rw [ha]; exact hle1
        have hleb : b ≤ outcard := by rw [hb]; exact hle2
      case' inr => -- e1 > e2
        let a := e2.val; let b := e1.val
        have ha : a = e2 := rfl; have hb : b = e1 := rfl
        have hlea : a ≤ outcard := by rw [ha]; exact hle2
        have hleb : b ≤ outcard := by rw [hb]; exact hle1
        have hrep := hrep.symm
      all_goals
        rw [←ha, ←hb] at hlt hrep
        clear * - hlea hleb hlt hrep all_eq_some k hk h run_table'_max_len_some
        obtain ⟨pa, p'a, mva, hsomea⟩ := all_eq_some a hlea
        have hmvleft : mva = .left := by
          cases mva with
          | left => rfl
          | right =>
            have hsomeb : m.run_table' t s p b = some (pa, p'a, .right) := by rwa [←hrep]
            obtain ⟨_, _, heq⟩ := run_table'_prefix_only_left hsomeb _ hlt
            simp [heq] at hsomea
        let d := b - a
        have hadd : b = a + d := by symm; exact Nat.add_sub_of_le <| Nat.le_of_lt hlt
        have hkpos : 0 < d := Nat.sub_pos_of_lt hlt
        rw [hadd] at hrep hleb
        let off := k - b
        have hadd2 : k = a + d + off := by
          unfold off; rw [hadd]
          symm
          apply Nat.add_sub_of_le
          apply Nat.le_trans hleb
          apply Nat.le_of_not_lt
          exact hk
        apply run_table'_max_len_some (k := a+off)
        rw [←h, hadd2]
        exact run_table'_rep_offset hrep

theorem run_table'_max_len_none {m : TwoDFA α σ} {t : BackTable σ} {s : TapeSymbol α} {p : σ} {k : Nat} (h : m.run_table' t s p k = none) :
    ∃ k' ≤ Fintype.card (σ × σ × Movement), m.run_table' t s p k' = none := by
  induction k with
  | zero => exists 0
  | succ k ih =>
    match hrun : m.run_table' t s p k with
    | .none => exact ih hrun
    | .some _ => 
      obtain ⟨k', hk', hrun'⟩ := m.run_table'_max_len_some hrun
      use k' + 1, hk'
      simpa [run_table', hrun', hrun] using h

-- The sequence of pᵢ, qᵢ pairs that step_right goes through as a List
def run_table (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ) : List (σ × σ) :=
  List.range (Fintype.card (σ × σ × Movement))
    |>.map (fun k ↦ m.run_table' t a p k |>.map fun (p', q, _) ↦ (p', q))
    |>.takeWhile Option.isSome
    |>.pmap Option.get <| fun _ ↦ List.mem_takeWhile_imp

theorem run_table_max_len (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ) : (m.run_table t a p).length ≤ Fintype.card (σ × σ × Movement) := by
  unfold run_table
  rw [List.length_pmap]
  suffices (List.map _ _).length = Fintype.card (σ × σ × Movement) by
    conv => rhs; rw [←this]
    apply List.length_takeWhile_le
  rw [List.length_map, List.length_range]

lemma run_table_getElem {m : TwoDFA α σ} {t : BackTable σ} {a : TapeSymbol α} {p : σ} {i : Nat} (hi : i < (m.run_table t a p).length) {p' q : σ} :
    (m.run_table t a p)[i] = (p', q) ↔ ∃ mv : Movement, m.run_table' t a p i = some (p', q, mv) where
  mp hgetElem := by
    conv at hgetElem =>
      unfold run_table
      lhs
      rw [List.getElem_pmap]
      arg 1
      rw [List.getElem_takeWhile, List.getElem_map]
      arg 2; arg 5
      rw [List.getElem_range]
    rw [Option.get_map] at hgetElem
    match hres : m.run_table' t a p i with
    | .none => -- should be able to get a contradiction
      simp only [Prod.mk.injEq] at hgetElem 
      have : ∀ {a : Option (σ × σ × Movement)} {hsome : a.isSome} {v : σ} (h : (a.get hsome).1 = v), a.isSome := by
        intro _ hsome _ _; exact hsome
      have := this hgetElem.left
      simp [hres] at this  -- yep, this gives  none.isSome = true
    | .some (_, _, mv) =>
      use mv
      rw [Option.some_inj]
      simpa [hres] using hgetElem

  mpr := by
    rintro ⟨mv, hrun⟩
    conv =>
      unfold run_table
      lhs
      rw [List.getElem_pmap]
      arg 1
      rw [List.getElem_takeWhile, List.getElem_map]
      arg 2; arg 5
      rw [List.getElem_range]
    simp [hrun]

lemma run_table_non_empty (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ) : (m.run_table t a p) ≠ [] := by
  suffices 0 < Fintype.card σ ∧ 0 < Fintype.card Movement ∧ m.run_table' t a p 0 ≠ none by simpa [run_table]
  constructor
  · have : Nonempty σ := .intro m.start
    apply Nat.pos_of_ne_zero
    exact Fintype.card_ne_zero
  · constructor
    · simp [Movement.card_eq_2]
    · simp [run_table']

lemma run_table'_isSome_of_lt_len {m : TwoDFA α σ} {t : BackTable σ} {a : TapeSymbol α} {p : σ} {i : Nat} (hlen : i < (m.run_table t a p).length) :
    m.run_table' t a p i |>.isSome := by
  let pair := (m.run_table t a p)[i]
  suffices ∃ mv, m.run_table' t a p i = some (pair.fst, pair.snd, mv) by 
    obtain ⟨_, h⟩ := this; rw [h]; simp
  rw [←run_table_getElem hlen]

def run_table_last_move (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ) : Movement :=
  have hlen : (m.run_table t a p).length.pred < (m.run_table t a p).length :=
    Nat.pred_lt <| Nat.ne_zero_of_lt <| List.length_pos_of_ne_nil <| m.run_table_non_empty t a p
  m.run_table' t a p (m.run_table t a p).length.pred |>.get (run_table'_isSome_of_lt_len hlen) |>.2.2

lemma run_table_len_eq_of_run_table'_mv_right {m : TwoDFA α σ} {t : BackTable σ} {a : TapeSymbol α} {p p' q : σ} {i : Nat}
  (hi : i < Fintype.card (σ × σ × Movement)) (h : (m.run_table' t a p i) = some (p', q, .right)) :
    (m.run_table t a p).length = i.succ := by
  unfold run_table
  rw [List.length_pmap, List.length_takeWhile (n := i.succ)]
  · conv in List.length _ =>
      rw [List.length_map, List.length_range]
    simpa using hi
  all_goals
    conv in _[_] =>
      rw [List.getElem_map]
      arg 2; arg 5
      rw [List.getElem_range]
  · rw [Option.isSome_map]
    simp [run_table', h]
  · intro k hk
    rw [Option.isSome_map]
    obtain ⟨_, _, _, hsome⟩ := run_table'_no_holes h k <| Nat.le_of_lt_succ <| by apply And.left; simpa [hi] using hk
    simp [hsome]

theorem run_table_start (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ) : 
    have := List.length_pos_of_ne_nil (m.run_table_non_empty t a p)
    (m.run_table t a p)[0].fst = p := by
  have := List.length_pos_of_ne_nil (m.run_table_non_empty t a p)
  let st := m.step a p
  suffices (m.run_table t a p)[0] = (p, st.fst) by simp [this]
  rw [run_table_getElem]
  use st.snd
  simp [run_table', st]

theorem run_table_single_steps (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ) (i : Nat) (hi : i < (m.run_table t a p).length.pred) 
  {q1 q2 : σ} (hfst : have := Nat.lt_of_lt_pred hi; q1 = (m.run_table t a p)[i].fst) (hsnd : have := Nat.lt_of_lt_pred hi; q2 = (m.run_table t a p)[i].snd) :
    m.step a q1 = (q2, .left) := by
  simp only at hfst hsnd
  have i_valid_idx := Nat.lt_of_lt_pred hi
  have : (m.run_table t a p)[i] = (q1, q2) := by simp [hfst , hsnd]
  rw [run_table_getElem] at this
  obtain ⟨mv, hrun'⟩ := this
  cases mv with
  | right =>
    suffices i = (m.run_table t a p).length.pred by simp [this] at hi
    symm
    apply Nat.pred_eq_of_eq_succ
    apply run_table_len_eq_of_run_table'_mv_right (h := hrun')
    apply Nat.lt_of_lt_of_le i_valid_idx
    apply run_table_max_len
  | left =>
    cases i with
    | zero => 
      suffices p = q1 ∧ m.step a p = (q2, Movement.left) by rw [←this.left, this.right]
      simpa only [run_table', Option.some_inj, Prod.mk_inj] using hrun'
    | succ i => 
      match hprev : m.run_table' t a p i with
      | .none | .some (_, _, .right) =>
        simp [run_table', hprev] at hrun'  -- contradiction, would give   run_table' .. (i+1) = none
      | .some (q1', q2', .left) => 
        suffices t.map q2' = some q1 ∧ m.step a q1 = (q2, .left) from this.right
        simpa [run_table', hprev] using hrun'

theorem run_table_links (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ) (i : Nat) (hi : i.succ < (m.run_table t a p).length) :
    t.map (m.run_table t a p)[i].snd = some (m.run_table t a p)[i.succ].fst := by
  have : (m.run_table t a p)[i] = ((m.run_table t a p)[i].fst, (m.run_table t a p)[i].snd) := rfl
  rw [run_table_getElem] at this
  obtain ⟨mv1, hrun1⟩ := this
  have : (m.run_table t a p)[i.succ] = ((m.run_table t a p)[i.succ].fst, (m.run_table t a p)[i.succ].snd) := rfl
  rw [run_table_getElem] at this
  obtain ⟨mv2, hrun2⟩ := this
  cases i with
  | zero =>
    have : m.step a p = ((m.run_table t a p)[0].2, mv1) := by apply And.right; simpa [run_table'] using hrun1
    cases mv1 with
    | right => simp [run_table', this] at hrun2
    | left =>
      apply And.left
      simpa [run_table', this] using hrun2
  | succ i =>
    unfold run_table' at hrun2
    cases mv1 with
    | right => simp [hrun1] at hrun2
    | left =>
      apply And.left
      simpa [hrun1] using hrun2

theorem run_table_single_step_end (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ)
  {q1 q2 : σ} (hfst : q1 = ((m.run_table t a p).getLast (m.run_table_non_empty t a p)).fst) (hsnd : q2 = ((m.run_table t a p).getLast (m.run_table_non_empty t a p)).snd) :
    ∃ mv, m.step a q1 = (q2, mv) := by
  have non_empty := m.run_table_non_empty t a p
  have : (m.run_table t a p).getLast non_empty = (q1, q2) := by simp [hfst , hsnd]
  rw [List.getLast_eq_getElem non_empty, run_table_getElem] at this
  obtain ⟨mv, hrun'⟩ := this
  use mv
  cases hrun : m.run_table t a p with
  | nil => contradiction
  | cons hd tl =>
    cases htl : tl with
    | nil =>
      rw [htl] at hrun
      have : (m.run_table t a p).length - 1 = 0 := by simp [hrun]
      conv at hrun' =>
        rw [this]
        simp only [run_table', Option.some.injEq, Prod.mk.injEq]
      simp [← hrun'.left, hrun'.right]
    | cons md tl =>
      have : (m.run_table t a p).length - 1 = ((m.run_table t a p).length - 2).succ := by
        suffices 2 ≤ (m.run_table t a p).length by simp [Nat.sub_add_cancel this]
        simp [hrun, htl]
      conv at hrun' =>
        rw [this]
        simp only [run_table']
      match hprev : m.run_table' t a p ((m.run_table t a p).length - 2) with
      | .none | .some (_, _, .right) => simp [hprev] at hrun'  -- contradiction
      | .some (_, _, .left) => 
        suffices m.step a q1 = (q2, mv) by simp only [this]
        apply And.right
        simpa [hprev] using hrun'

theorem run_table_len_eq_card_of_some_at_len {m : TwoDFA α σ} {t : BackTable σ} {a : TapeSymbol α} {p p' q : σ} {mv : Movement}
  (h : m.run_table' t a p (m.run_table t a p).length = some (p', q, mv)) :
    (m.run_table t a p).length = Fintype.card (σ × σ × Movement) := by
  by_contra hlen
  have hlen : (m.run_table t a p).length < Fintype.card (σ × σ × Movement) := Nat.lt_of_le_of_ne (m.run_table_max_len t a p) hlen
  have : (m.run_table t a p).length = (m.run_table t a p).length.pred.succ :=
    Eq.symm <| Nat.succ_pred <| Nat.ne_zero_of_lt <| List.length_pos_of_ne_nil <| m.run_table_non_empty t a p
  conv at h => rw [this]; simp only [run_table']
  match hpred : m.run_table' t a p (m.run_table t a p).length.pred with
  | .none | .some (_, _, .right) => rw [hpred] at h; simp at h
  | .some (_, _, .left) =>
    rw [hpred] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, existsAndEq, true_and] at h
    sorry

theorem run_table'_none_at_run_table_len (m : TwoDFA α σ) (t : BackTable σ) (a : TapeSymbol α) (p : σ) (h : m.run_table' t a p (m.run_table t a p).length ≠ none) :
    ∃ k' < (m.run_table t a p).length, m.run_table' t a p (m.run_table t a p).length = m.run_table' t a p k' := by
  obtain ⟨p', q, mv, hsome⟩ : ∃ p' q mv, m.run_table' t a p (m.run_table t a p).length = some (p', q, mv) := by
    rw [Option.ne_none_iff_exists'] at h
    obtain ⟨⟨p', q, mv⟩, h⟩ := h
    use p', q, mv
  obtain ⟨k', hk', hsome'⟩ := run_table'_max_len_some hsome
  have hlen := run_table_len_eq_card_of_some_at_len hsome
  rw [←hlen] at hk'
  use k', hk'
  exact hsome.trans hsome'.symm

end RunTable

section Proof

variable [Fintype σ]

def table_for (m : TwoDFA α σ) (w : List α) : BackTable σ := w.foldl m.step_table m.first_table

theorem table_for_nil (m : TwoDFA α σ) : m.table_for [] = m.first_table := by
  simp [table_for]

theorem table_for_step {m : TwoDFA α σ} (w : List α) (a : α) : m.step_table (m.table_for w) a = m.table_for (w ++ [a]) := by
  simp [table_for]

omit [Fintype σ] in
theorem table_for_step_right {m : TwoDFA α σ} (t : BackTable σ) (w : List α) (i : Fin (w.length+1)) (hi : i < w.length) (p q : σ) (fuel : Nat) (hmap : step_right.go m t w[↑i] p fuel = some q)
  (hind : ∀ (p q : σ), t.map p = some q → m.GoesLeftOf w.toWord i.castSucc { state := p, idx := i.castSucc } { state := q, idx := i.succ }) :
    m.GoesLeftOf w.toWord i.succ { state := p, idx := i.succ } { state := q, idx := i.succ + 1 } := by
  unfold step_right.go at hmap
  cases fuel with 
  | zero => simp at hmap  -- contradiction
  | succ fuel' =>
    have hint : i.succ.internal := by
      constructor
      · simp
      · apply Fin.ne_of_lt
        rw [Fin.lt_iff_val_lt_val, Fin.val_last]
        simp [hi]
    match hstep : m.step w[i.val] p with
    | (p', .right) => 
      simp only [Fin.getElem_fin, hstep, Option.some.injEq] at hmap
      rw [←hmap]
      have hvalid : Movement.right.isValid i.succ := by constructor <;> simp [hint.right]
      apply GoesLeftOf.single (hlt := by rfl)
      right
      · suffices w.toWord.get i.succ = w[i.val] by simpa [this]
        rw [Word.get_eq_symbol_of_internal w.toWord hint]
        simp [List.toWord, Vector.get]
      · suffices Movement.right.apply i.succ hvalid = i.succ + 1 by simpa
        simp only [Movement.apply, Fin.castLT]
        rw [←Fin.val_inj, Fin.val_add_one]
        simp [hint.right]
    | (p', .left) => 
      conv at hmap =>
        simp only [Fin.getElem_fin, hstep, Option.bind_eq_bind]
        rw [Option.bind_eq_some_iff]
      obtain ⟨q', hmap', hstep'⟩ := hmap
      have : i.succ = (⟨p, i.succ⟩ : Config σ w.length).idx := rfl
      rw [this]
      apply GoesLeftOf.head (hidx := by rfl)
      · have hvalid : Movement.left.isValid i.succ := by constructor <;> simp
        apply nextConfig.stepLeft (c2 := ⟨p', i.castSucc⟩)
        · rw [w.toWord.get_eq_symbol_of_internal hint]
          simp [Vector.get, List.toWord, hstep]
        · suffices Movement.left.apply i.succ hvalid = i.castSucc by simpa
          simp only [Movement.apply]
          rw [←Fin.val_inj]
          simp
      · trans
        · apply (hind _ _ hmap').castSucc
        · apply table_for_step_right (hmap := hstep') (hind := hind)

-- TODO: better names for all these things lol
omit [Fintype σ] in
theorem table_for_step_right' {m : TwoDFA α σ} (t : BackTable σ) (w : List α) (i : Fin (w.length+1)) (hi : i < w.length) (p q : σ)
  {last : Config _ _} (hgoes : m.GoesLeftOf w.toWord i.succ { state := p, idx := i.succ } last) (hstate : last.state = q) (hidx : last.idx = i.succ + 1)
  (hind : ∀ (p q : σ), m.GoesLeftOf w.toWord i.castSucc { state := p, idx := i.castSucc } { state := q, idx := i.succ } → t.map p = some q) :
    ∃ fuel, step_right.go m t w[↑i] p fuel = some q := by
  induction i using Fin.inductionOn with
  | zero =>
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod] at hi
    have : (1 : Fin (w.length + 1 + 1)) + 1 = 2 := by
      rw [←Fin.val_inj, Fin.val_add_eq_of_add_lt]
      <;> simp [hi, Nat.mod_eq_of_lt]
    simp [this] at hgoes hind hidx
    sorry
  | succ i ih =>
    sorry

theorem table_for_take_succ {m : TwoDFA α σ} {w : List α} (i : Fin w.length) (t1 t2 : BackTable σ)
  (h1 : t1 = m.table_for (w.take i)) (h2 : t2 = m.table_for (w.take i.succ)) :
    t2 = m.step_table t1 w[i.val] := by
  simp [h2, table_for, h1]
  rw [List.take_succ, List.foldl_append]
  simp

theorem table_for_take_map (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 2)) (hnelast : i ≠ Fin.last _)
  (ht : t = m.table_for (w.take i)) (p q : σ)  :
    t.map p = some q ↔ m.GoesLeftOf w.toWord i ⟨p, i⟩ ⟨q, i+1⟩ := by
  constructor
  · intro hmap
    induction i using Fin.inductionOn generalizing t p q with
    | zero =>
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.take_zero, List.foldl_nil] at ht
      unfold table_for at ht
      simp [ht, first_table] at hmap
      apply GoesLeftOf.single (hlt := by rfl)
      right
      · simp only
        rw [w.toWord.get_eq_left_of_eq_zero rfl]
        obtain ⟨q', h'⟩ := m.in_bounds_left p
        rw [h']; rw [h'] at hmap
        simpa using hmap
      · simp [Movement.apply, Fin.castLT]
      · constructor <;> simp
    | succ i ih =>
      simp only [Fin.coe_castSucc, Fin.coeSucc_eq_succ, forall_eq] at ih
      have hlt : i.val < w.length := by
        apply i.val_lt_last
        rwa [←i.succ_ne_last_iff]
      have hget : w[i.val]? = some w[i.val] := by simp
      let prev_t := List.foldl m.step_table m.first_table (w.take i)
      have hstep : t = m.step_table prev_t w[i.val] := by
        simp only [table_for, Fin.val_succ, List.take_succ, List.foldl_append, Option.foldl_toList] at ht
        rw [hget] at ht
        simpa using ht
      unfold step_table at hstep
      simp only [hstep, Option.bind_eq_bind] at hmap
      apply table_for_step_right
      · exact hmap
      · apply ih prev_t (by simp) rfl
  · intro hgl
    induction i using Fin.inductionOn generalizing t p q with
    | zero =>
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.take_zero,
          List.foldl_nil, table_for, first_table, List.foldl_nil] at ht
      rw [ht]
      simp only [Option.some_inj]
      rcases hgl with _ | ⟨hlt, (hrfl | ⟨hlt', _, tl'⟩), tl⟩
      -- Initial refl case is automatically discharged as impossible
      case tail.tail =>
        exfalso -- more than one step is impossible
        simp at hlt hlt'
        apply nextConfig.must_move
        · exact (hlt.trans hlt'.symm).symm
        · exact tl'
      case tail.refl => -- single step
        rcases tl with ⟨hstep, _, _⟩ | ⟨hstep, _, _⟩
        all_goals 
          simp only [Word.get_eq_left_of_eq_zero, Prod.ext_iff] at hstep
          exact hstep.left
    | succ i ih =>
      have hlt : i.val < w.length := by
        apply i.val_lt_last
        rwa [←i.succ_ne_last_iff]
      have hget : w[i.val]? = some w[i.val] := by simp
      let prev_t := List.foldl m.step_table m.first_table (w.take i)
      have hstep : t = m.step_table prev_t w[i.val] := by
        simp only [table_for, Fin.val_succ, List.take_succ, List.foldl_append, Option.foldl_toList] at ht
        rw [hget] at ht
        simpa using ht
      have := ih prev_t (by simp) rfl
      sorry

theorem table_for_take_init (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 1))
  (ht : t = m.table_for (w.take i)) {q : σ} (hinit : t.init = some q)
    : m.GoesLeftOf w.toWord i.castSucc m.init ⟨q, i.succ⟩ := by
  induction i using Fin.inductionOn generalizing t q with
  | zero =>
    conv at hinit =>
      rw [ht]
      simp [table_for, first_table]
    rw [←hinit]
    apply GoesLeftOf.single (hlt := by rfl)
    rw [←stepConfig_gives_nextConfig]
    simp only [stepConfig, Word.get_eq_left_of_eq_zero, Fin.succ_zero_eq_one, Config.mk.injEq, true_and]
    obtain ⟨_, hright⟩ := m.in_bounds_left m.start
    unfold step at hright
    conv => enter [1, 1, 1]; rw [hright]
    simp [Movement.apply, Fin.castLT]
  | succ i ih =>
    let prev_t := m.table_for (w.take i)
    have hstep : t = m.step_table prev_t w[i.val] := m.table_for_take_succ i prev_t t rfl ht
    have hinit_def : prev_t.init.bind (m.step_right prev_t w[i.val]) = t.init := by
      simp [hstep, step_table]
    rw [hinit, Option.bind_eq_some_iff] at hinit_def
    obtain ⟨prev_init, hprev, hstep_init⟩ := hinit_def
    trans
    · apply (ih prev_t rfl hprev).castSucc
    · have : i.succ.succ = i.castSucc.succ + 1 := by
        rw [←Fin.val_inj]
        simp [Fin.val_add_one]
      rw [this]
      apply m.table_for_step_right prev_t w i.castSucc i.is_lt prev_init q _ hstep_init
      have : i.castSucc.succ = i.castSucc.castSucc + 1 := by
        rw [←Fin.val_inj]
        simp [Fin.val_add_one]
      rw [this]
      intro p q
      exact m.table_for_take_map w prev_t i.castSucc.castSucc (by simp) rfl p q |>.mp

omit [Fintype σ] in
theorem table_for_accepting_go {m : TwoDFA α σ} (t : BackTable σ) (w : List α) (p q : σ) (fuel : Nat) (hmap : accepting_table.go m t p fuel = some q)
  (hind : ∀ (p q : σ), t.map p = some q → m.GoesLeftOf w.toWord (Fin.last _) { state := p, idx := Fin.ofNat _ w.length } { state := q, idx := Fin.last _ }) :
    m.GoesLeftOf w.toWord (Fin.last _) { state := p, idx := Fin.last _ } { state := q, idx := Fin.last _ } := by
  cases fuel with
  | zero => 
    have : p = q := by simpa [accepting_table.go] using hmap
    rw [this]
  | succ fuel =>
    obtain ⟨p', hp'⟩ := m.in_bounds_right p
    obtain ⟨q', hq', hmap'⟩ : ∃ a, t.map p' = some a ∧ accepting_table.go m t a fuel = some q := by
      simpa [accepting_table.go, hp', Option.bind_eq_some_iff] using hmap
    apply GoesLeftOf.head
    · suffices m.nextConfig w.toWord ⟨p, Fin.last _⟩ ⟨p', Fin.ofNat _ w.length⟩ from this
      rw [←stepConfig_gives_nextConfig]
      unfold step at hp'
      simp only [stepConfig, Word.get_eq_right_of_eq_last, hp', Fin.ofNat_eq_cast, Config.mk.injEq, true_and]
      rw [←Fin.val_inj]
      simp only [Movement.apply, Fin.predCast, Fin.castLE, Fin.coe_pred, Fin.val_last, add_tsub_cancel_right, Fin.val_natCast]
      have : w.length < w.length + 2 := by trans <;> apply Nat.lt_add_one
      symm
      simp [Nat.mod_eq_iff_lt, this]
    · trans
      · exact hind p' q' hq'
      · apply table_for_accepting_go (hmap := hmap') (hind := hind)
    · rfl


theorem accepts_of_table_for_accepting (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (hfor : t = m.table_for w) (hacc : m.accepting_table t) :
    m.GoesLeftOf w.toWord (Fin.last _) m.init ⟨m.accept, Fin.last _⟩ := by
  simp only [accepting_table, Option.bind_eq_bind, Option.bind_eq_some_iff] at hacc
  obtain ⟨init, hinit_some, hgo_accept⟩ := hacc
  have hfor' : t = m.table_for (List.take (↑(Fin.last w.length)) w) := by
    rwa [←List.take_length (l := w)] at hfor
  trans
  · exact (m.table_for_take_init w t (Fin.last (w.length)) hfor' hinit_some).castSucc
  · apply table_for_accepting_go (hmap := hgo_accept)
    intros p q hpq
    have : w.length < w.length + 1 + 1 := by trans <;> apply Nat.lt_add_one
    have : Fin.last (w.length + 1) = (Fin.ofNat (w.length + 2) w.length) + 1 := by
      rw [←Fin.val_inj, Fin.val_last, Fin.val_add_one]
      have : (Fin.ofNat (w.length + 2) w.length) ≠ Fin.last (w.length + 1) := by 
        rw [Fin.ne_iff_vne]
        simp [Nat.mod_eq_of_lt]
      simp only [this, ↓reduceIte]
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.add_right_cancel_iff]
      rwa [Nat.mod_eq_of_lt]
    rw [this]; clear this
    let i := Fin.ofNat (w.length + 2) w.length
    have i_val : i.val = w.length := by simpa [i]
    have : m.GoesLeftOf w.toWord i { state := p, idx := i } { state := q, idx := i + 1 } := by
      apply m.table_for_take_map w t _ _ _ _ _ |>.mp
      · assumption
      · rw [Fin.ne_iff_vne, Fin.val_ofNat, Fin.val_last]
        simp [Nat.mod_eq_of_lt]
      · simpa [i_val]
    apply this.castLE
    rw [Fin.le_iff_val_le_val, Fin.val_add]
    simp [i_val]

theorem GoesLeftOf_of_table_for_take_map {m : TwoDFA α σ} {w : List α} {i : Fin _} {p q : σ} (h : (m.table_for (w.take i)).map p = some q) :
    m.GoesLeftOf w.toWord i.castSucc ⟨p, i.castSucc⟩ ⟨q, i.succ⟩ := by
  sorry

theorem GoesLeftOf.step (m : TwoDFA α σ) (w : List α) {i : Fin _} (p q : σ) (hi : i ≠ Fin.last _) : m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩ ↔
    ∃ psqs : List (σ × σ), ∃ hlen : psqs.length ≠ 0,
      psqs[0].fst = p ∧ (psqs[psqs.length.pred]'(by simp [Nat.pos_of_ne_zero hlen])).snd = q ∧
      (∀ j, ∀ hj : j < psqs.length.pred,
        m.nextConfig w ⟨(psqs[j]'(Nat.lt_of_lt_pred hj)).fst, i.succ⟩ ⟨(psqs[j]'(Nat.lt_of_lt_pred hj)).snd, i.castSucc⟩ ∧
        m.GoesLeftOf w i.castSucc ⟨(psqs[j]'(Nat.lt_of_lt_pred hj)).snd, i.castSucc⟩ ⟨(psqs[j.succ]'(Nat.succ_lt_of_lt_pred hj)).fst, i.succ⟩) ∧
      m.nextConfig w ⟨(psqs[psqs.length.pred]'(by simp [Nat.pos_of_ne_zero hlen])).fst, i.succ⟩ ⟨(psqs[psqs.length.pred]'(by simp [Nat.pos_of_ne_zero hlen])).snd, i.succ + 1⟩ 
where
  mp hgoes := by
    have _ : i.val < w.length := Fin.lt_last_iff_ne_last.mpr hi
    have hget : TapeSymbol.symbol w[i] = w.toWord.get i.succ := by simp [List.toWord, Word.get, hi, Vector.get]
    use m.run_table (m.table_for (w.take i)) w[i] p
    use Nat.ne_zero_of_lt <| List.length_pos_of_ne_nil <| by apply run_table_non_empty
    constructorm* _ ∧ _
    · apply run_table_start
    · sorry
    · intro j hj
      constructor
      · have run_steps := run_table_single_steps _ _ _ _ _ hj rfl rfl
        unfold TwoDFA.step at run_steps
        rw [←stepConfig_gives_nextConfig]
        ext
        . simp only [stepConfig, ←hget, run_steps]
        . simp only [stepConfig, ←hget, run_steps]
          simp [Movement.apply]
      · apply GoesLeftOf_of_table_for_take_map
        apply run_table_links (hi := Nat.succ_lt_of_lt_pred hj)
    · sorry
  mpr := by
    rintro ⟨psqs, hlen, hstrt, hstp, hmap, hlast⟩
    cases psqs with
    | nil => simp at hlen -- psqs.length ≠ 0
    | cons hd tl =>
      cases tl with
      | nil => 
        clear hmap
        simp at hlast hstrt hstp
        rw [hstrt, hstp] at hlast
        apply single (hnext := hlast); simp
      | cons hd' tl' =>
        simp at hmap hlast hstrt hstp
        rw [hstp] at hlast
        apply tail (tail := hlast) (hlt := by simp)
        rw [←hstrt]
        exact step_mpr_go tl'.length (hd :: hd' :: tl') (by simp) hmap


theorem accepts_iff_table_for_accepting (m : TwoDFA α σ) (w : List α) : m.accepting_table (m.table_for w) ↔ m.GoesLeftOf w.toWord (Fin.last _) m.init ⟨m.accept, Fin.last _⟩ where
  mp := m.accepts_of_table_for_accepting w _ rfl
  mpr := sorry

/----------------------------------------------------------------
                            The Goal
----------------------------------------------------------------/
theorem to_one_way_correct (m : TwoDFA α σ) : m.language = m.to_one_way.accepts := by
  ext w
  suffices m.accepts w.toWord ↔ m.accepting_table (m.table_for w) from this
  rw [m.accepts_iff_table_for_accepting w]
  constructor
  · intro acc
    apply GoesLeftOf.attach
    exact m.reaches_accept_last_of_accepts w.toWord acc
  · intro hgoes
    use Fin.last _
    exact hgoes.forget

end Proof

end TwoDFA
