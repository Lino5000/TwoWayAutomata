import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Configurations
import TwoWayAutomata.Kozen.Language
import TwoWayAutomata.Kozen.Lemmas
import TwoWayAutomata.Kozen.Movement
import TwoWayAutomata.Kozen.Word

lemma List.Chain.append_singleton {α : Type _} {R : α → α → Prop} {l : List α} {a b : α}
  (hc : List.Chain R a l) (hr : R ((a :: l).getLast <| by simp) b) :
    List.Chain R a (l ++ [b]) := by
  induction hc with
  | nil => simpa
  | cons hr' hc ih =>
    have := ih <| by simpa using hr
    exact .cons hr' this

lemma List.Chain.trim_singleton {α : Type _} {R : α → α → Prop} {l : List α} {a b : α}
  (h : List.Chain R a (l ++ [b])) :
    List.Chain R a l ∧ R ((a :: l).getLast <| by simp) b := by
  induction l generalizing a with
  | nil => simpa using h
  | cons _ _ ih =>
    simp only [cons_append, chain_cons] at h
    simp [ih h.right, h]

lemma List.Chain.get_step {α : Type _} {R : α → α → Prop} {a : α} {b : List α} (c : Chain R a b) (idx : Nat) (hidx : idx < b.length) :
    have : idx < (a::b).length := Nat.lt_add_one_of_lt hidx; R (a :: b)[idx] b[idx] := by
  cases c with
  | nil => simp at hidx  -- Contradiction, idx < 0
  | cons ha c' =>
    cases idx with
    | zero => exact ha
    | succ idx' => apply c'.get_step idx'

theorem List.pidgeon_hole {α : Type _} [DecidableEq α] [fin : Fintype α] (l : List α) (h : fin.card < l.length) : ∃ x : α, l.Duplicate x := by
  obtain ⟨x, y, hne, hidx⟩ := Fintype.exists_ne_map_eq_of_card_lt (l.get) <| by simp [h]
  use l.get x
  rw [duplicate_iff_sublist]
  if hord : x < y
    then
      suffices [l.get x, l.get y].Sublist l by rwa [←hidx] at this
      have left : [l[x]].Sublist (l.take (x+1)) := by
        rw [singleton_sublist, mem_take_iff_getElem]
        suffices x.val < min (x.val+1) l.length by exists x, this
        simp [x.is_lt]
      have right : [l[y]].Sublist (l.drop (x+1)) := by
        rw [singleton_sublist, mem_drop_iff_getElem]
        have : y.val - (x.val + 1) + (x.val + 1) = y.val := by
          rwa [Nat.sub_add_cancel]
        use y.val - (x.val + 1), by rw [this]; exact y.is_lt
        conv in _ + _ + _ =>
          rw [Nat.add_comm, this]
        simp
      have : [l.get x, l.get y] = [l.get x] ++ [l.get y] := by simp
      rw [this, append_sublist_iff]
      use l.take (x+1), l.drop (x+1)
      simp only [take_append_drop, get_eq_getElem, true_and]
      exact ⟨left, right⟩
    else
      have : y < x := by simpa [hord] using Fin.lt_or_lt_of_ne hne
      suffices [l.get y, l.get x].Sublist l by rwa [←hidx] at this
      have left : [l[y]].Sublist (l.take (y+1)) := by
        rw [singleton_sublist, mem_take_iff_getElem]
        suffices y.val < min (y.val+1) l.length by exists y, this
        simp [y.is_lt]
      have right : [l[x]].Sublist (l.drop (y+1)) := by
        rw [singleton_sublist, mem_drop_iff_getElem]
        have : x.val - (y.val + 1) + (y.val + 1) = x.val := by
          rwa [Nat.sub_add_cancel]
        use x.val - (y.val + 1), by rw [this]; exact x.is_lt
        conv in _ + _ + _ =>
          rw [Nat.add_comm, this]
        simp
      have : [l.get y, l.get x] = [l.get y] ++ [l.get x] := by simp
      rw [this, append_sublist_iff]
      use l.take (y+1), l.drop (y+1)
      simp only [take_append_drop, get_eq_getElem, true_and]
      exact ⟨left, right⟩


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
  | k + 1 => m.stepConfig w <| stepTimes k strt

theorem stepTimes_comm (steps : Nat) (strt : Config σ n) :
    m.stepConfig w (m.stepTimes w steps strt) = m.stepTimes w steps (m.stepConfig w strt) := by
  induction steps with
  | zero => simp [stepTimes]
  | succ k ih => simp [stepTimes, ih]

theorem GoesTo_of_stepTimes {steps : Nat} {strt stp : Config σ n} (h : m.stepTimes w steps strt = stp) : m.GoesTo w strt stp := by
  cases steps with
  | zero =>
    simp [stepTimes] at h
    rw [h]
  | succ k =>
    rw [stepTimes, stepConfig_gives_nextConfig] at h
    apply GoesTo.tail
    · exact GoesTo_of_stepTimes (stp := m.stepTimes w k strt) rfl
    · exact h

@[ext]
structure ExecTrace : Type _ where
  strt : Config σ n
  rest : List (Config σ n)
  prf : rest.Chain (m.nextConfig w) strt

namespace ExecTrace

variable {m : TwoDFA α σ} {w : Word α n} 

@[simp]
def nil (cfg : Config σ n) : m.ExecTrace w where
  strt := cfg
  rest := []
  prf := .nil

@[simp]
def cons (head : Config σ n) (tail : m.ExecTrace w) (h : m.nextConfig w head tail.strt) : m.ExecTrace w where
  strt := head
  rest := tail.strt :: tail.rest
  prf := .cons h tail.prf

def toList (trace : m.ExecTrace w) : List (Config σ n) :=
  trace.strt :: trace.rest

def lastCfg (trace : m.ExecTrace w) : Config σ n := 
  match trace.rest with
  | [] => trace.strt
  | h :: t => (h :: t).getLast <| by simp

theorem lastCfg_eq_toList_getLast {trace : m.ExecTrace w} : trace.lastCfg = trace.toList.getLast (by simp [toList]) := by
  if h : trace.rest = []
    then
      conv =>
        lhs
        simp [lastCfg, h]
      simp [toList, h]
    else
      have : trace.rest = trace.rest.head h :: trace.rest.tail := by simp
      conv =>
        lhs
        unfold lastCfg
        rw [this]
        simp
      simp [toList, h]

def trans (t1 t2 : m.ExecTrace w) (h : m.nextConfig w t1.lastCfg t2.strt) : m.ExecTrace w where
  strt := t1.strt
  rest := t1.rest ++ t2.toList
  prf := by
    unfold toList
    rw [List.chain_split]
    refine ⟨?_, t2.prf⟩
    apply List.Chain.append_singleton
    · exact t1.prf
    · rwa [lastCfg_eq_toList_getLast] at h

def length (trace : m.ExecTrace w) : Nat := trace.rest.length + 1

@[simp]
theorem length_ne_0 (trace : m.ExecTrace w) : trace.length ≠ 0 := by simp [length]

instance {trace : m.ExecTrace w} : NeZero trace.length where
  out := trace.length_ne_0

def get (trace : m.ExecTrace w) (idx : Fin (trace.length)) : Config σ n :=
  trace.toList.get idx

def split (trace : m.ExecTrace w) (idx : Fin (trace.length)) (h : idx ≠ ⟨0, by simp [length]⟩) : m.ExecTrace w × m.ExecTrace w :=
  have h' : idx.val ≠ 0 := Fin.val_ne_of_ne h
  have : trace.rest = (trace.rest.take <| idx.pred h) ++ trace.get idx :: trace.rest.drop idx := by
    have valid : idx.val - 1 < trace.rest.length := by
      rw [←Nat.add_one_lt_add_one_iff, Nat.sub_one_add_one h']
      exact idx.is_lt
    have : trace.rest[idx.val - 1]'valid :: List.drop (idx.val) trace.rest = List.drop (idx.val - 1) trace.rest := by
      conv in List.drop _ _ => rw [←Nat.sub_one_add_one h']
      apply List.getElem_cons_drop
    simp [get, toList, List.getElem_cons, h', this]
  have : List.Chain (m.nextConfig w) trace.strt (_ ++ [_]) ∧ List.Chain (m.nextConfig w) _ _ := by
    rw [←List.chain_split, ←this]
    exact trace.prf
  ⟨⟨
    trace.strt,
    trace.rest.take <| idx.pred h,
    List.Chain.trim_singleton this.left |>.left,
  ⟩, ⟨
    trace.get idx,
    trace.rest.drop idx,
    this.right,
  ⟩⟩

lemma split_left_lastCfg (trace : m.ExecTrace w) (idx : Fin (trace.length)) (h : idx ≠ 0) :
    (trace.split idx h).1.lastCfg = trace.get (idx - 1) := by
  simp [split, lastCfg, get]
  cases hidx : idx.val - 1 with
  | zero =>
    have : (idx - 1).val = 0 := by rwa [Fin.val_sub_one_of_ne_zero h]
    conv in _[_] => lhs; rw [this]
    simp [toList]
  | succ k =>
    have : (idx - 1).val = k + 1 := by rwa [Fin.val_sub_one_of_ne_zero h]
    conv in _[_] => lhs; rw [this]
    simp only [toList, List.getElem_cons_succ]
    cases htake : trace.rest.take (k+1) with
    | nil =>
      conv at htake =>
        rw [List.take_eq_nil_iff]
        simp only [Nat.add_eq_zero, one_ne_zero, and_false, false_or]
      have len_one : trace.length = 1 := by simpa [length]
      have := idx.is_lt
      conv at this => rhs; rw [len_one]
      rw [Nat.lt_one_iff] at this
      rw [Fin.ne_iff_vne] at h
      contradiction
    | cons hd tl =>
      simp only
      conv in _ :: _ => rw [←htake]
      rw [List.getLast_take]
      suffices k < trace.rest.length by simp [List.getElem?_eq_getElem this]
      have := idx.is_lt.trans' <| Nat.sub_one_lt <| Fin.val_ne_of_ne h
      simpa [hidx, length]

lemma split_connect (trace : m.ExecTrace w) (idx : Fin (trace.length)) (h : idx ≠ 0) : 
    let (left, right) := trace.split idx h; m.nextConfig w left.lastCfg right.strt := by
  split 
  have h' : idx.val ≠ 0 := by simpa using Fin.val_ne_of_ne h
  have hlen : trace.length ≠ 1 := by
    by_contra hlen
    have := idx.is_lt
    conv at this => rhs; rw [hlen]
    rw [Nat.lt_one_iff] at this
    contradiction
  next _ left right heq =>
    conv at heq =>
      simp [split]
    rw [←heq.left, ←heq.right]
    simp only [lastCfg]
    rcases hrest : trace.rest.take (idx.val - 1) with _ | ⟨hd, tl⟩
    · simp only
      rcases List.take_eq_nil_iff.mp hrest with idx_one | rest_nil
      -- trace.rest.take _ = []  ∧  ↑idx-1 = 0
      · have one_mod_len : 1 % trace.toList.length = 1 := by rwa [Nat.one_mod_eq_one]
        have idx_one : idx = 1 := by
          rw [←Nat.add_one_inj, Nat.sub_one_add_one h', zero_add] at idx_one
          rw [←Fin.val_inj, idx_one]
          symm
          simpa only [Fin.coe_ofNat_eq_mod, length, toList] using one_mod_len
        rw [idx_one]
        simp only [get, List.get_eq_getElem, Fin.coe_ofNat_eq_mod, one_mod_len]
        simp [toList]
        apply trace.prf.get_step 0
      -- trace.rest.take _ = []  ∧  ↑idx-1 ≠ 0
      · have := idx.is_lt
        conv at this =>
          simp only [length, rest_nil]
          simp
        contradiction
    -- trace.rest.take _ = hd :: tl
    · simp only
      have _ : idx.val - 1 < trace.rest.length := by
        have := idx.is_lt
        unfold length at this
        rwa [←Nat.add_one_lt_add_one_iff, Nat.sub_one_add_one h']
      have hstep := trace.prf.get_step (idx.val - 1) <| by assumption
      have _ : idx.val - 1 < (trace.strt :: trace.rest).length := by
        simp only [List.length_cons]
        apply Nat.lt_of_le_of_lt (m := idx.val)
        · simp
        · exact idx.is_lt
      suffices (trace.strt :: trace.rest)[idx.val - 1] = (trace.rest.take (idx.val - 1)).getLast (by simp [hrest]) by
        conv in hd :: tl => rw [←hrest]
        rw [←this]
        have : trace.get idx = trace.rest[idx.val-1] := by simp [get, toList, List.getElem_cons, h]
        rwa [this]
      have idx_ne_one : idx.val - 1 ≠ 0 := by
        by_contra idx_one
        simp [idx_one] at hrest
      have := List.getLast_take (i := idx.val - 1) (l := trace.rest) <| by simp [hrest]
      rw [this]
      have : idx.val - 1 - 1 < trace.rest.length := by
        apply Nat.lt_of_le_of_lt (m := idx.val - 1)
        · simp
        · assumption
      have := List.getElem?_eq_getElem this
      simp [this, List.getElem_cons, idx_ne_one]

theorem split_trans (trace : m.ExecTrace w) (idx : Fin (trace.length)) (h : idx ≠ ⟨0, by simp [length]⟩) : 
    (trace.split idx h).1.trans (trace.split idx h).2 (by have := trace.split_connect idx h; simpa) = trace := by
  simp only [split, trans]
  ext : 1
  · rfl
  · suffices trace.get idx :: trace.rest.drop idx.val = trace.rest.drop (idx.val - 1) by simp [toList, this]
    have h' : idx.val ≠ 0 := by simpa using h
    have : idx.val = idx.val - 1 + 1 := Nat.sub_one_add_one h' |>.symm
    conv in List.drop _ _ => lhs; rw [this]
    have : idx.val - 1 < trace.rest.length := by
      have := idx.is_lt
      unfold length at this
      rwa [←Nat.add_one_lt_add_one_iff, Nat.sub_one_add_one h']
    simp [get, toList, List.getElem_cons, h', this]

end ExecTrace

def traceSteps' (strt : Config σ n) : Nat → List (Config σ n)
  | 0 => [strt]
  | k + 1 => strt :: traceSteps' (m.stepConfig w strt) k

lemma traceSteps'_nonempty (strt : Config σ n) (steps : Nat) : m.traceSteps' w strt steps ≠ [] := by
  cases steps <;> simp [traceSteps']

lemma traceSteps'_head (strt : Config σ n) : ∀ steps, ∃ l, m.traceSteps' w strt steps = strt :: l
  | 0 => by use []; simp [traceSteps']
  | k + 1 => by
    use m.traceSteps' w (m.stepConfig w strt) k
    simp [traceSteps']

lemma traceSteps'_chain (steps : Nat) {strt head : Config σ n} {tail : List (Config σ n)} (htrace : m.traceSteps' w strt steps = head :: tail) :
    tail.Chain (m.nextConfig w) head := by
  cases steps with
  | zero =>
    -- Contradiction at htrace : m.traceSteps' w strt 0 = head :: h :: t
    have : m.traceSteps' w strt 0 = [strt] := by simp [traceSteps']
    simp [this] at htrace
    rw [htrace.right]
    exact .nil
  | succ k =>
    simp [traceSteps'] at htrace
    cases tail with
    | nil => simp [traceSteps'_nonempty, htrace.right]
    | cons h t =>
      apply List.Chain.cons
      · rw [←stepConfig_gives_nextConfig, ←htrace.left]
        obtain ⟨_, hhead⟩ := m.traceSteps'_head w (m.stepConfig w strt) k
        simp [htrace.right] at hhead
        exact hhead.left.symm
      · exact traceSteps'_chain k htrace.right

theorem traceSteps'_succ (steps : Nat) (strt : Config σ n) : m.traceSteps' w strt steps = (m.traceSteps' w strt (steps + 1)).dropLast := by
  induction steps generalizing strt with
  | zero => simp [traceSteps']
  | succ k ih => 
    unfold traceSteps'
    suffices m.traceSteps' w (m.stepConfig w strt) (k + 1) =
            (m.stepConfig w strt) :: m.traceSteps' w (m.stepConfig w <| m.stepConfig w strt) k by simp [ih, this]
    conv => lhs; unfold traceSteps'; simp only

def traceSteps (steps : Nat) (strt : Config σ n) : m.ExecTrace w :=
  match h : m.traceSteps' w strt steps with
  | [] => by have := m.traceSteps'_nonempty w strt steps; contradiction
  | [single] => .nil single
  | head :: tail => ⟨head, tail, traceSteps'_chain m w steps h⟩

theorem traceSteps_length (steps : Nat) (strt : Config σ n) : (m.traceSteps w steps strt).length = steps + 1 := by
  simp only [traceSteps]
  split
  case h_1 heq =>
    have := m.traceSteps'_nonempty w strt steps
    contradiction
  case h_2 single heq =>
    cases steps with
    | zero => simp [ExecTrace.length]
    | succ k =>
      conv at heq =>
        simp [traceSteps', traceSteps'_nonempty]
      contradiction
  case h_3 head tail tailne heq =>
    simp only [ExecTrace.length]
    induction steps generalizing tail with
    | zero =>
      simp [traceSteps'] at heq
      simpa using heq.right
    | succ k ih =>
      have := m.traceSteps'_succ w k strt
      rw [heq] at this
      sorry

theorem traceSteps'_getLast_eq_stepTimes (steps : Nat) (strt : Config σ n) :
    m.stepTimes w steps strt = (m.traceSteps' w strt steps).getLast (traceSteps'_nonempty _ _ _ _) := by
  match steps with
  | 0 => simp [stepTimes, traceSteps']
  | k+1 =>
    simp only [stepTimes, traceSteps', List.getLast_cons <| traceSteps'_nonempty _ _ _ _]
    have hind := traceSteps'_getLast_eq_stepTimes k <| m.stepConfig w strt
    rwa [stepTimes_comm]

theorem traceSteps_last_cfg_eq_traceSteps'_getLast (steps : Nat) (strt : Config σ n) :
    (m.traceSteps w steps strt).lastCfg = (m.traceSteps' w strt steps).getLast (traceSteps'_nonempty _ _ _ _) := by
  rcases steps with _zero | _one | _more
  <;> simp [traceSteps, traceSteps', ExecTrace.lastCfg]

theorem traceSteps_equiv_stepTimes (steps : Nat) (strt : Config σ n) : m.stepTimes w steps strt = (m.traceSteps w steps strt).lastCfg := by
  trans
  · exact m.traceSteps'_getLast_eq_stepTimes w steps strt
  · symm; exact m.traceSteps_last_cfg_eq_traceSteps'_getLast w steps strt

def execute [DecidableEq σ] [fin_cfgs : Fintype (Config σ n)] : RunResult :=
  let last_config := m.stepTimes w fin_cfgs.card m.init
  if last_config.state = m.accept
    then .accept
    else if last_config.state = m.reject
      then .reject
      -- We step as many times as there are unique configurations; if we haven't terminated yet we never will
      else .cycle

theorem execute_accept_iff_stepTimes_state_eq_accept [DecidableEq σ] [fin_cfgs : Fintype (Config σ n)] :
    m.execute w = .accept ↔ (m.stepTimes w fin_cfgs.card m.init).state = m.accept where
  mp := by
    intro hexec
    by_contra hne
    simp [execute, hne] at hexec
    if h : (m.stepTimes w (Fintype.card (Config σ n)) m.init).state = m.reject
      then simp [h] at hexec
      else simp [h] at hexec
  mpr := by
    intro heq
    simp [execute, heq]

theorem execute_accept_iff_traceSteps_state_eq_accept [DecidableEq σ] [fin_cfgs : Fintype (Config σ n)] :
    m.execute w = .accept ↔ (m.traceSteps w fin_cfgs.card m.init).lastCfg.state = m.accept := by
  rw [execute_accept_iff_stepTimes_state_eq_accept, traceSteps_equiv_stepTimes]

theorem duplicate_of_gt_maxSteps [DecidableEq σ] [fin_cfgs : Fintype (Config σ n)] (steps : Nat) (hstep : fin_cfgs.card < steps) :
    ∃ c, (m.traceSteps w steps m.init).toList.Duplicate c := by
  apply List.pidgeon_hole
  sorry

theorem duplicate_of_not_accept_maxSteps [DecidableEq σ] [fin_cfgs : Fintype (Config σ n)]
  (ha : (m.traceSteps w fin_cfgs.card m.init).lastCfg.state ≠ m.accept) (hr : (m.traceSteps w fin_cfgs.card m.init).lastCfg.state ≠ m.reject) :
    ∃ c, (m.traceSteps w fin_cfgs.card m.init).toList.Duplicate c := by
  sorry

theorem todo [DecidableEq σ] [fin_cfgs : Fintype (Config σ n)] {steps : Nat} {strt : Config σ n} (h : fin_cfgs.card < steps) :
    (m.traceSteps w steps strt).lastCfg.state = m.accept ↔ (m.traceSteps w fin_cfgs.card strt).lastCfg.state = m.accept := by
  sorry

theorem accepts_iff_execute_eq_accept [DecidableEq σ] [Fintype σ] : m.accepts w ↔ m.execute w = .accept := by
  rw [execute_accept_iff_traceSteps_state_eq_accept]
  constructor
  -- m.accepts w → m.execute w = .accept
  · intro h
    sorry
  -- m.execute w = .accept → m.accepts w
  · intro h
    sorry

end TwoDFA
