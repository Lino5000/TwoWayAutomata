import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Computability.DFA

import TwoWayAutomata.Kozen.Language
import TwoWayAutomata.Kozen.Correctness

theorem Option.ne_some {α : Type _} (o : Option α) {a : α} (h : o ≠ some a) : o = none ∨ ∃ b : α, b ≠ a ∧ o = some b := by
  cases o with
  | none => simp
  | some b => right; use b; simpa using h

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

theorem table_for_take_succ {m : TwoDFA α σ} {w : List α} (i : Fin w.length) (t1 t2 : BackTable σ)
  (h1 : t1 = m.table_for (w.take i)) (h2 : t2 = m.table_for (w.take i.succ)) :
    t2 = m.step_table t1 w[i.val] := by
  simp [h2, table_for, h1]
  rw [List.take_succ, List.foldl_append]
  simp

theorem table_for_take_map (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 2)) (hnelast : i ≠ Fin.last _)
  (ht : t = m.table_for (w.take i)) (p q : σ) (hmap : t.map p = some q) :
    m.GoesLeftOf w.toWord i ⟨p, i⟩ ⟨q, i+1⟩ := by
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
    · exact ih (t := prev_t) (by simp) rfl

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
      exact m.table_for_take_map w prev_t i.castSucc.castSucc (by simp) rfl

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
      apply m.table_for_take_map w t
      · rw [Fin.ne_iff_vne, Fin.val_ofNat, Fin.val_last]
        simp [Nat.mod_eq_of_lt]
      · simpa [i_val]
      · assumption
    apply this.castLE
    rw [Fin.le_iff_val_le_val, Fin.val_add]
    simp [i_val]

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
