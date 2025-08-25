import Mathlib.Tactic.DeriveEncodable
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.Finset
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Fintype.Inv
import Mathlib.Computability.DFA

import TwoWayAutomata.Kozen.Conversion
import TwoWayAutomata.Visualise.TwoDFA

variable {α σ : Type*}

def DFA.asDotGraph_explicit
  (m : DFA α σ)
  (header := "DFA")
  (sym_disp : α → String)
  (state_disp : σ → String)
  (inc_states : List σ)
  (inc_syms : List α) 
  [DecidablePred (· ∈ m.accept)] :
  String := Id.run do
    let mut lines := #[s!"digraph \"{header}\" " ++ "{"]
    -- First add the nodes for states
    for (q, i) in inc_states.zipIdx do
      if q ∈ m.accept
        then
          lines := lines.push s!"  \"{state_disp q}\" [peripheries=2, label=\"T{i}\"];"
        else
          lines := lines.push s!"  \"{state_disp q}\" [label=\"T{i}\"];"

    -- Highlight start node
    lines := lines.push s!"  \"{state_disp m.start}\" [style=\"filled\", fillcolor=\"#EEEEBB\", color=\"#CCCC00\", penwidth=2.0];"

    -- Then add edges for transitions
    for p in inc_states do
      for a in inc_syms do
        let q := m.step p a
        -- We use intermediary nodes to encourage the edge labels into not overlapping other things.
        -- This might lead to transition edges moving well out of their way for no apparent reason
        lines := lines.push s!"  \"{state_disp p}-{sym_disp a}-{state_disp q}\" [label=\"{sym_disp a}\", shape=\"box\", style=\"filled\", color=\"#FFFFFF\"];"
        lines := lines.push s!"  \"{state_disp p}\" -> \"{state_disp p}-{sym_disp a}-{state_disp q}\" [arrowhead=\"none\"];"
        lines := lines.push s!"  \"{state_disp p}-{sym_disp a}-{state_disp q}\" -> \"{state_disp q}\" [];"
    
    lines := lines.push "}"
    return "\n".intercalate lines.toList

set_option linter.unusedVariables false -- linter complains about hfrontnonempty because it's only used in the termination proof?
def DFA.reachable.aux [Fintype σ] [DecidableEq σ] (m : DFA α σ) (inc_symbols : List α) (visited : List σ) (frontier : List σ)
  (hvisit : visited.Nodup) (hfrontdup : frontier.Nodup) (hfrontnonempty : frontier ≠ [])
  (hdisjoint : visited.Disjoint frontier) :
    List σ :=
  let visited' := visited ++ frontier
  let frontier' := frontier.flatMap go |>.dedup.filter (· ∉ visited')
  if hnil : frontier' = []
    then visited'
    else by
      have hvisit' : visited'.Nodup := by
        rw [List.nodup_append']
        constructorm* _ ∧ _ <;> assumption
      apply aux m inc_symbols visited' frontier'
      · exact hvisit'
      · apply List.Nodup.filter
        apply List.nodup_dedup
      · exact hnil
      · intro a _ hfiltered
        suffices a ∉ visited' by contradiction
        rw [List.mem_filter] at hfiltered
        simpa using hfiltered.right
  termination_by Fintype.card σ - visited.length
  decreasing_by
    rw [List.length_append]
    have : frontier.length ≠ 0 := by rwa [ne_eq, ←List.length_eq_zero_iff] at hfrontnonempty
    suffices visited.length + frontier.length ≤ Fintype.card σ by omega
    simpa [visited'] using hvisit'.length_le_card
  where
    go (q : σ) : List σ := inc_symbols.map (m.step q)
set_option linter.unusedVariables true

def DFA.reachable [Fintype σ] [DecidableEq σ] (m : DFA α σ) (inc_symbols : List α) : List σ := 
  DFA.reachable.aux m inc_symbols [] [m.start] List.nodup_nil (List.nodup_singleton _) (by simp) (List.disjoint_nil_left _)

section ConversionResult

/--
Note that although there needs to be a linear order on both the state and alphabet types, they do not need to be meaningful in any way.
The only need for these orders is to be able to extract a List of all elements of these finite types.
An easy way to implement such an order is with an injective map into the naturals (or a list of naturals) and the `LinearOrder.lift'` function from Mathlib.
All of the examples do this implicitly by providing and encoding of the type into the Naturals.
--/
def DFA.asDotGraph [ToString α] [Fintype α] [symord : LinearOrder α]
    [ToString σ] [Fintype σ] [stateord : LinearOrder σ]
    (m : DFA α σ) [dec_acc : DecidablePred (· ∈ m.accept)] (header := "DFA") : String :=
  m.asDotGraph_explicit (header := header) toString toString (Finset.univ.sort stateord.le) (Finset.univ.sort symord.le)

/--
Unlike DFA.asDotGraph, this function does not require an order on the states,
because it instead performs a breadth-first search of the DFA's transition
graph to compute a list of states which are reachable from the start state, and
then only includes those states in the output.
--/
def DFA.asPrunedDotGraph [ToString α] [Fintype α] [symord : LinearOrder α]
    [ToString σ] [Fintype σ] [DecidableEq σ]
    (m : DFA α σ) [dec_acc : DecidablePred (· ∈ m.accept)] (header := "DFA") : String :=
  let symbols := Finset.univ.sort symord.le
  m.asDotGraph_explicit (header := header) toString toString (m.reachable symbols) symbols

instance [enc : Encodable σ] : LinearOrder σ := LinearOrder.lift' enc.encode enc.encode_injective

deriving instance Encodable for State

variable [Fintype σ]

def Finset.decidableExistsUnique [DecidableEq α] (fs : Finset α) (ls : List α) (heq : ∀ a, a ∈ ls ↔ a ∈ fs) (p : α → Prop) [DecidablePred p] :
    Decidable (∃! a ∈ fs, p a) := by
  have list_dec : Decidable (∃! a, a ∈ ls ∧ p a) := List.decidableBExistsUnique (l := ls) (p := p)
  cases list_dec with
  | isTrue h => 
    apply Decidable.isTrue
    obtain ⟨a, hmemandp, huniq⟩ := h
    refine ⟨a, ?_, ?_⟩
    · rwa [heq] at hmemandp
    · intro b hmemandp'
      apply huniq
      rwa [←heq] at hmemandp'
  | isFalse h => 
    apply Decidable.isFalse
    rintro ⟨a, hmemandp, huniq⟩
    apply h
    refine ⟨a, ?_, ?_⟩
    · rwa [←heq] at hmemandp
    · intro b hmemandp'
      apply huniq
      rwa [heq] at hmemandp'

def table_map_from_finset [Encodable σ] (fs : Finset (State σ × Option (State σ))) : Option (State σ → Option (State σ)) :=
  have _ := fun q ↦
    have ord : LinearOrder (State σ × Option (State σ)) := by infer_instance
    fs.decidableExistsUnique (fs.sort ord.le) (fun a ↦ fs.mem_sort ord.le) <| fun p ↦ p.fst = q
  if h : ∀ q, ∃! p, p ∈ fs ∧ p.fst = q
    then some fun q ↦ (fs.choose _ <| h q).snd
    else none

theorem table_map_from_finset_inverse [Encodable σ] (f : State σ → Option (State σ)) :
    table_map_from_finset (Finset.image (fun q ↦ (q, f q)) Finset.univ) = f := by
  simp only [table_map_from_finset, Finset.mem_image, Finset.mem_univ, true_and, Option.dite_none_right_eq_some, Option.some.injEq]
  have : ∀ (q : State σ), ∃! p, (∃ a, (a, f a) = p) ∧ p.1 = q := by
    intro q
    exists (q, f q)
    constructor
    · simp
    · intro y ⟨⟨a, heq⟩, hfst⟩
      suffices a = q by symm; rwa [this] at heq
      simpa [←heq] using hfst
  use this
  have chosen : ∀ (q : State σ), ∃! p, p ∈ (Finset.univ.image fun q ↦ (q, f q)) ∧ p.1 = q := by
    intro q
    obtain ⟨p, ⟨⟨a, hp⟩, hfst⟩, huniq⟩ := this q
    exists p
    constructor
    · have : a = q := by simpa [←hp] using hfst
      simpa [←hp]
    · rintro _ ⟨hmem, hfst⟩
      apply huniq
      constructor
      · simpa using hmem
      · exact hfst
  ext p q
  obtain ⟨hmem, hprop⟩ := Finset.choose_spec _ _ (chosen p)
  constructor
  · intro hchoose
    have : (Finset.choose (fun a ↦ a.1 = p) (Finset.univ.image fun q ↦ (q, f q)) (chosen p)) = (p, some q) := by
      ext : 1 <;> simp [hprop, hchoose]
    simpa [this] using hmem
  · intro
    obtain ⟨a, ha⟩ : ∃ a, (a, f a) = _ := by simpa using hmem
    have : a = p := by simpa [←ha] using hprop
    rw [this] at ha
    simpa [←ha]

instance [Encodable σ] : Encodable (TwoDFA.BackTable σ) where
  encode t := 
    let all_qs : Finset (State σ) := Finset.univ
    Encodable.encode <| (t.init, all_qs.image fun q ↦ (q, t.map q))
  decode n := 
    let ls : Option (Option (State σ) × Finset (State σ × Option (State σ))) := Encodable.decode n
    ls.bind <| fun ⟨init, rest⟩ ↦
      table_map_from_finset rest |>.map (⟨init, ·⟩)
  encodek t := by
    simp only [Encodable.encode_prod_val, Encodable.decode_prod_val, Nat.unpair_pair,
      Encodable.encodek, Option.map_some, Option.bind_some, Option.map_eq_some_iff]
    use t.map
    simp [table_map_from_finset_inverse]

instance [enc : Encodable (TwoDFA.BackTable σ)] : ToString (TwoDFA.BackTable σ) where
  toString t := s! "T{enc.encode t}"

instance [DecidableEq σ] (m : TwoDFA α σ) : DecidablePred (· ∈ m.to_one_way.accept) := by
  unfold TwoDFA.to_one_way TwoDFA.accepting_table
  infer_instance

end ConversionResult
