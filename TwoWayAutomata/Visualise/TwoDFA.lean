import Mathlib.Data.Finset.Sort
import TwoWayAutomata.Kozen.Basics

variable {α σ : Type*}

instance : ToString Movement where
  toString
  | .left => "L"
  | .right => "R"

def TwoDFA.asDotGraph_explicit
  (m : TwoDFA α σ)
  (header := "2DFA")
  (sym_disp : TapeSymbol α → String)
  (state_disp : State σ → String)
  (inc_states : List σ)
  (inc_syms : List α) :
  String := Id.run do
    let mut lines := #[s!"digraph \"{header}\" " ++ "{"]
    -- First add the nodes for states
    lines := lines.push s!"  \"{state_disp .accept}\" [style=\"filled\", fillcolor=\"#BBEEBB\", fontcolor=\"#00AA00\", color=\"#00AA00\", penwidth=2.0];"
    lines := lines.push s!"  \"{state_disp .reject}\" [style=\"filled\", fillcolor=\"#EEBBBB\", fontcolor=\"#AA0000\", color=\"#AA0000\", penwidth=2.0];"
    for q in inc_states do
      lines := lines.push s!"  \"{state_disp q}\" [];"

    -- Highlight start node
    lines := lines.push s!"  \"{state_disp m.start}\" [style=\"filled\", fillcolor=\"#EEEEBB\", color=\"#CCCC00\", penwidth=2.0];"

    -- Then add edges for transitions
    let all_syms : List (TapeSymbol α) := TapeSymbol.left :: TapeSymbol.right :: inc_syms
    for p in inc_states do
      for a in all_syms do
        let ⟨q, mv⟩ := m.stepOther a p
        -- We use intermediary nodes to encourage the edge labels into not overlapping other things.
        -- This might lead to transition edges moving well out of their way for no apparent reason
        lines := lines.push s!"  \"{state_disp p}-{sym_disp a}-{state_disp q}\" [label=\"{sym_disp a}; {mv}\", shape=\"box\", style=\"filled\", color=\"#FFFFFF\"];"
        lines := lines.push s!"  \"{state_disp p}\" -> \"{state_disp p}-{sym_disp a}-{state_disp q}\" [arrowhead=\"none\"];"
        lines := lines.push s!"  \"{state_disp p}-{sym_disp a}-{state_disp q}\" -> \"{state_disp q}\" [];"
    
    lines := lines.push "}"
    return "\n".intercalate lines.toList

def default_sym_disp [ToString α] : TapeSymbol α → String
  | .left => "⊢"
  | .right => "⊣"
  | .symbol a => toString a

def default_state_disp [ToString σ] : State σ → String
  | .accept => "✓"
  | .reject => "✗"
  | .other q => toString q

/--
Note that although there needs to be a linear order on both the state and alphabet types, they do not need to be meaningful in any way.
The only need for these orders is to be able to extract a List of all elements of these finite types.
An easy way to implement such an order is with an injective map into the naturals (or a list of naturals) and the `LinearOrder.lift'` function from Mathlib.
--/
def TwoDFA.asDotGraph [ToString α] [Fintype α] [symord : LinearOrder α] [ToString σ] [Fintype σ] [stateord : LinearOrder σ]
    (m : TwoDFA α σ) (header := "2DFA") : String :=
  m.asDotGraph_explicit (header := header) default_sym_disp default_state_disp (Finset.univ.sort stateord.le) (Finset.univ.sort symord.le)
