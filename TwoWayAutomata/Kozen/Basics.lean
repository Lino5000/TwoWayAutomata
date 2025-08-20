import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.DeriveFintype

inductive TapeSymbol (α : Type _) : Type _ where
  | left : TapeSymbol α
  | right : TapeSymbol α
  | symbol : α → TapeSymbol α

instance {α : Type _} : Coe α (TapeSymbol α) where
  coe := TapeSymbol.symbol

inductive Movement : Type where
  | left : Movement
  | right : Movement
  deriving Fintype

inductive State (σ : Type _) : Type _ where
  | accept : State σ
  | reject : State σ
  | other : σ → State σ
  deriving DecidableEq, Fintype

instance {σ : Type _} : Coe σ (State σ) where
  coe := State.other

structure TwoDFA (α σ : Type*) : Type _ where
  stepOther : TapeSymbol α → σ → (State σ) × Movement
  start : σ
  stay_in_bounds : ∀ p, (∃ q, stepOther .left p = (q, .right)) ∧ (∃ q, stepOther .right p = (q, .left))

abbrev TwoDFA.step {α σ : Type*} (m : TwoDFA α σ) : TapeSymbol α → State σ → (State σ) × Movement
  | .right, .accept => (.accept, .left)
  | _, .accept => (.accept, .right)
  | .right, .reject => (.reject, .left)
  | _, .reject => (.reject, .right)
  | a, .other q => m.stepOther a q

theorem TwoDFA.in_bounds_left {α σ : Type*} (m : TwoDFA α σ) (p : State σ) :
    ∃ q, m.step .left p = (q, .right) := by
  cases p with
  | accept | reject => simp [step]
  | other p => 
    simp only [step]
    exact m.stay_in_bounds p |>.left

theorem TwoDFA.in_bounds_right {α σ : Type*} (m : TwoDFA α σ) (p : State σ) :
    ∃ q, m.step .right p = (q, .left) := by
  cases p with
  | accept | reject => simp [step]
  | other p => 
    simp only [step]
    exact m.stay_in_bounds p |>.right

theorem TwoDFA.halt_preserve_state {α σ : Type*} (m : TwoDFA α σ) (a : TapeSymbol α) :
    (∃ mv, m.step a .accept = (.accept, mv)) ∧ (∃ mv, m.step a .reject = (.reject, mv)) := by
  cases a <;> simp

theorem TwoDFA.halt_move_right {α σ : Type*} (m : TwoDFA α σ) (a : TapeSymbol α) (h : a ≠ .right) :
    m.step a .accept = (.accept, .right) ∧ m.step a .reject = (.reject, .right) := by
  cases a with
  | right => contradiction
  | left | symbol => simp

@[ext]
structure TwoDFA.Config (σ : Type _) (n : Nat) where
  state : State σ
  idx : Fin (n + 2)
  deriving DecidableEq, Fintype

structure Word (α : Type _) (n : Nat) : Type _ where
  val : Vector α n

@[reducible]
def List.toWord {α : Type _} (l : List α) : Word α (l.length) :=
  ⟨ l.toArray.toVector ⟩

namespace Word

variable {α : Type _}

def empty : Word α 0 := ⟨#[].toVector⟩

instance (x : List α) : CoeDep (List α) x (Word α (x.length)) where
  coe := x.toWord

def get {n : Nat} (w : Word α n) (i : Fin (n+2)) : TapeSymbol α :=
  if h : i = 0
    then .left
    else
      let k := i.pred h
      if h : k = Fin.last n
        then .right
        else
          let ltN := Fin.val_lt_last h
          w.val.get <| k.castLT ltN

abbrev split_type (α : Type _) {n : Nat} (i : Fin (n+2)) (h : i ≠ 0) : Type _ := 
  (Vector α (min (i.pred h) n) × Vector α (n - (i.pred h)))

--- Split the word before symbol i. Note that we can't split with i=0, since that would be trying to split before the left endmarker
def split {n : Nat} (w : Word α n) (i : Fin (n+2)) (h : i ≠ 0) : split_type α i h :=
  let last := i.pred h
  (Vector.cast (by simp [h, last]) <| w.val.take last, Vector.cast (by simp [h, last]) <| w.val.drop last)

end Word
