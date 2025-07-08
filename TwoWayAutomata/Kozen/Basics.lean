import Mathlib.Data.Fintype.Fin

inductive TapeSymbol (α : Type _) : Type _ where
  | left : TapeSymbol α
  | right : TapeSymbol α
  | symbol : α → TapeSymbol α

instance {α : Type _} : Coe α (TapeSymbol α) where
  coe := TapeSymbol.symbol

inductive Movement : Type where
  | left : Movement
  | right : Movement

structure TwoDFA (α σ : Type*) : Type _ where
  step : TapeSymbol α → σ → σ × Movement
  start : σ
  accept : σ
  reject : σ
  distinct_tr : accept ≠ reject
  in_bounds_left : ∀ q : σ, ∃ u : σ, step TapeSymbol.left q = (u, Movement.right)
  in_bounds_right : ∀ q : σ, ∃ u : σ, step TapeSymbol.right q = (u, Movement.left)
  halt_move_right : ∀ a : α, step a accept = (accept, Movement.right) ∧ step a reject = (reject, Movement.right)
  halt_preserve_state : ∀ a : TapeSymbol α, (∃ m : Movement, step a accept = (accept, m)) ∧ (∃ m : Movement, step a reject = (reject, m))

@[ext]
structure TwoDFA.Config (σ : Type _) (n : Nat) where
  state : σ
  idx : Fin (n + 2)

deriving instance DecidableEq for TwoDFA.Config

instance (n : Nat) (σ : Type _) [fin_states : Fintype σ] [DecidableEq σ] : Fintype (TwoDFA.Config σ n) where
  elems := (Fin.fintype (n+2)).elems.product fin_states.elems |>.image fun (i, q) ↦ ⟨q, i⟩
  complete := by rintro ⟨q, i⟩; simp [Fintype.elems, fin_states.complete]

structure Word (α : Type _) (n : Nat) : Type _ where
  val : Vector α n

section Word

variable {α : Type _}

def Word.empty : Word α 0 := ⟨#[].toVector⟩

def List.toWord (l : List α) : Word α (l.length) :=
  ⟨ l.toArray.toVector ⟩

instance (x : List α) : CoeDep (List α) x (Word α (x.length)) where
  coe := x.toWord

def Word.get {n : Nat} (w : Word α n) (i : Fin (n+2)) : TapeSymbol α :=
  if h : i = 0
    then .left
    else
      let k := i.pred h
      if h : k = Fin.last n
        then .right
        else
          let ltN := Fin.val_lt_last h
          w.val.get <| k.castLT ltN

abbrev Word.split_type (α : Type _) {n : Nat} (i : Fin (n+2)) (h : i ≠ 0) : Type _ := 
  (Vector α (min (i.pred h) n) × Vector α (n - (i.pred h)))

--- Split the word before symbol i. Note that we can't split with i=0, since that would be trying to split before the left endmarker
def Word.split {n : Nat} (w : Word α n) (i : Fin (n+2)) (h : i ≠ 0) : split_type α i h :=
  let last := i.pred h
  (Vector.cast (by simp [h, last]) <| w.val.take last, Vector.cast (by simp [h, last]) <| w.val.drop last)

end Word
