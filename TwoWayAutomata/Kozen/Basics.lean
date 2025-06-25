universe u v

inductive TapeSymbol (α : Type u) : Type u where
  | left : TapeSymbol α
  | right : TapeSymbol α
  | symbol : α → TapeSymbol α

instance {α : Type u} : Coe α (TapeSymbol α) where
  coe := TapeSymbol.symbol

inductive Movement : Type where
  | left : Movement
  | right : Movement

def Movement.opp : Movement → Movement
  | .left => .right
  | .right => .left

structure TwoDFA (α : Type u) (σ : Type v) : Type (max u v) where
  step : TapeSymbol α → σ → σ × Movement
  start : σ
  accept : σ
  reject : σ
  distinct_tr : accept ≠ reject
  in_bounds_left : ∀ q : σ, ∃ u : σ, step TapeSymbol.left q = (u, Movement.right)
  in_bounds_right : ∀ q : σ, ∃ u : σ, step TapeSymbol.right q = (u, Movement.left)
  halt_move_right : ∀ a : α, step a accept = (accept, Movement.right) ∧ step a reject = (reject, Movement.right)
  halt_preserve_state : ∀ a : TapeSymbol α, (∃ m : Movement, step a accept = (accept, m)) ∧ (∃ m : Movement, step a reject = (reject, m))

structure Word (α : Type u) (n : Nat) : Type u where
  val : Vector α n

def Word.empty {α : Type u} : Word α 0 := ⟨#[].toVector⟩

def List.toWord {α : Type u} (l : List α) : Word α (l.length) :=
  ⟨ l.toArray.toVector ⟩

def Word.get {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) : TapeSymbol α :=
  if h : i = 0
    then .left
    else
      let k := i.pred h
      if h : k = Fin.last n
        then .right
        else
          let ltN := Fin.val_lt_last h
          w.val.get <| k.castLT ltN

def Word.split_type (α : Type u) {n : Nat} (i : Fin (n+2)) (h : i ≠ 0) : Type u := 
  (Vector α (min (i.pred h) n) × Vector α (n - (i.pred h)))

--- Split the word before symbol i. Note that we can't split with i=0, since that would be trying to split before the left endmarker
def Word.split {α : Type u} {n : Nat} (w : Word α n) (i : Fin (n+2)) (h : i ≠ 0) : split_type α i h :=
  let last := i.pred h
  (Vector.cast (by simp [h, last]) <| w.val.take last, Vector.cast (by simp [h, last]) <| w.val.drop last)
