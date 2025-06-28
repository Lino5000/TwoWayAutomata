import Mathlib.Algebra.Group.Fin.Basic

import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Movement

namespace TwoDFA

@[simp]
def Config.castLE {σ : Type _} {n m : Nat} (h : n ≤ m) (c : Config σ n) : Config σ m where
  state := c.state
  idx := c.idx.castLE <| by simpa

abbrev init {n : Nat} {α σ : Type*} (m : TwoDFA α σ) : Config σ n := ⟨m.start, 0⟩

variable {n : Nat} {α σ : Type*} (m : TwoDFA α σ) (x : Word α n) 

inductive nextConfig (c1 c2 : Config σ n) : Prop where
  | stepLeft : m.step (x.get c1.idx) c1.state = (c2.state, .left) →
               (hvalid : Movement.left.isValid c1.idx) →
               (happly : Movement.left.apply c1.idx hvalid = c2.idx) →
             nextConfig c1 c2
  | stepRight : m.step (x.get c1.idx) c1.state = (c2.state, .right) →
                (hvalid : Movement.right.isValid c1.idx) →
                (happly : Movement.right.apply c1.idx hvalid = c2.idx) →
              nextConfig c1 c2

theorem nextConfig.push_lt {c1 c2 : Config σ n} (a : α) (hnext : m.nextConfig x c1 c2) (hlt : c1.idx < Fin.last (n+1)) :
    m.nextConfig (x.push a) (c1.castLE <| by simp) (c2.castLE <| by simp) := by
  have get_same : x.get c1.idx = (x.push a).get (c1.castLE <| by simp).idx := by
    have := x.get_push_lt a c1.idx hlt
    rw [this]
    simp only [Config.castLE]
  cases hnext with
  | stepLeft hstep hvalid happly =>
    left
    · rw [← get_same]
      simp only [Config.castLE]
      exact hstep
    · simp [Movement.apply, Fin.predCast, Fin.ext_iff] at *
      exact happly
    · apply Movement.isValid_castLE (valid := hvalid)
      simp
  | stepRight hstep hvalid happly =>
    right
    · rw [← get_same]
      simp only [Config.castLE]
      exact hstep
    · simp [Movement.apply, Fin.predCast, Fin.ext_iff] at *
      exact happly
    · apply Movement.isValid_castLE (valid := hvalid)
      simp

theorem nextConfig.push_eq (c1 : Config σ n) (c2 : Config σ (n+1)) {move : Movement} (a : α) (heq : c1.idx = Fin.last (n+1)) 
    (hstep : m.step a c1.state = ⟨c2.state, move⟩)
    (hmove : move.apply
               (c1.idx.castLE <| by simp)
               (move.isValid_castLE_of_lt_of_ne_0 c1.idx (by simp) (by simp [heq]))
             = c2.idx) :
    m.nextConfig (x.push a) (c1.castLE <| by simp) c2 := by
  have get_pushed : (x.push a).get (c1.castLE <| by simp).idx = a := x.get_push_eq a c1.idx heq
  have hvalid := move.isValid_castLE_of_lt_of_ne_0 c1.idx (by simp : n + 2 < n+3) (by simp [heq])
  cases move
  · left
    · rw [get_pushed]
      simpa only [Config.castLE]
    · suffices Movement.left.apply (c1.castLE <| by simp).idx hvalid = c2.idx from this
      exact hmove
  · right
    · rw [get_pushed]
      simpa only [Config.castLE]
    · suffices Movement.right.apply (c1.castLE <| by simp).idx hvalid = c2.idx from this
      exact hmove

end TwoDFA
