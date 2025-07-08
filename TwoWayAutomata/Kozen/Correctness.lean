import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Configurations
import TwoWayAutomata.Kozen.Execute
import TwoWayAutomata.Kozen.Language
import TwoWayAutomata.Kozen.Movement
import TwoWayAutomata.Kozen.Word

variable {n : Nat} {α σ : Type*}

def SplitPredicate (n : Nat) (α : Type _) : Type _ :=
  (i : Fin (n+2)) → {h : i ≠ 0} → (Vector α (min (↑(i.pred h)) n) × Vector α (n - ↑(i.pred h))) → Prop

@[inline]
def SplitPredicate.apply (sp : SplitPredicate n α) (w : Word α n) (i : Fin (n+2)) (h : i ≠ 0) : Prop :=
  sp i (h := h) <| w.split i h

structure TwoDFA.ConfigMeaning (n : Nat) (α σ : Type*) : Type _ where
  --- Meaning of being in the given state at the left end marker
  atLeft : σ → Vector α n → Prop
  --- Meaning of being in the given state at the given position in the input after the left endmarker
  inWord : σ → SplitPredicate n α 

def TwoDFA.ConfigMeaning.apply (cm : ConfigMeaning n α σ) (w : Word α n) (cfg : Config σ n) : Prop :=
  if hcfg : cfg.idx = 0
    then
      cm.atLeft cfg.state w.val
    else
      cm.inWord cfg.state |>.apply w cfg.idx hcfg

theorem TwoDFA.ConfigMeaning.apply_of_reachable (motive : ConfigMeaning n α σ) (m : TwoDFA α σ) (w : Word α n)
  (base : motive.apply w ⟨m.start, 0⟩) (ind : ∀ cfg : Config σ n, motive.apply w cfg → motive.apply w (m.stepConfig w cfg))
  (cfg : Config σ n) (hgoes : m.reaches w cfg) :
    motive.apply w cfg := by
  induction hgoes with
  | refl => exact base
  | @tail mid stp head tail head_ih =>
    have hind := ind mid head_ih
    have : m.stepConfig w mid = stp := by rwa [m.stepConfig_gives_nextConfig w mid stp]
    rwa [this] at hind
