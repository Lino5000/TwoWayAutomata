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

namespace TwoDFA

structure ConfigMeaning (n : Nat) (α σ : Type*) : Type _ where
  --- Meaning of being in the given state at the left end marker
  atLeft : σ → Vector α n → Prop
  --- Meaning of being in the given state at the given position in the input after the left endmarker
  inWord : σ → SplitPredicate n α 

namespace ConfigMeaning

def apply (cm : ConfigMeaning n α σ) (w : Word α n) (cfg : Config σ n) : Prop :=
  if hcfg : cfg.idx = 0
    then
      cm.atLeft cfg.state w.val
    else
      cm.inWord cfg.state |>.apply w cfg.idx hcfg

structure Inductive (m : TwoDFA α σ) (cm : ConfigMeaning n α σ) : Prop where
  base : ∀ w, cm.apply w m.init
  ind : ∀ w, ∀ cfg : Config σ n, cm.apply w cfg → cm.apply w (m.stepConfig w cfg)

theorem Inductive.apply_of_reachable {motive : ConfigMeaning n α σ} {m : TwoDFA α σ} (ind : motive.Inductive m)
  {w : Word α n} {cfg : Config σ n} (hgoes : m.reaches w cfg) :
    motive.apply w cfg := by
  induction hgoes with
  | refl => exact ind.base w
  | @tail mid stp head tail head_ih =>
    have hind := ind.ind w mid head_ih
    have : m.stepConfig w mid = stp := by rwa [m.stepConfig_gives_nextConfig w mid stp]
    rwa [this] at hind

end ConfigMeaning

theorem language_eq_of_inductive [Fintype σ] (m : TwoDFA α σ) (L : Language α) (cm : ∀ {n}, ConfigMeaning n α σ)
  (hind : ∀ {n}, cm.Inductive (n := n) m) 
  (hacc : ∀ {w : List α}, cm.apply w.toWord ⟨m.accept, Fin.last _⟩ → w ∈ L)
  (hrej : ∀ {w : List α}, cm.apply w.toWord ⟨m.reject, Fin.last _⟩ → w ∉ L)
  (hdiv : ∀ {w : List α}, m.diverges w.toWord → w ∉ L) :
    m.language = L := by
  unfold TwoDFA.language
  ext w
  rw [Set.mem_setOf]
  constructor
  · intro
    apply hacc
    apply hind.apply_of_reachable
    apply reaches_accept_last_of_accepts
    assumption
  · intro
    cases em (m.diverges w.toWord) with
    | inl h =>
      have : w ∉ L := hdiv h
      contradiction
    | inr h =>
      rw [m.divergence_iff, ←or_iff_not_and_not] at h
      cases h with
      | inl _ => assumption -- _ : m.accepts w
      | inr _ => -- _ : m.rejects w
        suffices w ∉ L by contradiction
        apply hrej
        apply hind.apply_of_reachable
        apply reaches_reject_last_of_rejects
        assumption

end TwoDFA
