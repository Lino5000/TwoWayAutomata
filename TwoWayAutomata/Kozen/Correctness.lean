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

-- TODO: remove SplitPredicate and just pass in the state, position, and the whole word
--       this removes the need to have both `atLeft` and `inWord`, and will
--       simplify proofs of `Inductive` when the condition does not utilise the
--       split word, which seems more common in the examples.
structure ConfigMeaning (n : Nat) (α σ : Type*) : Type _ where
  --- Meaning of being in the given state at the left end marker
  atLeft : σ → Vector α n → Prop
  --- Meaning of being in the given state at the given position in the input after the left endmarker
  inWord : σ → SplitPredicate n α 
  --- Meaning of being in the accept state
  accept : Vector α n → Prop
  --- Meaning of being in the reject state
  reject : Vector α n → Prop

namespace ConfigMeaning

@[reducible]
def apply (cm : ConfigMeaning n α σ) (w : Word α n) (cfg : Config σ n) : Prop :=
  match cfg with
  | ⟨.accept, _⟩ => cm.accept w.val
  | ⟨.reject, _⟩ => cm.reject w.val
  | ⟨.other q, i⟩ =>
    if hcfg : i = 0
      then
        cm.atLeft q w.val
      else
        cm.inWord q |>.apply w i hcfg

structure Inductive (m : TwoDFA α σ) (cm : ConfigMeaning n α σ) : Prop where
  base : ∀ w, cm.apply w m.init
  ind : ∀ w, ∀ (q : σ) (i : Fin _), cm.apply w ⟨q, i⟩ → cm.apply w (m.stepConfig w ⟨q, i⟩)

theorem Inductive.apply_of_reachable {motive : ConfigMeaning n α σ} {m : TwoDFA α σ} (ind : motive.Inductive m)
  {w : Word α n} {cfg : Config σ n} (hgoes : m.reaches w cfg) :
    motive.apply w cfg := by
  induction hgoes with
  | refl => exact ind.base w
  | @tail mid stp head tail head_ih =>
    match mid with
    | ⟨.accept, _⟩ =>
      have : stp = ⟨.accept, stp.idx⟩ := by ext <;> simp [tail.halt_preserve_state]
      rw [this]; simpa -- uses head_ih
    | ⟨.reject, _⟩ =>
      have : stp = ⟨.reject, stp.idx⟩ := by ext <;> simp [tail.halt_preserve_state]
      rw [this]; simpa -- uses head_ih
    | ⟨.other q, i⟩ =>
      have hind := ind.ind w q i head_ih
      have : m.stepConfig w ⟨q, i⟩ = stp := by rwa [m.stepConfig_gives_nextConfig w ⟨q, i⟩ stp]
      rwa [this] at hind

end ConfigMeaning

theorem language_eq_of_inductive [Fintype σ] (m : TwoDFA α σ) (L : Language α) (cm : ∀ {n}, ConfigMeaning n α σ)
  (hind : ∀ {n}, cm.Inductive (n := n) m) 
  (hacc : ∀ {w : List α}, cm.apply w.toWord ⟨.accept, Fin.last _⟩ → w ∈ L)
  (hrej : ∀ {w : List α}, cm.apply w.toWord ⟨.reject, Fin.last _⟩ → w ∉ L)
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
    by_cases h : m.diverges w.toWord
    · have : w ∉ L := hdiv h
      contradiction
    · rw [m.divergence_iff, ←or_iff_not_and_not] at h
      cases h
      -- m.accepts w
      · assumption
      -- m.rejects w
      · suffices w ∉ L by contradiction
        apply hrej
        apply hind.apply_of_reachable
        apply reaches_reject_last_of_rejects
        assumption

end TwoDFA
