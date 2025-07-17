import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Language

namespace TwoDFA

variable {α σ : Type*} {n : Nat}

--- m.nextConfig x but only acting on configurations that aren't in halting states.
--- This avoids the 'halting' cycles, while leaving any other cycles that may exist.
@[reducible]
def next_except_halt (m : TwoDFA α σ) (x : Word α n)  (c1 c2 : Config σ n) : Prop :=
  c2.state ≠ m.accept ∧ c2.state ≠ m.reject ∧ m.nextConfig x c1 c2

variable {m : TwoDFA α σ} {x : Word α n} 

lemma ne_accept_of_next_ne_accept (c1 c2 : Config σ n) (hne : c2.state ≠ m.accept) (hnext : m.nextConfig x c1 c2) : c1.state ≠ m.accept := by
  by_contra heq
  absurd hne
  apply m.accept_preserve_state x (c1.idx) _
  rw [←heq]
  exact GoesTo.single hnext

lemma ne_reject_of_next_ne_reject (c1 c2 : Config σ n) (hne : c2.state ≠ m.reject) (hnext : m.nextConfig x c1 c2) : c1.state ≠ m.reject := by
  by_contra heq
  absurd hne
  apply m.reject_preserve_state x (c1.idx) _
  rw [←heq]
  exact GoesTo.single hnext

theorem TransGen_next_except_halt_of_GoesTo_except_halt_of_ne (c1 c2 : Config σ n)
  (hna : c2.state ≠ m.accept) (hnr : c2.state ≠ m.reject) (hgoes : m.GoesTo x c1 c2) (hne : c1 ≠ c2) :
    Relation.TransGen (m.next_except_halt x) c1 c2 := by
  induction hgoes with
  | refl => contradiction
  | @tail mid _ _ tl ih =>
    have hna' : mid.state ≠ m.accept := ne_accept_of_next_ne_accept _ _ hna tl
    have hnr' : mid.state ≠ m.reject := ne_reject_of_next_ne_reject _ _ hnr tl
    cases em (c1 = mid) with
    | inl heq' =>
      apply Relation.TransGen.single
      rw [heq']
      exact ⟨hna, hnr, tl⟩
    | inr hne' =>
      apply Relation.TransGen.tail
      · exact ih hna' hnr' hne'
      · exact ⟨hna, hnr, tl⟩

theorem halts_of_next_except_halt_WF (hwf : WellFounded (m.next_except_halt x)) : ¬ m.diverges x := by
  by_contra hdiv
  obtain ⟨cfg, hreach, ⟨prev, path, link⟩, hnacc, hnrej⟩ := hdiv
  absurd (WellFounded.transGen hwf).isIrrefl.irrefl cfg
  apply Relation.TransGen.tail
  swap
  · exact ⟨hnacc, hnrej, link⟩
  · apply TransGen_next_except_halt_of_GoesTo_except_halt_of_ne (hgoes := path)
    · exact ne_accept_of_next_ne_accept _ _ hnacc link
    · exact ne_reject_of_next_ne_reject _ _ hnrej link
    · by_contra heq
      rw [←heq] at link
      have := nextConfig.irrefl m x cfg
      contradiction

structure WellFoundedEncoding (σ : Type _) : Type _ where
  E : Nat → Type _
  encode : {n : Nat} → Config σ n → E n
  wfrel : {n : Nat} → WellFoundedRelation (E n)

namespace WellFoundedEncoding

abbrev rel {n : Nat} (wfe : WellFoundedEncoding σ) := wfe.wfrel (n := n) |>.rel

def CfgRel (wfe : WellFoundedEncoding σ) : WellFoundedRelation (Config σ n) :=
  invImage wfe.encode wfe.wfrel

abbrev cfgRel {n : Nat} (wfe : WellFoundedEncoding σ) := wfe.CfgRel (n := n) |>.rel

abbrev cfgWf {n : Nat} (wfe : WellFoundedEncoding σ) := wfe.CfgRel (n := n) |>.isWellFounded

theorem CfgRel_def (wfe : WellFoundedEncoding σ) {n : Nat} {c1 c2 : Config σ n} :
    wfe.cfgRel c1 c2 ↔ wfe.rel (wfe.encode c1) (wfe.encode c2) := by
  simp only [cfgRel, CfgRel, invImage, InvImage]

end WellFoundedEncoding

theorem next_except_halt_WF_of_encoding (m : TwoDFA α σ) (wfe : WellFoundedEncoding σ) {n : Nat} {w : Word α n}
  (h : ∀ {c1 c2}, m.next_except_halt w c1 c2 → wfe.rel (wfe.encode c1) (wfe.encode c2)) :
    WellFounded (m.next_except_halt w) := by
  have wfe_cfgwf := wfe.cfgWf (n := n) |>.wf
  constructor
  intro c2
  apply wfe_cfgwf.apply c2 |>.ndrec
  intro _ _ ih
  constructor
  intro _ hprev
  apply ih
  exact h hprev

end TwoDFA
