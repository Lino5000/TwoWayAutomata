import TwoWayAutomata.Kozen.Basics
import TwoWayAutomata.Kozen.Language

namespace TwoDFA

variable {α σ : Type*} {n : Nat}

--- m.nextConfig x but only acting on configurations that aren't in halting states.
--- This avoids the 'halting' cycles, while leaving any other cycles that may exist.
@[reducible]
def next_except_halt (m : TwoDFA α σ) (x : Word α n) (c1 c2 : Config σ n) : Prop :=
  c2.state ≠ .accept ∧ c2.state ≠ .reject ∧ m.nextConfig x c1 c2

variable {m : TwoDFA α σ} {x : Word α n} 

lemma ne_accept_of_next_ne_accept (c1 c2 : Config σ n) (hne : c2.state ≠ .accept) (hnext : m.nextConfig x c1 c2) : c1.state ≠ .accept := by
  by_contra heq
  absurd hne
  apply m.accept_preserve_state x (c1.idx) _
  rw [←heq]
  exact GoesTo.single hnext

lemma ne_reject_of_next_ne_reject (c1 c2 : Config σ n) (hne : c2.state ≠ .reject) (hnext : m.nextConfig x c1 c2) : c1.state ≠ .reject := by
  by_contra heq
  absurd hne
  apply m.reject_preserve_state x (c1.idx) _
  rw [←heq]
  exact GoesTo.single hnext

theorem TransGen_next_except_halt_of_GoesTo_except_halt_of_ne (c1 c2 : Config σ n)
  (hna : c2.state ≠ .accept) (hnr : c2.state ≠ .reject) (hgoes : m.GoesTo x c1 c2) (hne : c1 ≠ c2) :
    Relation.TransGen (m.next_except_halt x) c1 c2 := by
  induction hgoes with
  | refl => contradiction
  | @tail mid _ _ tl ih =>
    have hna' : mid.state ≠ .accept := ne_accept_of_next_ne_accept _ _ hna tl
    have hnr' : mid.state ≠ .reject := ne_reject_of_next_ne_reject _ _ hnr tl
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
  obtain ⟨q, i, hreach, prev, path, link⟩ := hdiv
  absurd (WellFounded.transGen hwf).isIrrefl.irrefl ⟨q, i⟩
  apply Relation.TransGen.tail
  · apply TransGen_next_except_halt_of_GoesTo_except_halt_of_ne (hgoes := path)
    · exact ne_accept_of_next_ne_accept _ _ (by simp) link
    · exact ne_reject_of_next_ne_reject _ _ (by simp) link
    · by_contra heq
      rw [←heq] at link
      have := nextConfig.irrefl m x ⟨q, i⟩
      contradiction
  · simpa [next_except_halt]

structure WellFoundedEncoding (σ : Type _) : Type _ where
  E : Nat → Type _
  encode : {n : Nat} → (σ × Fin (n+2)) → E n
  wfrel : {n : Nat} → WellFoundedRelation (E n)

namespace WellFoundedEncoding

abbrev rel {n : Nat} (wfe : WellFoundedEncoding σ) := wfe.wfrel (n := n) |>.rel

def CfgRel (wfe : WellFoundedEncoding σ) : WellFoundedRelation (σ × Fin (n+2)) :=
  invImage wfe.encode wfe.wfrel

abbrev cfgRel {n : Nat} (wfe : WellFoundedEncoding σ) := wfe.CfgRel (n := n) |>.rel

abbrev cfgWf {n : Nat} (wfe : WellFoundedEncoding σ) := wfe.CfgRel (n := n) |>.isWellFounded

theorem CfgRel_def (wfe : WellFoundedEncoding σ) {n : Nat} {q1 q2 : σ} {i1 i2 : Fin (n+2)} :
    wfe.cfgRel (q1, i1) (q2, i2) ↔ wfe.rel (wfe.encode (q1, i1)) (wfe.encode (q2, i2)) := by
  simp only [cfgRel, CfgRel, invImage, InvImage]

end WellFoundedEncoding

theorem next_except_halt_WF_of_encoding (m : TwoDFA α σ) (wfe : WellFoundedEncoding σ) {n : Nat} {w : Word α n}
  (h : ∀ {q1 i1 q2 i2}, m.next_except_halt w ⟨.other q1, i1⟩ ⟨.other q2, i2⟩ → wfe.rel (wfe.encode (q1, i1)) (wfe.encode (q2, i2))) :
    WellFounded (m.next_except_halt w) := by
  have wfe_cfgwf := wfe.cfgWf (n := n) |>.wf
  constructor
  unfold next_except_halt
  rintro ⟨accept | reject | q, i⟩
  case accept | reject => 
    constructor; simp -- vacuously true
  case other =>
    apply wfe_cfgwf.apply (q, i) |>.ndrec (C := fun x ↦ Acc _ (⟨x.fst, x.snd⟩ : Config σ n))
    intro a _ ih
    simp only at ih
    constructor
    intro b hprev
    match b with
    | ⟨.accept, bi⟩ | ⟨.reject, bi⟩ =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and] at hprev
      have := hprev.halt_preserve_state <| by simp
      simp at this -- contradiction
    | ⟨.other qb, bi⟩ =>
      apply ih (qb, bi)
      suffices wfe.cfgRel (qb, bi) a from this
      rw [wfe.CfgRel_def]
      exact h hprev

end TwoDFA
