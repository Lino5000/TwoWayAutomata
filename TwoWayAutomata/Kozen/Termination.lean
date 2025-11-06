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

lemma eq_other_of_next_eq_other (c1 c2 : Config σ n) {p : σ}
  (heq : c2.state = .other p) (hnext : m.nextConfig x c1 c2) :
    ∃ q, c1.state = .other q := by
  cases hq1 : c1.state
  case other q => simp only [State.other.injEq, exists_eq']
  case' accept =>
    have hpreserve := m.accept_preserve_state x c1.idx c2
  case' reject =>
    have hpreserve := m.reject_preserve_state x c1.idx c2
  all_goals
    have := by
      apply hpreserve
      rw [←hq1]
      exact GoesTo.single hnext
    simp [this] at heq

theorem TransGen_next_except_halt_of_GoesTo_except_halt_of_ne (c1 c2 : Config σ n)
  {q : σ} (hoth : c2.state = .other q) (hgoes : m.GoesTo x c1 c2) (hne : c1 ≠ c2) :
    Relation.TransGen (m.next_except_halt x) c1 c2 := by
  induction hgoes generalizing q with
  | refl => contradiction
  | @tail mid _ _ tl ih =>
    by_cases heq' : c1 = mid
    · apply Relation.TransGen.single
      rw [heq']
      refine ⟨?_, ?_, tl⟩
      <;> simp [hoth]
    · apply Relation.TransGen.tail
      · obtain ⟨_, hoth'⟩ := eq_other_of_next_eq_other _ _ hoth tl
        exact ih hoth' heq'
      · refine ⟨?_, ?_, tl⟩
        <;> simp [hoth]

/---
If the nextConfig relation only has halting cycles, then the 2DFA must not diverge on this input.
--/
theorem halts_of_next_except_halt_WF (hwf : WellFounded (m.next_except_halt x)) : ¬ m.diverges x := by
  by_contra hdiv
  obtain ⟨q, i, hreach, prev, path, link⟩ := hdiv
  absurd (WellFounded.transGen hwf).isIrrefl.irrefl ⟨q, i⟩
  apply Relation.TransGen.tail
  · obtain ⟨p, hoth⟩ := eq_other_of_next_eq_other _ _ rfl link
    apply TransGen_next_except_halt_of_GoesTo_except_halt_of_ne (hgoes := path)
    · exact hoth
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
  (h : ∀ {q1 i1 q2 i2}, m.nextConfig w ⟨.other q1, i1⟩ ⟨.other q2, i2⟩ → wfe.rel (wfe.encode (q1, i1)) (wfe.encode (q2, i2))) :
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
      exact h hprev.right.right

end TwoDFA
