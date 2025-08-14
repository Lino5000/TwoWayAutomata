import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Computability.DFA

import TwoWayAutomata.Kozen.Language
import TwoWayAutomata.Kozen.Correctness

theorem Option.ne_some {α : Type _} (o : Option α) {a : α} (h : o ≠ some a) : o = none ∨ ∃ b : α, b ≠ a ∧ o = some b := by
  cases o with
  | none => simp
  | some b => right; use b; simpa using h

lemma List.length_takeWhile_le {α : Sort _} {l : List α} {p : α → Bool} : (l.takeWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih => 
    unfold List.takeWhile
    cases _ : p hd with
    | true => simpa
    | false => simp

lemma List.length_takeWhile {α : Sort _} {l : List α} {p : α → Bool} {n : Nat} (hat : ∀ hn : n < l.length, p l[n] = false)
  (hprev : ∀ k (hk : k < min n l.length), p (l[k]'((Nat.lt_min.mp hk).right)) = true) :
    (l.takeWhile p).length = min n l.length := by
  if hn : n < l.length
    then
      induction l generalizing n with
      | nil => simp at hn -- hn : n < 0
      | cons hd tl ih => 
        cases n with
        | zero => 
          have hd_false : p hd = false := by simpa using hat
          simp [takeWhile, hd_false]
        | succ n => 
          have hd_true : p hd = true := hprev 0 <| by simp
          simp [takeWhile, hd_true]
          apply ih 
          · simpa using hat
          · intro k hk
            have := hprev (k+1) <| by omega
            simpa
          · simpa using hn
    else
      have min_eq : min n l.length = l.length := by simpa using hn
      rw [min_eq]
      suffices l.takeWhile p = l by rw [this]
      rw [List.takeWhile_eq_self_iff]
      intro e he
      obtain ⟨_, _, heq⟩ := List.mem_iff_getElem.mp he
      rw [←heq]
      apply hprev
      rwa [min_eq]

lemma List.getElem_takeWhile {α : Sort _} {l : List α} {i : Nat} {p : α → Bool} {hi : i < (l.takeWhile p).length} :
    (l.takeWhile p)[i] = l[i]'(Nat.lt_of_lt_of_le hi List.length_takeWhile_le) := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    if hp : p hd
      then
        unfold List.takeWhile
        conv => lhs; arg 1; rw [hp]
        cases i <;> simp [ih]
      else
        have hp : p hd = false := by simp [hp]
        conv at hi =>
          rhs; arg 1; unfold List.takeWhile
          simp only [hp]
        simp at hi -- contradiction, hi : i < [].length

namespace TwoDFA

variable {α σ : Type*}

inductive GoesLeftOf {n : Nat} (m : TwoDFA α σ) (w : Word α n) (i : Fin (n+2)) : Config σ n → Config σ n → Prop where
  | refl {cfg : Config σ n} (hlt : cfg.idx ≤ i) : m.GoesLeftOf w i cfg cfg
  | tail {strt mid stp : Config σ n} (hlt : mid.idx ≤ i) (head : m.GoesLeftOf w i strt mid) (tail : m.nextConfig w mid stp) : m.GoesLeftOf w i strt stp

namespace GoesLeftOf

variable {n : Nat} {m : TwoDFA α σ} {w : Word α n} {i : Fin (n+2)} 

theorem forget {cfg1 cfg2 : Config σ n} (h : m.GoesLeftOf w i cfg1 cfg2) : m.GoesTo w cfg1 cfg2 := by
  induction h with
  | refl => rfl
  | tail _ _ tl ih => apply ih.tail tl

theorem single {strt stp : Config σ n} (hlt : strt.idx ≤ i) (hnext : m.nextConfig w strt stp) : m.GoesLeftOf w i strt stp := 
  .tail hlt (.refl hlt) hnext

theorem head {strt mid stp : Config σ n} (head : m.nextConfig w strt mid) (tail : m.GoesLeftOf w i mid stp) (hidx : strt.idx ≤ i) : m.GoesLeftOf w i strt stp := by
  induction tail with
  | refl => exact .tail hidx (.refl hidx) head
  | tail hlt _ tl ih => exact ih.tail hlt tl

@[trans]
theorem trans {strt mid stp : Config σ n} (ha : m.GoesLeftOf w i strt mid) (hb : m.GoesLeftOf w i mid stp) : m.GoesLeftOf w i strt stp := by
  induction hb with
  | refl => exact ha
  | tail hlt _ tl ih => exact ih.tail hlt tl

theorem castSucc {cfg1 cfg2 : Config σ n} {i : Fin _} (h : m.GoesLeftOf w i.castSucc cfg1 cfg2) : m.GoesLeftOf w i.succ cfg1 cfg2 := by
  induction h with
  | refl hlt => exact .refl <| hlt.trans <| by simp [Fin.le_iff_val_le_val]
  | tail hlt _ tl ih =>
    refine .tail ?_ ih tl
    apply hlt.trans
    simp [Fin.le_iff_val_le_val]

theorem castLE {cfg1 cfg2 : Config σ n} {j : Fin _} (hgoes : m.GoesLeftOf w i cfg1 cfg2) (hle : i ≤ j) : m.GoesLeftOf w j cfg1 cfg2 := by
  induction hgoes with
  | refl hlt => exact .refl <| hlt.trans hle
  | tail hlt _ tl ih => exact ih.tail (hlt.trans hle) tl

theorem attach {cfg1 cfg2 : Config σ n} (h : m.GoesTo w cfg1 cfg2) : m.GoesLeftOf w (Fin.last _) cfg1 cfg2 := by
  induction h with
  | refl => exact .refl <| Fin.le_last _
  | tail _ tl ih => exact ih.tail (Fin.le_last _) tl

theorem start_le {c1 c2 : Config σ n} (h : m.GoesLeftOf w i c1 c2) : c1.idx ≤ i := by
  induction h <;> assumption

theorem stop_idx_of_gt {c1 c2 : Config σ n} (h : m.GoesLeftOf w i c1 c2) (hgt : i < c2.idx) : c2.idx = i + 1 := by
  cases h with
  | refl hlt => omega  -- Finds  i < c1.idx ≤ i
  | @tail mid _ hlt _ tl => 
    have mid_ne_last : mid.idx ≠ Fin.last _ := by
      apply Fin.ne_last_of_lt
      apply Fin.lt_of_le_of_lt hlt hgt
    cases tl with
    | stepRight _ _ happly => 
      have : mid.idx + 1 = c2.idx := by simpa [Movement.apply, ←Fin.val_inj, Fin.val_add_one, mid_ne_last] using happly
      rw [←this]
      simp only [add_left_inj, ←Fin.val_inj]
      rw [Fin.le_iff_val_le_val] at hlt
      if heq : mid.idx.val = i.val
        then exact heq
        else
          exfalso
          rw [←this] at hgt
          have : mid.idx.val + 1 ≤ i.val := Nat.lt_of_le_of_ne hlt heq
          suffices i.val < mid.idx.val + 1 by omega  -- Finds  mid.idx + 1 ≤ i < mid.idx + 1
          rw [Fin.lt_iff_val_lt_val] at hgt
          simpa [Fin.val_add_one, mid_ne_last] using hgt
    | stepLeft _ _ happly =>
      exfalso  -- happly says we move left, so contradiction by  i ≥ mid.idx - 1 = c2.idx > i
      suffices mid.idx.val - 1 = c2.idx.val by omega
      simpa [Movement.apply, ←Fin.val_inj] using happly

theorem head_induction_on {stp strt : Config σ n} (hlt : stp.idx ≤ i) {motive : ∀ c : Config σ n, m.GoesLeftOf w i c stp → Prop} (h : m.GoesLeftOf w i strt stp)
  (refl : motive stp (.refl hlt))
  (head : ∀ {c1 c2 : Config σ n} (hnext : m.nextConfig w c1 c2) (hrest : m.GoesLeftOf w i c2 stp) (hidx : c1.idx ≤ i), motive c2 hrest → motive c1 (hrest.head hnext hidx)) :
    motive strt h := by
  induction h with
  | refl _ => exact refl
  | @tail mid stp hlt' _ tl ih =>
    apply ih
    · exact head tl _ hlt' refl
    · exact fun h1 h2 h3 ↦ head h1 (h2.tail hlt' tl) h3
    · exact hlt'

theorem as_head {strt stp : Config σ n} (h : m.GoesLeftOf w i strt stp) : strt = stp ∨ m.nextConfig w strt stp ∨ ∃ next, m.nextConfig w strt next ∧ m.GoesLeftOf w i next stp := by
  if hlt : stp.idx ≤ i
    then
      cases strt, h using head_induction_on hlt with
      | refl => left; rfl
      | @head _ mid _ _ _ => right; right; use mid
    else
      have : stp.idx = i + 1 := stop_idx_of_gt h <| by rwa [Fin.not_le] at hlt
      cases h with
      | refl => left; rfl
      | @tail mid _ hlt hd tl =>
        rcases hd.as_head with heq | hstep | ⟨mid', hstep, hgo⟩
        · right; left; rwa [heq]
        · right; right
          use mid
          constructor
          · exact hstep
          · apply GoesLeftOf.single <;> assumption
        · right; right
          use mid'
          constructor
          · exact hstep
          · exact hgo.tail hlt tl
  termination_by sizeOf stp.idx

theorem single_path {strt stp1 stp2 : Config σ n} (h1 : m.GoesLeftOf w i strt stp1) (h2 : m.GoesLeftOf w i strt stp2) :
    stp1 = stp2 ∨ m.GoesLeftOf w i stp1 stp2 ∨ m.GoesLeftOf w i stp2 stp1 := by
  rcases em (stp1.idx ≤ i ∧ stp2.idx ≤ i) with hidx | hidx
  · induction strt, h1 using head_induction_on hidx.left with
    | refl => right; left; exact h2
    | @head strt1 mid1 hd1 tl1 hlt1 ih1 =>
      induction strt1, h2 using head_induction_on hidx.right with
      | refl => right; right; exact tl1.head hd1 hlt1
      | @head strt2 mid2 hd2 tl2 hlt2 _ =>
        suffices mid1 = mid2 by apply ih1; rwa [this]
        exact nextConfig_right_unique hd1 hd2
  · rw [not_and_or] at hidx
    rcases hidx with hidx | hidx
    all_goals rw [Fin.not_le] at hidx
    · have _ := stop_idx_of_gt h1 hidx
      cases h1 with
      | refl => omega  -- Finds contradiction, i+1 ≤ i
      | tail hlt hd tl =>
        rcases single_path hd h2 with heq | hgo | hgo
        · right; right
          apply GoesLeftOf.single
          <;> rwa [←heq]
        · rcases hgo.as_head with heq | hstep | ⟨mid', hd', tl'⟩
          · right; right
            apply GoesLeftOf.single
            <;> rwa [←heq]
          · left; apply nextConfig_right_unique tl hstep
          · have : mid' = stp1 := by apply nextConfig_right_unique <;> assumption
            right; left
            rwa [←this]
        · right; right
          exact hgo.tail hlt tl
    · have _ := stop_idx_of_gt h2 hidx
      cases h2 with
      | refl => omega  -- Finds contradiction, i+1 ≤ i
      | tail hlt hd tl =>
        rcases single_path hd h1 with heq | hgo | hgo
        · right; left
          apply GoesLeftOf.single
          <;> rwa [←heq]
        · rcases hgo.as_head with heq | hstep | ⟨mid', hd', tl'⟩
          · right; left
            apply GoesLeftOf.single
            <;> rwa [←heq]
          · left; apply nextConfig_right_unique hstep tl
          · have : mid' = stp2 := by apply nextConfig_right_unique <;> assumption
            right; right
            rwa [←this]
        · right; left
          exact hgo.tail hlt tl
  termination_by sizeOf (stp1.idx, stp2.idx)

theorem single_exit {strt stp1 stp2 : Config σ n} (h1 : m.GoesLeftOf w i strt stp1) (hidx1 : i < stp1.idx) (h2 : m.GoesLeftOf w i strt stp2) (hidx2 : i < stp2.idx) :
    stp1 = stp2 := by
  rcases single_path h1 h2 with heq | hgo | hgo
  · exact heq
  all_goals
    have := hgo.start_le
    omega  -- finds an i < i contradiction

theorem as_step_out {strt stp : Config σ n} (hgo : m.GoesLeftOf w i strt stp) (hint : i.internal) (hidx : stp.idx = i+1) :
    ∃ prv, m.GoesLeftOf w i strt ⟨prv, i⟩ ∧ m.nextConfig w ⟨prv, i⟩ stp := by
  rw [←Fin.val_inj, Fin.val_add_one_of_lt <| Fin.lt_last_iff_ne_last.mpr hint.right] at hidx
  cases hgo with
  | refl hlt => 
    rw [Fin.le_iff_val_le_val] at hlt
    omega  -- contradiction; i+1 ≤ i
  | @tail mid _ hlt hd tl =>
    rw [Fin.le_iff_val_le_val] at hlt
    use mid.state
    suffices i = mid.idx by simp only [this, tl, and_true]; rwa [this] at hd
    rw [←Fin.val_inj]
    cases tl with
    | stepLeft _ _ happly =>
      suffices mid.idx.val - 1 = stp.idx.val by omega  -- Finds contradiction; i+1 = stp.idx = mid.idx - 1 ≤ i
      simpa [Movement.apply, ←Fin.val_inj] using happly
    | stepRight _ _ happly =>
      suffices mid.idx.val + 1 = stp.idx.val by omega  -- Finds mid.idx + 1 = stp.idx = i + 1
      simpa [Movement.apply, ←Fin.val_inj] using happly

end GoesLeftOf

abbrev CyclesLeftOf {n : Nat} (m : TwoDFA α σ) (w : Word α n) (i : Fin (n+2)) (strt : Config σ n) : Prop := strt.idx ≤ i ∧ ∃ nxt, m.nextConfig w strt nxt ∧ m.GoesLeftOf w i nxt strt

namespace CyclesLeftOf

variable {n : Nat} {m : TwoDFA α σ} {w : Word α n} {i : Fin (n+2)} 

theorem step {strt nxt : Config σ n} (hnxt : m.nextConfig w strt nxt) (hcyc : m.CyclesLeftOf w i strt) : m.CyclesLeftOf w i nxt := by
  obtain ⟨hstrt, nxt', hnxt', hcyc'⟩ := hcyc
  have heq : nxt = nxt' := nextConfig_right_unique hnxt hnxt'
  have hnxtle : nxt.idx ≤ i := by rw [heq]; exact hcyc'.start_le
  rcases hcyc'.as_head with heq | hsingle | ⟨mid, hd, tl⟩
  · exfalso
    rw [heq] at hnxt'
    exact hnxt'.irrefl
  · refine ⟨hnxtle, ?_⟩
    exists strt
    constructor
    · rwa [heq]
    · apply GoesLeftOf.single <;> assumption
  · refine ⟨hnxtle, ?_⟩
    exists mid
    constructor
    · rwa [heq]
    · exact tl.tail hstrt hnxt

theorem transfer {c1 c2 : Config σ n} {i j : Fin _} (hcyc : m.CyclesLeftOf w j c1) (hgo : m.GoesLeftOf w i c1 c2) : m.CyclesLeftOf w j c2 := by
  induction hgo with
  | refl _ => exact hcyc
  | tail _ _ tl ih => exact ih.step tl

theorem always_left {c1 c2 : Config σ n} {i j : Fin _} (hcyc : m.CyclesLeftOf w j c1) (hgo : m.GoesLeftOf w i c1 c2) : c2.idx ≤ j := by
  obtain ⟨hlt, _⟩ := hcyc.transfer hgo
  exact hlt

end CyclesLeftOf

namespace GoesLeftOf

variable {n : Nat} {m : TwoDFA α σ} {w : Word α n} {i : Fin (n+2)} 

-- Idea is that the accumulator holds exactly the states that are passed through *at index j*, and hacc holds proofs that we can get from any of those to the current start configuration
theorem prefix_left_of_go [Fintype σ] {strt stp : Config σ n} {j : Fin _} (hgo : m.GoesLeftOf w i strt stp) (hlt : j < i) (hstrt : strt.idx ≤ j) (hstp : j < stp.idx)
  (acc : List σ) (hdup : acc.Nodup) (hacc : ∀ q ∈ acc, m.GoesLeftOf w j ⟨q, j⟩ strt) :
    ∃ mid, j < mid.idx ∧ m.GoesLeftOf w j strt mid ∧ m.GoesLeftOf w i mid stp := by
  rcases hgo.as_head with heq | hnext | ⟨nxt, hnext, hgo'⟩
  · rw [←heq] at hstp; omega  -- Finds j < j
  · use stp
    constructorm* _ ∧ _
    · exact hstp
    · apply GoesLeftOf.single
      · exact hstrt
      · exact hnext
    · apply GoesLeftOf.refl
      suffices stp.idx = j + 1 by
        rw [this, Fin.le_iff_val_le_val, Fin.val_add_one_of_lt <| Fin.lt_last_iff_ne_last.mpr <| Fin.ne_last_of_lt hlt]
        rwa [Fin.lt_iff_val_lt_val] at hlt
      have hstrtadd := Fin.val_add_one_of_lt <| Fin.lt_last_iff_ne_last.mpr <| Fin.ne_last_of_lt <| Fin.lt_of_le_of_lt hstrt hlt
      have : stp.idx = strt.idx + 1 := by
        cases hnext with
        | stepRight _ _ happly => symm; simpa [Movement.apply, ←Fin.val_inj, hstrtadd] using happly
        | stepLeft _ hvalid happly => 
          exfalso
          have nezero : strt.idx ≠ 0 := by simpa using hvalid.hleft
          have : stp.idx = strt.idx - 1 := by symm; simpa [Movement.apply, ←Fin.val_inj, Fin.val_sub_one_of_ne_zero nezero] using happly
          rw [this] at hstp
          simpa [nezero] using Fin.lt_of_le_of_lt hstrt hstp
      rw [this, add_left_inj]
      rw [this] at hstp
      by_contra hne
      suffices strt.idx + 1 ≤ j by omega  -- Finds  j < strt.idx + 1 ≤ j
      rw [Fin.le_def, hstrtadd]
      have hstrt := Fin.lt_iff_le_and_ne.mpr <| And.intro hstrt hne
      rw [Fin.lt_def] at hstrt
      simpa using hstrt
  · cases hnext with
    | stepRight _ _ happly =>
      have hnext : m.nextConfig w strt nxt := by right <;> assumption
      if hstrt' : strt.idx = j
        then
          use nxt
          constructorm* _ ∧ _
          · suffices nxt.idx = strt.idx + 1 by simp [this, hstrt', Fin.lt_last_iff_ne_last.mpr <| Fin.ne_last_of_lt hlt]
            symm
            have := Fin.val_add_one_of_lt <| Fin.lt_last_iff_ne_last.mpr <| Fin.ne_last_of_lt <| Fin.lt_of_le_of_lt hstrt hstp
            simpa [Movement.apply, ←Fin.val_inj, this] using happly
          · apply GoesLeftOf.single
            · exact hstrt
            · exact hnext
          · exact hgo'
        else
          have hstrtlt : strt.idx < j := by rw [Fin.lt_iff_le_and_ne]; constructor <;> assumption
          have hmv : nxt.idx = strt.idx + 1 := by
            symm
            have := Fin.val_add_one_of_lt <| Fin.lt_last_iff_ne_last.mpr <| Fin.ne_last_of_lt hstrtlt
            simpa [Movement.apply, ←Fin.val_inj, this] using happly
          have hjnxt : nxt.idx ≤ j := by
            rw [hmv]
            exact Fin.add_one_le_of_lt hstrtlt
          have _term : nxt.idx.rev < strt.idx.rev := by
            rw [Fin.rev_lt_rev, hmv, Fin.lt_add_one_iff, Fin.lt_last_iff_ne_last]
            exact Fin.ne_last_of_lt hstrtlt
          have hacc' : ∀ q ∈ acc, m.GoesLeftOf w j ⟨q, j⟩ nxt := by
            intro q hmem
            apply GoesLeftOf.tail hstrt (tail := hnext)
            exact hacc q hmem
          obtain ⟨mid, hmidlt, hpref, hrest⟩ := prefix_left_of_go hgo' hlt hjnxt hstp acc hdup hacc'
          use mid
          constructorm* _ ∧ _
          · exact hmidlt
          · apply hpref.head
            · exact hnext
            · exact hstrt
          · exact hrest
    | stepLeft _ hvalid happly =>
      have hnext : m.nextConfig w strt nxt := by left <;> assumption
      cases hj : j using Fin.cases with
      | zero =>
        have : strt.idx ≠ 0 := by simpa using hvalid.hleft
        have : strt.idx = 0 := by simpa [hj] using hstrt
        contradiction
      | succ j' =>
        have _term : j'.castSucc < j := by simp [hj]
        have hji : j'.castSucc < i := Fin.lt_trans _term hlt
        have hjstp : j'.castSucc < stp.idx := Fin.lt_trans _term hstp
        have hjnxt : nxt.idx ≤ j'.castSucc := by
          have hsub : (strt.idx - 1).val = strt.idx.val - 1 := by 
            apply Fin.val_sub_one_of_ne_zero 
            simpa using hvalid.hleft
          have : nxt.idx = strt.idx - 1 := by
            symm; simpa [Movement.apply, ←Fin.val_inj, hsub] using happly
          simpa [this, hsub, hj, Fin.le_iff_val_le_val] using hstrt
        -- The accumulator isn't passed down because this call is using a different j position
        obtain ⟨mid, hlt', hpref, hrest⟩ := prefix_left_of_go (j := j'.castSucc) hgo' hji hjnxt hjstp [] List.nodup_nil <| by
          intro _ hmem; simp only [List.not_mem_nil] at hmem
        have hmideq : mid.idx = j := by
          have : mid.idx = j'.castSucc + 1 := hpref.stop_idx_of_gt hlt'
          simp [this, hj]
        have from_strt : m.GoesLeftOf w j strt mid := by
          rw [hj]
          apply hpref.castSucc.head hnext
          rwa [←hj]
        if hmem : mid.state ∈ acc
          then
            exfalso  -- Must be in a cycle, but then we cannot possibly reach position i
            suffices stp.idx ≤ j by omega
            suffices m.CyclesLeftOf w j strt by apply this.always_left hgo
            constructor
            · exact hstrt
            · exists nxt
              constructor
              · exact hnext
              · rw [hj]
                apply hpref.castSucc.trans
                rw [←hj]
                suffices ⟨mid.state, j⟩ = mid by rw [←this]; exact hacc _ hmem
                rw [←hmideq]
          else
            rcases em (strt.idx < j) with hstrtlt | hstrtlt
            case' inl =>
              have _term : mid.idx.rev < strt.idx.rev := by
                rw [Fin.rev_lt_rev, hmideq]
                exact hstrtlt
            case' inr =>
              have _term1 : mid.idx.rev = strt.idx.rev := by 
                suffices strt.idx = j by rwa [Fin.rev_eq_iff, Fin.rev_rev, this]
                cases Fin.lt_or_eq_of_le hstrt
                · contradiction
                · assumption
              have _term2 : Fintype.card σ - (acc.length + 1) < Fintype.card σ - acc.length := by
                have := (hdup.cons hmem).length_le_card
                rw [List.length_cons] at this
                omega
            all_goals
              have hacc' : ∀ q ∈ mid.state :: acc, m.GoesLeftOf w j ⟨q, j⟩ mid := by
                intro q hmem
                rw [List.mem_cons] at hmem
                rcases hmem with heq | hprev
                · have : ⟨q, j⟩ = mid := by simp [heq, ←hmideq]
                  rw [this]
                  apply GoesLeftOf.refl
                  simp [hmideq]
                · exact (hacc q hprev).trans from_strt
              obtain ⟨mid2, hlt2, hpref2, hrest2⟩ := prefix_left_of_go hrest hlt (Fin.le_of_eq hmideq) hstp (mid.state :: acc) (hdup.cons hmem) hacc'
              use mid2
              repeat rw [←hj]
              constructorm* _ ∧ _
              · exact hlt2
              · trans
                · apply GoesLeftOf.head
                  · left <;> assumption  -- rebuild hnext
                  · rw [hj]; exact hpref.castSucc
                  · exact hstrt
                · exact hpref2
              · exact hrest2
  termination_by (j, strt.idx.rev, Fintype.card σ - acc.length)
  decreasing_by 
    all_goals try decreasing_tactic
    -- only goal that fails is for the recursion in stepLeft | j = j'.succ | strt.idx = j
    simp [Prod.lex_def, _term1, _term2]

theorem prefix_left_of [Fintype σ] {strt stp : Config σ n} (hgo : m.GoesLeftOf w i strt stp) (j : Fin _) (hlt : j < i) (hstrt : strt.idx ≤ j) (hstp : j < stp.idx) :
    ∃ mid, j < mid.idx ∧ m.GoesLeftOf w j strt mid ∧ m.GoesLeftOf w i mid stp :=
  prefix_left_of_go hgo hlt hstrt hstp [] List.nodup_nil <| by
    intro _ hmem; simp only [List.not_mem_nil] at hmem  -- vacuous implication

lemma step_mpr_go {m : TwoDFA α σ} {w : Word α n} {i : Fin _} (j : Nat) (qs : List σ) (hj : j < qs.length.pred)
  (hmap : ∀ (j : ℕ) (hj : j < qs.length.pred), ∃ q',
      m.nextConfig w { state := (qs[j]'(Nat.lt_of_lt_pred hj)), idx := i.succ } { state := q', idx := i.castSucc } ∧
      m.GoesLeftOf w i.castSucc { state := q', idx := i.castSucc } { state := (qs[j+1]'(Nat.succ_lt_of_lt_pred hj)), idx := i.succ }) :
    m.GoesLeftOf w i.succ { state := (qs[0]'(Nat.lt_of_le_of_lt (by simp : 0 ≤ j) (Nat.lt_of_lt_pred hj))), idx := i.succ } { state := (qs[j+1]'(Nat.succ_lt_of_lt_pred hj)), idx := i.succ } := by
  induction j with
  | zero => 
    obtain ⟨q', hstep, hgoes⟩ := hmap 0 (Nat.lt_of_le_of_lt (by rfl) hj)
    apply head
    · exact hstep
    · apply castLE
      · exact hgoes
      · simp only [Fin.castSucc_le_succ]
    · simp
  | succ j ih =>
    have hlt : j < qs.length.pred := j.lt_add_one.trans hj
    have hgoes := ih hlt
    obtain ⟨q', hstep, hgoes'⟩ := hmap _ hj
    apply hgoes.trans
    apply head
    · exact hstep
    · apply castLE
      · exact hgoes'
      · simp only [Fin.castSucc_le_succ]
    · simp

end GoesLeftOf

--- A "table" that stores all the information needed to completely reconstruct the behaviour of a given 2DFA on a fixed input prefix.
structure BackTable (σ : Type _) : Type _ where
  --- The state the 2DFA is in the first time it exits the prefix.
  init : Option σ
  --- What state the 2DFA will be in when it exits the prefix, based on what state it re-entered (from the right) in.
  map : σ → Option σ

-- TODO: Find some way to not need the [DecidableEq σ] constraint
instance [DecidableEq σ] [Fintype σ] : Fintype (BackTable σ) := derive_fintype% _

--- The table for this 2DFA when the prefix is empty (just the left endmarker)
def first_table (m : TwoDFA α σ) : BackTable σ where
  -- The movements in both of these steps are always going to be "go right", so we don't need to repeat at all
  init := some <| (m.step .left m.start).1
  map q := some <| (m.step .left q).1

/--
Repeatedly apply the step function and the mapping for the prefix to
determine where a state should map in the table for appending `a` to the
prefix. Returning `none` indicates diverging due to entering a cycle.
-/
def step_right [DecidableEq σ] [Fintype σ] (m : TwoDFA α σ) (t : BackTable σ) (a : α) (q : σ) : Option σ := 
  -- acc collects the list of states we have already passed through (most recent at head),
  -- so hdup asserts that we never pass through the same state twice
  go q [] List.nodup_nil |>.map Prod.fst
  where
    go [fin_states : Fintype σ] (q : σ) (acc : List σ) (hdup : acc.Nodup) : Option (σ × List σ) :=
      match m.step a q with
      | ⟨p, .right⟩ => some (p, acc)
      | ⟨p, .left⟩ => do
        -- We've stepped back into the prefix, where do we end up?
        -- uses do-notation so if map returns none we immediately do the same
        let q' ← t.map p
        if hmem : q' ∈ acc
          then none
          else go q' (q' :: acc) <| hdup.cons hmem
    termination_by fin_states.card - acc.length
    decreasing_by 
      have := (hdup.cons hmem).length_le_card
      rw [List.length_cons] at this
      rw [List.length_cons]
      omega

def step_table [DecidableEq σ] [Fintype σ] (m : TwoDFA α σ) (t : BackTable σ) (a : α) : BackTable σ where
  init := t.init >>= m.step_right t a  -- Only step if t.init ≠ none
  map := m.step_right t a


/--
An accepting table is one where if we start with it's initial state and trace
it as the machine takes it between the table's prefix and the right endmarker,
it eventually ends up in the machine's accept state.
-/
def accepting_table [DecidableEq σ] [Fintype σ] (m : TwoDFA α σ) (t : BackTable σ) : Prop :=
  -- This absolutely will get stuck in a loop of some form; even the accept and reject states sit in a loop at the right endmarker forever
  -- What we want to know is whether the state we loop on is the accept state
  t.init >>= (go · [] List.nodup_nil) = some m.accept
  where
    go [fin_states : Fintype σ] (q : σ) (acc : List σ) (hdup : acc.Nodup) : Option σ := do
      let p' := (m.step .right q).1
      let q' ← t.map p'
      if hmem : q' ∈ acc
        then some q'
        else go q' (q' :: acc) <| hdup.cons hmem
    termination_by fin_states.card - acc.length
    decreasing_by 
      have := (hdup.cons hmem).length_le_card
      rw [List.length_cons] at this
      rw [List.length_cons]
      omega

--- Convert a TwoDFA into an equivalent (accepting the same language) One-Way DFA
def to_one_way [DecidableEq σ] [Fintype σ] (m : TwoDFA α σ) : DFA α (BackTable σ) where
  step := m.step_table
  start := m.first_table
  accept := {t | m.accepting_table t}

section Proof

variable [DecidableEq σ] [Fintype σ]

def table_for (m : TwoDFA α σ) (w : List α) : BackTable σ := w.foldl m.step_table m.first_table

theorem table_for_nil (m : TwoDFA α σ) : m.table_for [] = m.first_table := by
  simp [table_for]

theorem table_for_step {m : TwoDFA α σ} (w : List α) (a : α) : m.step_table (m.table_for w) a = m.table_for (w ++ [a]) := by
  simp [table_for]

theorem table_for_step_right {m : TwoDFA α σ} (t : BackTable σ) (w : List α) (i : Fin (w.length+1)) (hi : i < w.length) (p q : σ) (acc : List σ) (hdup : acc.Nodup)
  {qs : List σ} (hmap : step_right.go m t w[↑i] p acc hdup = some (q, qs))
  (hind : ∀ (p q : σ), t.map p = some q → m.GoesLeftOf w.toWord i.castSucc { state := p, idx := i.castSucc } { state := q, idx := i.succ }) :
    m.GoesLeftOf w.toWord i.succ { state := p, idx := i.succ } { state := q, idx := i.succ + 1 } := by
  unfold step_right.go at hmap
  have hint : i.succ.internal := by
    constructor
    · simp
    · apply Fin.ne_of_lt
      rw [Fin.lt_iff_val_lt_val, Fin.val_last]
      simp [hi]
  match hstep : m.step w[i.val] p with
  | (p', .right) => 
    simp only [Fin.getElem_fin, hstep, Option.some.injEq, Prod.ext_iff] at hmap
    rw [←hmap.left]
    have hvalid : Movement.right.isValid i.succ := by constructor <;> simp [hint.right]
    apply GoesLeftOf.single (hlt := by rfl)
    right
    · suffices w.toWord.get i.succ = w[i.val] by simpa [this]
      rw [Word.get_eq_symbol_of_internal w.toWord hint]
      simp [List.toWord, Vector.get]
    · suffices Movement.right.apply i.succ hvalid = i.succ + 1 by simpa
      simp only [Movement.apply, Fin.castLT]
      rw [←Fin.val_inj, Fin.val_add_one]
      simp [hint.right]
  | (p', .left) => 
    have : ∃ a, t.map p' = some a ∧ (if h : a ∈ acc then none else step_right.go m t w[↑i] a (a :: acc) (hdup.cons h)) = some (q, ?_) := by
      simpa [hstep, Option.bind_eq_some_iff] using hmap
    obtain ⟨q', hmap', hsome'⟩ := this
    if hmem : q' ∈ acc
      then simp [hmem] at hsome'  -- Contradiction
      else
        simp only [hmem, ↓reduceDIte, Fin.getElem_fin] at hsome'
        trans
        · apply GoesLeftOf.head
          · suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.castSucc⟩ from this
            unfold step at hstep
            simp only [Prod.ext_iff, ←Word.toWord_get_internal _ _ hint] at hstep
            simp only [← stepConfig_gives_nextConfig, stepConfig, Movement.apply, Config.mk.injEq, hstep.left, true_and]
            split 
            · simp [Fin.predCast, Fin.castSucc, Fin.castAdd, Fin.castLE]
            · rename (m.1 _ _).2 = _ => heq
              simp [hstep.right] at heq  -- contradiction
          · apply GoesLeftOf.castSucc
            exact hind _ _ hmap'
          · rfl
        · apply table_for_step_right (hind := hind) (hmap := hsome')
  termination_by Fintype.card σ - acc.length
  decreasing_by 
    have := (hdup.cons hmem).length_le_card
    rw [List.length_cons] at this
    rw [List.length_cons]
    omega

theorem table_for_take_succ {m : TwoDFA α σ} {w : List α} (i : Fin w.length) (t1 t2 : BackTable σ)
  (h1 : t1 = m.table_for (w.take i)) (h2 : t2 = m.table_for (w.take i.succ)) :
    t2 = m.step_table t1 w[i.val] := by
  simp [h2, table_for, h1]
  rw [List.take_succ, List.foldl_append]
  simp

lemma table_for_take_step_right_go {m : TwoDFA α σ} {w : List α} {t : BackTable σ} {i : Fin (w.length + 1)} (hi : i.val < w.length) (ht : t = m.table_for (w.take i))
  (hind : ∀ (p q : σ), t.map p = some q → m.GoesLeftOf w.toWord i.castSucc { state := p, idx := i.castSucc } { state := q, idx := i.castSucc + 1 })
  (p q : σ) (acc qs : List σ) (hdup : acc.Nodup) (hstep : step_right.go m t w[i.val] p acc hdup = some (q, qs)) :
    m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩ := by
  have hint : i.succ.internal := by
    suffices i ≠ Fin.last _ by simp [Fin.internal, this]
    apply Fin.ne_last_of_lt (b := Fin.last _)
    rw [Fin.lt_iff_val_lt_val]
    simp [hi]
  unfold step_right.go at hstep
  split at hstep
  case h_1 hstep' =>
    simp only [Option.some.injEq, Prod.mk.injEq, List.nil_eq] at hstep
    rw [hstep.left, step, ←Word.toWord_get_internal w i hint] at hstep'
    apply GoesLeftOf.single
    · simp
    · rw [←stepConfig_gives_nextConfig]
      simp only [stepConfig, hstep', Config.mk.injEq, true_and]
      rw [←Fin.val_inj]
      simp [Movement.apply, Fin.val_add_one, hint.right]
  case h_2 _ p' hstep' =>
    rw [←Word.toWord_get_internal w i hint] at hstep'
    have : ∃ a, t.map p' = some a ∧ ∃ hmem, step_right.go m t w[↑i] a (a :: acc) (hdup.cons hmem) = some (q, qs) := by
      simpa [Option.bind_eq_some_iff] using hstep
    obtain ⟨q', hmap', hmem, hstep_r⟩ := this
    have hmap' := hind _ _ hmap'
    apply GoesLeftOf.head (mid := ⟨p', i.castSucc⟩)
    · rw [←stepConfig_gives_nextConfig]
      simp only [stepConfig, hstep', Config.mk.injEq, true_and]
      rw [←Fin.val_inj]
      simp [Movement.apply]
    · trans
      · exact hmap'.castSucc
      · have : i.castSucc + 1 = i.succ := by rw [←Fin.val_inj]; simp
        simp only [this]
        apply table_for_take_step_right_go (hstep := hstep_r) (hind := hind)
        exact ht
    · rfl
  termination_by Fintype.card σ - acc.length
  decreasing_by 
    have := (hdup.cons hmem).length_le_card
    rw [List.length_cons] at this
    rw [List.length_cons]
    omega

theorem table_for_take_map_mp (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 2)) (hnelast : i ≠ Fin.last _)
  (ht : t = m.table_for (w.take i)) (p q : σ)  :
    t.map p = some q → m.GoesLeftOf w.toWord i ⟨p, i⟩ ⟨q, i+1⟩ := by
  induction i using Fin.inductionOn generalizing t p q with
  | zero => 
    simp only [table_for, first_table, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.take_zero, List.foldl_nil] at ht
    simp only [ht, Option.some.injEq, zero_add]
    intro hstep
    have : m.step .left p = (q, .right) := by
      ext
      · exact hstep
      · obtain ⟨_, h⟩ := m.in_bounds_left p
        rw [h]
    apply GoesLeftOf.single (hlt := by simp)
    rw [←stepConfig_gives_nextConfig]
    simp only [stepConfig, Word.get_eq_left_of_eq_zero, this]
    simp [Movement.apply, Fin.castLT]
  | succ i ih => 
    have hlt : i.val < w.length := by
      apply i.val_lt_last
      rwa [←i.succ_ne_last_iff]
    have hint : i.succ.internal := by simp [Fin.internal, hnelast]
    have hget : w[i.val]? = some w[i.val] := by simp
    let prev_t := List.foldl m.step_table m.first_table (w.take i)
    have hstep : t = m.step_table prev_t w[i.val] := by
      simp only [table_for, Fin.val_succ, List.take_succ, List.foldl_append, Option.foldl_toList] at ht
      rw [hget] at ht
      simpa using ht
    have hind := ih prev_t (by simp) rfl
    rw [hstep]
    intro hmap
    match hgo : step_right.go m prev_t w[i.val] p [] List.nodup_nil with
    | .none =>
      conv at hmap =>
        simp only [step_table, Option.bind_eq_bind]
        unfold step_right
      simp [hgo] at hmap -- hmap : none = some q
    | .some (q', qs) =>
      conv at hmap =>
        simp only [step_table, Option.bind_eq_bind]
        unfold step_right
        simp only [hgo, Option.map_some, Option.some.injEq]
      rw [hmap] at hgo
      apply table_for_take_step_right_go (hind := hind) (hstep := hgo)
      rfl

theorem step_right_go_acc_contained {m : TwoDFA α σ} {t : BackTable σ} {a : α} {p q : σ} {acc qs : List σ} {hdup : acc.Nodup}
    (h : step_right.go m t a p acc hdup = some (q, qs)) : acc ⊆ qs := by
  cases acc with
  | nil => apply List.nil_subset
  | cons hd tl =>
    rcases hstep : m.step a p with ⟨p', left | right⟩
    all_goals
      conv at h =>
        unfold step_right.go
        simp only [hstep]
    case right =>
      have : hd :: tl = qs := by apply And.right; simpa using h
      rw [this]
      apply List.Subset.refl
    case left =>
      obtain ⟨q', hmap, hne, hstep'⟩ : ∃ q', t.map p' = some q' ∧ ∃ hne : q' ∉ (hd :: tl), step_right.go m t a q' (q' :: hd :: tl) (hdup.cons hne) = some (q, qs) := by
        simpa [Option.bind_eq_some_iff] using h
      have hind := step_right_go_acc_contained hstep'
      rw [List.cons_subset] at hind
      exact hind.right
  termination_by Fintype.card σ - acc.length
  decreasing_by 
    have := (hdup.cons hne).length_le_card
    rename acc = _ => hacc
    rw [hacc]
    repeat rw [List.length_cons] at this
    repeat rw [List.length_cons]
    omega

theorem step_right_go_eq_none {m : TwoDFA α σ} {w : List α} {i : Fin _} {p : σ} (hi : i.val < w.length)
  {acc : List σ} {hdup : acc.Nodup} (hstepright : step_right.go m (m.table_for <| w.take i) w[i.val] p acc hdup = none) (q : σ) :
    ¬ m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩ := by
  unfold step_right.go at hstepright
  match hstep : m.step w[i.val] p with
  | (p', .right) => simp [hstep] at hstepright  -- contradiction; some _ = none
  | (p', .left) =>
    simp only [hstep, Option.bind_eq_bind, Option.bind_eq_none_iff, dite_eq_left_iff] at hstepright
    have hnext : m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.castSucc⟩ := sorry
    cases hmap : (m.table_for (w.take i)).map p' with
    | none => 
      have diverges : ∀ q', ¬ m.GoesLeftOf w.toWord i.castSucc ⟨p', i.castSucc⟩ ⟨q', i.succ⟩ := sorry
      by_contra hgo
      rcases hgo.as_head with heq | hnext' | ⟨nxt, hnext', hgo⟩
      · simp at heq  -- i.succ ≠ i.succ + 1
      · have hi' : i.val ≠ w.length := Nat.ne_of_lt hi
        have hne : i.castSucc ≠ i.succ + 1 := by
          simp only [ne_eq, ← Fin.val_inj, Fin.coe_castSucc, Fin.val_add_one, Fin.val_succ, Fin.val_last, Nat.add_right_cancel_iff, hi', ↓reduceIte]
          omega
        have := nextConfig_right_unique hnext hnext'
        simp [hne] at this
      · have : nxt = ⟨p', i.castSucc⟩ := nextConfig_right_unique hnext' hnext
        rw [this] at hgo; clear this hnext' nxt
        /- have := hgo.prefix_left_of -/
        sorry
    | some q' => sorry

lemma GoesLeftOf.step_mp_go {m : TwoDFA α σ} {w : List α} {i : Fin _} {p q : σ} (hi : i.val < w.length) (hgo : m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩) :
  ∃ out : List σ, ∃ hlen : out.length ≠ 0, out[0] = p ∧ 
    m.nextConfig w.toWord ⟨out[out.length.pred]'(by simp [Nat.pos_of_ne_zero hlen]), i.succ⟩ ⟨q, i.succ + 1⟩ ∧
    (∀ j, ∀ hj : j < out.length.pred, ∃ q',
      m.nextConfig w.toWord ⟨out[j]'(Nat.lt_of_lt_pred hj), i.succ⟩ ⟨q', i.castSucc⟩ ∧
      m.GoesLeftOf w.toWord i.castSucc ⟨q', i.castSucc⟩ ⟨out[j.succ]'(Nat.succ_lt_of_lt_pred hj), i.succ⟩) := by
  match hstepright : step_right.go m (m.table_for <| w.take i) w[i.val] p [] List.nodup_nil with
  | .none =>
    absurd hgo
    apply step_right_go_eq_none hi hstepright
  | .some (q', qs) =>
    use p :: qs.reverse, by simp
    constructorm* _ ∧ _
    · simp
    · cases qs with
      | nil =>
        match hstep' : m.step w[i.val] p with
        | (x, .right) =>
          conv at hstepright =>
            unfold step_right.go
            simp only [hstep', Option.some.injEq, Prod.mk.injEq, and_true]
          rw [hstepright] at hstep'
          have hltlast : i.succ < Fin.last _ := by simp [Fin.lt_iff_val_lt_val, hi]
          have hnext : m.nextConfig w.toWord ⟨p, i.succ⟩ ⟨q', i.succ + 1⟩ := by
            rw [←stepConfig_gives_nextConfig, stepConfig]
            have hint : i.succ.internal := by
              suffices i.succ ≠ Fin.last _ by simpa [Fin.internal]
              rwa [←Fin.lt_last_iff_ne_last]
            simp only [Word.toWord_get_internal w i hint, hstep', Config.mk.injEq, true_and]
            simp only [Movement.apply, ← Fin.val_inj, Fin.coe_castLT, Fin.val_succ]
            simp [Fin.val_add_one, hint.right]
          suffices q' = q by simpa [←this]
          have hlt : i.succ < i.succ + 1 := by rwa [Fin.lt_add_one_iff]
          have := single_exit (GoesLeftOf.single (by rfl) hnext) hlt hgo hlt
          simpa
        | (x, .left) =>
          conv at hstepright =>
            unfold step_right.go
            simp only [hstep', List.not_mem_nil, ↓reduceDIte, Option.bind_eq_bind, Option.bind_eq_some_iff]
          obtain ⟨p', hmap, hstepright⟩ := hstepright
          -- can get a contradiction, in the form of [p'] ⊆ []
          have := step_right_go_acc_contained hstepright
          simp at this
      | cons x xs =>
        have : (p :: (x :: xs).reverse)[(p :: (x :: xs).reverse).length.pred] = x := by simp
        rw [this]; clear this
        sorry
    · sorry

theorem GoesLeftOf.step (m : TwoDFA α σ) (w : List α) {i : Fin _} (p q : σ) (hi : i ≠ Fin.last _) : m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩ ↔
    ∃ out : List σ, ∃ hlen : out.length ≠ 0, out[0] = p ∧ 
      m.nextConfig w.toWord ⟨out[out.length.pred]'(by simp [Nat.pos_of_ne_zero hlen]), i.succ⟩ ⟨q, i.succ + 1⟩ ∧
      (∀ j, ∀ hj : j < out.length.pred, ∃ q',
        m.nextConfig w.toWord ⟨out[j]'(Nat.lt_of_lt_pred hj), i.succ⟩ ⟨q', i.castSucc⟩ ∧
        m.GoesLeftOf w.toWord i.castSucc ⟨q', i.castSucc⟩ ⟨out[j.succ]'(Nat.succ_lt_of_lt_pred hj), i.succ⟩)
where
  mp hgoes := by
    have hlt : i.val < w.length := by simpa [←Fin.lt_last_iff_ne_last] using hi
    apply step_mp_go hlt hgoes
  mpr := by
    rintro ⟨psqs, hlen, hstrt, hlast, hmap⟩
    cases psqs with
    | nil => simp at hlen -- psqs.length ≠ 0
    | cons hd tl =>
      cases tl with
      | nil => 
        clear hmap
        simp at hlast hstrt
        rw [hstrt] at hlast
        apply single (hnext := hlast); simp
      | cons hd' tl' =>
        simp at hmap hlast hstrt
        apply tail (tail := hlast) (hlt := by simp)
        rw [←hstrt]
        exact step_mpr_go tl'.length (hd :: hd' :: tl') (by simp) hmap

theorem table_for_take_map (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 2)) (hnelast : i ≠ Fin.last _)
  (ht : t = m.table_for (w.take i)) (p q : σ)  :
    t.map p = some q ↔ m.GoesLeftOf w.toWord i ⟨p, i⟩ ⟨q, i+1⟩ := by
  induction i using Fin.inductionOn generalizing t p q with
  | zero => 
    simp only [table_for, first_table, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.take_zero, List.foldl_nil] at ht
    simp only [ht, Option.some.injEq, zero_add]
    constructor
    · intro hstep
      have : m.step .left p = (q, .right) := by
        ext
        · exact hstep
        · obtain ⟨_, h⟩ := m.in_bounds_left p
          rw [h]
      apply GoesLeftOf.single (hlt := by simp)
      rw [←stepConfig_gives_nextConfig]
      simp only [stepConfig, Word.get_eq_left_of_eq_zero, this]
      simp [Movement.apply, Fin.castLT]
    · intro hgoes
      cases hgoes with
      | tail hlt hd tl => 
        cases hd with
        | tail hlt' _ tl' =>
          simp at hlt hlt'
          have := nextConfig.must_move m w (h := hlt'.trans hlt.symm)
          contradiction
        | refl =>
          rw [←stepConfig_gives_nextConfig] at tl
          apply And.left
          simpa [stepConfig, Word.get_eq_left_of_eq_zero] using tl
  | succ i ih => 
    have hlt : i.val < w.length := by
      apply i.val_lt_last
      rwa [←i.succ_ne_last_iff]
    have hint : i.succ.internal := by simp [Fin.internal, hnelast]
    have hget : w[i.val]? = some w[i.val] := by simp
    let prev_t := List.foldl m.step_table m.first_table (w.take i)
    have hstep : t = m.step_table prev_t w[i.val] := by
      simp only [table_for, Fin.val_succ, List.take_succ, List.foldl_append, Option.foldl_toList] at ht
      rw [hget] at ht
      simpa using ht
    have hind := ih prev_t (by simp) rfl
    rw [hstep]
    constructor
    · intro hmap
      match hgo : step_right.go m prev_t w[i.val] p [] List.nodup_nil with
      | .none =>
        conv at hmap =>
          simp only [step_table, Option.bind_eq_bind]
          unfold step_right
        simp [hgo] at hmap -- hmap : none = some q
      | .some (q', qs) =>
        conv at hmap =>
          simp only [step_table, Option.bind_eq_bind]
          unfold step_right
          simp only [hgo, Option.map_some, Option.some.injEq]
        rw [hmap] at hgo
        apply table_for_take_step_right_go (hind := fun p q ↦ (hind p q).mp) (hstep := hgo)
        rfl
    · intro hgl
      simp only [step_table, Option.bind_eq_bind, step_right, Option.map_eq_some_iff, Prod.exists,
        exists_and_right, exists_eq_right]
      unfold step_right.go
      split
      · rename m.step _ _ = _ => heq
        rename σ => p'
        -- will conclude that m.step w[i] p = (q, .right) 
        suffices p' = q by simpa
        have : m.GoesLeftOf w i.succ ⟨p, i.succ⟩ ⟨p', i.succ + 1⟩ := by
          apply GoesLeftOf.single
          · rfl
          · rw [←stepConfig_gives_nextConfig]
            simp only [stepConfig, Word.toWord_get_internal (int := hint), heq, Config.mk.injEq, true_and]
            rw [←Fin.val_inj]
            simp [Movement.apply, Fin.val_add_one, hint.right]
        have hlt : i.succ < i.succ + 1 := by simp [Fin.lt_last_iff_ne_last, hnelast]
        have := GoesLeftOf.single_exit this hlt hgl hlt
        simpa
      · rename m.step _ _ = _ => heq
        rename σ => p'
        simp only [List.not_mem_nil, ↓reduceDIte, Option.bind_eq_bind, Option.bind_eq_some_iff]
        sorry

theorem table_for_take_init (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 1))
  (ht : t = m.table_for (w.take i)) {q : σ} (hinit : t.init = some q)
    : m.GoesLeftOf w.toWord i.castSucc m.init ⟨q, i.succ⟩ := by
  induction i using Fin.inductionOn generalizing t q with
  | zero =>
    conv at hinit =>
      rw [ht]
      simp [table_for, first_table]
    rw [←hinit]
    apply GoesLeftOf.single (hlt := by rfl)
    rw [←stepConfig_gives_nextConfig]
    simp only [stepConfig, Word.get_eq_left_of_eq_zero, Fin.succ_zero_eq_one, Config.mk.injEq, true_and]
    obtain ⟨_, hright⟩ := m.in_bounds_left m.start
    unfold step at hright
    conv => enter [1, 1, 1]; rw [hright]
    simp [Movement.apply, Fin.castLT]
  | succ i ih =>
    let prev_t := m.table_for (w.take i)
    have hstep : t = m.step_table prev_t w[i.val] := m.table_for_take_succ i prev_t t rfl ht
    have hinit_def : prev_t.init.bind (m.step_right prev_t w[i.val]) = t.init := by
      simp [hstep, step_table]
    rw [hinit, Option.bind_eq_some_iff] at hinit_def
    obtain ⟨prev_init, hprev, hstep_init⟩ := hinit_def
    trans
    · apply (ih prev_t rfl hprev).castSucc
    · have : i.succ.succ = i.castSucc.succ + 1 := by
        rw [←Fin.val_inj]
        simp [Fin.val_add_one]
      rw [this]
      rw [step_right, Option.map_eq_some_iff] at hstep_init
      obtain ⟨⟨q', qs⟩, hstep_init, hq'⟩ := hstep_init
      simp only at hq'
      apply m.table_for_step_right prev_t w i.castSucc i.is_lt prev_init q [] List.nodup_nil (qs := qs)
      · simp [Fin.getElem_fin, hstep_init, hq']
      · intro p q hmap
        rwa [
          m.table_for_take_map w _ i.castSucc.castSucc (by simp) (by unfold prev_t; rfl),
          Fin.coeSucc_eq_succ
        ] at hmap

theorem table_for_accepting_go {m : TwoDFA α σ} (t : BackTable σ) (w : List α) (p q : σ) (acc : List σ) (hdup : acc.Nodup) (hmap : accepting_table.go m t p acc hdup = some q)
  (hind : ∀ (p q : σ), t.map p = some q → m.GoesLeftOf w.toWord (Fin.last _) { state := p, idx := Fin.ofNat _ w.length } { state := q, idx := Fin.last _ }) :
    m.GoesLeftOf w.toWord (Fin.last _) { state := p, idx := Fin.last _ } { state := q, idx := Fin.last _ } := by
  obtain ⟨p', hp'⟩ := m.in_bounds_right p
  obtain ⟨q', hq', hmap'⟩ : ∃ a, t.map p' = some a ∧ (if hmem : a ∈ acc then some a else accepting_table.go m t a (a :: acc) (hdup.cons hmem)) = some q := by
    unfold accepting_table.go at hmap
    simpa [Option.bind_eq_some_iff, hp'] using hmap
  apply GoesLeftOf.head
  · suffices m.nextConfig w.toWord ⟨p, Fin.last _⟩ ⟨p', Fin.ofNat _ w.length⟩ from this
    rw [←stepConfig_gives_nextConfig]
    unfold step at hp'
    simp only [stepConfig, Word.get_eq_right_of_eq_last, hp', Fin.ofNat_eq_cast, Config.mk.injEq, true_and]
    rw [←Fin.val_inj]
    simp only [Movement.apply, Fin.predCast, Fin.castLE, Fin.coe_pred, Fin.val_last, add_tsub_cancel_right, Fin.val_natCast]
    have : w.length < w.length + 2 := by trans <;> apply Nat.lt_add_one
    symm
    simp [Nat.mod_eq_iff_lt, this]
  · trans
    · exact hind p' q' hq'
    · if hmem : q' ∈ acc
        then
          suffices q' = q by rw [this]; exact .refl <| le_refl _
          simpa [hmem] using hmap'
        else
          apply table_for_accepting_go (acc := q' :: acc) (hind := hind)
          simpa [hmem] using hmap'
  · rfl
  termination_by Fintype.card σ - acc.length
  decreasing_by 
    have := hdup.length_le_card
    rw [List.length_cons] at this
    rw [List.length_cons]
    omega


theorem accepts_of_table_for_accepting (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (hfor : t = m.table_for w) (hacc : m.accepting_table t) :
    m.GoesLeftOf w.toWord (Fin.last _) m.init ⟨m.accept, Fin.last _⟩ := by
  simp only [accepting_table, Option.bind_eq_bind, Option.bind_eq_some_iff] at hacc
  obtain ⟨init, hinit_some, hgo_accept⟩ := hacc
  have hfor' : t = m.table_for (List.take (↑(Fin.last w.length)) w) := by
    rwa [←List.take_length (l := w)] at hfor
  trans
  · exact (m.table_for_take_init w t (Fin.last (w.length)) hfor' hinit_some).castSucc
  · apply table_for_accepting_go (hmap := hgo_accept)
    intros p q hpq
    have : w.length < w.length + 1 + 1 := by trans <;> apply Nat.lt_add_one
    have : Fin.last (w.length + 1) = (Fin.ofNat (w.length + 2) w.length) + 1 := by
      rw [←Fin.val_inj, Fin.val_last, Fin.val_add_one]
      have : (Fin.ofNat (w.length + 2) w.length) ≠ Fin.last (w.length + 1) := by 
        rw [Fin.ne_iff_vne]
        simp [Nat.mod_eq_of_lt]
      simp only [this, ↓reduceIte]
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.add_right_cancel_iff]
      rwa [Nat.mod_eq_of_lt]
    rw [this]; clear this
    let i := Fin.ofNat (w.length + 2) w.length
    have i_val : i.val = w.length := by simpa [i]
    have : m.GoesLeftOf w.toWord i { state := p, idx := i } { state := q, idx := i + 1 } := by
      apply m.table_for_take_map w t _ _ _ _ _ |>.mp
      · assumption
      · rw [Fin.ne_iff_vne, Fin.val_ofNat, Fin.val_last]
        simp [Nat.mod_eq_of_lt]
      · simpa [i_val]
    apply this.castLE
    rw [Fin.le_iff_val_le_val, Fin.val_add]
    simp [i_val]


theorem accepts_iff_table_for_accepting (m : TwoDFA α σ) (w : List α) : m.accepting_table (m.table_for w) ↔ m.GoesLeftOf w.toWord (Fin.last _) m.init ⟨m.accept, Fin.last _⟩ where
  mp := m.accepts_of_table_for_accepting w _ rfl
  mpr := sorry

/----------------------------------------------------------------
                            The Goal
----------------------------------------------------------------/
theorem to_one_way_correct (m : TwoDFA α σ) : m.language = m.to_one_way.accepts := by
  ext w
  suffices m.accepts w.toWord ↔ m.accepting_table (m.table_for w) from this
  rw [m.accepts_iff_table_for_accepting w]
  constructor
  · intro acc
    apply GoesLeftOf.attach
    exact m.reaches_accept_last_of_accepts w.toWord acc
  · intro hgoes
    use Fin.last _
    exact hgoes.forget

end Proof

end TwoDFA
