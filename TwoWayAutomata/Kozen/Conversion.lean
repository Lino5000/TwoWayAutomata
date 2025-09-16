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

theorem castLE {cfg1 cfg2 : Config σ n} {j : Fin _} (hgoes : m.GoesLeftOf w i cfg1 cfg2) (hle : i ≤ j) : m.GoesLeftOf w j cfg1 cfg2 := by
  induction hgoes with
  | refl hlt => exact .refl <| hlt.trans hle
  | tail hlt _ tl ih => exact ih.tail (hlt.trans hle) tl

theorem castSucc {cfg1 cfg2 : Config σ n} {i : Fin _} (h : m.GoesLeftOf w i.castSucc cfg1 cfg2) : m.GoesLeftOf w i.succ cfg1 cfg2 := by
  apply h.castLE
  simp [Fin.le_iff_val_le_val]

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

theorem as_tail {strt stp : Config σ n} (h : m.GoesLeftOf w i strt stp) : strt = stp ∨ ∃ next, m.GoesLeftOf w i strt next ∧ m.nextConfig w next stp := by
  cases h with
  | refl => left; rfl
  | @tail nxt _ _ hd tl => right; use nxt, by simp [hd]

theorem single_path {strt stp1 stp2 : Config σ n} (h1 : m.GoesLeftOf w i strt stp1) (h2 : m.GoesLeftOf w i strt stp2) :
    stp1 = stp2 ∨ m.GoesLeftOf w i stp1 stp2 ∨ m.GoesLeftOf w i stp2 stp1 := by
  by_cases hidx : stp1.idx ≤ i ∧ stp2.idx ≤ i
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

theorem transfer {c1 c2 : Config σ n} {j : Fin _} (hcyc : m.CyclesLeftOf w j c1) (hgo : m.GoesTo w c1 c2) : m.CyclesLeftOf w j c2 := by
  induction hgo with
  | refl => exact hcyc
  | tail _ tl ih => exact ih.step tl

theorem from_paths_of_ne {c1 c2 : Config σ n} (hne : c1 ≠ c2) (h1 : m.GoesLeftOf w i c1 c2) (h2 : m.GoesLeftOf w i c2 c1) : m.CyclesLeftOf w i c1 := by
  rcases h1.as_head with heq | hnext | ⟨nxt, hd, tl⟩
  · contradiction -- heq and hne
  · constructor
    · exact h1.start_le
    · use c2  -- Finds hnext and h2
  · constructor
    · exact h1.start_le
    · exists nxt
      constructor
      · exact hd
      · exact tl.trans h2

theorem always_left {c1 c2 : Config σ n} {j : Fin _} (hcyc : m.CyclesLeftOf w j c1) (hgo : m.GoesTo w c1 c2) : c2.idx ≤ j := by
  obtain ⟨hlt, _⟩ := hcyc.transfer hgo
  exact hlt

theorem castLE {c1 : Config σ n} {i j : Fin _} (hcyc : m.CyclesLeftOf w i c1) (hle : i ≤ j) : m.CyclesLeftOf w j c1 := by
  obtain ⟨hlt, nxt, hnxt, hloop⟩ := hcyc
  constructor
  · exact hlt.trans hle
  · exists nxt
    constructor
    · exact hnxt
    · exact hloop.castLE hle

theorem castSucc {c1 : Config σ n} {i : Fin _} (hcyc : m.CyclesLeftOf w i.castSucc c1) : m.CyclesLeftOf w i.succ c1 := by
  apply hcyc.castLE
  simp [Fin.le_iff_val_le_val]

theorem split {c1 c2 : Config σ n} {i : Fin _} (hcyc : m.CyclesLeftOf w i c1) (hgo : m.GoesTo w c1 c2) : m.GoesLeftOf w i c2 c1 := by
  have hle := always_left hcyc hgo
  induction hgo using GoesTo.head_induction_on with
  | refl => exact GoesLeftOf.refl hle
  | head hd tl ih =>
    trans
    · exact ih <| hcyc.step hd
    · obtain ⟨hlt', nxt, hnxt, hrest⟩ := hcyc
      have := nextConfig_right_unique hnxt hd
      rwa [this] at hrest

end CyclesLeftOf

namespace GoesLeftOf

variable {n : Nat} {m : TwoDFA α σ} {w : Word α n} {i : Fin (n+2)} 

-- Idea is that the accumulator holds exactly the states that are passed through *at index j*, and hacc holds proofs that we can get from any of those to the current start configuration
theorem prefix_left_of_go [Fintype σ] {strt stp : Config σ n} {j : Fin _} (hgo : m.GoesLeftOf w i strt stp) (hlt : j < i) (hstrt : strt.idx ≤ j) (hstp : j < stp.idx)
  (acc : List (State σ)) (hdup : acc.Nodup) (hacc : ∀ q ∈ acc, m.GoesLeftOf w j ⟨q, j⟩ strt) :
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
            suffices m.CyclesLeftOf w j strt by apply this.always_left hgo.forget
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
            by_cases hstrtlt : strt.idx < j
            case' pos =>
              have _term : mid.idx.rev < strt.idx.rev := by
                rw [Fin.rev_lt_rev, hmideq]
                exact hstrtlt
            case' neg =>
              have _term1 : mid.idx.rev = strt.idx.rev := by 
                suffices strt.idx = j by rwa [Fin.rev_eq_iff, Fin.rev_rev, this]
                cases Fin.lt_or_eq_of_le hstrt
                · contradiction
                · assumption
              have _term2 : Fintype.card (State σ) - (acc.length + 1) < Fintype.card (State σ) - acc.length := by
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
  termination_by (j, strt.idx.rev, Fintype.card (State σ) - acc.length)
  decreasing_by 
    all_goals try decreasing_tactic
    -- only goal that fails is for the recursion in stepLeft | j = j'.succ | strt.idx = j
    simp [Prod.lex_def, _term1, _term2]

theorem prefix_left_of [Fintype σ] {strt stp : Config σ n} (hgo : m.GoesLeftOf w i strt stp) (j : Fin _) (hlt : j < i) (hstrt : strt.idx ≤ j) (hstp : j < stp.idx) :
    ∃ mid, j < mid.idx ∧ m.GoesLeftOf w j strt mid ∧ m.GoesLeftOf w i mid stp :=
  prefix_left_of_go hgo hlt hstrt hstp [] List.nodup_nil <| by
    intro _ hmem; simp only [List.not_mem_nil] at hmem  -- vacuous implication

lemma step_mpr_go {m : TwoDFA α σ} {w : Word α n} {i : Fin _} (j : Nat) (qs : List (State σ)) (hj : j < qs.length.pred)
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
  init : Option (State σ)
  --- What state the 2DFA will be in when it exits the prefix, based on what state it re-entered (from the right) in.
  map : State σ → Option (State σ)

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
def step_right [DecidableEq σ] [Fintype σ] (m : TwoDFA α σ) (t : BackTable σ) (a : α) (q : State σ) : Option (State σ) := 
  -- acc collects the list of states we have already passed through (most recent at head),
  -- so hdup asserts that we never pass through the same state twice
  go q [] List.nodup_nil |>.map Prod.fst
  where
    go [fin_states : Fintype (State σ)] (q : State σ) (acc : List (State σ)) (hdup : acc.Nodup) : Option (State σ × List (State σ)) :=
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
The end state of a table is the state at the start of the inevitable loop the
2DFA ends up in at the right endmarker.
-/
def end_state [DecidableEq σ] [Fintype σ] (m : TwoDFA α σ) (t : BackTable σ) : Option (State σ) :=
  -- This absolutely will get stuck in a loop of some form; even the accept and reject states sit in a loop at the right endmarker forever
  -- What we want to know is whether it loops at the right end, and if so what state it loops with.
  t.init >>= (go · [] List.nodup_nil)
  where
    go [fin_states : Fintype (State σ)] (q : State σ) (acc : List (State σ)) (hdup : acc.Nodup) : Option (State σ) := do
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
def to_accept_DFA [DecidableEq σ] [Fintype σ] (m : TwoDFA α σ) : DFA α (BackTable σ) where
  step := m.step_table
  start := m.first_table
  --- A table is accepting iff its end state is the accept state
  accept := {t | m.end_state t = some .accept}

/--
Convert a TwoDFA `m` into a One-Way DFA that accepts the words which are
explicitly rejected by `m`, as opposed to accepting or diverging.
-/
def to_reject_DFA [DecidableEq σ] [Fintype σ] (m : TwoDFA α σ) : DFA α (BackTable σ) where
  step := m.step_table
  start := m.first_table
  accept := {t | m.end_state t = some .reject}

--- Convert a TwoDFA `m` into a One-Way DFA that accepts the words on which `m` diverges.
def to_diverge_DFA [DecidableEq σ] [Fintype σ] (m : TwoDFA α σ) : DFA α (BackTable σ) where
  step := m.step_table
  start := m.first_table
  accept := {t | m.end_state t ≠ some .accept ∧ m.end_state t ≠ some .reject}

section Proof

variable [DecidableEq σ] [Fintype σ]

def table_for (m : TwoDFA α σ) (w : List α) : BackTable σ := w.foldl m.step_table m.first_table

theorem table_for_nil (m : TwoDFA α σ) : m.table_for [] = m.first_table := by
  simp [table_for]

theorem table_for_step {m : TwoDFA α σ} (w : List α) (a : α) : m.step_table (m.table_for w) a = m.table_for (w ++ [a]) := by
  simp [table_for]

theorem table_for_step_right {m : TwoDFA α σ} (t : BackTable σ) (w : List α) (i : Fin (w.length+1)) (hi : i < w.length) (p q : State σ) (acc : List (State σ)) (hdup : acc.Nodup)
  {qs : List (State σ)} (hmap : step_right.go m t w[↑i] p acc hdup = some (q, qs))
  (hind : ∀ (p q : State σ), t.map p = some q → m.GoesLeftOf w.toWord i.castSucc { state := p, idx := i.castSucc } { state := q, idx := i.succ }) :
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
            · rename (m.step _ _).2 = _ => heq
              simp [hstep.right] at heq  -- contradiction
          · apply GoesLeftOf.castSucc
            exact hind _ _ hmap'
          · rfl
        · apply table_for_step_right (hind := hind) (hmap := hsome')
  termination_by Fintype.card (State σ) - acc.length
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

lemma table_for_take_step_right_go_some {m : TwoDFA α σ} {w : List α} {t : BackTable σ} {i : Fin (w.length + 1)} (hi : i.val < w.length) (ht : t = m.table_for (w.take i))
  (hind : ∀ (p q : State σ), t.map p = some q → m.GoesLeftOf w.toWord i.castSucc { state := p, idx := i.castSucc } { state := q, idx := i.castSucc + 1 })
  (p q : State σ) (acc qs : List (State σ)) (hdup : acc.Nodup) (hstep : step_right.go m t w[i.val] p acc hdup = some (q, qs)) :
    m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩ := by
  have hint : i.succ.internal := by
    suffices i ≠ Fin.last _ by simp [Fin.internal, this]
    apply Fin.ne_last_of_lt (b := Fin.last _)
    rw [Fin.lt_iff_val_lt_val]
    simp [hi]
  unfold step_right.go at hstep
  split at hstep
  case h_1 hstep' =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hstep
    rw [hstep.left, ←Word.toWord_get_internal w i hint] at hstep'
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
        apply table_for_take_step_right_go_some (hstep := hstep_r) (hind := hind)
        exact ht
    · rfl
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by 
    have := (hdup.cons hmem).length_le_card
    rw [List.length_cons] at this
    rw [List.length_cons]
    omega

theorem table_for_take_map_some (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 2)) (hnelast : i ≠ Fin.last _)
  (ht : t = m.table_for (w.take i)) (p q : State σ)  :
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
    have _ : i.val < w.length := by
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
      apply table_for_take_step_right_go_some (hind := hind) (hstep := hgo)
      rfl

theorem cycles_of_step_right_go_eq_none (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin _) (ht : t = m.table_for (w.take i)) (p : State σ)
  (acc : List (State σ)) (hdup : acc.Nodup) (hloop : ∀ q ∈ acc, m.GoesLeftOf w.toWord i.succ ⟨q, i.succ⟩ ⟨p, i.succ⟩)
  (hi : i.val < w.length) (hnone : step_right.go m t w[i.val] p acc hdup = none)
  (hind : ∀ (q : State σ), m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.castSucc⟩ → t.map q = none →
            ∃ p' j, m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨p', j⟩ ∧ j ≤ i.succ ∧ m.CyclesLeftOf w.toWord j ⟨p', j⟩) :
    ∃ s j, m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨s, j⟩ ∧ j ≤ i.succ ∧ m.CyclesLeftOf w.toWord j ⟨s, j⟩ := by
  unfold step_right.go at hnone
  split at hnone
  case h_1 => simp at hnone -- contradiction : some _ = none
  case h_2 p' hstep =>
    simp only [Option.bind_eq_bind, Option.bind_eq_none_iff, dite_eq_left_iff] at hnone
    have hnext : m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.castSucc⟩ := by
      left
      · suffices i ≠ Fin.last _ by simpa [Word.toWord_get_internal, Fin.internal, this] using hstep
        rw [Fin.ne_iff_vne]
        exact Nat.ne_of_lt hi
      · simp [Movement.apply, ←Fin.val_inj]
      · constructor <;> simp
    cases hmap : t.map p' with
    | none =>
      apply hind p' _ hmap
      apply GoesLeftOf.single
      · simp
      · exact hnext
    | some q =>
      have p_to_q : m.GoesLeftOf w.toWord i.succ { state := p, idx := i.succ } { state := q, idx := i.succ } := by
        apply GoesLeftOf.head
        · exact hnext
        · have hgo := m.table_for_take_map_some w t i.castSucc (by simp) ht p' q hmap
          simpa using hgo.castSucc
        · simp
      if hmem : q ∈ acc
        then
          exists q, i.succ
          constructorm* _ ∧ _
          · exact p_to_q
          · rfl
          · if heq : q = p
              then
                constructor
                · simp
                · exists ⟨p', i.castSucc⟩
                  constructor
                  · rwa [←heq] at hnext
                  · apply GoesLeftOf.castSucc
                    simpa using m.table_for_take_map_some w t i.castSucc (by simp) ht p' q hmap
              else
                apply CyclesLeftOf.from_paths_of_ne (c2 := ⟨p, i.succ⟩)
                · simp [heq]
                · exact hloop _ hmem
                · exact p_to_q
        else
          have hloop' : ∀ q' ∈ q :: acc, m.GoesLeftOf w.toWord i.succ ⟨q', i.succ⟩ ⟨q, i.succ⟩ := by
            intro q' hmem
            rw [List.mem_cons] at hmem
            rcases hmem with heq | hmem
            · rw [heq]; apply GoesLeftOf.refl; simp
            · exact (hloop q' hmem).trans p_to_q
          have hind' : ∀ p', m.GoesLeftOf w.toWord i.succ ⟨q, i.succ⟩ ⟨p', i.castSucc⟩ → t.map p' = none →
                          ∃ s j, m.GoesLeftOf w.toWord i.succ ⟨q, i.succ⟩ ⟨s, j⟩ ∧ j ≤ i.succ ∧ m.CyclesLeftOf w.toWord j ⟨s, j⟩ := by
            intro p' hstrt hmap
            obtain ⟨s, j, hpref, hlt, hcyc⟩ := hind p' (p_to_q.trans hstrt) hmap
            exists s, j
            refine ⟨?_, hlt, hcyc⟩
            rcases p_to_q.single_path hpref with heq | hgo | hgo
            · rw [←heq]
              apply GoesLeftOf.refl
              simp
            · exact hgo
            · exact hcyc.castLE hgo.start_le |>.split hgo.forget
          obtain ⟨s, j, hpref, hcyc⟩ := m.cycles_of_step_right_go_eq_none w t i ht q (q :: acc) (hdup.cons hmem) hloop' hi (hnone q hmap hmem) hind'
          exists s, j
          constructor
          · exact p_to_q.trans hpref
          · exact hcyc
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    have := (hdup.cons hmem).length_le_card
    rw [List.length_cons] at this
    rw [List.length_cons]
    omega

theorem table_for_take_map_none (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 2)) (hnelast : i ≠ Fin.last _)
  (ht : t = m.table_for (w.take i)) (p : State σ) :
    t.map p = none → ∃ p' j, m.GoesLeftOf w.toWord i ⟨p, i⟩ ⟨p', j⟩ ∧ j ≤ i ∧ m.CyclesLeftOf w.toWord j ⟨p', j⟩ := by
  induction i using Fin.inductionOn generalizing t p  with
  | zero =>
    simp only [table_for, first_table, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.take_zero, List.foldl_nil] at ht
    simp [ht] -- Find the implication to be vacuous
  | succ i ih =>
    have hlt : i.val < w.length := by
      apply i.val_lt_last
      rwa [←i.succ_ne_last_iff]
    let prev_t := List.foldl m.step_table m.first_table (w.take i)
    have hstep : t = m.step_table prev_t w[i.val] := by
      simp only [table_for, Fin.val_succ, List.take_succ, List.foldl_append, Option.foldl_toList] at ht
      have hget : w[i.val]? = some w[i.val] := by simp
      rw [hget] at ht
      simpa using ht
    rw [hstep]; clear hstep
    intro hmap
    conv at hmap =>
      simp only [step_table, Option.bind_eq_bind]
      unfold step_right
      rw [Option.map_eq_none_iff]
    -- simp finds hloop is a vacuous implication
    have hind : ∀ (q : State σ), m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.castSucc⟩ → prev_t.map q = none →
                    ∃ p' j, m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨p', j⟩ ∧ j ≤ i.succ ∧ m.CyclesLeftOf w.toWord j ⟨p', j⟩ := by
      intro q hstrt hnone
      obtain ⟨s, j, hpref, hlt, hcyc⟩ := ih prev_t (by simp) rfl q hnone
      exists s, j
      constructorm* _ ∧ _
      · exact hstrt.trans hpref.castSucc
      · exact hlt.trans i.castSucc_le_succ
      · exact hcyc
    exact m.cycles_of_step_right_go_eq_none w prev_t i rfl p [] List.nodup_nil (by simp) hlt hmap hind

theorem step_right_go_acc_is_tail {m : TwoDFA α σ} {t : BackTable σ} {a : α} {p q : State σ} {acc qs : List (State σ)} {hdup : acc.Nodup}
    (h : step_right.go m t a p acc hdup = some (q, qs)) : ∃ hd, qs = hd ++ acc := by
  cases acc with
  | nil => use qs, by simp
  | cons hd tl =>
    unfold step_right.go at h
    split at h
    next p' hstep =>
      exists []
      symm
      apply And.right
      simpa using h
    next p' hstep =>
      obtain ⟨q', hmap, hne, hrec⟩ : ∃ q', t.map p' = some q' ∧ ∃ hne : q' ∉ (hd :: tl), step_right.go m t a q' (q' :: hd :: tl) (hdup.cons hne) = some (q, qs) := by
        simpa [Option.bind_eq_some_iff] using h
      obtain ⟨pref, hpref⟩ := step_right_go_acc_is_tail hrec
      exists pref ++ [q']
      simpa using hpref
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by 
    have := (hdup.cons hne).length_le_card
    rename acc = _ => hacc
    rw [hacc]
    repeat rw [List.length_cons] at this
    repeat rw [List.length_cons]
    omega

theorem step_right_go_acc_contained {m : TwoDFA α σ} {t : BackTable σ} {a : α} {p q : State σ} {acc qs : List (State σ)} {hdup : acc.Nodup}
    (h : step_right.go m t a p acc hdup = some (q, qs)) : acc ⊆ qs := by
  obtain ⟨_, happend⟩ := step_right_go_acc_is_tail h
  simp [happend]

theorem step_right_go_eq_none {m : TwoDFA α σ} {w : List α} {i : Fin _} {p : State σ} (hi : i.val < w.length)
  {acc : List (State σ)} {hdup : acc.Nodup} (hacc : ∀ q ∈ acc, m.GoesLeftOf w.toWord i.succ ⟨q, i.succ⟩ ⟨p, i.succ⟩)
  (hstepright : step_right.go m (m.table_for <| w.take i) w[i.val] p acc hdup = none) (q : State σ) :
    ¬ m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩ := by
  unfold step_right.go at hstepright
  match hstep : m.step w[i.val] p with
  | (p', .right) => simp [hstep] at hstepright  -- contradiction; some _ = none
  | (p', .left) =>
    simp only [hstep, Option.bind_eq_bind, Option.bind_eq_none_iff, dite_eq_left_iff] at hstepright
    have hnext : m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.castSucc⟩ := by
      have hint : i.succ.internal := by
        suffices i.succ ≠ Fin.last _ by simp [Fin.internal, this]
        rw [Fin.ne_iff_vne, Fin.val_last, Fin.val_succ, Nat.add_one_ne_add_one_iff]
        exact Nat.ne_of_lt hi
      left
      · simpa [Word.toWord_get_internal w _ hint]
      · simp [Movement.apply, ←Fin.val_inj]
      · constructor <;> simp
    by_contra hgo
    rcases hgo.as_head with heq | hnext' | ⟨nxt, hnext', hgo'⟩
    · simp at heq  -- i.succ ≠ i.succ + 1
    · have hi' : i.val ≠ w.length := Nat.ne_of_lt hi
      have hne : i.castSucc ≠ i.succ + 1 := by
        simp only [ne_eq, ← Fin.val_inj, Fin.coe_castSucc, Fin.val_add_one, Fin.val_succ, Fin.val_last, Nat.add_right_cancel_iff, hi', ↓reduceIte]
        omega
      have := nextConfig_right_unique hnext hnext'
      simp [hne] at this
    · have : nxt = ⟨p', i.castSucc⟩ := nextConfig_right_unique hnext' hnext
      rw [this] at hgo'; clear this hnext' nxt
      cases hmap : (m.table_for (w.take i)).map p' with
      | none =>
        have diverges : ∀ s, ¬ m.GoesLeftOf w.toWord i.castSucc ⟨p', i.castSucc⟩ ⟨s, i.succ⟩ := by
          intro s
          by_contra hgos
          obtain ⟨base, j, hreach, hlt, hcyc⟩ := m.table_for_take_map_none w _ i.castSucc (by simp) rfl _ hmap
          rcases hgos.single_path hreach with heq | hgo | hgo
          -- all cases end up with the contradiction i.succ ≤ i
          · simp only [Config.mk.injEq] at heq
            simp [←heq.right] at hlt
          · simpa using hgo.start_le
          · suffices i.succ ≤ i.castSucc by simpa
            exact hcyc.always_left hgo.forget |>.trans hgo.start_le
        obtain ⟨mid, hmid, hpref, hrest⟩ := hgo'.prefix_left_of i.castSucc (by simp) (by simp) <| by
          have : i.castSucc < i.succ := by simp
          apply this.trans; clear this
          suffices i.succ < Fin.last _ by simp [this]
          simpa [Fin.lt_def, Fin.val_succ, Fin.val_last] using hi
        have : mid = ⟨mid.state, i.succ⟩ := by
          suffices mid.idx = i.succ by rw [←this]
          simpa using hpref.stop_idx_of_gt hmid
        apply diverges mid.state
        rwa [this] at hpref
      | some q' => 
        have hmap_goes := m.table_for_take_map_some w (m.table_for <| w.take i) i.castSucc (by simp) (by simp) p' q' hmap
        rw [(by simp : i.castSucc + 1 = i.succ)] at hmap_goes
        if hmem : q' ∈ acc
          then
            have hcyc : m.CyclesLeftOf w i.succ ⟨p, i.succ⟩ := by
              constructor
              · simp
              · exists ⟨p', i.castSucc⟩
                constructor
                · exact hnext
                · apply hmap_goes.castSucc.trans
                  exact hacc q' hmem
            suffices i.succ ≠ Fin.last _ by simpa [this] using hcyc.always_left hgo.forget
            rw [Fin.ne_iff_vne, Fin.val_last, Fin.val_succ, Nat.add_one_ne_add_one_iff]
            exact Nat.ne_of_lt hi
          else
            have hacc' : ∀ s ∈ q' :: acc, m.GoesLeftOf w.toWord i.succ ⟨s, i.succ⟩ ⟨q', i.succ⟩ := by
              intro s hmem
              rw [List.mem_cons] at hmem
              rcases hmem with heq | hmem
              · rw [heq]; apply GoesLeftOf.refl; simp
              · apply (hacc s hmem).trans
                apply hmap_goes.castSucc.head
                · exact hnext
                · simp
            apply step_right_go_eq_none hi hacc' (hstepright q' hmap hmem) q
            rcases hgo'.single_path hmap_goes.castSucc with heq | hpath | hpath
            · simp at heq -- contradiction
            · suffices i ≠ Fin.last _ by simpa [this] using hpath.start_le -- : i.succ + 1 ≤ i.succ
              rw [Fin.ne_iff_vne, Fin.val_last]
              exact Nat.ne_of_lt hi
            · exact hpath
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    have := (hdup.cons hmem).length_le_card
    repeat rw [List.length_cons] at this
    repeat rw [List.length_cons]
    omega

theorem step_right_go_eq_some_last_step' {m : TwoDFA α σ} {w : List α} {i : Fin _} {hi : i.val < w.length} {p q : State σ} {qs : List (State σ)}
  {acc : List (State σ)} {hdup : (p :: acc).Nodup} (hstepright : step_right.go m (m.table_for <| w.take i) w[i.val] p (p :: acc) hdup = some (q, qs)) :
    m.nextConfig w.toWord ⟨(p :: qs.reverse).getLast (by simp), i.succ⟩ ⟨q, i.succ + 1⟩ := by
  unfold step_right.go at hstepright
  split at hstepright
  next p' hstep =>
    obtain ⟨hp, hqs⟩ : p' = q ∧ (p :: acc) = qs := by simpa using hstepright
    suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.succ + 1⟩ by simpa [←hp, ←hqs]
    have hint : i.succ.internal := by
      suffices i ≠ Fin.last _ by simpa [Fin.internal]
      simpa [Fin.ne_iff_vne, Fin.val_last] using Nat.ne_of_lt hi
    right
    · simpa [Word.toWord_get_internal (int := hint)] using hstep
    · suffices i.val + 1 + 1 = (i.succ + 1).val by simpa [Movement.apply, ←Fin.val_inj]
      rw [Fin.val_add_one]
      simp [hint.right]
    · constructor <;> simp [hint.right]
  next =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.dite_none_left_eq_some] at hstepright
    obtain ⟨q', hmap, hmem, hrec⟩ := hstepright
    have : (p :: qs.reverse).getLast (by simp) = (q' :: qs.reverse).getLast (by simp) := by
      suffices qs ≠ [] by simp [this]
      obtain ⟨_, hqs⟩ := step_right_go_acc_is_tail hrec
      simp [hqs]
    rw [this]
    apply step_right_go_eq_some_last_step' hrec
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    have := (hdup.cons hmem).length_le_card
    repeat rw [List.length_cons] at this
    repeat rw [List.length_cons]
    omega

theorem step_right_go_eq_some_last_step {m : TwoDFA α σ} {w : List α} {i : Fin _} {hi : i.val < w.length} {p q : State σ} {qs : List (State σ)}
  (hstepright : step_right.go m (m.table_for <| w.take i) w[i.val] p [] List.nodup_nil = some (q, qs)) :
    m.nextConfig w.toWord ⟨(p :: qs.reverse).getLast (by simp), i.succ⟩ ⟨q, i.succ + 1⟩ := by
  unfold step_right.go at hstepright
  split at hstepright
  next p' hstep =>
    obtain ⟨hp, hqs⟩ : p' = q ∧ [] = qs := by simpa using hstepright
    suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.succ + 1⟩ by simpa [←hp, ←hqs]
    have hint : i.succ.internal := by
      suffices i ≠ Fin.last _ by simpa [Fin.internal]
      simpa [Fin.ne_iff_vne, Fin.val_last] using Nat.ne_of_lt hi
    right
    · simpa [Word.toWord_get_internal (int := hint)] using hstep
    · suffices i.val + 1 + 1 = (i.succ + 1).val by simpa [Movement.apply, ←Fin.val_inj]
      rw [Fin.val_add_one]
      simp [hint.right]
    · constructor <;> simp [hint.right]
  next =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.dite_none_left_eq_some] at hstepright
    obtain ⟨q', hmap, hmem, hrec⟩ := hstepright
    have : (p :: qs.reverse).getLast (by simp) = (q' :: qs.reverse).getLast (by simp) := by
      suffices qs ≠ [] by simp [this]
      obtain ⟨_, hqs⟩ := step_right_go_acc_is_tail hrec
      simp [hqs]
    rw [this]
    apply step_right_go_eq_some_last_step' hrec

theorem step_right_go_eq_some_links' {m : TwoDFA α σ} {w : List α} {i : Fin _} {hi : i.val < w.length} {p q : State σ} {qs : List (State σ)}
  {acc : List (State σ)} {hdup : (p :: acc).Nodup} (hstepright : step_right.go m (m.table_for <| w.take i) w[i.val] p (p :: acc) hdup = some (q, qs))
  (j : Nat) (hj : j < qs.length.pred) (hacclen : acc.length ≤ j) :
    ∃ q', m.nextConfig w.toWord ⟨qs.reverse[j]'(by simp [Nat.lt_of_lt_pred hj]), i.succ⟩ ⟨q', i.castSucc⟩ ∧
      m.GoesLeftOf w.toWord i.castSucc ⟨q', i.castSucc⟩ ⟨qs.reverse[j.succ]'(by simp [Nat.succ_lt_of_lt_pred hj]), i.succ⟩ := by
  unfold step_right.go at hstepright
  split at hstepright
  next =>
    have : (p :: acc) = qs := by apply And.right; simpa using hstepright
    have : j < acc.length := by simpa [←this] using hj
    omega -- Finds contradiction : acc.length ≤ j < acc.length
  next p' hstep =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.dite_none_left_eq_some] at hstepright
    obtain ⟨q', hmap, hmem, hrec⟩ := hstepright
    if hacclen' : (q' :: acc).length ≤ j
      then
        exact step_right_go_eq_some_links' hrec j hj hacclen'
      else
        obtain ⟨pref, happend⟩ := step_right_go_acc_is_tail hrec
        have hj : j = acc.length := by
          rw [List.length_cons] at hacclen'
          apply Nat.eq_of_le_of_lt_succ
          · exact hacclen
          · rwa [Nat.not_le_eq] at hacclen'
        exists p'
        have hrest := m.table_for_take_map_some w _ i.castSucc (by simp) rfl _ _ hmap
        suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.castSucc⟩ by simpa [hj, happend, this] using hrest
        left
        · have hint : i.succ.internal := by
            suffices i ≠ Fin.last _ by simpa [Fin.internal]
            simpa [Fin.ne_iff_vne, Fin.val_last] using Nat.ne_of_lt hi
          simpa [Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj]
        · constructor <;> simp
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    have := (hdup.cons hmem).length_le_card
    repeat rw [List.length_cons] at this
    repeat rw [List.length_cons]
    omega

theorem step_right_go_eq_some_links {m : TwoDFA α σ} {w : List α} {i : Fin _} {hi : i.val < w.length} {p q : State σ} {qs : List (State σ)}
  (hstepright : step_right.go m (m.table_for <| w.take i) w[i.val] p [] List.nodup_nil = some (q, qs)) (j : Nat) (hj : j < qs.length.pred) :
    ∃ q', m.nextConfig w.toWord ⟨qs.reverse[j]'(by simp [Nat.lt_of_lt_pred hj]), i.succ⟩ ⟨q', i.castSucc⟩ ∧
      m.GoesLeftOf w.toWord i.castSucc ⟨q', i.castSucc⟩ ⟨qs.reverse[j.succ]'(by simp [Nat.succ_lt_of_lt_pred hj]), i.succ⟩ := by
  unfold step_right.go at hstepright
  split at hstepright
  next =>
    have : [] = qs := by apply And.right; simpa using hstepright
    simp [←this] at hj -- contradiction : j < 0
  next p' hstep =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.dite_none_left_eq_some] at hstepright
    obtain ⟨q', hmap, hmem, hrec⟩ := hstepright
    apply step_right_go_eq_some_links' hrec
    · exact hj
    · simp

omit [Fintype σ] in
lemma GoesLeftOf.fold_list {m : TwoDFA α σ} {w : List α} {i : Fin _} (qs : List (State σ)) (hqs : qs ≠ [])
  (hlink : ∀ j, ∀ hj : j < qs.length.pred, m.GoesLeftOf w.toWord i ⟨qs[j]'(Nat.lt_of_lt_pred hj), i⟩ ⟨qs[j.succ]'(Nat.succ_lt_of_lt_pred hj), i⟩) :
    m.GoesLeftOf w.toWord i ⟨qs.head hqs, i⟩ ⟨qs.getLast hqs, i⟩ := by
  induction qs with
  | nil => contradiction
  | cons q qs ih =>
    if hqs' : qs = []
      then
        simp only [hqs', List.head_cons, List.getLast_singleton]
        apply GoesLeftOf.refl
        simp
      else
        simp only [List.head_cons, ne_eq, hqs', not_false_eq_true, List.getLast_cons]
        apply GoesLeftOf.trans (mid := ⟨qs.head hqs', i⟩)
        · have hlen : 0 < qs.length := List.length_pos_of_ne_nil hqs'
          have : qs.head hqs' = (q :: qs)[1]'(by simp [hlen]) := by
            simp [List.head_eq_getElem_zero hqs']
          rw [this]; clear this
          exact hlink 0 <| by simp [hlen]
        · apply ih hqs'
          intro j hj
          have := hlink j.succ <| by simpa using Nat.succ_lt_of_lt_pred hj
          simpa

lemma step_right_go_nodup {m : TwoDFA α σ} {w : List α} {i : Fin (w.length + 1)} (hi : i.val < w.length) {p q : State σ} {qs : List (State σ)}
  {acc : List (State σ)} {hdup : (p :: acc).Nodup} (hstepright : step_right.go m (m.table_for (List.take (↑i) w)) w[↑i] p (p :: acc) hdup = some (q, qs)) :
    qs.reverse.Nodup := by
  unfold step_right.go at hstepright
  split at hstepright
  next p' heq =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hstepright
    rwa [←hstepright.right, List.nodup_reverse]
  next p' heq =>
    simp only [Fin.getElem_fin, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.dite_none_left_eq_some] at hstepright
    obtain ⟨p'', hmap, hmem, hrec⟩ := hstepright
    apply step_right_go_nodup hi hrec
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    have := (hdup.cons hmem).length_le_card
    repeat rw [List.length_cons] at this
    repeat rw [List.length_cons]
    omega

lemma step_right_go_none_of_cycle {m : TwoDFA α σ} {w : List α} {i : Fin (w.length + 1)} (hi : i.val < w.length) (p : State σ)
  (acc : List (State σ)) (hdup : acc.Nodup) (hcyc : m.CyclesLeftOf w i.succ ⟨p, i.succ⟩) :
    step_right.go m (m.table_for (List.take (↑i) w)) w[↑i] p acc hdup = none := by
  have hint : i.succ.internal := by
    suffices i ≠ Fin.last _ by simpa [Fin.internal]
    rw [Fin.ne_iff_vne, Fin.val_last]
    exact Nat.ne_of_lt hi
  unfold step_right.go
  split
  next p'' hstep =>
    exfalso
    suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p'', i.succ + 1⟩ by
      obtain ⟨hlt, _⟩ := hcyc.step this
      simp [hint.right] at hlt
    right
    · simpa [Word.toWord_get_internal (int := hint)] using hstep
    · simp [Movement.apply, ←Fin.val_inj, Fin.val_add_one, hint.right]
    · constructor <;> simp [hint.right]
  next p'' hstep =>
    simp only [Fin.getElem_fin, Option.bind_eq_bind, Option.bind_eq_none_iff, dite_eq_left_iff]
    intro q' hmap hmem
    apply step_right_go_none_of_cycle hi
    suffices m.GoesLeftOf w i.succ ⟨p, i.succ⟩ ⟨q', i.succ⟩ from hcyc.transfer this.forget
    apply GoesLeftOf.head
    · apply TwoDFA.nextConfig.stepLeft (c2 := ⟨p'', i.castSucc⟩)
      · have hint : i.succ.internal := by
          suffices i ≠ Fin.last _ by simpa [Fin.internal]
          rw [Fin.ne_iff_vne, Fin.val_last]
          exact Nat.ne_of_lt hi
        simpa [Word.toWord_get_internal (int := hint)] using hstep
      · simp [Movement.apply, ←Fin.val_inj]
      · constructor <;> simp
    · apply GoesLeftOf.castSucc
      rw [(by simp : i.succ = i.castSucc + 1)]
      exact m.table_for_take_map_some w _ i.castSucc (by simp) rfl _ _ hmap
    · simp
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    have := (hdup.cons hmem).length_le_card
    repeat rw [List.length_cons] at this
    repeat rw [List.length_cons]
    omega

lemma step_right_go_some_not_mem.go {m : TwoDFA α σ} {w : List α} {i : Fin (w.length + 1)} (hi : i.val < w.length) {p p' q : State σ} {qs : List (State σ)}
  {acc : List (State σ)} {hdup : acc.Nodup} (hstepright : step_right.go m (m.table_for (List.take (↑i) w)) w[↑i] p' acc hdup = some (q, qs))
  (hpgoes : m.GoesLeftOf w i.succ ⟨p, i.succ⟩ ⟨p', i.succ⟩) (hpmem : p ∉ acc) :
    p ∉ qs := by
  have hint : i.succ.internal := by
    suffices i ≠ Fin.last _ by simpa [Fin.internal]
    rw [Fin.ne_iff_vne, Fin.val_last]
    exact Nat.ne_of_lt hi
  unfold step_right.go at hstepright
  split at hstepright
  next =>
    suffices acc = qs by simpa [this] using hpmem
    apply And.right; simpa using hstepright
  next p'' hstep =>
    simp only [Fin.getElem_fin, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.dite_none_left_eq_some] at hstepright
    obtain ⟨q', hmap, hmem, hrec⟩ := hstepright
    if heq : p = q'
      then
        exfalso
        suffices m.CyclesLeftOf w.toWord i.succ ⟨q', i.succ⟩ by
          simpa [hrec] using m.step_right_go_none_of_cycle hi q' (q' :: acc) (hdup.cons hmem) this
        rw [heq] at hpgoes
        apply CyclesLeftOf.from_paths_of_ne (c2 := ⟨p'', i.castSucc⟩)
        · simp [Fin.ne_iff_vne]
        · apply hpgoes.tail
          · simp
          · left
            · simpa [Word.toWord_get_internal (int := hint)] using hstep
            · simp [Movement.apply, ←Fin.val_inj]
            · constructor <;> simp
        · apply GoesLeftOf.castSucc
          rw [(by simp : i.succ = i.castSucc + 1)]
          exact m.table_for_take_map_some w _ i.castSucc (by simp) rfl _ _ hmap
      else
        apply step_right_go_some_not_mem.go hi hrec
        · apply hpgoes.trans
          apply GoesLeftOf.head
          · apply TwoDFA.nextConfig.stepLeft (c2 := ⟨p'', i.castSucc⟩)
            · have hint : i.succ.internal := by
                suffices i ≠ Fin.last _ by simpa [Fin.internal]
                rw [Fin.ne_iff_vne, Fin.val_last]
                exact Nat.ne_of_lt hi
              simpa [Word.toWord_get_internal (int := hint)] using hstep
            · simp [Movement.apply, ←Fin.val_inj]
            · constructor <;> simp
          · apply GoesLeftOf.castSucc
            rw [(by simp : i.succ = i.castSucc + 1)]
            exact m.table_for_take_map_some w _ i.castSucc (by simp) rfl _ _ hmap
          · simp
        · simp [heq, hpmem]
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    have := (hdup.cons hmem).length_le_card
    repeat rw [List.length_cons] at this
    repeat rw [List.length_cons]
    omega

lemma step_right_go_some_not_mem {m : TwoDFA α σ} {w : List α} {i : Fin (w.length + 1)} (hi : i.val < w.length) {p q : State σ} {qs : List (State σ)}
  (hstepright : step_right.go m (m.table_for (List.take (↑i) w)) w[↑i] p [] List.nodup_nil = some (q, qs)) :
    p ∉ qs := by
  apply step_right_go_some_not_mem.go hi hstepright ?_ <| List.not_mem_nil
  apply GoesLeftOf.refl; simp

lemma GoesLeftOf.step_mp_go {m : TwoDFA α σ} {w : List α} {i : Fin _} {p q : State σ} (hi : i.val < w.length) (hgo : m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩) :
  ∃ (out : List (State σ)) (hlen : out.length ≠ 0) (hdup : out.Nodup), out[0] = p ∧ 
    m.nextConfig w.toWord ⟨out[out.length.pred]'(by simp [Nat.pos_of_ne_zero hlen]), i.succ⟩ ⟨q, i.succ + 1⟩ ∧
    (∀ j, ∀ hj : j < out.length.pred, ∃ q',
      m.nextConfig w.toWord ⟨out[j]'(Nat.lt_of_lt_pred hj), i.succ⟩ ⟨q', i.castSucc⟩ ∧
      m.GoesLeftOf w.toWord i.castSucc ⟨q', i.castSucc⟩ ⟨out[j.succ]'(Nat.succ_lt_of_lt_pred hj), i.succ⟩) := by
  match hstepright : step_right.go m (m.table_for <| w.take i) w[i.val] p [] List.nodup_nil with
  | .none =>
    absurd hgo
    apply step_right_go_eq_none hi (by simp) hstepright
  | .some (q', qs) =>
    have hdupqs : (p :: qs.reverse).Nodup := by
      have hmem := step_right_go_some_not_mem hi hstepright
      unfold step_right.go at hstepright
      split at hstepright
      next =>
        simp only [Option.some.injEq, Prod.mk.injEq, List.nil_eq] at hstepright
        simp [hstepright.right]
      next p' hstep =>
        simp only [List.not_mem_nil, ↓reduceDIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstepright
        obtain ⟨p'', hmap, hrec⟩ := hstepright
        rw [List.nodup_cons]
        constructor
        · rwa [←List.mem_reverse] at hmem
        · apply step_right_go_nodup hi hrec

    use p :: qs.reverse, by simp, hdupqs
    -- This is the second part of the result, but it's also used to prove the first part, so we do it separately here
    have hlinks : ∀ (j : ℕ) (hj : j < (p :: qs.reverse).length.pred), ∃ q',
          m.nextConfig w.toWord ⟨(p :: qs.reverse)[j]'(Nat.lt_of_lt_pred hj), i.succ⟩ ⟨q', i.castSucc⟩ ∧
          m.GoesLeftOf w.toWord i.castSucc ⟨q', i.castSucc⟩ ⟨(p :: qs.reverse)[j.succ]'(Nat.succ_lt_of_lt_pred hj), i.succ⟩ := by
      cases qs with
      | nil => simp -- vacuous, hypothesis : _ < 0
      | cons x xs =>
        intro j hlt
        simp only [List.length_cons, Nat.pred_eq_sub_one, Nat.add_one_sub_one] at hlt
        cases j with
        | zero => 
          have : (x :: xs).reverse[0] = (x :: xs).getLast (by simp) := by
            rw [←List.getElem_cons_length]
            · exact List.getElem_reverse (i := 0) <| Nat.pos_of_ne_zero <| Nat.ne_zero_of_lt hlt
            · simp
          conv in _[Nat.succ 0] =>
            simp only [Nat.succ_eq_add_one, zero_add, List.getElem_cons_succ, this]
          simp only [List.getElem_cons_zero]
          unfold step_right.go at hstepright 
          split at hstepright
          case h_1 => simp at hstepright -- contradiction : [] = x :: xs
          case h_2 p' hstep =>
            exists p'
            have hint : i.succ.internal := by
              simpa [Fin.internal, Fin.ne_iff_vne, Fin.val_last] using Nat.ne_of_lt hi
            constructor
            · left
              · simpa [Word.toWord_get_internal (int := hint)] using hstep
              · simp [Movement.apply, ←Fin.val_inj]
              · constructor <;> simp
            · simp only [List.not_mem_nil, ↓reduceDIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstepright
              obtain ⟨q', hmap, hrec⟩ := hstepright
              obtain ⟨_, htail⟩ := step_right_go_acc_is_tail hrec
              simpa [htail] using m.table_for_take_map_some w _ i.castSucc (by simp) rfl _ _ hmap
        | succ j =>
          simp only [List.getElem_cons_succ, Nat.succ_eq_add_one]
          apply step_right_go_eq_some_links hstepright j
          simpa using hlt

    have hlt : i.succ < i.succ + 1 := by rwa [Fin.lt_add_one_iff, Fin.lt_iff_val_lt_val, Fin.val_last, Fin.val_succ, Nat.add_one_lt_add_one_iff]
    constructorm* _ ∧ _
    · simp
    · have hlaststep := step_right_go_eq_some_last_step hstepright
      cases qs with
      | nil =>
        suffices q = q' by simpa [this] using hlaststep
        simpa using hgo.single_exit hlt (GoesLeftOf.single (by simp) hlaststep) hlt
      | cons x xs =>
        have : (p :: (x :: xs).reverse)[(p :: (x :: xs).reverse).length.pred] = (p :: (x :: xs).reverse).getLast (by simp) :=
          by simp
        rw [this]; clear this
        suffices q = q' by simpa [this] using hlaststep
        apply And.left (b := i.succ + 1 = i.succ + 1)
        rw [←Config.mk.injEq]
        apply hgo.single_exit hlt _ hlt
        apply GoesLeftOf.tail (mid := ⟨x, i.succ⟩)
        · simp
        · have : (p :: (x :: xs).reverse).head (by simp) = p := by simp
          rw [←this]; clear this
          have : (p :: (x :: xs).reverse).getLast (by simp) = x := by simp
          rw [←this]; clear this
          apply GoesLeftOf.fold_list (p :: (x :: xs).reverse)
          intro j hj
          obtain ⟨nxt, hnxt, hrest⟩ := hlinks j hj
          exact hrest.castSucc.head hnxt (by simp)
        · simpa using hlaststep
    · exact hlinks

theorem GoesLeftOf.step (m : TwoDFA α σ) (w : List α) {i : Fin _} (p q : State σ) (hi : i ≠ Fin.last _) : m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩ ↔
    ∃ (out : List (State σ)) (hlen : out.length ≠ 0) (hdup : out.Nodup), out[0] = p ∧ 
      m.nextConfig w.toWord ⟨out[out.length.pred]'(by simp [Nat.pos_of_ne_zero hlen]), i.succ⟩ ⟨q, i.succ + 1⟩ ∧
      (∀ j, ∀ hj : j < out.length.pred, ∃ q',
        m.nextConfig w.toWord ⟨out[j]'(Nat.lt_of_lt_pred hj), i.succ⟩ ⟨q', i.castSucc⟩ ∧
        m.GoesLeftOf w.toWord i.castSucc ⟨q', i.castSucc⟩ ⟨out[j.succ]'(Nat.succ_lt_of_lt_pred hj), i.succ⟩)
where
  mp hgoes := by
    have hlt : i.val < w.length := by simpa [←Fin.lt_last_iff_ne_last] using hi
    apply step_mp_go hlt hgoes
  mpr := by
    rintro ⟨psqs, hlen, hdup, hstrt, hlast, hmap⟩
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

theorem step_right_go_from_parts {m : TwoDFA α σ} {w : List α} {t : BackTable σ} {i : Fin (w.length + 1)} (hi : i.val < w.length) (p q q' q'' : State σ)
  (qs : List (State σ)) (hdupqs : (q' :: q'' :: qs).Nodup)
  (hend : m.nextConfig w.toWord ⟨(q' :: q'' :: qs)[(q' :: q'' :: qs).length.pred]'(by simp), i.succ⟩ ⟨q, i.succ + 1⟩)
  (hsteps : ∀ j, ∀ hj : j < (q' :: q'' :: qs).length.pred, ∃ p',
            m.nextConfig w.toWord ⟨(q' :: q'' :: qs)[j]'(Nat.lt_of_lt_pred hj), i.succ⟩ ⟨p', i.castSucc⟩ ∧
            t.map p' = some ((q' :: q'' :: qs)[j.succ]'(Nat.succ_lt_of_lt_pred hj)))
  (acc : List (State σ)) (hdup : (p :: acc).Nodup) (hacc : ∃ hd, (q'' :: qs) = (hd ++ p :: acc).reverse) :
    step_right.go m t w[i.val] p (p :: acc) hdup = some (q, (q'' :: qs).reverse) := by
  have hint : i.succ.internal := by
    suffices i ≠ Fin.last _ by simpa [Fin.internal]
    simpa [Fin.ne_iff_vne, Fin.val_last] using Nat.ne_of_lt hi
  unfold step_right.go
  if hlen : acc.length < qs.length
    then
      obtain ⟨hd, hacc⟩ := hacc
      have hlen' : acc.length+1 < (q'' :: qs).length := by simp [hlen]
      have hnil : hd ≠ [] := by
        by_contra hnil
        simp [hacc, hnil] at hlen'
      have hget : (q' :: q'' :: qs)[acc.length+1]'(by simp only [List.length_cons]; omega) = p := by
        conv in _[_] => arg 1; rw [hacc]
        simp
      split
      next p'' hstep =>
        obtain ⟨p', hnext, _⟩ := hsteps (acc.length+1) (by simp [hlen])
        rw [hget] at hnext
        exfalso
        suffices i.castSucc = i.succ + 1 by
          have : i.val = i.val + 1 + 1 := by simpa [←Fin.val_inj, Fin.val_add_one, Nat.ne_of_lt hi]
          omega
        suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p'', i.succ + 1⟩ by apply And.right; simpa using nextConfig_right_unique hnext this
        right
        · simpa [Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj, Fin.val_add_one_of_lt <| Fin.lt_last_iff_ne_last.mpr hint.right]
        · constructor <;> simp [hint.right]
      next p'' hstep =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
        exists (q'' :: qs)[acc.length+1]
        constructor
        · obtain ⟨p', hnext, hmap⟩ := hsteps (acc.length+1) (by simp [hlen])
          rw [hget] at hnext
          simp only [Nat.succ_eq_add_one, List.getElem_cons_succ] at hnext hmap
          suffices p'' = p' by rwa [this]
          suffices m.nextConfig w.toWord ⟨p, i.succ⟩ ⟨p'', i.castSucc⟩ by simpa using nextConfig_right_unique this hnext
          left
          · simpa [Word.toWord_get_internal (int := hint)] using hstep
          · simp [Movement.apply, ←Fin.val_inj]
          · constructor <;> simp
        · if hmem : (q'' :: qs)[acc.length+1] ∈ p :: acc
            then
              exfalso
              have _ : hd.length - 1 < hd.length := by simp [List.length_pos_of_ne_nil hnil]
              have hmem : (q' :: q'' :: qs)[acc.length + 2]'(by simpa) ∈ p :: acc := by simpa using hmem
              have hmem : hd[hd.length - 1] ∈ p :: acc := by simpa [hacc] using hmem
              rw [hacc, List.nodup_cons, List.nodup_reverse] at hdupqs
              have hdisjoint := List.disjoint_of_nodup_append hdupqs.right
              rw [List.disjoint_iff_ne] at hdisjoint
              apply hdisjoint _ ?_ _ hmem (rfl : hd[hd.length - 1] = _)
              simp  -- hd[hd.length - 1] ∈ hd
            else
              simp only [hmem, ↓reduceDIte]
              apply step_right_go_from_parts hi _ _ q' q'' qs hdupqs hend hsteps (p :: acc) (hdup.cons hmem)
              -- Just need the new hacc
              have hdeq : hd = hd.dropLast ++ [hd.getLast hnil] := by symm; apply List.dropLast_append_getLast
              conv in _[_] => arg 1; rw [hacc]
              have : hd.getLast hnil = (q' :: q'' :: qs)[acc.length + 2]'(by simpa) := by 
                conv in _[_] => arg 1; rw [hacc]
                simp [List.getLast_eq_getElem]
              use hd.dropLast
              simpa [List.getElem_length_sub_one_eq_getLast, hacc]
    else -- hlen : ¬ acc.length < qs.length + 1
      obtain ⟨hd, hacc⟩ := hacc
      have hnil : hd = [] := by
        cases hd with
        | nil => rfl
        | cons => 
          exfalso
          suffices (p :: acc).reverse.length < (q'' :: qs).length by simpa [hlen]
          simp [hacc]
      have hqs : q'' :: qs = (p :: acc).reverse := by simpa [hnil] using hacc
      have hnext : m.nextConfig w ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩ := by simpa [hqs] using hend
      split
      next p' hstep =>
        suffices p' = q by simpa [hqs]
        suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.succ + 1⟩ by simpa using nextConfig_right_unique this hnext
        right
        · simpa [Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj, Fin.val_add_one_of_lt <| Fin.lt_last_iff_ne_last.mpr hint.right]
        · constructor <;> simp [hint.right]
      next p' hstep =>
        exfalso
        suffices i.castSucc = i.succ + 1 by
          have : i.val = i.val + 1 + 1 := by simpa [←Fin.val_inj, Fin.val_add_one, Nat.ne_of_lt hi]
          omega
        suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.castSucc⟩ by apply And.right; simpa using nextConfig_right_unique this hnext
        left
        · simpa [Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj]
        · constructor <;> simp
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    have := (hdup.cons hmem).length_le_card
    repeat rw [List.length_cons] at this
    repeat rw [List.length_cons]
    omega

theorem step_table_map_from_parts {m : TwoDFA α σ} {w : List α} {t : BackTable σ} {i : Fin (w.length + 1)} (hi : i.val < w.length) {p q : State σ} 
  (qs : List (State σ)) (hdup : qs.Nodup) (hlen : qs.length ≠ 0) (hstrt : qs[0] = p)
  (hend : m.nextConfig w.toWord ⟨qs[qs.length.pred]'(by simp [Nat.pos_of_ne_zero hlen]), i.succ⟩ ⟨q, i.succ + 1⟩)
  (hsteps : ∀ j, ∀ hj : j < qs.length.pred, ∃ p',
            m.nextConfig w.toWord ⟨qs[j]'(Nat.lt_of_lt_pred hj), i.succ⟩ ⟨p', i.castSucc⟩ ∧
            t.map p' = some (qs[j.succ]'(Nat.succ_lt_of_lt_pred hj))) :
    (m.step_table t w[i.val]).map p = some q := by
  have hint : i.succ.internal := by
    suffices i ≠ Fin.last _ by simpa [Fin.internal]
    simpa [Fin.ne_iff_vne, Fin.val_last] using Nat.ne_of_lt hi
  simp only [step_table, step_right, Option.map_eq_some_iff]
  cases qs with
  | nil => simp at hlen
  | cons q' qs => 
    simp only [List.getElem_cons_zero] at hstrt
    cases qs with
    | nil =>
      clear hsteps -- cannot satisfy j < [q'].length.pred = 0
      simp only [List.length_cons, List.length_nil, zero_add, Nat.pred_eq_sub_one, tsub_self, List.getElem_cons_zero] at hend
      unfold step_right.go
      split
      next p' hstep => 
        use (q, [])
        suffices p' = q by simpa
        apply And.left (b := i.succ + 1 = i.succ + 1)
        rw [←Config.mk.injEq]
        symm
        apply nextConfig_right_unique hend
        right
        · simpa [hstrt, Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj, Fin.val_add_one_of_lt <| Fin.lt_last_iff_ne_last.mpr hint.right]
        · constructor <;> simp [hint.right]
      next p' hstep => 
        exfalso
        suffices i.castSucc = i.succ + 1 by
          have : i.val = i.val + 1 + 1 := by simpa [←Fin.val_inj, Fin.val_add_one, Nat.ne_of_lt hi]
          omega
        suffices m.nextConfig w ⟨q', i.succ⟩ ⟨p', i.castSucc⟩ by apply And.right; simpa using nextConfig_right_unique this hend
        left
        · simpa [hstrt, Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj]
        · constructor <;> simp
    | cons q'' qs =>
      exists (q, (q'' :: qs).reverse)
      simp only [and_true]
      obtain ⟨p'', hnext, hmap⟩ := hsteps 0 (by simp)
      simp only [hstrt, List.getElem_cons_zero] at hnext
      simp only [hstrt, Nat.succ_eq_add_one, zero_add, List.getElem_cons_succ, List.getElem_cons_zero] at hmap
      unfold step_right.go
      split
      next p' hstep =>
        exfalso
        suffices i.castSucc = i.succ + 1 by
          have : i.val = i.val + 1 + 1 := by simpa [←Fin.val_inj, Fin.val_add_one, Nat.ne_of_lt hi]
          omega
        suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.succ + 1⟩ by apply And.right; simpa using nextConfig_right_unique hnext this
        right
        · simpa [Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj, Fin.val_add_one_of_lt <| Fin.lt_last_iff_ne_last.mpr hint.right]
        · constructor <;> simp [hint.right]
      next p' hstep =>
        simp only [List.not_mem_nil, ↓reduceDIte, Option.bind_eq_bind, Option.bind_eq_some_iff]
        exists q''
        constructor
        · suffices p'' = p' by rwa [this] at hmap
          suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p', i.castSucc⟩ by simpa using nextConfig_right_unique hnext this
          left
          · simpa [Word.toWord_get_internal (int := hint)] using hstep
          · simp [Movement.apply, ←Fin.val_inj]
          · constructor <;> simp
        · apply step_right_go_from_parts hi _ _ _ _ _ hdup hend hsteps [] (List.nodup_singleton _)
          exists qs.reverse; simp

theorem table_for_take_map (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 2)) (hnelast : i ≠ Fin.last _)
  (ht : t = m.table_for (w.take i)) (p q : State σ)  :
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
        apply table_for_take_step_right_go_some (hind := fun p q ↦ (hind p q).mp) (hstep := hgo)
        rfl
    · rw [GoesLeftOf.step (hi := by rwa [←i.succ_ne_last_iff])]
      rintro ⟨qs, hlen, hdup, hstrt, hend, hlinks⟩
      apply step_table_map_from_parts hlt qs hdup hlen hstrt hend
      -- Just need the links using prev_t.map rather than GoesLeftOf
      intro j hj
      obtain ⟨p', hnxt, hlnk⟩ := hlinks j hj
      rw [(by simp : i.succ = i.castSucc + 1), ←hind] at hlnk
      use p', hnxt, hlnk

theorem step_right_init_of_goes (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 1)) (hi : i.val < w.length) (p q : State σ) 
  (ht : t = m.table_for (w.take i)) (hgo : m.GoesLeftOf w.toWord i.succ ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩) :
    m.step_right t w[i.val] p = some q := by
  simp only [step_right, Option.map_eq_some_iff, Prod.exists, exists_and_right, exists_eq_right]
  have ne_last : i ≠ Fin.last _ := by simpa [Fin.ne_iff_vne] using Nat.ne_of_lt hi
  have hint : i.succ.internal := by simpa [Fin.internal]
  rw [GoesLeftOf.step (hi := ne_last)] at hgo
  obtain ⟨qs, hlen, hdup, hstrt, hend, hlinks⟩ := hgo
  cases qs with
  | nil => simp at hlen -- contradiction : 0 ≠ 0
  | cons q' qs =>
    rw [List.getElem_cons_zero] at hstrt
    cases qs with
    | nil =>
      exists []
      have hnext : m.nextConfig w ⟨p, i.succ⟩ ⟨q, i.succ + 1⟩ := by simpa [hstrt] using hend
      unfold step_right.go
      split
      next p'' hstep => -- step right
        suffices p'' = q by simpa
        suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p'', i.succ + 1⟩ by simpa using nextConfig_right_unique this hnext
        right
        · simpa [Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj, Fin.val_add_one, hint.right]
        · constructor <;> simp [hint.right]
      next p'' hstep => -- step left
        exfalso
        suffices i.castSucc = i.succ + 1 by
          have : i.val = i.val + 1 + 1 := by simpa [←Fin.val_inj, Fin.val_add_one, Nat.ne_of_lt hi]
          omega
        suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p'', i.castSucc⟩ by apply And.right; simpa using nextConfig_right_unique this hnext
        left
        · simpa [Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj]
        · constructor <;> simp
    | cons q'' qs =>
      exists (q'' :: qs).reverse
      obtain ⟨nxt, hnext, hlink⟩ := hlinks 0 (by simp)
      simp only [hstrt, List.getElem_cons_zero] at hnext
      unfold step_right.go
      split
      next p'' hstep => -- step right
        exfalso
        suffices i.castSucc = i.succ + 1 by
          have : i.val = i.val + 1 + 1 := by simpa [←Fin.val_inj, Fin.val_add_one, Nat.ne_of_lt hi]
          omega
        suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p'', i.succ + 1⟩ by apply And.right; simpa using nextConfig_right_unique hnext this
        right
        · simpa [Word.toWord_get_internal (int := hint)] using hstep
        · simp [Movement.apply, ←Fin.val_inj, Fin.val_add_one, hint.right]
        · constructor <;> simp [hint.right]
      next p'' hstep => -- step left
        simp only [List.not_mem_nil, ↓reduceDIte, Option.bind_eq_bind, Option.bind_eq_some_iff]
        exists q''
        constructor
        · rw [m.table_for_take_map w t i.castSucc (by simp) ht]
          suffices p'' = nxt by simpa [this] using hlink
          suffices m.nextConfig w ⟨p, i.succ⟩ ⟨p'', i.castSucc⟩ by simpa using nextConfig_right_unique this hnext
          left
          · simpa [Word.toWord_get_internal (int := hint)] using hstep
          · simp [Movement.apply, ←Fin.val_inj]
          · constructor <;> simp
        · apply m.step_right_go_from_parts hi _ _ _ _ _ hdup hend ?hlinks [] _ <| by exists qs.reverse; simp
          -- Convert hlinks to use t.map rather than GoesLeftOf
          intro j hj
          obtain ⟨nxt, hnxt, hlnk⟩ := hlinks j hj
          have hmap := m.table_for_take_map w t i.castSucc (by simp) ht
          rw [(by simp : i.succ = i.castSucc + 1), ←hmap] at hlnk
          use nxt, hnxt, hlnk

theorem table_for_take_init (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 1))
  (ht : t = m.table_for (w.take i)) {q : State σ} :
    t.init = some q ↔ m.GoesLeftOf w.toWord i.castSucc m.init ⟨q, i.succ⟩ := by
  induction i using Fin.inductionOn generalizing t q with
  | zero =>
    conv =>
      lhs
      rw [ht]
      simp [table_for, first_table]
    constructor
    · intro hinit
      rw [←hinit]
      apply GoesLeftOf.single (hlt := by rfl)
      rw [←stepConfig_gives_nextConfig]
      simp only [stepConfig, Word.get_eq_left_of_eq_zero, Fin.succ_zero_eq_one, Config.mk.injEq, true_and]
      obtain ⟨_, hright⟩ := m.in_bounds_left m.start
      simp only [step] at hright
      conv => enter [1, 1, 1]; rw [hright]
      simp [Movement.apply, Fin.castLT]
    · intro hgo
      suffices m.stepConfig w.toWord m.init = ⟨q, 1⟩ by apply And.left; simpa [stepConfig, Word.get_eq_left_of_eq_zero]
      rw [stepConfig_gives_nextConfig]
      cases hgo with
      | tail hlt hd tl =>
        cases hd with
        | refl => exact tl
        | tail hlt' _ tl =>
          exfalso
          rw [Fin.castSucc_zero, Fin.le_zero_iff] at hlt hlt'
          apply nextConfig.must_move _ _ _ _ (hlt'.trans hlt.symm) tl
  | succ i ih =>
    let prev_t := m.table_for (w.take i)
    have hstep : t = m.step_table prev_t w[i.val] := m.table_for_take_succ i prev_t t rfl ht
    have hinit_def : prev_t.init.bind (m.step_right prev_t w[i.val]) = t.init := by
      simp [hstep, step_table]
    rw [←Fin.succ_castSucc]
    have hind : ∀ q, prev_t.init = some q ↔ _ := fun {q} ↦ ih prev_t rfl
    have hsuccsucceq : i.succ.succ = i.castSucc.succ + 1 := by
      rw [←Fin.val_inj]
      simp [Fin.val_add_one]
    rw [hsuccsucceq]
    constructor
    · intro hinit
      rw [hinit, Option.bind_eq_some_iff] at hinit_def
      obtain ⟨prev_init, hprev, hstep_init⟩ := hinit_def
      trans
      · apply GoesLeftOf.castSucc
        rwa [hind] at hprev
      · rw [step_right, Option.map_eq_some_iff] at hstep_init
        obtain ⟨⟨q', qs⟩, hstep_init, hq'⟩ := hstep_init
        simp only at hq'
        apply m.table_for_step_right prev_t w i.castSucc i.is_lt prev_init q [] List.nodup_nil (qs := qs)
        · simp [Fin.getElem_fin, hstep_init, hq']
        · intro p q hmap
          rwa [
            m.table_for_take_map w _ i.castSucc.castSucc (by simp) (by unfold prev_t; rfl),
            Fin.coeSucc_eq_succ
          ] at hmap
    · intro hgo
      obtain ⟨⟨mid, mididx⟩, hgt, hpref, hrest⟩ := hgo.prefix_left_of i.castSucc.castSucc (by simp) (by simp) <| by
        suffices i.val < i.val + 2 by simp [Fin.lt_iff_val_lt_val, Fin.val_add_one, this]
        apply Nat.lt_add_of_pos_right
        apply Nat.ofNat_pos
      have : mididx = i.castSucc.succ := by simpa using hpref.stop_idx_of_gt hgt
      rw [this] at hpref hrest; clear this hgt mididx
      rw [←hind] at hpref
      simp only [hstep, step_table, Option.bind_eq_bind, Option.bind_eq_some_iff]
      exists mid
      constructor
      · exact hpref
      · apply m.step_right_init_of_goes w prev_t i.castSucc (by simp) mid q rfl hrest

theorem table_for_take_init_none (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 1))
  (ht : t = m.table_for (w.take i)) (hinit : t.init = none) :
    ∃ (q : _) (j : Fin _), m.GoesLeftOf w.toWord i.castSucc m.init ⟨q, j⟩ ∧ j ≤ i.castSucc ∧ m.CyclesLeftOf w.toWord j ⟨q, j⟩ := by
  induction i using Fin.inductionOn generalizing t with
  | zero => 
    exfalso
    simp only [table_for, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.take_zero, List.foldl_nil] at ht
    simp [ht, first_table] at hinit
  | succ i ih =>
    let prev_t := m.table_for (w.take i)
    have hstep : t = m.step_table prev_t w[i.val] := m.table_for_take_succ i prev_t t rfl ht
    cases hinit' : prev_t.init with
    | none =>
      obtain ⟨q, j, hreach, hlt, hcyc⟩ := ih prev_t rfl hinit'
      refine ⟨q, j, hreach.castLE ?_, hlt.trans ?_, hcyc.castLE ?s_le_s⟩
      case s_le_s => rfl
      all_goals exact Fin.le_of_lt i.castSucc_lt_succ
    | some q =>
      have hinit_def : prev_t.init.bind (m.step_right prev_t w[i.val]) = t.init := by
        simp [hstep, step_table]
      simp only [hinit', step_right, Option.bind_some, hinit, Option.map_eq_none_iff] at hinit_def
      have hlt : i.castSucc.val < w.length := by simp [i.is_lt]
      obtain ⟨s, j, hreach, hlt, hcyc⟩ := m.cycles_of_step_right_go_eq_none w prev_t i.castSucc rfl _ _ _ (by simp) hlt hinit_def <| by
        intro q' hgo hmap
        obtain ⟨p', j, hgo', hlt, hcyc⟩ := m.table_for_take_map_none w prev_t i.castSucc.castSucc (by simp) rfl _ hmap
        use p', j
        constructorm* _ ∧ _
        · exact hgo.trans hgo'.castSucc
        · apply hlt.trans
          apply Fin.castSucc_le_succ
        · exact hcyc
      rw [m.table_for_take_init w prev_t i.castSucc rfl] at hinit'
      use s, j
      constructorm* _ ∧ _
      · exact hinit'.castSucc.trans hreach
      · simpa using hlt
      · apply hcyc.castLE
        rfl

theorem table_for_end_state_go {m : TwoDFA α σ} (t : BackTable σ) (w : List α) (p q : State σ) (acc : List (State σ)) (hdup : acc.Nodup)
  (hacc : ∀ p' ∈ acc, m.GoesTo w.toWord ⟨p', Fin.last _⟩ ⟨p, Fin.last _⟩) (hmap : end_state.go m t p acc hdup = some q)
  (hind : ∀ (p q : State σ), t.map p = some q → m.GoesTo w.toWord ⟨p, Fin.ofNat _ w.length⟩ ⟨q, Fin.last _⟩) :
    m.GoesTo w.toWord ⟨p, Fin.last _⟩ ⟨q, Fin.last _⟩ ∧ m.CyclesAt w.toWord ⟨q, Fin.last _⟩ := by
  obtain ⟨p', hp'⟩ := m.in_bounds_right p
  obtain ⟨q', hq', hmap'⟩ : ∃ a, t.map p' = some a ∧ (if hmem : a ∈ acc then some a else end_state.go m t a (a :: acc) (hdup.cons hmem)) = some q := by
    unfold end_state.go at hmap
    simpa [Option.bind_eq_some_iff, hp'] using hmap
  have hnext : m.nextConfig w.toWord ⟨p, Fin.last _⟩ ⟨p', Fin.ofNat _ w.length⟩ := by
    rw [←stepConfig_gives_nextConfig]
    unfold step at hp'
    simp only [stepConfig, Word.get_eq_right_of_eq_last, hp', Fin.ofNat_eq_cast, Config.mk.injEq, true_and]
    rw [←Fin.val_inj]
    simp only [Movement.apply, Fin.predCast, Fin.castLE, Fin.coe_pred, Fin.val_last, add_tsub_cancel_right, Fin.val_natCast]
    have : w.length < w.length + 2 := by trans <;> apply Nat.lt_add_one
    symm
    simp [this]
  have hpref := hind _ _ hq'
  have hpref' := hpref.head hnext

  if hmem : q' ∈ acc
    then
      have heq : q' = q := by simpa [hmem] using hmap'
      constructor
      · rwa [heq] at hpref'
      · rw [←heq]
        apply CyclesAt.transfer _ hpref
        refine ⟨_, ?_, hnext⟩
        exact hpref.trans <| hacc _ hmem
    else
      suffices ∀ p' ∈ q' :: acc, m.GoesTo w.toWord ⟨p', Fin.last _⟩ ⟨q', Fin.last _⟩ by
        obtain ⟨hreach, hcyc⟩ := table_for_end_state_go _ _ q' q (q' :: acc) (hdup.cons hmem) this (by simpa [hmem] using hmap') hind
        exact ⟨hpref'.trans hreach, hcyc⟩
      simp only [List.mem_cons, forall_eq_or_imp, GoesTo.refl, true_and]
      intro p' hmem'
      exact hacc p' hmem' |>.trans hpref'
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by 
    have := (hdup.cons hmem).length_le_card
    rw [List.length_cons] at this
    rw [List.length_cons]
    omega

theorem goes_of_table_for_end_state (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (hfor : t = m.table_for w) {q : State σ} (hend : m.end_state t = some q) :
    m.GoesTo w.toWord m.init ⟨q, Fin.last _⟩ ∧ m.CyclesAt w.toWord ⟨q, Fin.last _⟩ := by
  simp only [end_state, Option.bind_eq_bind, Option.bind_eq_some_iff] at hend
  obtain ⟨init, hinit_some, hgo⟩ := hend
  have hfor' : t = m.table_for (List.take (↑(Fin.last w.length)) w) := by
    rwa [←List.take_length (l := w)] at hfor
  suffices (∀ (p q : State σ), t.map p = some q → m.GoesTo w.toWord ⟨p, Fin.ofNat _ w.length⟩ ⟨q, Fin.last _⟩) by
    have ⟨hreach, hcyc⟩ := table_for_end_state_go (hmap := hgo) (hind := this) (hacc := by simp)
    rewrite [m.table_for_take_init w t (Fin.last (w.length)) hfor'] at hinit_some
    exact ⟨hinit_some.forget.trans hreach, hcyc⟩
  -- Produce the inductive hypothesis for the table_for_end_state_go call
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
  exact this.forget

theorem table_for_full_map_some (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (hfor : t = m.table_for w) (hnil : w ≠ [])
    {p q : State σ} (hmap : t.map p = some q) : m.GoesTo w.toWord ⟨p, (Fin.last _).castSucc⟩ ⟨q, Fin.last _⟩ := by
  let prev_t := m.table_for w.dropLast
  have hstept : t = m.step_table prev_t (w.getLast hnil) := by
    rw [←List.dropLast_append_getLast hnil] at hfor
    simp [hfor, prev_t, table_for]
  have hidx_val : (Fin.ofNat (w.length + 1) w.length.pred).val = w.length - 1 := by
    suffices w.length - 1 < w.length + 1 by simpa
    omega
  have prev_for_take : prev_t = m.table_for (w.take (Fin.ofNat (w.length + 1) w.length.pred).val) := by
    suffices w.take (Fin.ofNat (w.length + 1) w.length.pred).val = w.dropLast by rw [this]
    simp only [List.dropLast_eq_take, List.take_eq_take_iff]
    omega
  have hlen_pos : 0 < w.length := List.length_pos_of_ne_nil hnil
  have hind := m.table_for_take_step_right_go_some (w := w) (i := Fin.ofNat _ w.length.pred) (t := prev_t) (by omega) prev_for_take <|
    m.table_for_take_map_some w prev_t _ (by simp) prev_for_take
  simp only [hstept, step_table, step_right, Option.map_eq_some_iff] at hmap
  obtain ⟨⟨_, qs⟩, hstep_go, hstate_eq⟩ := hmap
  simp only at hstate_eq
  rw [hstate_eq] at hstep_go
  clear hstate_eq
  have hget_idx : w.getLast hnil = w[(Fin.ofNat (w.length + 1) w.length.pred).val] := by
    simp only [hidx_val, List.getLast_eq_getElem]
  rw [hget_idx] at hstep_go
  have out := hind _ _ _ _ _ hstep_go |>.forget
  clear * - out hnil
  have h1 : w.length - 1 < w.length + 1 := by omega
  have h2 : 0 < w.length := List.length_pos_of_ne_nil hnil
  have : (Fin.ofNat (w.length + 1) w.length.pred).succ = (Fin.last _).castSucc := by
    simp [←Fin.val_inj, Nat.mod_eq_of_lt h1, Nat.sub_one_add_one <| Nat.ne_zero_of_lt h2]
  rw [this] at out
  have : (Fin.last w.length).castSucc + 1 = Fin.last _ := by simp
  rwa [this] at out

lemma step_right_go_none (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (i : Fin (w.length + 1)) (hi : i.val < w.length) (hfor : t = m.table_for (w.take i))
  {p : State σ} {acc : List (State σ)} {hdup : acc.Nodup} (hacc : ∀ q' ∈ acc, m.GoesLeftOf w.toWord i.succ ⟨q', i.succ⟩ ⟨p, i.succ⟩)
  (hmap : step_right.go m t w[i.val] p acc hdup = none) :
    (∃ c, m.GoesTo w.toWord ⟨p, i.succ⟩ c ∧ m.CyclesLeftOf w.toWord i.succ c) ∨ ∃ p', t.map p' = none ∧ m.GoesTo w.toWord ⟨p, i.succ⟩ ⟨p', i.castSucc⟩ := by
  unfold step_right.go at hmap
  split at hmap
  next => contradiction -- hmap : some _ = none
  next p' hstep =>
    have hnext : m.nextConfig w.toWord ⟨p, i.succ⟩ ⟨p', i.castSucc⟩ := by
      have hint : i.succ.internal := by
        constructor; simp
        rw [Fin.ne_iff_vne, Fin.val_succ, Fin.val_last]
        omega
      left
      · simpa [Word.toWord_get_internal w i hint] using hstep
      · simp [Movement.apply, ←Fin.val_inj]
      · constructor <;> simp
    cases hmap' : t.map p' with
    | none => right; exact ⟨p', hmap', GoesTo.single hnext⟩
    | some q' =>
      have hpref' : m.GoesLeftOf w.toWord i.castSucc ⟨p', i.castSucc⟩ ⟨q', i.succ⟩ := by
        have : i.castSucc + 1 = i.succ := by simp
        rw [←this]
        exact m.table_for_take_map_some w t i.castSucc (by simp) hfor _ _ hmap'
      have hpref := hpref'.castSucc.head hnext <| by simp
      if hmem : q' ∈ acc
        then
          left
          exact ⟨_, .refl, by simp, _, hnext, hpref'.castSucc.trans <| hacc _ hmem⟩
        else
          simp only [Option.bind_eq_bind, Option.bind_eq_none_iff, dite_eq_left_iff] at hmap
          have hacc' : ∀ q'' ∈ q' :: acc, m.GoesLeftOf w.toWord i.succ ⟨q'', i.succ⟩ ⟨q', i.succ⟩ := by
            simp only [List.mem_cons, forall_eq_or_imp, le_refl, GoesLeftOf.refl, true_and]
            intro _ hmem'
            exact hacc _ hmem' |>.trans hpref
          rcases m.step_right_go_none w t i hi hfor hacc' <| hmap _ hmap' hmem with ⟨c, hreach, hcyc⟩ | ⟨c, hmapc, hgoc⟩
          · left; exact ⟨c, hpref.forget.trans hreach, hcyc⟩
          · right; exact ⟨c, hmapc, hpref.forget.trans hgoc⟩
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    have := (hdup.cons hmem).length_le_card
    rw [List.length_cons] at this
    rw [List.length_cons]
    omega

theorem not_reach_last_of_end_state_go_none (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (hfor : t = m.table_for w)
  (p : State σ) (acc : List (State σ)) (hdup : acc.Nodup) (hend : end_state.go m t p acc hdup = none) :
    ∃ c i, m.GoesTo w.toWord ⟨p, Fin.last _⟩ c ∧ i < Fin.last _ ∧ m.CyclesLeftOf w.toWord i c := by
  unfold end_state.go at hend
  simp only [Option.bind_eq_bind, Option.bind_eq_none_iff] at hend
  cases hmap : t.map (m.step .right p).1 with
  | some p' =>
    have := hend _ hmap
    split at this; contradiction -- some _ = none
    rename p' ∉ acc => hmem
    obtain ⟨c, j, hgo, hlt, hcyc⟩ := m.not_reach_last_of_end_state_go_none w t hfor p' (p' :: acc) (hdup.cons hmem) this
    refine ⟨c, j, GoesTo.trans ?_ hgo, hlt, hcyc⟩
    if hnil : w = []
      then
        rw [hnil]
        simp only [List.length_nil, Nat.reduceAdd, Fin.isValue, Fin.reduceLast]
        apply GoesTo.head (mid := ⟨(m.step .right p).1, 0⟩)
        · obtain ⟨_, mv⟩ := m.in_bounds_right p
          simp only [Fin.isValue, mv, ←stepConfig_gives_nextConfig, stepConfig, Nat.reduceAdd,
            Fin.reduceLast, Word.get_eq_right_of_eq_last, Config.mk.injEq, true_and]
          simp [Movement.apply, ←Fin.val_inj]
        · apply GoesTo.single
          simp only [hfor, hnil, table_for_nil, first_table, Option.some.injEq] at hmap
          obtain ⟨_, mv⟩ := m.in_bounds_left (m.step .right p).1
          simp only [Fin.isValue, ← stepConfig_gives_nextConfig, stepConfig, Nat.reduceAdd,
            Word.get_eq_left_of_eq_zero, mv, Config.mk.injEq]
          constructor
          · simpa [mv] using hmap
          · simp [Movement.apply, ←Fin.val_inj]
      else
        apply m.table_for_full_map_some w t hfor hnil hmap |>.head
        obtain ⟨_, mv⟩ := m.in_bounds_right p
        simp only [← stepConfig_gives_nextConfig, stepConfig, Word.get_eq_right_of_eq_last,
          Config.mk.injEq, true_and, mv]
        simp [Movement.apply, ←Fin.val_inj]
  | none =>
    clear hend
    if hnil : w = []
      then simp [hfor, hnil, table_for_nil, first_table] at hmap -- Reduces to hmap : some _ = none
      else
        let prev_t := m.table_for w.dropLast
        have hstept : t = m.step_table prev_t (w.getLast hnil) := by
          rw [←List.dropLast_append_getLast hnil] at hfor
          simp [hfor, prev_t, table_for]
        have hidx_val : (Fin.ofNat (w.length + 2) w.length.pred).val = w.length - 1 := by
          suffices w.length - 1 < w.length + 2 by simpa
          omega
        have hidx_val2 : (Fin.ofNat (w.length + 1) w.length.pred).val = w.length - 1 := by
          suffices w.length - 1 < w.length + 1 by simpa
          omega
        have prev_for_take : prev_t = m.table_for (w.take (Fin.ofNat (w.length + 2) w.length.pred).val) := by
          suffices w.take (Fin.ofNat (w.length + 2) w.length.pred).val = w.dropLast by rw [this]
          simp only [List.dropLast_eq_take, List.take_eq_take_iff]
          omega
        have hlen_pos : 0 < w.length := List.length_pos_of_ne_nil hnil
        simp only [hstept, step_table, step_right, List.getLast_eq_getElem hnil, Option.map_eq_none_iff] at hmap

        have hidx_ne : Fin.ofNat (w.length + 2) w.length.pred ≠ Fin.last (w.length + 1) := by
          rw [Fin.ne_iff_vne, hidx_val, Fin.val_last]; omega
        have hind := m.table_for_take_map_none w prev_t _ hidx_ne prev_for_take

        rw [hidx_val, ←hidx_val2] at prev_for_take
        simp only [←hidx_val2] at hmap
        have := m.step_right_go_none w prev_t (Fin.ofNat _ w.length.pred) (by rw [hidx_val2]; omega) prev_for_take (by simp) hmap
        rcases this with ⟨c, hreach, hcyc⟩ | ⟨p', hmap', hpref⟩
        · refine ⟨_, _, hreach.head ?_, ?_, hcyc⟩
          · obtain ⟨_, mv⟩ := m.in_bounds_right p
            simp only [mv, Nat.pred_eq_sub_one, Fin.ofNat_eq_cast, ← stepConfig_gives_nextConfig,
              stepConfig, Word.get_eq_right_of_eq_last, Config.mk.injEq, true_and]
            have : w.length - 1 < w.length + 1 := by omega
            simp [Movement.apply, ←Fin.val_inj, Nat.mod_eq_of_lt this, Nat.sub_one_add_one <| Nat.ne_zero_of_lt hlen_pos]
          · rw [Fin.lt_iff_val_lt_val, Fin.val_last, Fin.val_succ, hidx_val2]; omega
        · obtain ⟨c, j, hreach, hlt, hcyc⟩ := hind _ hmap'
          have end_eq : (Fin.ofNat (w.length + 1) w.length.pred).castSucc = Fin.ofNat (w.length + 2) w.length.pred := by
            rw [←Fin.val_inj, Fin.coe_castSucc, hidx_val, hidx_val2]
          rw [end_eq] at hpref
          refine ⟨⟨c, _⟩, j, (hpref.trans hreach.forget).head ?_, Fin.lt_of_le_of_lt hlt <| Fin.lt_last_iff_ne_last.mpr hidx_ne, hcyc⟩
          obtain ⟨_, mv⟩ := m.in_bounds_right p
          simp only [mv, Nat.pred_eq_sub_one, Fin.ofNat_eq_cast, ← stepConfig_gives_nextConfig,
            stepConfig, Word.get_eq_right_of_eq_last, Config.mk.injEq, true_and]
          have : w.length - 1 < w.length + 1 := by omega
          simp [Movement.apply, ←Fin.val_inj, Nat.mod_eq_of_lt this, Nat.sub_one_add_one <| Nat.ne_zero_of_lt hlen_pos]
  termination_by Fintype.card (State σ) - acc.length
  decreasing_by
    rename _ ∉ acc => hmem
    have := (hdup.cons hmem).length_le_card
    rw [List.length_cons] at this
    rw [List.length_cons]
    omega

theorem not_reach_last_of_end_state_none (m : TwoDFA α σ) (w : List α) (t : BackTable σ) (hfor : t = m.table_for w)
  (hend : m.end_state t = none) :
    ∃ c i, m.reaches w.toWord c ∧ i < Fin.last _ ∧ m.CyclesLeftOf w.toWord i c := by
  simp [end_state] at hend
  cases hinit : t.init with
  | none =>
    obtain ⟨q, j, hreach, hlt, hcyc⟩ := m.table_for_take_init_none w t (Fin.last _) (by simp [hfor]) hinit
    refine ⟨⟨q, j⟩, _, hreach.forget, ?_, hcyc⟩
    apply Fin.lt_of_le_of_lt hlt
    simp
  | some q =>
    have hend := hend _ hinit
    obtain ⟨c, i, hreach, hlt, hcyc⟩ := m.not_reach_last_of_end_state_go_none w t hfor _ _ _ hend
    refine ⟨c, i, GoesTo.trans ?_ hreach, hlt, hcyc⟩
    rw [m.table_for_take_init w t (Fin.last _) (by simp [hfor])] at hinit
    simp only [Fin.succ_last, Nat.succ_eq_add_one] at hinit
    exact hinit.forget

theorem table_for_end_state_iff_goes_to_cycle (m : TwoDFA α σ) (w : List α) (q' : State σ) :
    (∃ q, (m.end_state (m.table_for w) = some q ∧ m.GoesTo w.toWord ⟨q, Fin.last _⟩ ⟨q', Fin.last _⟩)) ↔
    (m.GoesTo w.toWord m.init ⟨q', Fin.last _⟩ ∧ m.CyclesAt w.toWord ⟨q', Fin.last _⟩) where
  mp := by
    rintro ⟨q, hend, hgo⟩
    obtain ⟨hreach, hcyc⟩ := m.goes_of_table_for_end_state w _ rfl hend
    constructor
    · exact hreach.trans hgo
    · exact hcyc.transfer hgo
  mpr := by
    rintro ⟨hreach, hcyc⟩
    rcases hend : m.end_state (m.table_for w) with _ | ⟨_ | _ | q⟩
    case none =>
      exfalso
      obtain ⟨c, i, hreach', hlt, hcyc'⟩ := m.not_reach_last_of_end_state_none w _ rfl hend
      rcases m.single_path _ hreach hreach' with hgo | hgo
      case' inl =>
        have hgo := hcyc.split hgo -- Use hcyc to reverse the single path
      all_goals
        have := hcyc'.always_left hgo
        simp only at this
        omega -- Finds contradiction : Fin.last ≤ i < Fin.last
    case' accept =>
      use .accept, rfl
    case' reject =>
      use .reject, rfl
    case' other =>
      use q, rfl
    all_goals
      obtain ⟨hreach', _⟩ := m.goes_of_table_for_end_state w _ rfl hend
      rcases m.single_path _ hreach' hreach with hgo | hgo
      · exact hgo
      · exact hcyc.split hgo

/----------------------------------------------------------------
                            The Goal
----------------------------------------------------------------/

theorem to_accept_DFA_correct (m : TwoDFA α σ) : { w | m.accepts w.toWord } = m.to_accept_DFA.accepts := by
  ext w; exact go w
  where
    go (w : List α) : m.accepts w.toWord ↔ m.end_state (m.table_for w) = some .accept := by
      have end_iff_cyc := m.table_for_end_state_iff_goes_to_cycle w .accept
      constructor
      · intro hgo
        have := And.intro
          (m.reaches_accept_last_of_accepts w.toWord hgo)
          (m.accept_cycle w.toWord)
        rw [reaches, ←end_iff_cyc] at this
        obtain ⟨q, hend, hgo'⟩ := this
        suffices q = .accept by simpa [hend]
        obtain ⟨_, hcyc⟩ := m.goes_of_table_for_end_state w _ rfl hend
        simpa using m.accept_preserve_state _ _ _ <| hcyc.split hgo'
      · intro hend
        have : ∃ q, m.end_state _ = some q ∧ m.GoesTo _ ⟨q, _⟩ _ :=
          Exists.intro State.accept <| And.intro hend (.refl : m.GoesTo w.toWord ⟨.accept, Fin.last _⟩ _)
        rw [end_iff_cyc] at this
        use Fin.last _, this.left

theorem to_reject_DFA_correct (m : TwoDFA α σ) : { w | m.rejects w.toWord } = m.to_reject_DFA.accepts := by
  ext w; exact go w
  where
    go (w : List α) : m.rejects w.toWord ↔ m.end_state (m.table_for w) = some .reject := by
      have end_iff_cyc := m.table_for_end_state_iff_goes_to_cycle w .reject
      constructor
      · intro hgo
        have := And.intro
          (m.reaches_reject_last_of_rejects w.toWord hgo)
          (m.reject_cycle w.toWord)
        rw [reaches, ←end_iff_cyc] at this
        obtain ⟨q, hend, hgo'⟩ := this
        suffices q = .reject by simpa [hend]
        obtain ⟨_, hcyc⟩ := m.goes_of_table_for_end_state w _ rfl hend
        simpa using m.reject_preserve_state _ _ _ <| hcyc.split hgo'
      · intro hend
        have : ∃ q, m.end_state _ = some q ∧ m.GoesTo _ ⟨q, _⟩ _ :=
          Exists.intro State.reject <| And.intro hend (.refl : m.GoesTo w.toWord ⟨.reject, Fin.last _⟩ _)
        rw [end_iff_cyc] at this
        use Fin.last _, this.left

theorem to_diverge_DFA_correct (m : TwoDFA α σ) : { w | m.diverges w.toWord } = m.to_diverge_DFA.accepts := by
  ext w
  suffices m.diverges w.toWord ↔ (m.end_state (m.table_for w) ≠ some .accept ∧ m.end_state (m.table_for w) ≠ some .reject) from this
  rw [divergence_iff, to_accept_DFA_correct.go, to_reject_DFA_correct.go]

end Proof

end TwoDFA
