import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_1141 : (∀ (n : Nat) (par : Fin n → Fin n), (∀ i, par i ≤ i) →
  ∀ (allow : Fin n → Bool → Bool → Bool) (r : Fin n) (T : Finset (Fin n)), r ∉ T →
  let xs := (Finset.univ : Finset (Finset (Fin n))).filter (fun x =>
    ∀ i, allow i (decide (par i ∈ x)) (decide (i ∈ x)) = true)
  let pin := fun (b : Bool) (S B : Finset (Fin n)) =>
    (xs.filter (fun x => decide (r ∈ x) = b ∧ x ∩ S = B)).card
  let independent := fun (S : Finset (Fin n)) =>
    ∀ B ⊆ S, pin false S B * pin true ∅ ∅ = pin true S B * pin false ∅ ∅
  let joint := fun (i : Fin n) (a b : Bool) =>
    (xs.filter (fun x => decide (par i ∈ x) = a ∧ decide (i ∈ x) = b)).card
  let splits := fun (i : Fin n) =>
    joint i false false * joint i true true = joint i false true * joint i true false
  (independent T ↔ ∀ i ∈ T, independent {i}) ∧
    (independent T ↔ ∃ U : Finset (Fin n), r ∈ U ∧ Disjoint U T ∧
      ∀ i, (decide (i ∈ U) != decide (par i ∈ U)) = true → splits i)) := by
  intro n par hpar allow r T hrT xs pin independent joint splits
  let mix := fun (D x y : Finset (Fin n)) => (x ∩ D) ∪ (y \ D)
  have hm1 : ∀ D x y a, a ∈ D → (a ∈ mix D x y ↔ a ∈ x) := by
    intro D x y a h; simp [mix, h]
  have hm2 : ∀ D x y a, a ∉ D → (a ∈ mix D x y ↔ a ∈ y) := by
    intro D x y a h; simp [mix, h]
  have hinv : ∀ D x y, mix D (mix D x y) (mix D y x) = x := by
    intro D x y
    ext a
    by_cases h : a ∈ D
    · rw [hm1 _ _ _ _ h, hm1 _ _ _ _ h]
    · rw [hm2 _ _ _ _ h, hm2 _ _ _ _ h]
  have hswap : ∀ (D : Finset (Fin n)) (P1 P2 Q1 Q2 : Finset (Fin n) → Prop)
      [DecidablePred P1] [DecidablePred P2] [DecidablePred Q1] [DecidablePred Q2],
      (∀ z ∈ xs, ∀ w ∈ xs, P1 z → P2 w →
        mix D z w ∈ xs ∧ mix D w z ∈ xs ∧ Q1 (mix D z w) ∧ Q2 (mix D w z)) →
      (∀ z ∈ xs, ∀ w ∈ xs, Q1 z → Q2 w →
        mix D z w ∈ xs ∧ mix D w z ∈ xs ∧ P1 (mix D z w) ∧ P2 (mix D w z)) →
      (xs.filter P1).card * (xs.filter P2).card = (xs.filter Q1).card * (xs.filter Q2).card := by
    intro D P1 P2 Q1 Q2 _ _ _ _ hf hb
    rw [← Finset.card_product, ← Finset.card_product]
    refine Finset.card_bij' (fun p _ => (mix D p.1 p.2, mix D p.2 p.1))
      (fun p _ => (mix D p.1 p.2, mix D p.2 p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter] at hp ⊢
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hp
      obtain ⟨c1, c2, c3, c4⟩ := hf _ a1 _ b1 a2 b2
      exact ⟨⟨c1, c3⟩, ⟨c2, c4⟩⟩
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter] at hp ⊢
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hp
      obtain ⟨c1, c2, c3, c4⟩ := hb _ a1 _ b1 a2 b2
      exact ⟨⟨c1, c3⟩, ⟨c2, c4⟩⟩
    · intro p _
      exact Prod.ext (hinv D p.1 p.2) (hinv D p.2 p.1)
    · intro p _
      exact Prod.ext (hinv D p.1 p.2) (hinv D p.2 p.1)
  have hclose : ∀ (D : Finset (Fin n)) (s : Fin n), (∀ j, j = s ∨ par j = s ∨ (j ∈ D ↔ par j ∈ D)) →
      ∀ x ∈ xs, ∀ y ∈ xs, (s ∈ x ↔ s ∈ y) → mix D x y ∈ xs := by
    intro D s hD x hx y hy hs
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => ?_⟩
    have hx' := (Finset.mem_filter.1 hx).2 j
    have hy' := (Finset.mem_filter.1 hy).2 j
    have hsm : s ∈ mix D x y ↔ s ∈ x := by
      by_cases h : s ∈ D
      · exact hm1 _ _ _ _ h
      · rw [hm2 _ _ _ _ h]; exact hs.symm
    have key : (par j ∈ mix D x y ↔ par j ∈ x) ∧ (j ∈ mix D x y ↔ j ∈ x) ∨
        (par j ∈ mix D x y ↔ par j ∈ y) ∧ (j ∈ mix D x y ↔ j ∈ y) := by
      rcases hD j with h | h | h
      · have hj : (j ∈ mix D x y ↔ j ∈ x) := by rw [h]; exact hsm
        have hj' : (j ∈ mix D x y ↔ j ∈ y) := by rw [h]; exact hsm.trans hs
        by_cases hp : par j ∈ D
        · exact Or.inl ⟨hm1 _ _ _ _ hp, hj⟩
        · exact Or.inr ⟨hm2 _ _ _ _ hp, hj'⟩
      · have hp : (par j ∈ mix D x y ↔ par j ∈ x) := by rw [h]; exact hsm
        have hp' : (par j ∈ mix D x y ↔ par j ∈ y) := by rw [h]; exact hsm.trans hs
        by_cases hj : j ∈ D
        · exact Or.inl ⟨hp, hm1 _ _ _ _ hj⟩
        · exact Or.inr ⟨hp', hm2 _ _ _ _ hj⟩
      · by_cases hj : j ∈ D
        · exact Or.inl ⟨hm1 _ _ _ _ (h.1 hj), hm1 _ _ _ _ hj⟩
        · exact Or.inr ⟨hm2 _ _ _ _ (fun hp => hj (h.2 hp)), hm2 _ _ _ _ hj⟩
    rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · rw [decide_eq_decide.2 k1, decide_eq_decide.2 k2]; exact hx'
    · rw [decide_eq_decide.2 k1, decide_eq_decide.2 k2]; exact hy'
  let M := fun (u v : Fin n) (a b : Bool) =>
    (xs.filter (fun x => decide (u ∈ x) = a ∧ decide (v ∈ x) = b)).card
  let m := fun (s : Fin n) (b : Bool) => (xs.filter (fun x => decide (s ∈ x) = b)).card
  let Tc := fun (u s v : Fin n) (a b c : Bool) =>
    (xs.filter (fun x => decide (u ∈ x) = a ∧ decide (s ∈ x) = b ∧ decide (v ∈ x) = c)).card
  let det := fun (u v : Fin n) =>
    (M u v false false : Int) * (M u v true true : Int)
      - (M u v false true : Int) * (M u v true false : Int)
  have hsplit : ∀ (u v s : Fin n) (a c : Bool), M u v a c = Tc u s v a false c + Tc u s v a true c := by
    intro u v s a c
    dsimp only [M, Tc]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => decide (s ∈ x)) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _), Fintype.sum_bool, add_comm]
    simp only [Finset.filter_filter]
    congr 1 <;> congr 1 <;> apply Finset.filter_congr <;> intro x _ <;> tauto
  have hid : ∀ (D : Finset (Fin n)) (s t : Fin n), (∀ j, j = s ∨ par j = s ∨ (j ∈ D ↔ par j ∈ D)) →
      r ∈ D → t ∉ D → (m s false : Int) ≠ 0 → (m s true : Int) ≠ 0 →
      (m s false : Int) * (m s true : Int) * det r t = det r s * det s t := by
    intro D s t hD hrD htD h0 h1
    have hT : ∀ a b c, Tc r s t a b c * m s b = M r s a b * M s t b c := by
      intro a b c
      refine hswap D _ _ _ _ ?_ ?_
      · intro z hz w hw p1 p2
        have ag : s ∈ z ↔ s ∈ w := decide_eq_decide.1 (p1.2.1.trans p2.symm)
        refine ⟨hclose D s hD z hz w hw ag, hclose D s hD w hw z hz ag.symm, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · rw [decide_eq_decide.2 (hm1 _ _ _ _ hrD)]; exact p1.1
        · by_cases hs : s ∈ D
          · rw [decide_eq_decide.2 (hm1 _ _ _ _ hs)]; exact p1.2.1
          · rw [decide_eq_decide.2 (hm2 _ _ _ _ hs)]; exact p2
        · by_cases hs : s ∈ D
          · rw [decide_eq_decide.2 (hm1 _ _ _ _ hs)]; exact p2
          · rw [decide_eq_decide.2 (hm2 _ _ _ _ hs)]; exact p1.2.1
        · rw [decide_eq_decide.2 (hm2 _ _ _ _ htD)]; exact p1.2.2
      · intro z hz w hw q1 q2
        have ag : s ∈ z ↔ s ∈ w := decide_eq_decide.1 (q1.2.trans q2.1.symm)
        refine ⟨hclose D s hD z hz w hw ag, hclose D s hD w hw z hz ag.symm, ⟨?_, ?_, ?_⟩, ?_⟩
        · rw [decide_eq_decide.2 (hm1 _ _ _ _ hrD)]; exact q1.1
        · by_cases hs : s ∈ D
          · rw [decide_eq_decide.2 (hm1 _ _ _ _ hs)]; exact q1.2
          · rw [decide_eq_decide.2 (hm2 _ _ _ _ hs)]; exact q2.1
        · rw [decide_eq_decide.2 (hm2 _ _ _ _ htD)]; exact q2.2
        · by_cases hs : s ∈ D
          · rw [decide_eq_decide.2 (hm1 _ _ _ _ hs)]; exact q2.1
          · rw [decide_eq_decide.2 (hm2 _ _ _ _ hs)]; exact q1.2
    have h : ∀ a b c, (Tc r s t a b c : Int) * (m s b : Int) = (M r s a b : Int) * (M s t b c : Int) := by
      intro a b c; exact_mod_cast hT a b c
    have hE : ∀ a c, (m s false : Int) * (m s true : Int) * (M r t a c : Int)
        = (m s true : Int) * ((M r s a false : Int) * (M s t false c : Int))
          + (m s false : Int) * ((M r s a true : Int) * (M s t true c : Int)) := by
      intro a c
      rw [← h, ← h, hsplit r t s a c]
      push_cast
      ring
    have h2 : ((m s false : Int) * (m s true : Int)) *
        ((m s false : Int) * (m s true : Int) * det r t)
        = ((m s false : Int) * (m s true : Int)) * (det r s * det s t) := by
      dsimp only [det]
      calc _ = ((m s false : Int) * (m s true : Int) * (M r t false false : Int))
              * ((m s false : Int) * (m s true : Int) * (M r t true true : Int))
            - ((m s false : Int) * (m s true : Int) * (M r t false true : Int))
              * ((m s false : Int) * (m s true : Int) * (M r t true false : Int)) := by ring
        _ = _ := by rw [hE, hE, hE, hE]; ring
    exact mul_left_cancel₀ (mul_ne_zero h0 h1) h2
  let Adj := fun (v w : Fin n) => ∃ i, ¬ splits i ∧ par i ≠ i ∧
    ((par i = v ∧ i = w) ∨ (par i = w ∧ i = v))
  have hMsym : ∀ u v a b, M u v a b = M v u b a := by
    intro u v a b
    dsimp only [M]
    congr 1
    apply Finset.filter_congr
    intro x _
    exact and_comm
  have hdsym : ∀ u v, det u v = det v u := by
    intro u v
    dsimp only [det]
    rw [hMsym u v false false, hMsym u v true true, hMsym u v false true, hMsym u v true false]
    ring
  have hMle : ∀ u v a c, M u v a c ≤ m u a := by
    intro u v a c
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩
  have hmarg : ∀ u v, det u v ≠ 0 → (m u false : Int) ≠ 0 ∧ (m u true : Int) ≠ 0 := by
    intro u v h
    constructor
    · intro h0
      have h0' : m u false = 0 := by exact_mod_cast h0
      apply h
      have e1 : M u v false false = 0 := Nat.le_zero.1 (h0' ▸ hMle u v false false)
      have e2 : M u v false true = 0 := Nat.le_zero.1 (h0' ▸ hMle u v false true)
      dsimp only [det]
      rw [e1, e2]; simp
    · intro h0
      have h0' : m u true = 0 := by exact_mod_cast h0
      apply h
      have e1 : M u v true false = 0 := Nat.le_zero.1 (h0' ▸ hMle u v true false)
      have e2 : M u v true true = 0 := Nat.le_zero.1 (h0' ▸ hMle u v true true)
      dsimp only [det]
      rw [e1, e2]; simp
  have hge : ∀ k j, par^[k] j ≤ j := by
    intro k
    induction k with
    | zero => intro j; simp
    | succ k ih =>
      intro j
      rw [Function.iterate_succ_apply]
      exact le_trans (ih (par j)) (hpar j)
  have hstep : ∀ v w, Adj v w → (v = r ∨ det r v ≠ 0) → (w = r ∨ det r w ≠ 0) := by
    rintro v w ⟨i, hns, hpi, hor⟩ hv
    classical
    have hJ : det (par i) i ≠ 0 := by
      intro h0
      apply hns
      have h1 : (M (par i) i false false : Int) * (M (par i) i true true : Int)
          = (M (par i) i false true : Int) * (M (par i) i true false : Int) := sub_eq_zero.1 h0
      change M (par i) i false false * M (par i) i true true
        = M (par i) i false true * M (par i) i true false
      exact_mod_cast h1
    have hvw : det v w ≠ 0 := by
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hJ
      · rw [← h1, ← h2, hdsym]; exact hJ
    have mv := hmarg v w hvw
    have mw := hmarg w v (by rw [hdsym]; exact hvw)
    have hrv : det r v ≠ 0 := by
      rcases hv with h | h
      · rw [← h]
        have e1 : ∀ a, M v v a a = m v a := by
          intro a
          dsimp only [M, m]
          congr 1
          apply Finset.filter_congr
          intro x _
          exact and_self_iff
        have e2 : M v v false true = 0 := by
          apply Finset.card_eq_zero.2
          apply Finset.filter_eq_empty_iff.2
          rintro x _ ⟨a1, a2⟩
          rw [a1] at a2
          exact Bool.false_ne_true a2
        dsimp only [det]
        rw [e1, e1, e2, Nat.cast_zero, zero_mul, sub_zero]
        exact mul_ne_zero mv.1 mv.2
      · exact h
    by_cases hwr : w = r
    · exact Or.inl hwr
    right
    let Dsc := Finset.univ.filter (fun j => ∃ k, par^[k] j = i)
    have hiD : i ∈ Dsc := Finset.mem_filter.2 ⟨Finset.mem_univ _, 0, rfl⟩
    have hpD : par i ∉ Dsc := by
      intro h
      obtain ⟨k, hk⟩ := (Finset.mem_filter.1 h).2
      have := hge k (par i)
      rw [hk] at this
      exact hpi (le_antisymm (hpar i) this)
    have hcross : ∀ j, j = i ∨ (j ∈ Dsc ↔ par j ∈ Dsc) := by
      intro j
      by_cases hj : j = i
      · exact Or.inl hj
      right
      constructor
      · intro h
        obtain ⟨k, hk⟩ := (Finset.mem_filter.1 h).2
        cases k with
        | zero => exact absurd hk hj
        | succ k =>
          rw [Function.iterate_succ_apply] at hk
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, k, hk⟩
      · intro h
        obtain ⟨k, hk⟩ := (Finset.mem_filter.1 h).2
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, k + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        exact hk
    have c1 : ∀ s, (s = i ∨ s = par i) → ∀ j, j = s ∨ par j = s ∨ (j ∈ Dsc ↔ par j ∈ Dsc) := by
      intro s hs j
      rcases hcross j with h | h
      · rcases hs with e | e
        · exact Or.inl (h.trans e.symm)
        · exact Or.inr (Or.inl (by rw [h, e]))
      · exact Or.inr (Or.inr h)
    have c2 : ∀ s, (s = i ∨ s = par i) → ∀ j, j = s ∨ par j = s ∨ (j ∈ Dscᶜ ↔ par j ∈ Dscᶜ) := by
      intro s hs j
      rcases c1 s hs j with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by rw [Finset.mem_compl, Finset.mem_compl, h]))
    have fwd : ∀ D : Finset (Fin n), (∀ j, j = v ∨ par j = v ∨ (j ∈ D ↔ par j ∈ D)) →
        r ∈ D → w ∉ D → det r w ≠ 0 := by
      intro D a b c h0
      have e := hid D v w a b c mv.1 mv.2
      rw [h0, mul_zero] at e
      exact mul_ne_zero hrv hvw e.symm
    have bwd : ∀ D : Finset (Fin n), (∀ j, j = w ∨ par j = w ∨ (j ∈ D ↔ par j ∈ D)) →
        r ∈ D → v ∉ D → det r w ≠ 0 := by
      intro D a b c h0
      have e := hid D w v a b c mw.1 mw.2
      rw [h0, zero_mul] at e
      exact mul_ne_zero (mul_ne_zero mw.1 mw.2) hrv e
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hr : r ∈ Dsc
      · exact bwd Dsc (c1 w (Or.inl h2.symm)) hr (h1 ▸ hpD)
      · exact fwd Dscᶜ (c2 v (Or.inr h1.symm)) (Finset.mem_compl.2 hr)
          (fun h => Finset.mem_compl.1 h (h2 ▸ hiD))
    · by_cases hr : r ∈ Dsc
      · exact fwd Dsc (c1 v (Or.inl h2.symm)) hr (h1 ▸ hpD)
      · exact bwd Dscᶜ (c2 w (Or.inr h1.symm)) (Finset.mem_compl.2 hr)
          (fun h => Finset.mem_compl.1 h (h2 ▸ hiD))
  have h1 : independent T → ∀ i ∈ T, independent {i} := by
    intro h i hi B _
    have hTi : T ∩ {i} = {i} := Finset.inter_singleton_of_mem hi
    have hsum : ∀ b, pin b {i} B
        = ∑ B' ∈ T.powerset.filter (fun B' => B' ∩ {i} = B), pin b T B' := by
      intro b
      dsimp only [pin]
      rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x ∩ T)
        (t := T.powerset.filter (fun B' => B' ∩ {i} = B))]
      · refine Finset.sum_congr rfl (fun B' hB' => ?_)
        rw [Finset.filter_filter]
        congr 1
        apply Finset.filter_congr
        intro x _
        have hh := (Finset.mem_filter.1 hB').2
        constructor
        · rintro ⟨⟨a1, _⟩, a3⟩; exact ⟨a1, a3⟩
        · rintro ⟨a1, a3⟩
          refine ⟨⟨a1, ?_⟩, a3⟩
          rw [← hh, ← a3, Finset.inter_assoc, hTi]
      · intro x hx
        have hx' := (Finset.mem_filter.1 hx).2
        refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 Finset.inter_subset_right, ?_⟩
        show x ∩ T ∩ {i} = B
        rw [Finset.inter_assoc, hTi]
        exact hx'.2
    rw [hsum false, hsum true, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl
      (fun B' hB' => h B' (Finset.mem_powerset.1 (Finset.mem_filter.1 hB').1))
  have h2 : (∀ i ∈ T, independent {i}) → ∃ U : Finset (Fin n), r ∈ U ∧ Disjoint U T ∧
      ∀ i, (decide (i ∈ U) != decide (par i ∈ U)) = true → splits i := by
    intro hs
    classical
    refine ⟨Finset.univ.filter (fun v => Relation.ReflTransGen Adj r v),
      Finset.mem_filter.2 ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩, ?_, ?_⟩
    · refine Finset.disjoint_left.2 (fun t htU htT => ?_)
      have reach : ∀ v, Relation.ReflTransGen Adj r v → v = r ∨ det r v ≠ 0 := by
        intro v hv
        induction hv with
        | refl => exact Or.inl rfl
        | tail _ hadj ih => exact hstep _ _ hadj ih
      rcases reach t (Finset.mem_filter.1 htU).2 with h | h
      · exact hrT (h ▸ htT)
      apply h
      have e := hs t htT ∅ (Finset.empty_subset _)
      have a1 : ∀ b, pin b {t} ∅ = M r t b false := by
        intro b
        dsimp only [pin, M]
        congr 1
        apply Finset.filter_congr
        intro x _
        rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_singleton_right]
        simp
      have a2 : ∀ b, pin b ∅ ∅ = M r t b false + M r t b true := by
        intro b
        dsimp only [pin, M]
        rw [Finset.card_eq_sum_card_fiberwise (f := fun x => decide (t ∈ x)) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _), Fintype.sum_bool, add_comm]
        simp only [Finset.filter_filter, Finset.inter_empty, and_true]
      rw [a1 false, a1 true, a2 true, a2 false] at e
      have e' : (M r t false false : Int) * ((M r t true false : Int) + (M r t true true : Int))
          = (M r t true false : Int) * ((M r t false false : Int) + (M r t false true : Int)) := by
        exact_mod_cast e
      dsimp only [det]
      linear_combination e'
    · intro i hi
      by_contra hns
      have hpi : par i ≠ i := by
        intro e
        rw [e] at hi
        simp at hi
      have a1 : Adj (par i) i := ⟨i, hns, hpi, Or.inl ⟨rfl, rfl⟩⟩
      have a2 : Adj i (par i) := ⟨i, hns, hpi, Or.inr ⟨rfl, rfl⟩⟩
      have hiff : i ∈ Finset.univ.filter (fun v => Relation.ReflTransGen Adj r v) ↔
          par i ∈ Finset.univ.filter (fun v => Relation.ReflTransGen Adj r v) := by
        constructor
        · intro h
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 h).2.tail a2⟩
        · intro h
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 h).2.tail a1⟩
      rw [bne_iff_ne] at hi
      exact hi (decide_eq_decide.2 hiff)
  have h3 : (∃ U : Finset (Fin n), r ∈ U ∧ Disjoint U T ∧
      ∀ i, (decide (i ∈ U) != decide (par i ∈ U)) = true → splits i) → independent T := by
    rintro ⟨U, hrU, hdisj, hbd⟩ B _
    have hall : ∀ j, splits j → ∀ x ∈ xs, ∀ y ∈ xs,
        allow j (decide (par j ∈ x)) (decide (j ∈ y)) = true := by
      intro j hs x hx y hy
      by_contra h
      have h0 : joint j (decide (par j ∈ x)) (decide (j ∈ y)) = 0 := by
        apply Finset.card_eq_zero.2
        apply Finset.filter_eq_empty_iff.2
        rintro z hz ⟨a1, a2⟩
        apply h
        rw [← a1, ← a2]
        exact (Finset.mem_filter.1 hz).2 j
      have hx1 : 0 < joint j (decide (par j ∈ x)) (decide (j ∈ x)) :=
        Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨hx, rfl, rfl⟩⟩
      have hy1 : 0 < joint j (decide (par j ∈ y)) (decide (j ∈ y)) :=
        Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨hy, rfl, rfl⟩⟩
      change joint j false false * joint j true true = joint j false true * joint j true false at hs
      revert h0 hx1 hy1
      generalize decide (par j ∈ x) = a
      generalize decide (j ∈ y) = b
      generalize decide (j ∈ x) = c
      generalize decide (par j ∈ y) = d
      intro h0 hx1 hy1
      cases a <;> cases b <;> cases c <;> cases d <;>
        first
        | exact absurd h0 (Nat.ne_of_gt hx1)
        | exact absurd h0 (Nat.ne_of_gt hy1)
        | (have p := Nat.mul_pos hx1 hy1
           rw [h0] at hs
           simp at hs
           rcases hs with q | q <;> rw [q] at p <;> simp at p)
    have hcl : ∀ x ∈ xs, ∀ y ∈ xs, mix U x y ∈ xs := by
      intro x hx y hy
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => ?_⟩
      by_cases hside : (j ∈ U ↔ par j ∈ U)
      · by_cases hj : j ∈ U
        · rw [decide_eq_decide.2 (hm1 U x y _ (hside.1 hj)), decide_eq_decide.2 (hm1 U x y _ hj)]
          exact (Finset.mem_filter.1 hx).2 j
        · rw [decide_eq_decide.2 (hm2 U x y _ (fun hp => hj (hside.2 hp))),
            decide_eq_decide.2 (hm2 U x y _ hj)]
          exact (Finset.mem_filter.1 hy).2 j
      · have hs : splits j := by
          apply hbd
          by_cases a : j ∈ U <;> by_cases b : par j ∈ U <;> simp [a, b] at hside ⊢
        by_cases hj : j ∈ U
        · have hp : par j ∉ U := fun hp => hside ⟨fun _ => hp, fun _ => hj⟩
          rw [decide_eq_decide.2 (hm2 U x y _ hp), decide_eq_decide.2 (hm1 U x y _ hj)]
          exact hall j hs y hy x hx
        · have hp : par j ∈ U := by
            by_contra hp
            exact hside ⟨fun a => absurd a hj, fun a => absurd a hp⟩
          rw [decide_eq_decide.2 (hm1 U x y _ hp), decide_eq_decide.2 (hm2 U x y _ hj)]
          exact hall j hs x hx y hy
    have hrest : ∀ x y : Finset (Fin n), mix U x y ∩ T = y ∩ T := by
      intro x y
      ext a
      simp only [Finset.mem_inter]
      exact and_congr_left (fun ha => hm2 _ _ _ _ (fun h => Finset.disjoint_left.1 hdisj h ha))
    have e : ∀ b, pin b T B * (xs.filter (fun _ => True)).card
        = (xs.filter (fun x => decide (r ∈ x) = b)).card * (xs.filter (fun x => x ∩ T = B)).card := by
      intro b
      refine hswap U _ _ _ _ ?_ ?_
      · intro z hz w hw p1 _
        refine ⟨hcl z hz w hw, hcl w hw z hz, ?_, ?_⟩
        · rw [decide_eq_decide.2 (hm1 _ _ _ _ hrU)]; exact p1.1
        · rw [hrest]; exact p1.2
      · intro z hz w hw q1 q2
        refine ⟨hcl z hz w hw, hcl w hw z hz, ⟨?_, ?_⟩, trivial⟩
        · rw [decide_eq_decide.2 (hm1 _ _ _ _ hrU)]; exact q1
        · rw [hrest]; exact q2
    have hp : ∀ b, pin b ∅ ∅ = (xs.filter (fun x => decide (r ∈ x) = b)).card := by
      intro b
      dsimp only [pin]
      congr 1
      apply Finset.filter_congr
      intro x _
      simp
    by_cases hN : (xs.filter (fun _ => True)).card = 0
    · have hxs : xs = ∅ := by
        rw [Finset.filter_true] at hN
        exact Finset.card_eq_zero.1 hN
      have z : ∀ b S B', pin b S B' = 0 := by
        intro b S B'
        dsimp only [pin]
        rw [hxs]
        simp
      rw [z false T B, z true T B, Nat.zero_mul, Nat.zero_mul]
    · apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN)
      calc pin false T B * pin true ∅ ∅ * (xs.filter (fun _ => True)).card
          = (pin false T B * (xs.filter (fun _ => True)).card) * pin true ∅ ∅ := by ring
        _ = ((xs.filter (fun x => decide (r ∈ x) = false)).card * (xs.filter (fun x => x ∩ T = B)).card)
              * (xs.filter (fun x => decide (r ∈ x) = true)).card := by rw [e false, hp true]
        _ = ((xs.filter (fun x => decide (r ∈ x) = true)).card * (xs.filter (fun x => x ∩ T = B)).card)
              * (xs.filter (fun x => decide (r ∈ x) = false)).card := by ring
        _ = (pin true T B * (xs.filter (fun _ => True)).card) * pin false ∅ ∅ := by rw [e true, hp false]
        _ = pin true T B * pin false ∅ ∅ * (xs.filter (fun _ => True)).card := by ring
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨fun h => h2 (h1 h), h3⟩⟩
