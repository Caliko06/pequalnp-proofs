import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25459 : (∀ (n m t : ℕ) (K : Bool → Bool → (Fin n → Bool) → (Fin m → Bool) → Bool) (A : Fin n → Fin m → Bool), 1 ≤ t → t + 2 ≤ n → t ≤ m → (t + 3 ≤ n ∨ t + 3 ≤ m) → (∀ (a a' b b' : Bool) (x x' : Fin n → Bool) (y y' : Fin m → Bool), a ≤ a' → b ≤ b' → (∀ i, x i ≤ x' i) → (∀ j, y j ≤ y' j) → K a b x y ≤ K a' b' x' y') → (∀ (a b : Bool) (x x' : Fin n → Bool) (y y' : Fin m → Bool), (∀ i : Fin n, t < i.val → i.val < n - 1 → x i = x' i) → (∀ j : Fin m, t ≤ j.val → j.val < m - 1 → y j = y' j) → K a b x y = K a b x' y') → A = (fun u v => K (!(decide (u.val = v.val ∧ u.val < t))) (!(decide (u.val = t))) (fun p => decide (p = u)) (fun q => decide (q = v))) → (∃ u u' : Fin n, u ≠ u' ∧ ∀ v, A u v = A u' v) ∨ (∃ v v' : Fin m, v ≠ v' ∧ ∀ u, A u v = A u v')) := by
  intro n m t K A ht htn htm hbig hmono hind hA
  subst hA
  let u0 : Fin n := ⟨0, by omega⟩
  let uL : Fin n := ⟨n - 1, by omega⟩
  let v0 : Fin m := ⟨0, by omega⟩
  have hu0L : u0 ≠ uL := by
    intro h
    have := congrArg Fin.val h
    simp [u0, uL] at this
    omega
  have hx_eq : ∀ i : Fin n, t < i.val → i.val < n - 1 →
      (fun p => decide (p = u0)) i = (fun p => decide (p = uL)) i := by
    intro i hi1 hi2
    have h1 : i ≠ u0 := fun h => by subst h; simp [u0] at hi1
    have h2 : i ≠ uL := fun h => by subst h; simp [uL] at hi2
    simp [h1, h2]
  by_cases hval : K (!decide (uL.val = v0.val ∧ uL.val < t)) (!decide (uL.val = t))
      (fun p => decide (p = uL)) (fun q => decide (q = v0)) = false
  · left
    refine ⟨u0, uL, hu0L, fun v => ?_⟩
    dsimp only
    have hb0 : (!decide (u0.val = t)) = true := by simp [u0]; omega
    have hbL : (!decide (uL.val = t)) = true := by simp [uL]; omega
    have haL : (!decide (uL.val = v.val ∧ uL.val < t)) = true := by simp [uL]; omega
    by_cases hv : v = v0
    · subst hv
      have hle : K (!decide (u0.val = v0.val ∧ u0.val < t)) (!decide (u0.val = t))
          (fun p => decide (p = u0)) (fun q => decide (q = v0)) ≤
          K (!decide (uL.val = v0.val ∧ uL.val < t)) (!decide (uL.val = t))
          (fun p => decide (p = uL)) (fun q => decide (q = v0)) := by
        rw [hind _ _ _ (fun p => decide (p = uL)) _ _ hx_eq (fun _ _ _ => rfl)]
        exact hmono _ _ _ _ _ _ _ _ (by rw [haL]; exact Bool.le_true _) (by rw [hb0, hbL])
          (fun _ => le_rfl) (fun _ => le_rfl)
      rw [hval] at hle
      cases hcur : K (!decide (u0.val = v0.val ∧ u0.val < t)) (!decide (u0.val = t))
          (fun p => decide (p = u0)) (fun q => decide (q = v0))
      · exact hval.symm
      · rw [hcur] at hle; exact absurd hle (by decide)
    · have ha0 : (!decide (u0.val = v.val ∧ u0.val < t)) = true := by
        have hv0 : v.val ≠ 0 := fun h => hv (Fin.ext h)
        simp [u0, hv0.symm]
      rw [ha0, haL, hb0, hbL]
      exact hind true true _ _ _ _ hx_eq (fun _ _ _ => rfl)
  · have htrue : K true true (fun _ => false) (fun _ => false) = true := by
      have haL : (!decide (uL.val = v0.val ∧ uL.val < t)) = true := by simp [uL]; omega
      have hbL : (!decide (uL.val = t)) = true := by simp [uL]; omega
      rw [haL, hbL] at hval
      have h1 : K true true (fun p => decide (p = uL)) (fun q => decide (q = v0)) = true :=
        Bool.eq_true_of_not_eq_false hval
      have heq := hind true true (fun p => decide (p = uL)) (fun _ => false)
        (fun q => decide (q = v0)) (fun _ => false)
        (fun i _ hi2 => by
          have : i ≠ uL := fun h => by subst h; simp [uL] at hi2
          simp [this])
        (fun j hj1 _ => by
          have : j ≠ v0 := fun h => by subst h; simp [v0] at hj1; omega
          simp [this])
      rw [← heq]
      exact h1
    have hall : ∀ (u : Fin n) (v : Fin m), u.val ≠ t → ¬(u.val = v.val ∧ u.val < t) →
        K (!decide (u.val = v.val ∧ u.val < t)) (!decide (u.val = t))
          (fun p => decide (p = u)) (fun q => decide (q = v)) = true := by
      intro u v hut huv
      have ha : (!decide (u.val = v.val ∧ u.val < t)) = true := by simp [huv]
      have hb : (!decide (u.val = t)) = true := by simp [hut]
      rw [ha, hb]
      have hle := hmono true true true true (fun _ => false) (fun p => decide (p = u))
        (fun _ => false) (fun q => decide (q = v)) le_rfl le_rfl
        (fun _ => Bool.false_le _) (fun _ => Bool.false_le _)
      rw [htrue] at hle
      cases hcur : K true true (fun p => decide (p = u)) (fun q => decide (q = v))
      · rw [hcur] at hle; exact absurd hle (by decide)
      · rfl
    rcases hbig with hn3 | hm3
    · left
      let u1 : Fin n := ⟨t + 1, by omega⟩
      refine ⟨u1, uL, ?_, fun v => ?_⟩
      · intro h
        have := congrArg Fin.val h
        simp [u1, uL] at this
        omega
      · dsimp only
        rw [hall u1 v (by simp [u1]) (by simp [u1]),
            hall uL v (by simp [uL]; omega) (by simp [uL]; omega)]
    · right
      let v1 : Fin m := ⟨t, by omega⟩
      let v2 : Fin m := ⟨t + 1, by omega⟩
      let v3 : Fin m := ⟨t + 2, by omega⟩
      let ut : Fin n := ⟨t, by omega⟩
      have hne12 : v1 ≠ v2 := fun h => by have := congrArg Fin.val h; simp [v1, v2] at this
      have hne13 : v1 ≠ v3 := fun h => by have := congrArg Fin.val h; simp [v1, v3] at this
      have hne23 : v2 ≠ v3 := fun h => by have := congrArg Fin.val h; simp [v2, v3] at this
      have hcol : ∀ (va vb : Fin m), t ≤ va.val → t ≤ vb.val →
          K (!decide (ut.val = va.val ∧ ut.val < t)) (!decide (ut.val = t))
            (fun p => decide (p = ut)) (fun q => decide (q = va)) =
          K (!decide (ut.val = vb.val ∧ ut.val < t)) (!decide (ut.val = t))
            (fun p => decide (p = ut)) (fun q => decide (q = vb)) →
          ∀ u : Fin n,
            K (!decide (u.val = va.val ∧ u.val < t)) (!decide (u.val = t))
              (fun p => decide (p = u)) (fun q => decide (q = va)) =
            K (!decide (u.val = vb.val ∧ u.val < t)) (!decide (u.val = t))
              (fun p => decide (p = u)) (fun q => decide (q = vb)) := by
        intro va vb hva hvb heq u
        by_cases hu : u = ut
        · subst hu; exact heq
        · have hut : u.val ≠ t := fun h => hu (Fin.ext h)
          rw [hall u va hut (by omega), hall u vb hut (by omega)]
      generalize hb1 : K (!decide (ut.val = v1.val ∧ ut.val < t)) (!decide (ut.val = t))
          (fun p => decide (p = ut)) (fun q => decide (q = v1)) = b1
      generalize hb2 : K (!decide (ut.val = v2.val ∧ ut.val < t)) (!decide (ut.val = t))
          (fun p => decide (p = ut)) (fun q => decide (q = v2)) = b2
      generalize hb3 : K (!decide (ut.val = v3.val ∧ ut.val < t)) (!decide (ut.val = t))
          (fun p => decide (p = ut)) (fun q => decide (q = v3)) = b3
      have hv1 : t ≤ v1.val := by simp [v1]
      have hv2 : t ≤ v2.val := by simp [v2]
      have hv3 : t ≤ v3.val := by simp [v3]
      cases b1 <;> cases b2 <;> cases b3
      · exact ⟨v1, v2, hne12, hcol v1 v2 hv1 hv2 (hb1.trans hb2.symm)⟩
      · exact ⟨v1, v2, hne12, hcol v1 v2 hv1 hv2 (hb1.trans hb2.symm)⟩
      · exact ⟨v1, v3, hne13, hcol v1 v3 hv1 hv3 (hb1.trans hb3.symm)⟩
      · exact ⟨v2, v3, hne23, hcol v2 v3 hv2 hv3 (hb2.trans hb3.symm)⟩
      · exact ⟨v2, v3, hne23, hcol v2 v3 hv2 hv3 (hb2.trans hb3.symm)⟩
      · exact ⟨v1, v3, hne13, hcol v1 v3 hv1 hv3 (hb1.trans hb3.symm)⟩
      · exact ⟨v1, v2, hne12, hcol v1 v2 hv1 hv2 (hb1.trans hb2.symm)⟩
      · exact ⟨v1, v2, hne12, hcol v1 v2 hv1 hv2 (hb1.trans hb2.symm)⟩
