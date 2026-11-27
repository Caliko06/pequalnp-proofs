import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25758

open scoped BigOperators

private def radFn25758 (f : Bool → Bool → Bool) : ℕ :=
  let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
  if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3

private def mkGate25758 (b00 b01 b10 b11 : Bool) : Bool → Bool → Bool
  | false, false => b00
  | false, true  => b01
  | true,  false => b10
  | true,  true  => b11

private lemma eq_mkGate25758 (f : Bool → Bool → Bool) :
    f = mkGate25758 (f false false) (f false true) (f true false) (f true true) := by
  funext a b
  cases a <;> cases b <;> rfl

private def selEnc25758 (e0 e1 e2 : Bool × Bool) {r : ℕ} (c : Fin r) : Bool × Bool :=
  if c.val = 0 then e0 else if c.val = 1 then e1 else e2

private def selDec25758 {r : ℕ} (d00 d01 d10 d11 : Fin r) : Bool × Bool → Fin r
  | (false, false) => d00
  | (false, true)  => d01
  | (true,  false) => d10
  | (true,  true)  => d11

private lemma mkGate_enc_dec25758 : ∀ (b00 b01 b10 b11 : Bool),
    let g := mkGate25758 b00 b01 b10 b11
    ∃ (e0 e1 e2 : Bool × Bool) (d00 d01 d10 d11 : Fin (radFn25758 g)),
      (∀ c₁ c₂ : Fin (radFn25758 g),
        (g (selEnc25758 e0 e1 e2 c₁).1 (selEnc25758 e0 e1 e2 c₂).2 =
         g (selEnc25758 e0 e1 e2 c₂).1 (selEnc25758 e0 e1 e2 c₁).2) ↔ c₁ = c₂) ∧
      (∀ p₁ p₂ : Bool × Bool,
        selDec25758 d00 d01 d10 d11 p₁ = selDec25758 d00 d01 d10 d11 p₂ →
          g p₁.1 p₂.2 = g p₂.1 p₁.2) := by
  decide

private lemma gate_enc_dec25758 (f : Bool → Bool → Bool) :
    ∃ (enc : Fin (radFn25758 f) → Bool × Bool) (dec : Bool × Bool → Fin (radFn25758 f)),
      (∀ c₁ c₂ : Fin (radFn25758 f), (f (enc c₁).1 (enc c₂).2 = f (enc c₂).1 (enc c₁).2) ↔ c₁ = c₂) ∧
      (∀ p₁ p₂ : Bool × Bool, dec p₁ = dec p₂ → f p₁.1 p₂.2 = f p₂.1 p₁.2) := by
  rw [eq_mkGate25758 f]
  obtain ⟨e0, e1, e2, d00, d01, d10, d11, h1, h2⟩ :=
    mkGate_enc_dec25758 (f false false) (f false true) (f true false) (f true true)
  exact ⟨selEnc25758 e0 e1 e2, selDec25758 d00 d01 d10 d11, h1, h2⟩

private def piFinEquiv25758 : {q : ℕ} → (d : Fin q → ℕ) → ((t : Fin q) → Fin (d t)) ≃ Fin (∏ t : Fin q, d t)
  | 0, _ =>
    { toFun := fun _ => ⟨0, by simp⟩
      invFun := fun _ t => t.elim0
      left_inv := fun _ => funext fun t => t.elim0
      right_inv := fun ⟨v, hv⟩ => by simp at hv; subst hv; rfl }
  | q + 1, d =>
    let e1 : ((t : Fin (q + 1)) → Fin (d t)) ≃ Fin (d 0) × ((i : Fin q) → Fin (d i.succ)) :=
      { toFun := fun f => (f 0, fun i => f i.succ)
        invFun := fun p => Fin.cases p.1 p.2
        left_inv := fun f => funext fun t => Fin.cases rfl (fun _ => rfl) t
        right_inv := fun ⟨_, _⟩ => Prod.ext (by simp) (funext fun _ => by simp) }
    e1.trans ((Equiv.prodCongr (Equiv.refl _) (piFinEquiv25758 (fun i => d i.succ))).trans
      (finProdFinEquiv.trans (Fin.castOrderIso (Fin.prod_univ_succ d).symm).toEquiv))

private lemma pair_eq_cases25758 {α : Type*} [DecidableEq α] {a b c d : α}
    (h : ({a, b} : Finset α) = {c, d}) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ ({c, d} : Finset α) := h ▸ by simp
  have hb : b ∈ ({c, d} : Finset α) := h ▸ by simp
  have hc : c ∈ ({a, b} : Finset α) := h.symm ▸ by simp
  have hd : d ∈ ({a, b} : Finset α) := h.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rcases hd with rfl | rfl <;> simp
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · rcases hc with rfl | rfl <;> simp

private lemma pair_eq_of_le25758 {n : ℕ} {a b c d : Fin n}
    (hab : a ≤ b) (hcd : c ≤ d) (h : ({a, b} : Finset (Fin n)) = {c, d}) :
    a = c ∧ b = d := by
  rcases pair_eq_cases25758 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨le_antisymm hab hcd, le_antisymm hcd hab⟩

end PEqualNP.Outside.L_meta_25758

theorem PEqualNP.Outside.L_meta_25758 : (∀ (n q : ℕ) (op : Fin q → Bool → Bool → Bool),
  let I := Fin n
  let rad := fun (f : Bool → Bool → Bool) =>
    let ones := ((Finset.univ : Finset (Bool × Bool)).filter (fun z => f z.1 z.2)).card
    if ones = 0 ∨ ones = 4 then 1 else if ones = 2 then 2 else 3
  let D := ∏ t : Fin q, rad (op t)
  ∀ (H : I → I → Bool) (π : Equiv.Perm I) (e : ℕ),
    (∃ (R C : Fin q → I → Bool) (out : Finset I → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (I × I)).filter (fun z =>
        out {z.1,z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2))).card ≤ e) ↔
    ∃ label : I → Fin D,
      ((Finset.univ : Finset (I × I)).filter (fun z =>
        z.1 < z.2 ∧ label z.1 = label z.2 ∧ H z.1 (π z.2) ≠ H z.2 (π z.1))).card ≤ e) := by
  classical
  intro n q op I rad D H π e
  let equivD : ((t : Fin q) → Fin (rad (op t))) ≃ Fin D :=
    PEqualNP.Outside.L_meta_25758.piFinEquiv25758 (fun t => rad (op t))
  choose enc dec henc hdec using fun t => PEqualNP.Outside.L_meta_25758.gate_enc_dec25758 (op t)
  constructor
  · rintro ⟨R, C, out, herr⟩
    let coord : I → (t : Fin q) → Fin (rad (op t)) := fun x t => dec t (R t x, C t (π x))
    let label : I → Fin D := fun x => equivD (coord x)
    refine ⟨label, ?_⟩
    let S_bad := (Finset.univ : Finset (I × I)).filter (fun z =>
      z.1 < z.2 ∧ label z.1 = label z.2 ∧ H z.1 (π z.2) ≠ H z.2 (π z.1))
    let T_bad := (Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1, z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2))
    let φ : I × I → I × I := fun z =>
      if out {z.1, z.2} (fun t => op t (R t z.1) (C t (π z.2))) ≠ H z.1 (π z.2) then z else (z.2, z.1)
    have hmaps : Set.MapsTo φ S_bad T_bad := by
      intro ⟨x, y⟩ hz
      simp only [S_bad, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rcases hz with ⟨_, hlab, hH⟩
      have hcoord : coord x = coord y := equivD.injective hlab
      have hv : (fun t => op t (R t x) (C t (π y))) = (fun t => op t (R t y) (C t (π x))) := by
        funext t
        exact hdec t (R t x, C t (π x)) (R t y, C t (π y)) (congr_fun hcoord t)
      dsimp only [φ]
      split_ifs with h1
      · simp only [T_bad, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1
      · have h1_eq : out {x, y} (fun t => op t (R t x) (C t (π y))) = H x (π y) :=
          Classical.not_not.mp h1
        simp only [T_bad, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Finset.pair_comm y x, ← hv, h1_eq]
        exact hH
    have hinj : Set.InjOn φ S_bad := by
      intro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ heq
      simp only [S_bad, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      have hp₁ : ({(φ (x₁, y₁)).1, (φ (x₁, y₁)).2} : Finset I) = {x₁, y₁} := by
        dsimp only [φ]; split_ifs <;> simp [Finset.pair_comm]
      have hp₂ : ({(φ (x₂, y₂)).1, (φ (x₂, y₂)).2} : Finset I) = {x₂, y₂} := by
        dsimp only [φ]; split_ifs <;> simp [Finset.pair_comm]
      have hset : ({x₁, y₁} : Finset I) = {x₂, y₂} := by rw [← hp₁, heq, hp₂]
      obtain ⟨rfl, rfl⟩ := PEqualNP.Outside.L_meta_25758.pair_eq_of_le25758 (le_of_lt h₁.1) (le_of_lt h₂.1) hset
      rfl
    exact le_trans (Finset.card_le_card_of_injOn φ hmaps hinj) herr
  · rintro ⟨label, hlab_err⟩
    let coord : I → (t : Fin q) → Fin (rad (op t)) := fun x => equivD.symm (label x)
    let R : Fin q → I → Bool := fun t x => (enc t (coord x t)).1
    let C : Fin q → I → Bool := fun t u => (enc t (coord (π.symm u) t)).2
    have hC : ∀ t x, C t (π x) = (enc t (coord x t)).2 := fun t x => by simp [C]
    let v : I → I → Fin q → Bool := fun x y t => op t (R t x) (C t (π y))
    have hv_eq : ∀ x y, v x y = v y x ↔ label x = label y := by
      intro x y
      constructor
      · intro hv
        have hc : coord x = coord y := by
          funext t
          have ht := congr_fun hv t
          simp only [v, R, hC] at ht
          exact (henc t (coord x t) (coord y t)).mp ht
        exact equivD.symm.injective hc
      · intro hl
        have hc : coord x = coord y := congr_arg equivD.symm hl
        funext t
        simp only [v, R, hC]
        exact (henc t (coord x t) (coord y t)).mpr (congr_fun hc t)
    let out : Finset I → (Fin q → Bool) → Bool := fun S w =>
      if h1 : ∃ p : I × I, ({p.1, p.2} : Finset I) = S ∧ p.1 ≤ p.2 ∧ v p.1 p.2 = w then
        H (Classical.choose h1).1 (π (Classical.choose h1).2)
      else if h2 : ∃ p : I × I, ({p.1, p.2} : Finset I) = S ∧ v p.1 p.2 = w then
        H (Classical.choose h2).1 (π (Classical.choose h2).2)
      else false
    refine ⟨R, C, out, ?_⟩
    let T_bad := (Finset.univ : Finset (I × I)).filter (fun z => out {z.1, z.2} (v z.1 z.2) ≠ H z.1 (π z.2))
    let S_bad := (Finset.univ : Finset (I × I)).filter (fun z =>
      z.1 < z.2 ∧ label z.1 = label z.2 ∧ H z.1 (π z.2) ≠ H z.2 (π z.1))
    let sw : I × I → I × I := fun z => (z.2, z.1)
    have hmaps : Set.MapsTo sw T_bad S_bad := by
      intro ⟨a, b⟩ hz
      simp only [T_bad, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      by_cases hab : a ≤ b
      · exfalso
        have h1 : ∃ p : I × I, ({p.1, p.2} : Finset I) = {a, b} ∧ p.1 ≤ p.2 ∧ v p.1 p.2 = v a b :=
          ⟨(a, b), rfl, hab, rfl⟩
        have hout : out {a, b} (v a b) = H (Classical.choose h1).1 (π (Classical.choose h1).2) := by
          simp only [out, h1, ↓reduceDIte]
        obtain ⟨hp_set, hp_le, _⟩ := Classical.choose_spec h1
        obtain ⟨heq1, heq2⟩ := PEqualNP.Outside.L_meta_25758.pair_eq_of_le25758 hp_le hab hp_set
        rw [hout, heq1, heq2] at hz
        exact hz rfl
      · have hba : b < a := lt_of_not_ge hab
        by_cases h1 : ∃ p : I × I, ({p.1, p.2} : Finset I) = {a, b} ∧ p.1 ≤ p.2 ∧ v p.1 p.2 = v a b
        · obtain ⟨hp_set, hp_le, hp_v⟩ := Classical.choose_spec h1
          have hset_ba : ({(Classical.choose h1).1, (Classical.choose h1).2} : Finset I) = {b, a} := by
            rw [hp_set, Finset.pair_comm]
          obtain ⟨heq1, heq2⟩ := PEqualNP.Outside.L_meta_25758.pair_eq_of_le25758 hp_le (le_of_lt hba) hset_ba
          have hout : out {a, b} (v a b) = H b (π a) := by
            simp only [out, h1, ↓reduceDIte, heq1, heq2]
          have hv_ba : v b a = v a b := by
            simpa [heq1, heq2] using hp_v
          have hlab_ba : label b = label a := (hv_eq b a).mp hv_ba
          have hH_ba : H b (π a) ≠ H a (π b) := by
            rw [← hout]; exact hz
          simp only [sw, S_bad, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hba, hlab_ba, hH_ba⟩
        · exfalso
          have h2 : ∃ p : I × I, ({p.1, p.2} : Finset I) = {a, b} ∧ v p.1 p.2 = v a b :=
            ⟨(a, b), rfl, rfl⟩
          have hout : out {a, b} (v a b) = H (Classical.choose h2).1 (π (Classical.choose h2).2) := by
            simp only [out, h1, h2, ↓reduceDIte]
          obtain ⟨hp_set, hp_v⟩ := Classical.choose_spec h2
          rcases PEqualNP.Outside.L_meta_25758.pair_eq_cases25758 hp_set with ⟨heq1, heq2⟩ | ⟨heq1, heq2⟩
          · rw [hout, heq1, heq2] at hz
            exact hz rfl
          · apply h1
            refine ⟨(b, a), Finset.pair_comm b a, le_of_lt hba, ?_⟩
            simpa [heq1, heq2] using hp_v
    have hinj : Set.InjOn sw T_bad := by
      intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ heq
      cases heq
      rfl
    exact le_trans (Finset.card_le_card_of_injOn sw hmaps hinj) hlab_err
