import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_471

abbrev F := ZMod 2

lemma f2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma f2_add_self (a : F) : a + a = 0 := by
  rcases f2_cases a with rfl | rfl <;> decide

lemma f2_one_add_one : (1 : F) + 1 = 0 := by decide

lemma f2_eq_iff_add_eq_zero (a b : F) : a = b ↔ a + b = 0 := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl <;> decide

def sgn (z : F) : ℤ := if z = 0 then 1 else -1

lemma sgn_zero : sgn 0 = 1 := rfl
lemma sgn_one : sgn 1 = -1 := by decide

lemma sgn_add (a b : F) : sgn (a + b) = sgn a * sgn b := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl <;> decide

lemma sgn_mul_self (a : F) : sgn a * sgn a = 1 := by
  rcases f2_cases a with rfl | rfl <;> decide

lemma sgn_eq_one_iff (a : F) : sgn a = 1 ↔ a = 0 := by
  rcases f2_cases a with rfl | rfl <;> decide

lemma sgn_sum_eq {α : Type*} [Fintype α] (g : α → F) :
    ∑ i : α, sgn (g i) = 2 * (Finset.univ.filter (fun i => g i = 0)).card - Fintype.card α := by
  have h1 : ∀ i : α, sgn (g i) = (if g i = 0 then (2 : ℤ) else 0) - 1 := by
    intro i; rcases f2_cases (g i) with h | h <;> simp [sgn, h]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  ring

def Mval (m : ℕ) : ℕ := (4 ^ m - 1) / 3

lemma three_dvd_four_pow_sub_one (m : ℕ) : 3 ∣ 4 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : 4 ^ (k + 1) - 1 = 4 * (4 ^ k - 1) + 3 := by
      rw [pow_succ]; omega
    rw [h2]
    exact Nat.dvd_add (dvd_mul_of_dvd_right ih 4) (dvd_refl 3)

lemma three_mul_Mval (m : ℕ) : 3 * Mval m = 4 ^ m - 1 := by
  unfold Mval
  exact Nat.mul_div_cancel' (three_dvd_four_pow_sub_one m)

lemma Mval_succ (m : ℕ) : Mval (m + 1) = 4 * Mval m + 1 := by
  have h1 : 3 * Mval (m + 1) = 3 * (4 * Mval m + 1) := by
    rw [three_mul_Mval]
    have h0 := three_mul_Mval m
    have hp : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    omega
  omega

lemma Mval_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Mval m := by
  have h := three_mul_Mval m
  have hp : 4 ≤ 4 ^ m := by
    calc 4 = 4 ^ 1 := by simp
    _ ≤ 4 ^ m := Nat.pow_le_pow_right (by omega) hm
  omega

lemma Mval_odd (m : ℕ) (hm : 1 ≤ m) : Mval m % 2 = 1 := by
  have h := three_mul_Mval m
  have hev : 4 ^ m % 2 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rw [pow_succ]; omega
  have hp : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by omega)
  omega

lemma coprime_M_plus_pow_two_M {m : ℕ} (hm : 2 ≤ m) :
    Nat.Coprime (Mval m + 2 ^ (m - 1)) (2 * Mval m) := by
  have hodd : Mval m % 2 = 1 := Mval_odd m (by omega)
  have hpow_even : 2 ^ (m - 1) % 2 = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, m - 1 = k + 1 := ⟨m - 2, by omega⟩
    rw [hk, pow_succ]; omega
  have hcop2 : Nat.Coprime (Mval m + 2 ^ (m - 1)) 2 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  have hcop2M : Nat.Coprime 2 (Mval m) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  have hcopPowM : Nat.Coprime (2 ^ (m - 1)) (Mval m) := hcop2M.pow_left (m - 1)
  have hcopM : Nat.Coprime (Mval m + 2 ^ (m - 1)) (Mval m) := by
    simpa [Nat.coprime_self_add_left] using hcopPowM
  exact hcop2.mul_right hcopM

abbrev Y (m : ℕ) := (Fin m → F) × (Fin m → F)

def dotY {m : ℕ} (α y : Y m) : F :=
  (∑ j : Fin m, α.1 j * y.1 j) + (∑ j : Fin m, α.2 j * y.2 j)

def f0 {m : ℕ} (y : Y m) : F :=
  ∑ j : Fin m, y.1 j * y.2 j

def omegaY {m : ℕ} (α β : Y m) : F :=
  (∑ j : Fin m, α.1 j * β.2 j) + (∑ j : Fin m, α.2 j * β.1 j)

lemma dotY_zero_left {m : ℕ} (y : Y m) : dotY 0 y = 0 := by
  simp [dotY]

lemma dotY_zero_right {m : ℕ} (α : Y m) : dotY α 0 = 0 := by
  simp [dotY]

lemma dotY_add_left {m : ℕ} (α β y : Y m) : dotY (α + β) y = dotY α y + dotY β y := by
  simp only [dotY, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma dotY_add_right {m : ℕ} (α y z : Y m) : dotY α (y + z) = dotY α y + dotY α z := by
  simp only [dotY, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

lemma f0_zero {m : ℕ} : f0 (0 : Y m) = 0 := by
  simp [f0]

lemma f0_add {m : ℕ} (u v : Y m) : f0 (u + v) = f0 u + f0 v + omegaY u v := by
  simp only [f0, omegaY, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have h : ∀ j : Fin m, (u.1 j + v.1 j) * (u.2 j + v.2 j) =
      u.1 j * u.2 j + v.1 j * v.2 j + (u.1 j * v.2 j + u.2 j * v.1 j) := by
    intro j; ring
  simp_rw [h, Finset.sum_add_distrib]

lemma omegaY_self {m : ℕ} (u : Y m) : omegaY u u = 0 := by
  simp only [omegaY]
  have h : ∑ j : Fin m, u.2 j * u.1 j = ∑ j : Fin m, u.1 j * u.2 j := by
    congr 1; funext j; ring
  rw [h, f2_add_self]

lemma omegaY_comm {m : ℕ} (u v : Y m) : omegaY u v = omegaY v u := by
  simp only [omegaY]
  have h1 : ∑ j : Fin m, u.1 j * v.2 j = ∑ j : Fin m, v.2 j * u.1 j := by
    congr 1; funext j; ring
  have h2 : ∑ j : Fin m, u.2 j * v.1 j = ∑ j : Fin m, v.1 j * u.2 j := by
    congr 1; funext j; ring
  rw [h1, h2, add_comm]

lemma omegaY_add_left {m : ℕ} (u v w : Y m) : omegaY (u + v) w = omegaY u w + omegaY v w := by
  simp only [omegaY, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma omegaY_swap_dotY {m : ℕ} (u v : Y m) : omegaY u (v.2, v.1) = dotY v u := by
  simp only [omegaY, dotY]
  congr 1 <;> (congr 1; funext j; ring)

lemma card_Y (m : ℕ) : Fintype.card (Y m) = 4 ^ m := by
  simp only [Y, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have : (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
  omega

lemma dotY_lin_rep {m : ℕ} (L : Y m →ₗ[F] F) : ∃ α : Y m, ∀ y : Y m, L y = dotY α y := by
  let e1 : Fin m → Y m := fun j => (Pi.single j 1, 0)
  let e2 : Fin m → Y m := fun j => (0, Pi.single j 1)
  refine ⟨(fun j => L (e1 j), fun j => L (e2 j)), fun y => ?_⟩
  have hy : y = (∑ j : Fin m, y.1 j • e1 j) + (∑ j : Fin m, y.2 j • e2 j) := by
    ext j
    · simp only [Prod.fst_add, Prod.fst_sum, e1, e2, Prod.smul_fst, smul_zero, Finset.sum_const_zero, add_zero, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    · simp only [Prod.snd_add, Prod.snd_sum, e1, e2, Prod.smul_snd, smul_zero, Finset.sum_const_zero, zero_add, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  conv_lhs => rw [hy]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, dotY]
  congr 1 <;> (congr 1; funext j; ring)

lemma sum_sgn_dotY {m : ℕ} (α : Y m) :
    ∑ y : Y m, sgn (dotY α y) = if α = 0 then (4 ^ m : ℤ) else 0 := by
  by_cases hα : α = 0
  · subst hα
    simp only [dotY_zero_left, sgn_zero, Finset.sum_const, Finset.card_univ, card_Y,
      nsmul_eq_mul, mul_one, ↓reduceIte]
    push_cast; rfl
  · simp only [hα, ↓reduceIte]
    have hex : ∃ z : Y m, dotY α z = 1 := by
      have hne : (∃ j, α.1 j ≠ 0) ∨ (∃ j, α.2 j ≠ 0) := by
        by_contra hc
        push Not at hc
        apply hα
        ext j
        · exact hc.1 j
        · exact hc.2 j
      rcases hne with ⟨j, hj⟩ | ⟨j, hj⟩
      · refine ⟨(Pi.single j 1, 0), ?_⟩
        have hj1 : α.1 j = 1 := by rcases f2_cases (α.1 j) with h | h <;> [contradiction; exact h]
        simp [dotY, Pi.single_apply, hj1]
      · refine ⟨(0, Pi.single j 1), ?_⟩
        have hj1 : α.2 j = 1 := by rcases f2_cases (α.2 j) with h | h <;> [contradiction; exact h]
        simp [dotY, Pi.single_apply, hj1]
    rcases hex with ⟨z, hz⟩
    have hshift : ∑ y : Y m, sgn (dotY α y) = ∑ y : Y m, sgn (dotY α (y + z)) := by
      exact (Fintype.sum_equiv (Equiv.addRight z) _ _ (fun y => rfl)).symm
    have hneg : ∑ y : Y m, sgn (dotY α (y + z)) = -(∑ y : Y m, sgn (dotY α y)) := by
      simp_rw [dotY_add_right, hz, sgn_add, sgn_one, mul_neg_one, Finset.sum_neg_distrib]
    linarith

lemma sum_f0_chi {m : ℕ} (α : Y m) :
    ∑ y : Y m, sgn (f0 y + dotY α y) = (2 ^ m : ℤ) * sgn (f0 α) := by
  induction m with
  | zero =>
    have h0 : ∀ y : Y 0, y = 0 := fun y => by ext j <;> exact j.elim0
    rw [Fintype.sum_eq_single 0 (fun y hy => (hy (h0 y)).elim)]
    simp [f0, dotY, sgn]
  | succ k ih =>
    let split : Y (k + 1) ≃ Y k × (F × F) :=
      { toFun := fun y => ((fun j => y.1 j.castSucc, fun j => y.2 j.castSucc),
          (y.1 (Fin.last k), y.2 (Fin.last k)))
        invFun := fun p => (Fin.snoc p.1.1 p.2.1, Fin.snoc p.1.2 p.2.2)
        left_inv := fun y => by
          ext j
          · exact congr_fun (Fin.snoc_init_self y.1) j
          · exact congr_fun (Fin.snoc_init_self y.2) j
        right_inv := fun p => by
          ext j <;> simp [Fin.snoc_castSucc, Fin.snoc_last] }
    rw [Fintype.sum_equiv split _ (fun p => sgn (f0 (split.symm p) + dotY α (split.symm p)))
      (fun y => by simp)]
    rw [Fintype.sum_prod_type]
    let α' : Y k := (fun j => α.1 j.castSucc, fun j => α.2 j.castSucc)
    let a0 : F := α.1 (Fin.last k)
    let b0 : F := α.2 (Fin.last k)
    have hdecomp : ∀ (y' : Y k) (ab : F × F),
        f0 (split.symm (y', ab)) + dotY α (split.symm (y', ab)) =
        (f0 y' + dotY α' y') + (ab.1 * ab.2 + a0 * ab.1 + b0 * ab.2) := by
      intro y' ab
      simp only [split, Equiv.coe_fn_symm_mk, f0, dotY, α', a0, b0,
        Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      ring
    have hdecomp_sgn : ∀ (y' : Y k) (ab : F × F),
        sgn (f0 (split.symm (y', ab)) + dotY α (split.symm (y', ab))) =
        sgn (f0 y' + dotY α' y') * sgn (ab.1 * ab.2 + a0 * ab.1 + b0 * ab.2) := fun y' ab => by
      rw [hdecomp, sgn_add]
    simp_rw [hdecomp_sgn, ← Finset.mul_sum]
    have hinner : ∑ ab : F × F, sgn (ab.1 * ab.2 + a0 * ab.1 + b0 * ab.2) =
        2 * sgn (a0 * b0) := by
      have hgen : ∀ x y : F, ∑ ab : F × F, sgn (ab.1 * ab.2 + x * ab.1 + y * ab.2) =
          2 * sgn (x * y) := by
        intro x y
        rcases f2_cases x with rfl | rfl <;> rcases f2_cases y with rfl | rfl <;> decide
      exact hgen a0 b0
    have hinner' : ∀ y' : Y k, sgn (f0 y' + dotY α' y') *
        ∑ ab : F × F, sgn (ab.1 * ab.2 + a0 * ab.1 + b0 * ab.2) =
        sgn (f0 y' + dotY α' y') * (2 * sgn (a0 * b0)) := fun y' => by rw [hinner]
    rw [Finset.sum_congr rfl (fun y' _ => hinner' y'), ← Finset.sum_mul, ih α']
    have hf0α : f0 α = f0 α' + a0 * b0 := by
      unfold f0; exact Fin.sum_univ_castSucc (fun j : Fin (k + 1) => α.1 j * α.2 j)
    rw [hf0α, sgn_add, pow_succ]
    ring

lemma two_bit_fourier_l1 (g : (Fin 2 → F) → F) :
    |∑ u : Fin 2 → F, sgn (g u) * sgn (u 0)| +
    |∑ u : Fin 2 → F, sgn (g u) * sgn (u 1)| +
    |∑ u : Fin 2 → F, sgn (g u) * sgn (u 0 + u 1)| ≤ 6 := by
  let g00 := g ![0, 0]
  let g01 := g ![0, 1]
  let g10 := g ![1, 0]
  let g11 := g ![1, 1]
  have hsum : ∀ (w : (Fin 2 → F) → ℤ),
      ∑ u : Fin 2 → F, w u = w ![0, 0] + w ![0, 1] + w ![1, 0] + w ![1, 1] := by
    intro w
    have h1 : (Finset.univ : Finset (Fin 2 → F)) = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by
      ext u; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases f2_cases (u 0) with h0 | h0 <;> rcases f2_cases (u 1) with h1 | h1
      · left; ext i; fin_cases i <;> assumption
      · right; left; ext i; fin_cases i <;> assumption
      · right; right; left; ext i; fin_cases i <;> assumption
      · right; right; right; ext i; fin_cases i <;> assumption
    rw [h1]
    have hd1 : (![0, 0] : Fin 2 → F) ∉ ({![0, 1], ![1, 0], ![1, 1]} : Finset (Fin 2 → F)) := by decide
    have hd2 : (![0, 1] : Fin 2 → F) ∉ ({![1, 0], ![1, 1]} : Finset (Fin 2 → F)) := by decide
    have hd3 : (![1, 0] : Fin 2 → F) ≠ ![1, 1] := by decide
    rw [Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_pair hd3]
    ring
  simp_rw [hsum]
  change |sgn g00 * sgn ((![0, 0] : Fin 2 → F) 0) + sgn g01 * sgn ((![0, 1] : Fin 2 → F) 0) +
      sgn g10 * sgn ((![1, 0] : Fin 2 → F) 0) + sgn g11 * sgn ((![1, 1] : Fin 2 → F) 0)| +
    |sgn g00 * sgn ((![0, 0] : Fin 2 → F) 1) + sgn g01 * sgn ((![0, 1] : Fin 2 → F) 1) +
      sgn g10 * sgn ((![1, 0] : Fin 2 → F) 1) + sgn g11 * sgn ((![1, 1] : Fin 2 → F) 1)| +
    |sgn g00 * sgn ((![0, 0] : Fin 2 → F) 0 + (![0, 0] : Fin 2 → F) 1) +
      sgn g01 * sgn ((![0, 1] : Fin 2 → F) 0 + (![0, 1] : Fin 2 → F) 1) +
      sgn g10 * sgn ((![1, 0] : Fin 2 → F) 0 + (![1, 0] : Fin 2 → F) 1) +
      sgn g11 * sgn ((![1, 1] : Fin 2 → F) 0 + (![1, 1] : Fin 2 → F) 1)| ≤ 6
  rcases f2_cases g00 with h00 | h00 <;> rcases f2_cases g01 with h01 | h01 <;>
    rcases f2_cases g10 with h10 | h10 <;> rcases f2_cases g11 with h11 | h11 <;>
    rw [h00, h01, h10, h11] <;> decide

lemma two_bit_fourier_expand (g : (Fin 2 → F) → F) (v : Fin 2 → F) :
    4 * sgn (g v) =
      (∑ u : Fin 2 → F, sgn (g u)) +
      (∑ u : Fin 2 → F, sgn (g u) * sgn (u 0)) * sgn (v 0) +
      (∑ u : Fin 2 → F, sgn (g u) * sgn (u 1)) * sgn (v 1) +
      (∑ u : Fin 2 → F, sgn (g u) * sgn (u 0 + u 1)) * sgn (v 0 + v 1) := by
  have hsum : ∀ (w : (Fin 2 → F) → ℤ),
      ∑ u : Fin 2 → F, w u = w ![0, 0] + w ![0, 1] + w ![1, 0] + w ![1, 1] := by
    intro w
    have h1 : (Finset.univ : Finset (Fin 2 → F)) = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by
      ext u; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases f2_cases (u 0) with h0 | h0 <;> rcases f2_cases (u 1) with h1 | h1
      · left; ext i; fin_cases i <;> assumption
      · right; left; ext i; fin_cases i <;> assumption
      · right; right; left; ext i; fin_cases i <;> assumption
      · right; right; right; ext i; fin_cases i <;> assumption
    rw [h1]
    have hd1 : (![0, 0] : Fin 2 → F) ∉ ({![0, 1], ![1, 0], ![1, 1]} : Finset (Fin 2 → F)) := by decide
    have hd2 : (![0, 1] : Fin 2 → F) ∉ ({![1, 0], ![1, 1]} : Finset (Fin 2 → F)) := by decide
    have hd3 : (![1, 0] : Fin 2 → F) ≠ ![1, 1] := by decide
    rw [Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_pair hd3]
    ring
  simp_rw [hsum]
  rcases f2_cases (v 0) with hv0 | hv0 <;> rcases f2_cases (v 1) with hv1 | hv1
  · have hv : v = ![0, 0] := by ext i; fin_cases i <;> assumption
    subst hv; simp [f2_one_add_one, sgn]; split_ifs <;> ring
  · have hv : v = ![0, 1] := by ext i; fin_cases i <;> assumption
    subst hv; simp [f2_one_add_one, sgn]; split_ifs <;> ring
  · have hv : v = ![1, 0] := by ext i; fin_cases i <;> assumption
    subst hv; simp [f2_one_add_one, sgn]; split_ifs <;> ring
  · have hv : v = ![1, 1] := by ext i; fin_cases i <;> assumption
    subst hv; simp [f2_one_add_one, sgn]; split_ifs <;> ring

lemma single_query_weighted_bound {m : ℕ} (hm : 1 ≤ m)
    (A : Y m →ₗ[F] (Fin 2 → F)) (out : (Fin 2 → F) → F) :
    ∑ y : Y m, ((2 ^ m : ℤ) - sgn (f0 y)) * (sgn (out (A y)) * sgn (f0 y)) ≤
      3 * 2 ^ (2 * m - 1) := by
  let L0 : Y m →ₗ[F] F := (LinearMap.proj (R := F) (0 : Fin 2)).comp A
  let L1 : Y m →ₗ[F] F := (LinearMap.proj (R := F) (1 : Fin 2)).comp A
  obtain ⟨α, hα⟩ := dotY_lin_rep L0
  obtain ⟨β, hβ⟩ := dotY_lin_rep L1
  have hA0 : ∀ y, A y 0 = dotY α y := fun y => hα y
  have hA1 : ∀ y, A y 1 = dotY β y := fun y => hβ y
  have hA01 : ∀ y, A y 0 + A y 1 = dotY (α + β) y := fun y => by
    rw [hA0, hA1, dotY_add_left]
  set c00 : ℤ := ∑ u : Fin 2 → F, sgn (out u)
  set c10 : ℤ := ∑ u : Fin 2 → F, sgn (out u) * sgn (u 0)
  set c01 : ℤ := ∑ u : Fin 2 → F, sgn (out u) * sgn (u 1)
  set c11 : ℤ := ∑ u : Fin 2 → F, sgn (out u) * sgn (u 0 + u 1)
  have h4 : 4 * (∑ y : Y m, ((2 ^ m : ℤ) - sgn (f0 y)) * (sgn (out (A y)) * sgn (f0 y))) =
      4 * (2 ^ m : ℤ) * (∑ y : Y m, sgn (out (A y)) * sgn (f0 y)) -
      4 * (∑ y : Y m, sgn (out (A y))) := by
    have hstep : ∀ y : Y m, ((2 ^ m : ℤ) - sgn (f0 y)) * (sgn (out (A y)) * sgn (f0 y)) =
        (2 ^ m : ℤ) * (sgn (out (A y)) * sgn (f0 y)) - sgn (out (A y)) := by
      intro y
      have hs := sgn_mul_self (f0 y)
      calc ((2 ^ m : ℤ) - sgn (f0 y)) * (sgn (out (A y)) * sgn (f0 y))
          = (2 ^ m : ℤ) * (sgn (out (A y)) * sgn (f0 y)) - sgn (out (A y)) * (sgn (f0 y) * sgn (f0 y)) := by ring
        _ = (2 ^ m : ℤ) * (sgn (out (A y)) * sgn (f0 y)) - sgn (out (A y)) := by rw [hs, mul_one]
    simp_rw [hstep, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hsum1 : 4 * (∑ y : Y m, sgn (out (A y)) * sgn (f0 y)) =
      (2 ^ m : ℤ) * (c00 + c10 * sgn (f0 α) + c01 * sgn (f0 β) + c11 * sgn (f0 (α + β))) := by
    rw [Finset.mul_sum]
    have hterm : ∀ y : Y m, 4 * (sgn (out (A y)) * sgn (f0 y)) =
        c00 * sgn (f0 y + dotY 0 y) +
        c10 * sgn (f0 y + dotY α y) +
        c01 * sgn (f0 y + dotY β y) +
        c11 * sgn (f0 y + dotY (α + β) y) := by
      intro y
      have hexp := two_bit_fourier_expand out (A y)
      rw [hA0, hA1, ← dotY_add_left] at hexp
      simp only [dotY_zero_left, add_zero, sgn_add]
      calc 4 * (sgn (out (A y)) * sgn (f0 y)) = (4 * sgn (out (A y))) * sgn (f0 y) := by ring
        _ = _ := by rw [hexp]; ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, sum_f0_chi, f0_zero, sgn_zero]
    ring
  have hsum2 : 4 * (∑ y : Y m, sgn (out (A y))) =
      c00 * (4 ^ m : ℤ) +
      c10 * (if α = 0 then (4 ^ m : ℤ) else 0) +
      c01 * (if β = 0 then (4 ^ m : ℤ) else 0) +
      c11 * (if α + β = 0 then (4 ^ m : ℤ) else 0) := by
    rw [Finset.mul_sum]
    have hterm : ∀ y : Y m, 4 * sgn (out (A y)) =
        c00 * sgn (dotY 0 y) +
        c10 * sgn (dotY α y) +
        c01 * sgn (dotY β y) +
        c11 * sgn (dotY (α + β) y) := by
      intro y
      have hexp := two_bit_fourier_expand out (A y)
      rw [hA0, hA1, ← dotY_add_left] at hexp
      simp only [dotY_zero_left, sgn_zero, mul_one]
      exact hexp
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, sum_sgn_dotY]
    simp
  have h2m4m : (2 ^ m : ℤ) * (2 ^ m : ℤ) = (4 ^ m : ℤ) := by
    rw [← mul_pow]; norm_num
  have hterm_le : ∀ (c : ℤ) (γ : Y m),
      c * (4 ^ m : ℤ) * sgn (f0 γ) - c * (if γ = 0 then (4 ^ m : ℤ) else 0) ≤
        |c| * (4 ^ m : ℤ) := by
    intro c γ
    by_cases hγ : γ = 0
    · subst hγ
      simp only [f0_zero, sgn_zero, mul_one, ↓reduceIte, sub_self]
      positivity
    · simp only [hγ, ↓reduceIte, mul_zero, sub_zero]
      have h1 : c * sgn (f0 γ) ≤ |c| := by
        rcases f2_cases (f0 γ) with h | h
        · simp [h, sgn, le_abs_self]
        · simp [h, sgn, neg_le_abs]
      have h4p : (0 : ℤ) ≤ 4 ^ m := by positivity
      nlinarith
  have h4eq : 4 * (∑ y : Y m, ((2 ^ m : ℤ) - sgn (f0 y)) * (sgn (out (A y)) * sgn (f0 y))) =
      (c10 * (4 ^ m : ℤ) * sgn (f0 α) - c10 * (if α = 0 then (4 ^ m : ℤ) else 0)) +
      (c01 * (4 ^ m : ℤ) * sgn (f0 β) - c01 * (if β = 0 then (4 ^ m : ℤ) else 0)) +
      (c11 * (4 ^ m : ℤ) * sgn (f0 (α + β)) - c11 * (if α + β = 0 then (4 ^ m : ℤ) else 0)) := by
    have hmul : 4 * (2 ^ m : ℤ) * (∑ y : Y m, sgn (out (A y)) * sgn (f0 y)) =
        (2 ^ m : ℤ) * (4 * (∑ y : Y m, sgn (out (A y)) * sgn (f0 y))) := by ring
    rw [h4, hmul, hsum1, hsum2]
    have : (2 ^ m : ℤ) * ((2 ^ m : ℤ) * (c00 + c10 * sgn (f0 α) + c01 * sgn (f0 β) + c11 * sgn (f0 (α + β)))) =
        (4 ^ m : ℤ) * (c00 + c10 * sgn (f0 α) + c01 * sgn (f0 β) + c11 * sgn (f0 (α + β))) := by
      rw [← mul_assoc, h2m4m]
    rw [this]
    ring
  have hl1 : |c10| + |c01| + |c11| ≤ 6 := two_bit_fourier_l1 out
  have h4le : 4 * (∑ y : Y m, ((2 ^ m : ℤ) - sgn (f0 y)) * (sgn (out (A y)) * sgn (f0 y))) ≤
      6 * (4 ^ m : ℤ) := by
    rw [h4eq]
    have b1 := hterm_le c10 α
    have b2 := hterm_le c01 β
    have b3 := hterm_le c11 (α + β)
    have h4p : (0 : ℤ) ≤ 4 ^ m := by positivity
    nlinarith
  have hpow : (4 : ℤ) * (3 * 2 ^ (2 * m - 1)) = 6 * (4 ^ m : ℤ) := by
    have h2 : (2 : ℤ) * 2 ^ (2 * m - 1) = 4 ^ m := by
      have he : 2 * m - 1 + 1 = 2 * m := by omega
      calc (2 : ℤ) * 2 ^ (2 * m - 1) = 2 ^ (2 * m - 1 + 1) := by rw [pow_succ]; ring
      _ = 2 ^ (2 * m) := by rw [he]
      _ = (2 ^ 2) ^ m := by rw [pow_mul]
      _ = 4 ^ m := by norm_num
    linarith
  linarith

lemma lower_bound_normal {m T : ℕ} (hm : 2 ≤ m)
    (A : Fin T → Y m →ₗ[F] (Fin 2 → F)) (out : Fin T → (Fin 2 → F) → F)
    (hpred : ∀ y : Y m, (Mval m + 2 ^ (m - 1)) * T ≤
      (2 * Mval m) * Nat.card {i : Fin T // out i (A i y) = f0 y}) :
    2 * Mval m ∣ T := by
  set M := Mval m
  let score : Y m → ℤ := fun y => ∑ i : Fin T, sgn (out i (A i y)) * sgn (f0 y)
  have hscore_eq : ∀ y : Y m,
      score y = 2 * (Nat.card {i : Fin T // out i (A i y) = f0 y} : ℤ) - T := by
    intro y
    have hcard : Nat.card {i : Fin T // out i (A i y) = f0 y} =
        (Finset.univ.filter (fun i : Fin T => out i (A i y) + f0 y = 0)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1; ext i
      simp [f2_eq_iff_add_eq_zero]
    rw [hcard]
    have hs := sgn_sum_eq (fun i : Fin T => out i (A i y) + f0 y)
    simp only [Fintype.card_fin] at hs
    calc score y = ∑ i : Fin T, sgn (out i (A i y) + f0 y) := by
          dsimp only [score]; apply Finset.sum_congr rfl; intro i _; exact (sgn_add _ _).symm
      _ = _ := hs
  have hscore_ge : ∀ y : Y m, (2 ^ (m - 1) : ℤ) * T ≤ (M : ℤ) * score y := by
    intro y
    have hp := hpred y
    have hpz : ((M + 2 ^ (m - 1)) * T : ℤ) ≤ (2 * M : ℤ) * (Nat.card {i : Fin T // out i (A i y) = f0 y} : ℤ) := by
      exact_mod_cast hp
    rw [hscore_eq y]
    linarith
  let w : Y m → ℤ := fun y => (2 ^ m : ℤ) - sgn (f0 y)
  have hw_pos : ∀ y : Y m, 0 < w y := by
    intro y
    have h2 : (4 : ℤ) ≤ 2 ^ m := by
      have : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
      exact_mod_cast this
    rcases f2_cases (f0 y) with h | h <;> simp [w, h, sgn] <;> linarith
  have hw_sum : ∑ y : Y m, w y = 3 * (M : ℤ) * (2 ^ m : ℤ) := by
    simp only [w, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_Y, nsmul_eq_mul]
    have hf0sum : ∑ y : Y m, sgn (f0 y) = (2 ^ m : ℤ) := by
      have h := sum_f0_chi (0 : Y m)
      simp only [dotY_zero_left, add_zero, f0_zero, sgn_zero, mul_one] at h
      exact h
    rw [hf0sum]
    have h3M : (3 * M : ℤ) = (4 ^ m : ℤ) - 1 := by
      have h := three_mul_Mval m
      have hp : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by omega)
      have h' : 3 * M + 1 = 4 ^ m := by omega
      have h'' : (3 * M + 1 : ℤ) = (4 ^ m : ℤ) := by exact_mod_cast h'
      linarith
    have h4m : ((4 ^ m : ℕ) : ℤ) = (4 ^ m : ℤ) := by push_cast; rfl
    rw [h4m]
    calc (4 ^ m : ℤ) * (2 ^ m : ℤ) - (2 ^ m : ℤ) = ((4 ^ m : ℤ) - 1) * (2 ^ m : ℤ) := by ring
      _ = (3 * (M : ℤ)) * (2 ^ m : ℤ) := by rw [← h3M]
      _ = 3 * (M : ℤ) * (2 ^ m : ℤ) := by ring
  have hupper : (M : ℤ) * ∑ y : Y m, w y * score y ≤ (M : ℤ) * (T : ℤ) * (3 * 2 ^ (2 * m - 1)) := by
    have hswap : ∑ y : Y m, w y * score y =
        ∑ i : Fin T, ∑ y : Y m, w y * (sgn (out i (A i y)) * sgn (f0 y)) := by
      simp_rw [score, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hswap]
    have hle : ∑ i : Fin T, ∑ y : Y m, w y * (sgn (out i (A i y)) * sgn (f0 y)) ≤
        ∑ _i : Fin T, (3 * 2 ^ (2 * m - 1) : ℤ) := by
      exact Finset.sum_le_sum (fun i _ => single_query_weighted_bound (by omega) (A i) (out i))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
    have hMp : (0 : ℤ) ≤ M := by positivity
    nlinarith
  have hlower_sum : ∑ y : Y m, w y * ((M : ℤ) * score y - (2 ^ (m - 1) : ℤ) * T) ≤ 0 := by
    have h1 : ∑ y : Y m, w y * ((M : ℤ) * score y - (2 ^ (m - 1) : ℤ) * T) =
        (M : ℤ) * (∑ y : Y m, w y * score y) - (∑ y : Y m, w y) * ((2 ^ (m - 1) : ℤ) * T) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
      congr 1; funext y; ring
    rw [h1, hw_sum]
    have hpow : (2 ^ m : ℤ) * (2 ^ (m - 1) : ℤ) = 2 ^ (2 * m - 1) := by
      rw [← pow_add]
      congr 1; omega
    have hrhs : 3 * (M : ℤ) * (2 ^ m : ℤ) * ((2 ^ (m - 1) : ℤ) * T) =
        (M : ℤ) * (T : ℤ) * (3 * 2 ^ (2 * m - 1)) := by
      calc 3 * (M : ℤ) * (2 ^ m : ℤ) * ((2 ^ (m - 1) : ℤ) * T)
          = 3 * (M : ℤ) * (T : ℤ) * ((2 ^ m : ℤ) * (2 ^ (m - 1) : ℤ)) := by ring
        _ = 3 * (M : ℤ) * (T : ℤ) * 2 ^ (2 * m - 1) := by rw [hpow]
        _ = (M : ℤ) * (T : ℤ) * (3 * 2 ^ (2 * m - 1)) := by ring
    linarith
  have hterm_nonneg : ∀ y : Y m, 0 ≤ w y * ((M : ℤ) * score y - (2 ^ (m - 1) : ℤ) * T) := by
    intro y
    exact mul_nonneg (le_of_lt (hw_pos y)) (sub_nonneg.2 (hscore_ge y))
  have hzero0 : w 0 * ((M : ℤ) * score 0 - (2 ^ (m - 1) : ℤ) * T) = 0 := by
    have hle0 : w 0 * ((M : ℤ) * score 0 - (2 ^ (m - 1) : ℤ) * T) ≤
        ∑ y : Y m, w y * ((M : ℤ) * score y - (2 ^ (m - 1) : ℤ) * T) :=
      Finset.single_le_sum (fun y _ => hterm_nonneg y) (Finset.mem_univ 0)
    linarith [hterm_nonneg 0]
  have heq0 : (M : ℤ) * score 0 = (2 ^ (m - 1) : ℤ) * T := by
    rcases mul_eq_zero.1 hzero0 with hw0 | hdiff
    · linarith [hw_pos 0]
    · linarith
  rw [hscore_eq 0] at heq0
  have hdvd_z : ((2 * M : ℕ) : ℤ) ∣ (((M + 2 ^ (m - 1)) * T : ℕ) : ℤ) := by
    refine ⟨(Nat.card {i : Fin T // out i (A i (0 : Y m)) = f0 (0 : Y m)} : ℤ), ?_⟩
    push_cast
    linarith
  have hdvd : (2 * M) ∣ (M + 2 ^ (m - 1)) * T := Int.ofNat_dvd.1 hdvd_z
  exact (coprime_M_plus_pow_two_M hm).symm.dvd_of_dvd_mul_left hdvd

def planeOut {m : ℕ} (α β : Y m) (u : Fin 2 → F) : F :=
  if (-sgn (omegaY α β) + sgn (f0 α) * sgn (u 0) + sgn (f0 β) * sgn (u 1) +
      sgn (f0 (α + β)) * sgn (u 0 + u 1)) = 2 then 0 else 1

lemma planeOut_sgn {m : ℕ} (α β : Y m) (u : Fin 2 → F) :
    2 * sgn (planeOut α β u) =
      -sgn (omegaY α β) + sgn (f0 α) * sgn (u 0) + sgn (f0 β) * sgn (u 1) +
        sgn (f0 (α + β)) * sgn (u 0 + u 1) := by
  have hf : f0 (α + β) = f0 α + f0 β + omegaY α β := f0_add α β
  unfold planeOut
  rw [hf]
  rcases f2_cases (f0 α) with h1 | h1 <;> rcases f2_cases (f0 β) with h2 | h2 <;>
    rcases f2_cases (omegaY α β) with h3 | h3 <;>
    rcases f2_cases (u 0) with h4 | h4 <;> rcases f2_cases (u 1) with h5 | h5 <;>
    rw [h1, h2, h3, h4, h5] <;> decide

def planeA {m : ℕ} (α β : Y m) : Y m →ₗ[F] (Fin 2 → F) where
  toFun y := ![dotY α y, dotY β y]
  map_add' x y := by
    ext i; fin_cases i <;> simp [dotY_add_right]
  map_smul' c x := by
    ext i; rcases f2_cases c with rfl | rfl <;> fin_cases i <;> simp [dotY_zero_right]

structure PlaneCover (m : ℕ) where
  planes : List (Y m × Y m)
  len_eq : planes.length = 2 * Mval m
  nonzero : ∀ p ∈ planes, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0
  cover_eq : ∀ γ : Y m, γ ≠ 0 →
    (planes.map (fun p => (if p.1 = γ then 1 else 0) + (if p.2 = γ then 1 else 0) +
      (if p.1 + p.2 = γ then 1 else 0))).sum = 2
  surplus_eq : (planes.map (fun p => -sgn (omegaY p.1 p.2))).sum = 2

def bitF (k i : ℕ) : F := if (k / 2 ^ i) % 2 = 1 then 1 else 0

def vec2 (k : ℕ) : Y 2 :=
  (![bitF k 3, bitF k 1], ![bitF k 2, bitF k 0])

def basePlanes2 : List (Y 2 × Y 2) :=
  [(1, 2), (1, 2), (4, 8), (4, 9), (6, 8), (6, 11), (7, 9), (7, 11), (5, 10), (5, 10)].map
    (fun p => (vec2 p.1, vec2 p.2))

def baseCover2 : PlaneCover 2 where
  planes := basePlanes2
  len_eq := by decide
  nonzero := by decide
  cover_eq := by decide
  surplus_eq := by decide

def indBlock2 : List (ℕ × ℕ) :=
  [(1, 4), (6, 8), (7, 11), (1, 2), (2, 13), (3, 9)]

def indBlockY2 : List (Y 2 × Y 2) :=
  indBlock2.map (fun p => (vec2 p.1, vec2 p.2))

lemma indBlockY2_len : indBlockY2.length = 6 := by decide

lemma indBlockY2_nonzero : ∀ p ∈ indBlockY2, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0 := by decide

lemma indBlockY2_surplus : (indBlockY2.map (fun p => -sgn (omegaY p.1 p.2))).sum = 4 := by decide

lemma indBlockY2_cover : ∀ γ : Y 2, γ ≠ 0 →
    (indBlockY2.map (fun p => (if p.1 = γ then 1 else 0) + (if p.2 = γ then 1 else 0) +
      (if p.1 + p.2 = γ then 1 else 0))).sum =
      if γ.1 0 = 0 ∧ γ.2 0 = 0 then 2 else 1 := by decide

def inLeft {m : ℕ} (v : Y m) : Y (m + 1) :=
  (Fin.snoc v.1 0, Fin.snoc v.2 0)

def inRight {m : ℕ} (a b : F) : Y (m + 1) :=
  (Fin.snoc 0 a, Fin.snoc 0 b)

lemma inLeft_add {m : ℕ} (u v : Y m) : inLeft (u + v) = inLeft u + inLeft v := by
  ext j
  · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft]
  · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft]

lemma inRight_add {m : ℕ} (a1 b1 a2 b2 : F) :
    inRight (m := m) (a1 + a2) (b1 + b2) = inRight a1 b1 + inRight a2 b2 := by
  ext j
  · refine Fin.lastCases ?_ ?_ j <;> simp [inRight]
  · refine Fin.lastCases ?_ ?_ j <;> simp [inRight]

lemma inLeft_inRight_eq_iff {m : ℕ} (u v : Y m) (x y a b : F) :
    (inLeft u + inRight x y = inLeft v + inRight a b) ↔ (u = v ∧ x = a ∧ y = b) := by
  constructor
  · intro h
    have h1 := congr_arg (fun z : Y (m + 1) => z.1 (Fin.last m)) h
    have h2 := congr_arg (fun z : Y (m + 1) => z.2 (Fin.last m)) h
    simp only [inLeft, inRight, Prod.fst_add, Prod.snd_add, Pi.add_apply, Fin.snoc_last,
      zero_add] at h1 h2
    refine ⟨?_, h1, h2⟩
    ext j
    · simpa [inLeft, inRight] using congr_arg (fun z : Y (m + 1) => z.1 j.castSucc) h
    · simpa [inLeft, inRight] using congr_arg (fun z : Y (m + 1) => z.2 j.castSucc) h
  · rintro ⟨rfl, rfl, rfl⟩; rfl

lemma inLeft_inRight_zero_iff {m : ℕ} (u : Y m) (x y : F) :
    (inLeft u + inRight x y = 0) ↔ (u = 0 ∧ x = 0 ∧ y = 0) := by
  have h0 : (0 : Y (m + 1)) = inLeft 0 + inRight 0 0 := by
    ext j
    · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft, inRight]
    · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft, inRight]
  rw [h0]
  exact inLeft_inRight_eq_iff u 0 x y 0 0

lemma omegaY_inLeft_inRight {m : ℕ} (u v : Y m) (a1 b1 a2 b2 : F) :
    omegaY (inLeft u + inRight a1 b1) (inLeft v + inRight a2 b2) =
      omegaY u v + (a1 * b2 + b1 * a2) := by
  simp only [omegaY, inLeft, inRight, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, add_zero, zero_add]
  ring

def embedBlock {m : ℕ} (α0 β0 : Y m) (z : Y 2) : Y (m + 1) :=
  inLeft (z.1 0 • α0 + z.2 0 • β0) + inRight (z.1 1) (z.2 1)

lemma embedBlock_add {m : ℕ} (α0 β0 : Y m) (z1 z2 : Y 2) :
    embedBlock α0 β0 (z1 + z2) = embedBlock α0 β0 z1 + embedBlock α0 β0 z2 := by
  simp only [embedBlock, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul]
  rw [show z1.1 0 • α0 + z2.1 0 • α0 + (z1.2 0 • β0 + z2.2 0 • β0) =
      (z1.1 0 • α0 + z1.2 0 • β0) + (z2.1 0 • α0 + z2.2 0 • β0) by abel]
  rw [inLeft_add, inRight_add]
  abel

lemma symp_lin_indep {m : ℕ} {α0 β0 : Y m} (hω : omegaY α0 β0 = 1) (c d : F) :
    c • α0 + d • β0 = 0 ↔ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have hsmul : ∀ (x : F) (u v : Y m), omegaY (x • u) v = x * omegaY u v := by
      intro x u v; rcases f2_cases x with rfl | rfl <;> simp [omegaY]
    have h1 := congr_arg (fun w => omegaY w β0) h
    have h2 := congr_arg (fun w => omegaY w α0) h
    simp only [omegaY_add_left, hsmul, omegaY_self, hω, omegaY_comm β0 α0, mul_zero, mul_one, zero_add, add_zero] at h1 h2
    have hz : omegaY (0 : Y m) β0 = 0 := by simp [omegaY]
    have hz2 : omegaY (0 : Y m) α0 = 0 := by simp [omegaY]
    rw [hz] at h1; rw [hz2] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; simp

lemma embedBlock_injective {m : ℕ} {α0 β0 : Y m} (hω : omegaY α0 β0 = 1) :
    Function.Injective (embedBlock α0 β0) := by
  intro z1 z2 h
  have hsub : embedBlock α0 β0 (z1 + z2) = 0 := by
    rw [embedBlock_add, h]
    ext j <;> exact f2_add_self _
  rw [embedBlock, inLeft_inRight_zero_iff, symp_lin_indep hω] at hsub
  rcases hsub with ⟨⟨h10, h20⟩, h11, h21⟩
  ext i
  · fin_cases i
    · exact (f2_eq_iff_add_eq_zero _ _).2 h10
    · exact (f2_eq_iff_add_eq_zero _ _).2 h11
  · fin_cases i
    · exact (f2_eq_iff_add_eq_zero _ _).2 h20
    · exact (f2_eq_iff_add_eq_zero _ _).2 h21

lemma omegaY_embedBlock {m : ℕ} (α0 β0 : Y m) (hω : omegaY α0 β0 = 1) (z1 z2 : Y 2) :
    omegaY (embedBlock α0 β0 z1) (embedBlock α0 β0 z2) = omegaY z1 z2 := by
  simp only [embedBlock, omegaY_inLeft_inRight]
  have hL : omegaY (z1.1 0 • α0 + z1.2 0 • β0) (z2.1 0 • α0 + z2.2 0 • β0) =
      z1.1 0 * z2.2 0 + z1.2 0 * z2.1 0 := by
    have hsmul : ∀ (c : F) (u v : Y m), omegaY (c • u) v = c * omegaY u v := by
      intro c u v; rcases f2_cases c with rfl | rfl <;> simp [omegaY]
    have hsmulR : ∀ (c : F) (u v : Y m), omegaY u (c • v) = c * omegaY u v := by
      intro c u v; rw [omegaY_comm, hsmul, omegaY_comm]
    rw [omegaY_add_left, omegaY_comm _ (z2.1 0 • α0 + z2.2 0 • β0), omegaY_add_left,
      omegaY_comm _ (z1.1 0 • α0), omegaY_comm _ (z1.1 0 • α0),
      omegaY_comm (z1.2 0 • β0) (z2.1 0 • α0 + z2.2 0 • β0), omegaY_add_left,
      omegaY_comm _ (z1.2 0 • β0), omegaY_comm _ (z1.2 0 • β0)]
    simp only [hsmul, hsmulR, omegaY_self, mul_zero, add_zero, zero_add, omegaY_comm β0 α0, hω,
      mul_one]
  rw [hL]
  simp only [omegaY, Fin.sum_univ_two]
  ring

def graphPlanes {m : ℕ} (p : Y m × Y m) : List (Y (m + 1) × Y (m + 1)) :=
  [ (inLeft p.1 + inRight 1 0, inLeft p.2 + inRight 0 1),
    (inLeft p.1 + inRight 0 1, inLeft p.2 + inRight 1 1),
    (inLeft p.1 + inRight 1 1, inLeft p.2 + inRight 1 0) ]

lemma graphPlanes_surplus {m : ℕ} (p : Y m × Y m) :
    ((graphPlanes p).map (fun q => -sgn (omegaY q.1 q.2))).sum =
      3 * sgn (omegaY p.1 p.2) := by
  simp only [graphPlanes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    omegaY_inLeft_inRight]
  rcases f2_cases (omegaY p.1 p.2) with h | h <;> rw [h] <;> decide

lemma graphPlanes_cover {m : ℕ} (p : Y m × Y m) (v : Y m) (a b : F) :
    ((graphPlanes p).map (fun q => (if q.1 = inLeft v + inRight a b then 1 else 0) +
      (if q.2 = inLeft v + inRight a b then 1 else 0) +
      (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0))).sum =
    if a = 0 ∧ b = 0 then 0
    else (if p.1 = v then 1 else 0) + (if p.2 = v then 1 else 0) + (if p.1 + p.2 = v then 1 else 0) := by
  have hadd : ∀ (u1 u2 : Y m) (x1 y1 x2 y2 : F),
      (inLeft u1 + inRight x1 y1) + (inLeft u2 + inRight x2 y2) =
        inLeft (u1 + u2) + inRight (x1 + x2) (y1 + y2) := by
    intro u1 u2 x1 y1 x2 y2
    rw [inLeft_add, inRight_add]; abel
  simp only [graphPlanes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    hadd, inLeft_inRight_eq_iff]
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl <;>
    simp [f2_one_add_one] <;> omega

lemma exists_symp_of_cover {m : ℕ} (C : PlaneCover m) :
    ∃ p0 ∈ C.planes, omegaY p0.1 p0.2 = 1 := by
  by_contra h
  push Not at h
  have hall : ∀ p ∈ C.planes, -sgn (omegaY p.1 p.2) = -1 := by
    intro p hp
    have h0 : omegaY p.1 p.2 = 0 := by
      rcases f2_cases (omegaY p.1 p.2) with h0 | h1
      · exact h0
      · exact (h p hp h1).elim
    simp [h0, sgn]
  have hsum : (C.planes.map (fun p => -sgn (omegaY p.1 p.2))).sum ≤ 0 := by
    have hgen : ∀ l : List (Y m × Y m), (∀ p ∈ l, -sgn (omegaY p.1 p.2) = -1) →
        (l.map (fun p => -sgn (omegaY p.1 p.2))).sum = -(l.length : ℤ) := by
      intro l hl
      induction l with
      | nil => simp
      | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [hl a (by simp), ih (fun p hp => hl p (by simp [hp]))]
        push_cast; ring
    rw [hgen C.planes hall]; omega
  linarith [C.surplus_eq]

lemma list_sum_flatMap {α β : Type*} [AddCommMonoid β] (l : List α) (g : α → List β) :
    (l.flatMap g).sum = (l.map (fun x => (g x).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.sum_append, ih]

noncomputable def stepCover {m : ℕ} (C : PlaneCover m) : PlaneCover (m + 1) := by
  classical
  have hex := exists_symp_of_cover C
  let p0 := Classical.choose hex
  have hp0_mem : p0 ∈ C.planes := (Classical.choose_spec hex).1
  have hp0_ω : omegaY p0.1 p0.2 = 1 := (Classical.choose_spec hex).2
  let rest := C.planes.erase p0
  have hperm : C.planes.Perm (p0 :: rest) := List.perm_cons_erase hp0_mem
  let L_left : List (Y (m + 1) × Y (m + 1)) := rest.map (fun p => (inLeft p.1, inLeft p.2))
  let L_graph : List (Y (m + 1) × Y (m + 1)) := rest.flatMap graphPlanes
  let L_blk : List (Y (m + 1) × Y (m + 1)) :=
    indBlockY2.map (fun q => (embedBlock p0.1 p0.2 q.1, embedBlock p0.1 p0.2 q.2))
  refine ⟨L_left ++ L_graph ++ L_blk, ?_, ?_, ?_, ?_⟩
  ·
    have hrest_len : rest.length + 1 = 2 * Mval m := by
      have := hperm.length_eq
      simp only [List.length_cons] at this
      rw [C.len_eq] at this
      omega
    have hgl : L_graph.length = 3 * rest.length := by
      simp only [L_graph, List.length_flatMap]
      have : (rest.map (fun p => (graphPlanes p).length)).sum = 3 * rest.length := by
        induction rest with
        | nil => simp
        | cons a l ih => simp [graphPlanes, ih]; omega
      exact this
    simp only [List.length_append, L_left, List.length_map, hgl, L_blk, indBlockY2_len, Mval_succ]
    omega
  ·
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · simp only [L_left, List.mem_map] at hq
      rcases hq with ⟨p, hp, rfl⟩
      have hpm : p ∈ C.planes := hperm.mem_iff.2 (List.mem_cons_of_mem _ hp)
      obtain ⟨h1, h2, h3⟩ := C.nonzero p hpm
      have hinj : ∀ u : Y m, u ≠ 0 → inLeft u ≠ 0 := by
        intro u hu h0
        apply hu
        ext j
        · have := congr_arg (fun z : Y (m + 1) => z.1 j.castSucc) h0; simpa [inLeft] using this
        · have := congr_arg (fun z : Y (m + 1) => z.2 j.castSucc) h0; simpa [inLeft] using this
      refine ⟨hinj p.1 h1, hinj p.2 h2, ?_⟩
      rw [← inLeft_add]; exact hinj _ h3
    · simp only [L_graph, List.mem_flatMap] at hq
      rcases hq with ⟨p, _, hqg⟩
      simp only [graphPlanes, List.mem_cons, List.not_mem_nil, or_false] at hqg
      have hadd : ∀ (u1 u2 : Y m) (x1 y1 x2 y2 : F),
          (inLeft u1 + inRight x1 y1) + (inLeft u2 + inRight x2 y2) =
            inLeft (u1 + u2) + inRight (x1 + x2) (y1 + y2) := by
        intro u1 u2 x1 y1 x2 y2; rw [inLeft_add, inRight_add]; abel
      rcases hqg with rfl | rfl | rfl <;>
        simp only [hadd, ne_eq, inLeft_inRight_zero_iff, f2_one_add_one] <;>
        refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have h10 : (1 : F) ≠ 0 := by decide
      · exact h10 h.2.1
      · exact h10 h.2.2
      · exact h10 (by simpa using h.2.1)
      · exact h10 h.2.2
      · exact h10 h.2.1
      · exact h10 (by simpa using h.2.1)
      · exact h10 h.2.1
      · exact h10 h.2.1
      · exact h10 (by simpa using h.2.2)
    · simp only [L_blk, List.mem_map] at hq
      rcases hq with ⟨r, hr, rfl⟩
      obtain ⟨h1, h2, h3⟩ := indBlockY2_nonzero r hr
      have hz0 : embedBlock p0.1 p0.2 0 = 0 := by
        simp [embedBlock, inLeft_inRight_zero_iff]
      have hinj : ∀ z : Y 2, z ≠ 0 → embedBlock p0.1 p0.2 z ≠ 0 := by
        intro z hz h0
        apply hz
        exact embedBlock_injective hp0_ω (h0.trans hz0.symm)
      refine ⟨hinj r.1 h1, hinj r.2 h2, ?_⟩
      rw [← embedBlock_add]; exact hinj _ h3
  ·
    intro γ hγ
    set v : Y m := (fun j => γ.1 j.castSucc, fun j => γ.2 j.castSucc)
    set a : F := γ.1 (Fin.last m)
    set b : F := γ.2 (Fin.last m)
    have hγ_eq : γ = inLeft v + inRight a b := by
      ext j
      · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft, inRight, v, a]
      · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft, inRight, v, b]
    rw [hγ_eq]
    simp only [List.map_append, List.sum_append]
    let cnt : Y m × Y m → ℕ := fun p =>
      (if p.1 = v then 1 else 0) + (if p.2 = v then 1 else 0) + (if p.1 + p.2 = v then 1 else 0)
    have hrest_cnt : (rest.map cnt).sum + cnt p0 = if v = 0 then 0 else 2 := by
      have hp := (hperm.map cnt).sum_eq
      simp only [List.map_cons, List.sum_cons] at hp
      by_cases hv : v = 0
      · have hzero : ∀ l : List (Y m × Y m), (∀ p ∈ l, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0) →
            (l.map cnt).sum = 0 := by
          intro l hl
          induction l with
          | nil => simp
          | cons x t ih =>
            obtain ⟨h1, h2, h3⟩ := hl x (by simp)
            rw [List.map_cons, List.sum_cons, ih (fun p hp => hl p (by simp [hp]))]
            simp [cnt, hv, h1, h2, h3]
        rw [if_pos hv]
        have hC0 := hzero C.planes C.nonzero
        omega
      · rw [if_neg hv]
        have hc := C.cover_eq v hv
        have hc' : (C.planes.map cnt).sum = 2 := hc
        omega

    have hL_left : (L_left.map (fun q => (if q.1 = inLeft v + inRight a b then 1 else 0) +
        (if q.2 = inLeft v + inRight a b then 1 else 0) +
        (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0))).sum =
        if a = 0 ∧ b = 0 then (rest.map cnt).sum else 0 := by
      simp only [L_left, List.map_map]
      have hterm : ∀ p : Y m × Y m,
          ((if inLeft p.1 = inLeft v + inRight a b then 1 else 0) +
           (if inLeft p.2 = inLeft v + inRight a b then 1 else 0) +
           (if inLeft p.1 + inLeft p.2 = inLeft v + inRight a b then 1 else 0)) =
          if a = 0 ∧ b = 0 then cnt p else 0 := by
        intro p
        have h0r : ∀ u : Y m, inLeft u = inLeft u + inRight 0 0 := by
          intro u; ext j
          · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft, inRight]
          · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft, inRight]
        rw [← inLeft_add]
        conv_lhs => rw [h0r p.1, h0r p.2, h0r (p.1 + p.2)]
        simp only [inLeft_inRight_eq_iff, cnt]
        by_cases hab : a = 0 ∧ b = 0
        · rcases hab with ⟨ha0, hb0⟩; simp [ha0, hb0]
        · simp only [hab, ↓reduceIte]
          have hna : ¬(0 = a ∧ 0 = b) := fun ⟨h1, h2⟩ => hab ⟨h1.symm, h2.symm⟩
          simp [hna]
      have hmap : rest.map ((fun q => (if q.1 = inLeft v + inRight a b then 1 else 0) +
          (if q.2 = inLeft v + inRight a b then 1 else 0) +
          (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0)) ∘ (fun p => (inLeft p.1, inLeft p.2))) =
          rest.map (fun p => if a = 0 ∧ b = 0 then cnt p else 0) := by
        congr 1; ext p; exact hterm p
      rw [hmap]
      by_cases hab : a = 0 ∧ b = 0
      · simp [hab]
      · simp [hab]

    have hL_graph : (L_graph.map (fun q => (if q.1 = inLeft v + inRight a b then 1 else 0) +
        (if q.2 = inLeft v + inRight a b then 1 else 0) +
        (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0))).sum =
        if a = 0 ∧ b = 0 then 0 else (rest.map cnt).sum := by
      simp only [L_graph, List.map_flatMap, list_sum_flatMap]
      have hmap : rest.map (fun p => ((graphPlanes p).map (fun q =>
          (if q.1 = inLeft v + inRight a b then 1 else 0) +
          (if q.2 = inLeft v + inRight a b then 1 else 0) +
          (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0))).sum) =
          rest.map (fun p => if a = 0 ∧ b = 0 then 0 else cnt p) := by
        congr 1; ext p; exact graphPlanes_cover p v a b
      rw [hmap]
      by_cases hab : a = 0 ∧ b = 0
      · simp [hab]
      · simp [hab]

    have hL_blk : (L_blk.map (fun q => (if q.1 = inLeft v + inRight a b then 1 else 0) +
        (if q.2 = inLeft v + inRight a b then 1 else 0) +
        (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0))).sum =
        if v = 0 then (if a = 0 ∧ b = 0 then 0 else 2) else cnt p0 := by
      have hcnt_p0 : cnt p0 = if v = p0.1 ∨ v = p0.2 ∨ v = p0.1 + p0.2 then 1 else 0 := by
        have hne1 : p0.1 ≠ p0.2 := by
          intro heq
          have h0 : p0.1 + p0.2 = 0 := by rw [heq]; ext j <;> exact f2_add_self _
          exact (C.nonzero p0 hp0_mem).2.2 h0
        have hne2 : p0.1 ≠ p0.1 + p0.2 := by
          intro heq
          have h0 : p0.2 = 0 := by
            have := congr_arg (fun z => p0.1 + z) heq
            simpa [← add_assoc, show p0.1 + p0.1 = 0 by ext j <;> exact f2_add_self _] using this.symm
          exact (C.nonzero p0 hp0_mem).2.1 h0
        have hne3 : p0.2 ≠ p0.1 + p0.2 := by
          intro heq
          have h0 : p0.1 = 0 := by
            have := congr_arg (fun z => z + p0.2) heq
            simpa [add_assoc, show p0.2 + p0.2 = 0 by ext j <;> exact f2_add_self _] using this.symm
          exact (C.nonzero p0 hp0_mem).1 h0
        simp only [cnt]
        by_cases h1 : v = p0.1
        · simp [h1, hne1.symm, hne2.symm]
        · by_cases h2 : v = p0.2
          · simp [h1, h2, hne1, hne3.symm]
          · by_cases h3 : v = p0.1 + p0.2
            · simp [h1, h2, h3, hne2, hne3]
            · simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]
      by_cases hexz : ∃ z : Y 2, embedBlock p0.1 p0.2 z = inLeft v + inRight a b
      · rcases hexz with ⟨z, hz⟩
        have hz_ne : z ≠ 0 := by
          intro hz0; subst hz0
          have h00 : (0 : Y (m + 1)) = inLeft 0 + inRight 0 0 :=
            ((inLeft_inRight_zero_iff 0 0 0).2 ⟨rfl, rfl, rfl⟩).symm
          have : (0 : Y (m + 1)) = inLeft v + inRight a b := by
            rw [h00]; simpa [embedBlock] using hz
          exact hγ (hγ_eq.trans this.symm)
        have hsum_z : (L_blk.map (fun q => (if q.1 = inLeft v + inRight a b then 1 else 0) +
            (if q.2 = inLeft v + inRight a b then 1 else 0) +
            (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0))).sum =
            if z.1 0 = 0 ∧ z.2 0 = 0 then 2 else 1 := by
          simp only [L_blk, List.map_map]
          have hmap : indBlockY2.map ((fun q => (if q.1 = inLeft v + inRight a b then 1 else 0) +
              (if q.2 = inLeft v + inRight a b then 1 else 0) +
              (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0)) ∘
              (fun q => (embedBlock p0.1 p0.2 q.1, embedBlock p0.1 p0.2 q.2))) =
              indBlockY2.map (fun q => (if q.1 = z then 1 else 0) +
                (if q.2 = z then 1 else 0) + (if q.1 + q.2 = z then 1 else 0)) := by
            congr 1; ext q
            simp only [Function.comp_apply, ← embedBlock_add, ← hz,
              (embedBlock_injective hp0_ω).eq_iff]
          rw [hmap]
          exact indBlockY2_cover z hz_ne
        rw [hsum_z]
        rw [embedBlock, inLeft_inRight_eq_iff] at hz
        rcases hz with ⟨hvz, haz, hbz⟩
        by_cases hz00 : z.1 0 = 0 ∧ z.2 0 = 0
        · rcases hz00 with ⟨hz1, hz2⟩
          have hv0 : v = 0 := by simpa [hz1, hz2] using hvz.symm
          have hnab : ¬(a = 0 ∧ b = 0) := by
            intro ⟨ha0, hb0⟩
            apply hγ; rw [hγ_eq, hv0, ha0, hb0, inLeft_inRight_zero_iff]; exact ⟨rfl, rfl, rfl⟩
          simp [hz1, hz2, hv0, hnab]
        · have hv_ne : v ≠ 0 := by
            intro hv0
            rw [hv0, symp_lin_indep hp0_ω] at hvz
            exact hz00 hvz
          have hv_mem : v = p0.1 ∨ v = p0.2 ∨ v = p0.1 + p0.2 := by
            rcases f2_cases (z.1 0) with h1 | h1 <;> rcases f2_cases (z.2 0) with h2 | h2
            · exact (hz00 ⟨h1, h2⟩).elim
            · right; left; simpa [h1, h2] using hvz.symm
            · left; simpa [h1, h2] using hvz.symm
            · right; right; simpa [h1, h2] using hvz.symm
          simp [hz00, hv_ne, hcnt_p0, hv_mem]
      · push Not at hexz
        have hzero_blk : (L_blk.map (fun q => (if q.1 = inLeft v + inRight a b then 1 else 0) +
            (if q.2 = inLeft v + inRight a b then 1 else 0) +
            (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0))).sum = 0 := by
          simp only [L_blk, List.map_map]
          have hmap : indBlockY2.map ((fun q => (if q.1 = inLeft v + inRight a b then 1 else 0) +
              (if q.2 = inLeft v + inRight a b then 1 else 0) +
              (if q.1 + q.2 = inLeft v + inRight a b then 1 else 0)) ∘
              (fun q => (embedBlock p0.1 p0.2 q.1, embedBlock p0.1 p0.2 q.2))) =
              indBlockY2.map (fun _ => 0) := by
            congr 1; ext q
            simp only [Function.comp_apply, ← embedBlock_add]
            simp [hexz q.1, hexz q.2, hexz (q.1 + q.2)]
          rw [hmap]; simp
        rw [hzero_blk]
        have hv_not0 : v ≠ 0 := by
          intro hv0
          apply hexz ((![0, a], ![0, b]) : Y 2)
          simp [embedBlock, hv0]
        have hv_notmem : ¬(v = p0.1 ∨ v = p0.2 ∨ v = p0.1 + p0.2) := by
          rintro (h1 | h2 | h3)
          · exact hexz ((![1, a], ![0, b]) : Y 2) (by simp [embedBlock, h1])
          · exact hexz ((![0, a], ![1, b]) : Y 2) (by simp [embedBlock, h2])
          · exact hexz ((![1, a], ![1, b]) : Y 2) (by simp [embedBlock, h3])
        simp [hv_not0, hcnt_p0, hv_notmem]
    rw [hL_left, hL_graph, hL_blk]
    by_cases hv : v = 0
    · by_cases hab : a = 0 ∧ b = 0
      · exfalso; apply hγ; rw [hγ_eq, hv, hab.1, hab.2, inLeft_inRight_zero_iff]; exact ⟨rfl, rfl, rfl⟩
      · simp [hv, hab] at hrest_cnt ⊢; omega
    · by_cases hab : a = 0 ∧ b = 0 <;> simp [hv, hab] at hrest_cnt ⊢ <;> omega
  ·
    simp only [List.map_append, List.sum_append]
    have h1 : (L_left.map (fun q => -sgn (omegaY q.1 q.2))).sum =
        (rest.map (fun p => -sgn (omegaY p.1 p.2))).sum := by
      have h0r : ∀ u : Y m, inLeft u = inLeft u + inRight 0 0 := by
        intro u; ext j
        · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft, inRight]
        · refine Fin.lastCases ?_ ?_ j <;> simp [inLeft, inRight]
      have hω : ∀ p : Y m × Y m, omegaY (inLeft p.1) (inLeft p.2) = omegaY p.1 p.2 := by
        intro p
        conv_lhs => rw [h0r p.1, h0r p.2]
        rw [omegaY_inLeft_inRight]; simp
      simp only [L_left, List.map_map]
      apply congr_arg List.sum
      apply List.map_congr_left
      intro p _
      exact congr_arg (fun z => -sgn z) (hω p)
    have h2 : (L_graph.map (fun q => -sgn (omegaY q.1 q.2))).sum =
        -3 * (rest.map (fun p => -sgn (omegaY p.1 p.2))).sum := by
      simp only [L_graph, List.map_flatMap, list_sum_flatMap]
      have hstep : ∀ l : List (Y m × Y m),
          (l.map (fun p => ((graphPlanes p).map (fun q => -sgn (omegaY q.1 q.2))).sum)).sum =
            -3 * (l.map (fun p => -sgn (omegaY p.1 p.2))).sum := by
        intro l
        induction l with
        | nil => simp
        | cons a t ih =>
          rw [List.map_cons, List.sum_cons, graphPlanes_surplus, ih, List.map_cons, List.sum_cons]
          ring
      exact hstep rest
    have h3 : (L_blk.map (fun q => -sgn (omegaY q.1 q.2))).sum = 4 := by
      simp only [L_blk, List.map_map]
      have hmap : indBlockY2.map ((fun q => -sgn (omegaY q.1 q.2)) ∘
          (fun q => (embedBlock p0.1 p0.2 q.1, embedBlock p0.1 p0.2 q.2))) =
          indBlockY2.map (fun q => -sgn (omegaY q.1 q.2)) := by
        congr 1; ext q
        simp only [Function.comp_apply, omegaY_embedBlock p0.1 p0.2 hp0_ω]
      rw [hmap]
      exact indBlockY2_surplus
    have hrest_sur : (rest.map (fun p => -sgn (omegaY p.1 p.2))).sum = 1 := by
      have hp := (hperm.map (fun p => -sgn (omegaY p.1 p.2))).sum_eq
      simp only [List.map_cons, List.sum_cons, hp0_ω, sgn_one, neg_neg] at hp
      linarith [C.surplus_eq]
    rw [h1, h2, h3, hrest_sur]
    ring

noncomputable def mkPlaneCover : ∀ m : ℕ, 2 ≤ m → PlaneCover m
  | 0, hm => (by omega : False).elim
  | 1, hm => (by omega : False).elim
  | 2, _ => baseCover2
  | m + 3, _ => stepCover (mkPlaneCover (m + 2) (by omega))

lemma planeCover_sum_sgn {m : ℕ} (C : PlaneCover m) (y : Y m) :
    (C.planes.map (fun p => sgn (planeOut p.1 p.2 (planeA p.1 p.2 y)))).sum =
      (2 ^ m : ℤ) * sgn (f0 y) := by
  have h2 : 2 * (C.planes.map (fun p => sgn (planeOut p.1 p.2 (planeA p.1 p.2 y)))).sum =
      (C.planes.map (fun p => -sgn (omegaY p.1 p.2))).sum +
      (C.planes.map (fun p =>
        sgn (f0 p.1) * sgn (dotY p.1 y) +
        sgn (f0 p.2) * sgn (dotY p.2 y) +
        sgn (f0 (p.1 + p.2)) * sgn (dotY (p.1 + p.2) y))).sum := by
    have hmul : ∀ (l : List (Y m × Y m)),
        2 * (l.map (fun p => sgn (planeOut p.1 p.2 (planeA p.1 p.2 y)))).sum =
        (l.map (fun p => -sgn (omegaY p.1 p.2))).sum +
        (l.map (fun p =>
          sgn (f0 p.1) * sgn (dotY p.1 y) +
          sgn (f0 p.2) * sgn (dotY p.2 y) +
          sgn (f0 (p.1 + p.2)) * sgn (dotY (p.1 + p.2) y))).sum := by
      intro l
      induction l with
      | nil => simp
      | cons p t ih =>
        simp only [List.map_cons, List.sum_cons]
        have hp := planeOut_sgn p.1 p.2 (planeA p.1 p.2 y)
        have hA0 : planeA p.1 p.2 y 0 = dotY p.1 y := rfl
        have hA1 : planeA p.1 p.2 y 1 = dotY p.2 y := rfl
        rw [hA0, hA1, ← dotY_add_left] at hp
        linarith
    exact hmul C.planes
  have hchar : (C.planes.map (fun p =>
      sgn (f0 p.1) * sgn (dotY p.1 y) +
      sgn (f0 p.2) * sgn (dotY p.2 y) +
      sgn (f0 (p.1 + p.2)) * sgn (dotY (p.1 + p.2) y))).sum =
      2 * ∑ γ ∈ Finset.univ.erase (0 : Y m), sgn (f0 γ) * sgn (dotY γ y) := by
    have hswap : ∀ (l : List (Y m × Y m)),
        (∀ p ∈ l, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0) →
        (l.map (fun p =>
          sgn (f0 p.1) * sgn (dotY p.1 y) +
          sgn (f0 p.2) * sgn (dotY p.2 y) +
          sgn (f0 (p.1 + p.2)) * sgn (dotY (p.1 + p.2) y))).sum =
        ∑ γ ∈ Finset.univ.erase (0 : Y m),
          ((l.map (fun p => (if p.1 = γ then (1 : ℕ) else 0) + (if p.2 = γ then (1 : ℕ) else 0) +
            (if p.1 + p.2 = γ then (1 : ℕ) else 0))).sum : ℤ) * (sgn (f0 γ) * sgn (dotY γ y)) := by
      intro l hl
      induction l with
      | nil => simp
      | cons p t ih =>
        obtain ⟨h1, h2, h3⟩ := hl p (by simp)
        simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib]
        rw [ih (fun q hq => hl q (by simp [hq]))]
        congr 1
        have hpt : ∀ u : Y m, u ≠ 0 →
            ∑ γ ∈ Finset.univ.erase (0 : Y m), ((if u = γ then (1 : ℕ) else 0) : ℤ) *
              (sgn (f0 γ) * sgn (dotY γ y)) = sgn (f0 u) * sgn (dotY u y) := by
          intro u hu
          rw [Finset.sum_eq_single u]
          · simp
          · intro γ _ hne; simp [Ne.symm hne]
          · intro hmem; exact (hmem (Finset.mem_erase.2 ⟨hu, Finset.mem_univ u⟩)).elim
        rw [← hpt p.1 h1, ← hpt p.2 h2, ← hpt (p.1 + p.2) h3]
        simp_rw [← Finset.sum_add_distrib, ← add_mul]
        apply Finset.sum_congr rfl
        intro γ _
        push_cast; rfl
    rw [hswap C.planes C.nonzero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hc := C.cover_eq γ (Finset.mem_erase.1 hγ).1
    have hcz : ((C.planes.map (fun p => (if p.1 = γ then (1 : ℕ) else 0) + (if p.2 = γ then (1 : ℕ) else 0) +
        (if p.1 + p.2 = γ then (1 : ℕ) else 0))).sum : ℤ) = 2 := by exact_mod_cast hc
    rw [hcz]
  have hwalsh : (1 : ℤ) + ∑ γ ∈ Finset.univ.erase (0 : Y m), sgn (f0 γ) * sgn (dotY γ y) =
      (2 ^ m : ℤ) * sgn (f0 y) := by
    have h0 : ∑ γ : Y m, sgn (f0 γ) * sgn (dotY γ y) =
        sgn (f0 (0 : Y m)) * sgn (dotY 0 y) +
        ∑ γ ∈ Finset.univ.erase (0 : Y m), sgn (f0 γ) * sgn (dotY γ y) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Y m))]
    have hsym : ∑ γ : Y m, sgn (f0 γ) * sgn (dotY γ y) = (2 ^ m : ℤ) * sgn (f0 y) := by
      have hc : ∀ γ : Y m, dotY γ y = dotY y γ := by
        intro γ; simp only [dotY]; congr 1 <;> (congr 1; funext j; ring)
      calc ∑ γ : Y m, sgn (f0 γ) * sgn (dotY γ y)
          = ∑ γ : Y m, sgn (f0 γ + dotY y γ) := by
            congr 1; funext γ; rw [← hc, sgn_add]
        _ = (2 ^ m : ℤ) * sgn (f0 y) := sum_f0_chi y
    simp only [f0_zero, dotY_zero_left, sgn_zero, mul_one] at h0
    linarith
  rw [C.surplus_eq, hchar] at h2
  linarith

lemma upper_bound_normal {m T : ℕ} (hm : 2 ≤ m) (hT : 0 < T) (hdvd : 2 * Mval m ∣ T) :
    ∃ (A : Fin T → Y m →ₗ[F] (Fin 2 → F)) (out : Fin T → (Fin 2 → F) → F),
      ∀ y : Y m, (Mval m + 2 ^ (m - 1)) * T ≤
        (2 * Mval m) * Nat.card {i : Fin T // out i (A i y) = f0 y} := by
  set M := Mval m
  have hMpos : 0 < M := Mval_pos (by omega)
  let C := mkPlaneCover m hm
  rcases hdvd with ⟨q, hTq⟩
  have h2Mpos : 0 < 2 * M := by omega
  let getP : Fin T → Y m × Y m := fun i =>
    C.planes.get ⟨i.val % (2 * M), by rw [C.len_eq]; exact Nat.mod_lt _ h2Mpos⟩
  refine ⟨fun i => planeA (getP i).1 (getP i).2, fun i => planeOut (getP i).1 (getP i).2, ?_⟩
  intro y
  have hsum_single : ∑ j : Fin (2 * M), sgn (planeOut (C.planes.get ⟨j.val, by rw [C.len_eq]; exact j.isLt⟩).1
      (C.planes.get ⟨j.val, by rw [C.len_eq]; exact j.isLt⟩).2
      (planeA (C.planes.get ⟨j.val, by rw [C.len_eq]; exact j.isLt⟩).1
        (C.planes.get ⟨j.val, by rw [C.len_eq]; exact j.isLt⟩).2 y)) = (2 ^ m : ℤ) * sgn (f0 y) := by
    have h1 := planeCover_sum_sgn C y
    rw [← h1]
    have hlen : C.planes.length = 2 * M := C.len_eq
    let e : Fin (2 * M) ≃ Fin C.planes.length := finCongr hlen.symm
    have hlist : ∀ (l : List (Y m × Y m)) (g : Y m × Y m → ℤ),
        (l.map g).sum = ∑ k : Fin l.length, g (l.get k) := by
      intro l g
      induction l with
      | nil => simp
      | cons a t ih =>
        rw [List.map_cons, List.sum_cons, ih]
        symm
        exact Fin.sum_univ_succ (fun k : Fin (a :: t).length => g ((a :: t).get k))
    rw [hlist C.planes]
    exact Fintype.sum_equiv e _ (fun k : Fin C.planes.length =>
      sgn (planeOut (C.planes.get k).1 (C.planes.get k).2
        (planeA (C.planes.get k).1 (C.planes.get k).2 y))) (fun j => rfl)
  have hsum_T : ∑ i : Fin T, sgn (planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y)) =
      (q : ℤ) * ((2 ^ m : ℤ) * sgn (f0 y)) := by
    let e : Fin T ≃ Fin q × Fin (2 * M) :=
      (finCongr (by rw [hTq, mul_comm])).trans finProdFinEquiv.symm
    rw [Fintype.sum_equiv e _ (fun p : Fin q × Fin (2 * M) =>
      sgn (planeOut (C.planes.get ⟨p.2.val, by rw [C.len_eq]; exact p.2.isLt⟩).1
        (C.planes.get ⟨p.2.val, by rw [C.len_eq]; exact p.2.isLt⟩).2
        (planeA (C.planes.get ⟨p.2.val, by rw [C.len_eq]; exact p.2.isLt⟩).1
          (C.planes.get ⟨p.2.val, by rw [C.len_eq]; exact p.2.isLt⟩).2 y))) ?_]
    · rw [Fintype.sum_prod_type]
      simp_rw [hsum_single, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · intro i
      have hmod : (e i).2.val = i.val % (2 * M) := by
        simp [e, finProdFinEquiv]
      simp [getP, hmod]
  have hscore : ∑ i : Fin T, sgn (planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y) + f0 y) =
      (q : ℤ) * (2 ^ m : ℤ) := by
    simp_rw [sgn_add, ← Finset.sum_mul, hsum_T]
    have hs := sgn_mul_self (f0 y)
    calc (q : ℤ) * ((2 ^ m : ℤ) * sgn (f0 y)) * sgn (f0 y)
        = (q : ℤ) * (2 ^ m : ℤ) * (sgn (f0 y) * sgn (f0 y)) := by ring
      _ = (q : ℤ) * (2 ^ m : ℤ) := by rw [hs, mul_one]
  have hcard : Nat.card {i : Fin T // planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y) = f0 y} =
      (Finset.univ.filter (fun i : Fin T =>
        planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y) + f0 y = 0)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext i
    simp [f2_eq_iff_add_eq_zero]
  have hs := sgn_sum_eq (fun i : Fin T => planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y) + f0 y)
  simp only [Fintype.card_fin] at hs
  rw [hscore] at hs
  have h2m : (2 ^ m : ℤ) = 2 * (2 ^ (m - 1) : ℤ) := by
    have : m = (m - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  have hcard_z : (2 * M : ℤ) * ((Finset.univ.filter (fun i : Fin T =>
      planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y) + f0 y = 0)).card : ℤ) =
      ((M + 2 ^ (m - 1)) * T : ℤ) := by
    have hTq_z : (T : ℤ) = 2 * (M : ℤ) * (q : ℤ) := by exact_mod_cast hTq
    have h2card : 2 * ((Finset.univ.filter (fun i : Fin T =>
        planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y) + f0 y = 0)).card : ℤ) =
        (T : ℤ) + (q : ℤ) * (2 ^ m : ℤ) := by linarith
    calc (2 * (M : ℤ)) * ((Finset.univ.filter (fun i : Fin T =>
            planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y) + f0 y = 0)).card : ℤ)
        = (M : ℤ) * (2 * ((Finset.univ.filter (fun i : Fin T =>
            planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y) + f0 y = 0)).card : ℤ)) := by ring
      _ = (M : ℤ) * ((T : ℤ) + (q : ℤ) * (2 ^ m : ℤ)) := by rw [h2card]
      _ = (M : ℤ) * (T : ℤ) + (2 ^ (m - 1) : ℤ) * (2 * (M : ℤ) * (q : ℤ)) := by rw [h2m]; ring
      _ = (M : ℤ) * (T : ℤ) + (2 ^ (m - 1) : ℤ) * (T : ℤ) := by rw [← hTq_z]
      _ = ((M + 2 ^ (m - 1)) * T : ℤ) := by ring
  rw [hcard]
  have : ((M + 2 ^ (m - 1)) * T : ℤ) ≤
      (2 * M : ℤ) * ((Finset.univ.filter (fun i : Fin T =>
        planeOut (getP i).1 (getP i).2 (planeA (getP i).1 (getP i).2 y) + f0 y = 0)).card : ℤ) :=
    le_of_eq hcard_z.symm
  exact_mod_cast this

lemma symplectic_basis_subspace {n : ℕ} (B : (Fin n → F) → (Fin n → F) → F)
    (hB_add_l : ∀ u v w, B (u + v) w = B u w + B v w)
    (hB_comm : ∀ u v, B u v = B v u)
    (hB_self : ∀ u, B u u = 0) :
    ∀ (d : ℕ) (W : Submodule F (Fin n → F)),
      Module.finrank F W = d →
      (∀ u ∈ W, (∀ v ∈ W, B u v = 0) → u = 0) →
      ∃ (k : ℕ) (eW : W ≃ₗ[F] Y k), d = 2 * k ∧ ∀ u v : W, B u.1 v.1 = omegaY (eW u) (eW v) := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro W hdim hnd
    by_cases hd0 : d = 0
    · have hWbot : W = ⊥ := Submodule.finrank_eq_zero.1 (hdim.trans hd0)
      refine ⟨0, ?_, by omega, ?_⟩
      · refine
          { toFun := fun _ => 0
            invFun := fun _ => 0
            map_add' := fun _ _ => by simp
            map_smul' := fun _ _ => by simp
            left_inv := fun u => by
              ext j
              have hu : u.1 = 0 := by rw [← Submodule.mem_bot (R := F), ← hWbot]; exact u.2
              simp [hu]
            right_inv := fun y => by ext j <;> exact j.elim0 }
      · intro u v
        have hu : u.1 = 0 := by rw [← Submodule.mem_bot (R := F), ← hWbot]; exact u.2
        have hB0 : B 0 v.1 = 0 := by
          have := hB_add_l 0 0 v.1
          simp only [zero_add] at this
          have := congr_arg (fun z => z + B 0 v.1) this
          simpa [f2_add_self] using this.symm
        simp [hu, hB0, omegaY]
    · have hWne : W ≠ ⊥ := by
        intro hbot; apply hd0; rw [← hdim, hbot, finrank_bot]
      obtain ⟨e, heW, he0⟩ : ∃ e ∈ W, e ≠ 0 := by
        by_contra h
        push Not at h
        apply hWne
        exact (Submodule.eq_bot_iff W).2 h
      obtain ⟨d0, hd0W, hBed⟩ : ∃ d0 ∈ W, B e d0 = 1 := by
        by_contra h
        push Not at h
        apply he0
        apply hnd e heW
        intro v hv
        rcases f2_cases (B e v) with h0 | h1
        · exact h0
        · exact (h v hv h1).elim
      have hB_add_r : ∀ u v w, B u (v + w) = B u v + B u w := fun u v w => by
        rw [hB_comm, hB_add_l, hB_comm v u, hB_comm w u]
      have hB_smul_l : ∀ (c : F) u v, B (c • u) v = c * B u v := by
        intro c u v
        rcases f2_cases c with rfl | rfl
        · simp only [zero_smul, zero_mul]
          have := hB_add_l 0 0 v; simp only [zero_add] at this
          have := congr_arg (fun z => z + B 0 v) this
          simpa [f2_add_self] using this.symm
        · simp
      have hB_smul_r : ∀ (c : F) u v, B u (c • v) = c * B u v := fun c u v => by
        rw [hB_comm, hB_smul_l, hB_comm]
      let W' : Submodule F (Fin n → F) :=
        { carrier := {w | w ∈ W ∧ B e w = 0 ∧ B d0 w = 0}, add_mem' := fun hx hy => ⟨W.add_mem hx.1 hy.1, by rw [hB_add_r, hx.2.1, hy.2.1, add_zero],
            by rw [hB_add_r, hx.2.2, hy.2.2, add_zero]⟩
          zero_mem' := ⟨W.zero_mem, by simpa using hB_smul_r 0 e 0, by simpa using hB_smul_r 0 d0 0⟩
          smul_mem' := fun c x hx => ⟨W.smul_mem c hx.1, by rw [hB_smul_r, hx.2.1, mul_zero],
            by rw [hB_smul_r, hx.2.2, mul_zero]⟩ }
      have hdecomp : ∀ w ∈ W, ∃ (a b : F) (w' : W'), w = a • e + b • d0 + w'.1 := by
        intro w hw
        refine ⟨B d0 w, B e w, ⟨w + B d0 w • e + B e w • d0, ?_⟩, ?_⟩
        · refine ⟨W.add_mem (W.add_mem hw (W.smul_mem _ heW)) (W.smul_mem _ hd0W), ?_, ?_⟩
          · rw [hB_add_r, hB_add_r, hB_smul_r, hB_smul_r, hB_self, hBed, mul_zero, mul_one, add_zero, f2_add_self]
          · rw [hB_add_r, hB_add_r, hB_smul_r, hB_smul_r, hB_comm d0 e, hBed, hB_self,
              mul_one, mul_zero, add_zero, f2_add_self]
        · ext j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have h1 := f2_add_self (B d0 w * e j)
          have h2 := f2_add_self (B e w * d0 j)
          linear_combination -h1 - h2
      have hnd' : ∀ u ∈ W', (∀ v ∈ W', B u v = 0) → u = 0 := by
        intro u hu h0
        apply hnd u hu.1
        intro v hv
        obtain ⟨a, b, v', rfl⟩ := hdecomp v hv
        rw [hB_add_r, hB_add_r, hB_smul_r, hB_smul_r, hB_comm u e, hu.2.1, hB_comm u d0, hu.2.2,
          h0 v'.1 v'.2, mul_zero, mul_zero, add_zero, add_zero]
      let eSplit : W ≃ₗ[F] (F × F) × W' :=
        { toFun := fun w => ((B d0 w.1, B e w.1), ⟨w.1 + B d0 w.1 • e + B e w.1 • d0,
            ⟨W.add_mem (W.add_mem w.2 (W.smul_mem _ heW)) (W.smul_mem _ hd0W),
              by rw [hB_add_r, hB_add_r, hB_smul_r, hB_smul_r, hB_self, hBed, mul_zero, mul_one, add_zero, f2_add_self],
              by rw [hB_add_r, hB_add_r, hB_smul_r, hB_smul_r, hB_comm d0 e, hBed, hB_self,
                mul_one, mul_zero, add_zero, f2_add_self]⟩⟩)
          invFun := fun p => ⟨p.1.1 • e + p.1.2 • d0 + p.2.1,
            W.add_mem (W.add_mem (W.smul_mem _ heW) (W.smul_mem _ hd0W)) p.2.2.1⟩
          map_add' := fun u v => by
            apply Prod.ext
            · apply Prod.ext
              · exact hB_add_r d0 u.1 v.1
              · exact hB_add_r e u.1 v.1
            · apply Subtype.ext
              ext j
              simp only [Prod.snd_add, Submodule.coe_add, hB_add_r, add_smul, Pi.add_apply,
                Pi.smul_apply, smul_eq_mul]
              ring
          map_smul' := fun c u => by
            have hB0 : ∀ x, B x 0 = 0 := fun x => by simpa using hB_smul_r 0 x 0
            apply Prod.ext
            · apply Prod.ext
              · simp [hB_smul_r]
              · simp [hB_smul_r]
            · apply Subtype.ext
              ext j
              rcases f2_cases c with rfl | rfl <;> simp [hB0]
          left_inv := fun w => by
            ext j
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have h1 := f2_add_self (B d0 w.1 * e j)
            have h2 := f2_add_self (B e w.1 * d0 j)
            linear_combination h1 + h2
          right_inv := fun p => by
            have hBd : B d0 (p.1.1 • e + p.1.2 • d0 + p.2.1) = p.1.1 := by
              rw [hB_add_r, hB_add_r, hB_smul_r, hB_smul_r, hB_comm d0 e, hBed, hB_self,
                p.2.2.2.2, mul_one, mul_zero, add_zero, add_zero]
            have hBe : B e (p.1.1 • e + p.1.2 • d0 + p.2.1) = p.1.2 := by
              rw [hB_add_r, hB_add_r, hB_smul_r, hB_smul_r, hB_self, hBed, p.2.2.2.1,
                mul_zero, mul_one, zero_add, add_zero]
            apply Prod.ext
            · apply Prod.ext
              · exact hBd
              · exact hBe
            · apply Subtype.ext
              ext j
              simp only [hBd, hBe, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              have h1 := f2_add_self (p.1.1 * e j)
              have h2 := f2_add_self (p.1.2 * d0 j)
              linear_combination h1 + h2 }
      have hdim_split : d = 2 + Module.finrank F W' := by
        have h1 : Module.finrank F W = Module.finrank F ((F × F) × W') := eSplit.finrank_eq
        rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self] at h1
        omega
      have hdlt : Module.finrank F W' < d := by omega
      obtain ⟨k, eW', hk_dim, hB'⟩ := ih (Module.finrank F W') hdlt W' rfl hnd'
      let eProd : ((F × F) × Y k) ≃ₗ[F] Y (k + 1) := LinearEquiv.mk
        { toFun := fun p => (Fin.snoc p.2.1 p.1.1, Fin.snoc p.2.2 p.1.2)
          map_add' := fun p q => by
            ext j
            · refine Fin.lastCases ?_ ?_ j <;> simp
            · refine Fin.lastCases ?_ ?_ j <;> simp
          map_smul' := fun c p => by
            ext j
            · refine Fin.lastCases ?_ ?_ j <;> simp
            · refine Fin.lastCases ?_ ?_ j <;> simp }
        (fun y => ((y.1 (Fin.last k), y.2 (Fin.last k)),
          (fun j => y.1 j.castSucc, fun j => y.2 j.castSucc)))
        (fun p => by ext j <;> simp [Fin.snoc_castSucc, Fin.snoc_last])
        (fun y => by
          ext j
          · exact congr_fun (Fin.snoc_init_self y.1) j
          · exact congr_fun (Fin.snoc_init_self y.2) j)
      let eFull : W ≃ₗ[F] Y (k + 1) :=
        (eSplit.trans (LinearEquiv.prodCongr (LinearEquiv.refl F (F × F)) eW')).trans eProd
      refine ⟨k + 1, eFull, by omega, ?_⟩
      intro u v
      have hu : u.1 = (eSplit u).1.1 • e + (eSplit u).1.2 • d0 + (eSplit u).2.1 :=
        congr_arg Subtype.val (eSplit.left_inv u).symm
      have hv : v.1 = (eSplit v).1.1 • e + (eSplit v).1.2 • d0 + (eSplit v).2.1 :=
        congr_arg Subtype.val (eSplit.left_inv v).symm
      have hBuv : B u.1 v.1 =
          ((eSplit u).1.1 * (eSplit v).1.2 + (eSplit u).1.2 * (eSplit v).1.1) +
            B (eSplit u).2.1 (eSplit v).2.1 := by
        conv_lhs => rw [hu, hv]
        simp only [hB_add_l, hB_add_r, hB_smul_l, hB_smul_r, hB_self, hBed, hB_comm d0 e,
          (eSplit u).2.2.2.1, (eSplit u).2.2.2.2, (eSplit v).2.2.2.1, (eSplit v).2.2.2.2,
          hB_comm (eSplit u).2.1 e, hB_comm (eSplit u).2.1 d0]
        ring
      rw [hBuv, hB' (eSplit u).2 (eSplit v).2]
      simp only [eFull, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
        Prod.map_apply, eProd, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, omegaY,
        Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      ring

lemma normal_form_reduction {n : ℕ} (f : (Fin n → F) → F)
    (hquad : ∀ p u v : Fin n → F,
      f (p + u + v) + f (p + u) + f (p + v) + f p = f (u + v) + f u + f v + f 0)
    (hunbal : Nat.card {x : Fin n → F // f x = 0} ≠ Nat.card {x : Fin n → F // f x = 1}) :
    let B := fun u v : Fin n → F => f (u + v) + f u + f v + f 0
    let m := (n - (Nat.card {u : Fin n → F // ∀ v : Fin n → F, B u v = 0}).log2) / 2
    ∃ (π : (Fin n → F) →ₗ[F] Y m) (σ : Y m →ₗ[F] (Fin n → F)) (t0 : Y m) (c0 : F),
      (∀ y : Y m, π (σ y) = y) ∧
      (∀ x : Fin n → F, f x = f0 (π x + t0) + c0) := by
  intro B m
  have hB_self : ∀ u, B u u = 0 := by
    intro u
    simp only [B, show u + u = 0 by ext j; exact f2_add_self _]
    have h1 := f2_add_self (f 0); have h2 := f2_add_self (f u)
    linear_combination h1 + h2
  have hB_comm : ∀ u v, B u v = B v u := by
    intro u v; simp only [B, add_comm u v]; ring
  have h2F : (2 : F) = 0 := rfl
  have hB_add_l : ∀ u v w, B (u + v) w = B u w + B v w := by
    intro u v w
    have h1 := hquad u v w
    simp only [B] at h1 ⊢
    have haux : ∀ a b c d e g h k : F, a + b + c + d = e + g + h + k →
        a + b + h + k = (c + d + h + k) + (e + g + h + k) := by decide
    exact haux _ _ _ _ _ _ _ _ h1
  have hB_add_r : ∀ u v w, B u (v + w) = B u v + B u w := fun u v w => by
    rw [hB_comm, hB_add_l, hB_comm v u, hB_comm w u]
  have hB_smul_l : ∀ (c : F) u v, B (c • u) v = c * B u v := by
    intro c u v
    rcases f2_cases c with rfl | rfl
    · simp only [zero_smul, zero_mul, B, zero_add]
      have h1 := f2_add_self (f v); have h2 := f2_add_self (f 0)
      linear_combination h1 + h2
    · simp
  let K : Submodule F (Fin n → F) :=
    { carrier := {u | ∀ v, B u v = 0}, add_mem' := fun hx hy v => by rw [hB_add_l, hx v, hy v, add_zero]
      zero_mem' := fun v => by simpa using hB_smul_l 0 0 v
      smul_mem' := fun c x hx v => by rw [hB_smul_l, hx v, mul_zero] }
  have hf_K : ∀ u ∈ K, f u = f 0 := by
    intro u hu
    by_contra hne
    have h1 : f u + f 0 = 1 := by
      rcases f2_cases (f u) with ha | ha <;> rcases f2_cases (f 0) with hb | hb <;>
        simp [ha, hb] at hne ⊢
    have hflip : ∀ x : Fin n → F, f (x + u) = f x + 1 := by
      intro x
      have hBu : B u x = 0 := hu x
      simp only [B, add_comm u x] at hBu
      linear_combination hBu + h1 - f x * h2F - f u * h2F - f 0 * h2F
    have heq : Nat.card {x : Fin n → F // f x = 0} = Nat.card {x : Fin n → F // f x = 1} := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1 + u, by rw [hflip, x.2, zero_add]⟩
          invFun := fun x => ⟨x.1 + u, by rw [hflip, x.2, f2_one_add_one]⟩
          left_inv := fun x => by ext j; simp [add_assoc, f2_add_self]
          right_inv := fun x => by ext j; simp [add_assoc, f2_add_self] }
    exact hunbal heq
  have hf_shift_K : ∀ x, ∀ u ∈ K, f (x + u) = f x := by
    intro x u hu
    have hBu : B u x = 0 := hu x
    have hfu : f u = f 0 := hf_K u hu
    simp only [B, add_comm u x, hfu] at hBu
    have h1 := f2_add_self (f x); have h2 := f2_add_self (f 0)
    linear_combination hBu - h1 - h2
  obtain ⟨W, hKW⟩ := Submodule.exists_isCompl K
  have hndW : ∀ u ∈ W, (∀ v ∈ W, B u v = 0) → u = 0 := by
    intro u hu h0
    have huK : u ∈ K := by
      intro v
      have hv : v ∈ K ⊔ W := by rw [hKW.sup_eq_top]; trivial
      rcases Submodule.mem_sup.1 hv with ⟨k, hk, w, hw, rfl⟩
      rw [hB_add_r, hB_comm u k, hk u, h0 w hw, add_zero]
    have hmem : u ∈ K ⊓ W := ⟨huK, hu⟩
    rw [hKW.inf_eq_bot] at hmem
    exact hmem
  obtain ⟨k, eW, hk_dim, hBW⟩ := symplectic_basis_subspace B hB_add_l hB_comm hB_self
    (Module.finrank F W) W rfl hndW
  have hcardK : Nat.card {u : Fin n → F // ∀ v : Fin n → F, B u v = 0} = 2 ^ Module.finrank F K := by
    change Nat.card K = 2 ^ Module.finrank F K
    letI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F), ZMod.card]
  have hlogK : (Nat.card {u : Fin n → F // ∀ v : Fin n → F, B u v = 0}).log2 =
      Module.finrank F K := by
    rw [hcardK, Nat.log2_two_pow]
  have hsum_dim : Module.finrank F K + Module.finrank F W = n := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K W
    rw [hKW.sup_eq_top, hKW.inf_eq_bot, finrank_top, finrank_bot, add_zero,
      Module.finrank_fin_fun] at h1
    exact h1.symm
  have hkm : k = m := by
    change k = (n - (Nat.card {u : Fin n → F // ∀ v : Fin n → F, B u v = 0}).log2) / 2
    rw [hlogK]
    omega
  subst hkm
  let projW : (Fin n → F) →ₗ[F] W := Submodule.linearProjOfIsCompl W K hKW.symm
  let π : (Fin n → F) →ₗ[F] Y m := eW.toLinearMap.comp projW
  let σ : Y m →ₗ[F] (Fin n → F) := W.subtype.comp eW.symm.toLinearMap
  have hπσ : ∀ y : Y m, π (σ y) = y := by
    intro y
    change eW (projW (eW.symm y).1) = y
    have hp : projW (eW.symm y).1 = eW.symm y :=
      Submodule.linearProjOfIsCompl_apply_left hKW.symm (eW.symm y)
    rw [hp, eW.apply_symm_apply]
  have hdiffK : ∀ x : Fin n → F, x + σ (π x) ∈ K := by
    intro x
    have hx : x ∈ K ⊔ W := by rw [hKW.sup_eq_top]; trivial
    rcases Submodule.mem_sup.1 hx with ⟨u, hu, w, hw, rfl⟩
    have hp : projW (u + w) = ⟨w, hw⟩ := by
      rw [map_add]
      have h1 : projW u = 0 := Submodule.linearProjOfIsCompl_apply_right hKW.symm ⟨u, hu⟩
      have h2 : projW w = ⟨w, hw⟩ := Submodule.linearProjOfIsCompl_apply_left hKW.symm ⟨w, hw⟩
      rw [h1, h2, zero_add]
    have hσπ : σ (π (u + w)) = w := by
      change (eW.symm (eW (projW (u + w)))).1 = w
      rw [hp, eW.symm_apply_apply]
    rw [hσπ]
    have heq : u + w + w = u := by ext j; simp [add_assoc, f2_add_self]
    rw [heq]; exact hu
  let Llin : Y m →ₗ[F] F :=
    { toFun := fun y => f (σ y) + f0 y + f 0
      map_add' := fun y1 y2 => by
        have h1 : B (σ y1) (σ y2) = omegaY y1 y2 := by
          have := hBW (eW.symm y1) (eW.symm y2)
          simpa [σ] using this
        have h2 : f (σ (y1 + y2)) = f (σ y1) + f (σ y2) + f 0 + omegaY y1 y2 := by
          rw [map_add]
          simp only [B] at h1
          have ha := f2_add_self (f (σ y1))
          have hb := f2_add_self (f (σ y2))
          have hc := f2_add_self (f 0)
          linear_combination h1 - ha - hb - hc
        rw [h2, f0_add]
        have haux : ∀ a b c d e g : F, (a + b + c + d) + (e + g + d) + c = (a + e + c) + (b + g + c) := by decide
        exact haux _ _ _ _ _ _
      map_smul' := fun c y => by
        rcases f2_cases c with rfl | rfl
        · simp [f0_zero, f2_add_self]
        · simp }
  obtain ⟨α, hα⟩ := dotY_lin_rep Llin
  let t0 : Y m := (α.2, α.1)
  let c0 : F := f 0 + f0 t0
  refine ⟨π, σ, t0, c0, hπσ, ?_⟩
  intro x
  have hfx : f x = f (σ (π x)) := by
    have h1 := hf_shift_K (σ (π x)) (x + σ (π x)) (hdiffK x)
    have h2 : σ (π x) + (x + σ (π x)) = x := by
      ext j; simp only [Pi.add_apply]
      have ha := f2_add_self (σ (π x) j); linear_combination ha
    rw [h2] at h1; exact h1
  rw [hfx]
  have hL := hα (π x)
  simp only [Llin, LinearMap.coe_mk, AddHom.coe_mk] at hL
  rw [f0_add, show omegaY (π x) t0 = dotY α (π x) from omegaY_swap_dotY (π x) α]
  simp only [c0]
  have h1 := f2_add_self (f0 (π x))
  have h2 := f2_add_self (f 0)
  have h3 := f2_add_self (f0 t0)
  linear_combination hL - h1 - h2 - h3

end PEqualNP.Outside.L_pcx_471

theorem PEqualNP.Outside.L_pcx_471 : (∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ f : X → F,
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p=B u v) →
    let m := (n-(Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
    Nat.card {x : X // f x=0} ≠ Nat.card {x : X // f x=1} →
    2 ≤ m →
    let M := (4^m-1)/3
    ∀ T : ℕ, 0 < T →
      ((∃ (A : Fin T → X →ₗ[F] (Fin 2 → F)) (out : Fin T → (Fin 2 → F) → F),
         ∀ x : X, (M+2^(m-1))*T ≤
           (2*M)*Nat.card {i : Fin T // out i (A i x) = f x}) ↔ 2*M ∣ T)) := by
  intro n F X f B hquad m hunbal hm M T hT
  obtain ⟨π, σ, t0, c0, hπσ, hfx⟩ := PEqualNP.Outside.L_pcx_471.normal_form_reduction f hquad hunbal
  constructor
  · rintro ⟨A, out, hpred⟩
    let A' : Fin T → PEqualNP.Outside.L_pcx_471.Y m →ₗ[F] (Fin 2 → F) := fun i => (A i).comp σ
    let out' : Fin T → (Fin 2 → F) → F := fun i w => out i (w + A i (σ t0)) + c0
    refine PEqualNP.Outside.L_pcx_471.lower_bound_normal hm A' out' ?_
    intro y
    have hx := hpred (σ (y + t0))
    have hfx_y : f (σ (y + t0)) = PEqualNP.Outside.L_pcx_471.f0 y + c0 := by
      rw [hfx, hπσ]
      have : y + t0 + t0 = y := by
        ext j
        · simp [add_assoc, PEqualNP.Outside.L_pcx_471.f2_add_self]
        · simp [add_assoc, PEqualNP.Outside.L_pcx_471.f2_add_self]
      rw [this]
    have hcard_eq : Nat.card {i : Fin T // out i (A i (σ (y + t0))) = f (σ (y + t0))} =
        Nat.card {i : Fin T // out' i (A' i y) = PEqualNP.Outside.L_pcx_471.f0 y} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
      rw [hfx_y]
      simp only [A', out', LinearMap.comp_apply, map_add]
      constructor
      · intro h; rw [h, add_assoc, PEqualNP.Outside.L_pcx_471.f2_add_self, add_zero]
      · intro h
        have := congr_arg (fun z => z + c0) h
        simpa [add_assoc, PEqualNP.Outside.L_pcx_471.f2_add_self] using this
    rw [hcard_eq] at hx
    exact hx
  · intro hdvd
    obtain ⟨A', out', hpred⟩ := PEqualNP.Outside.L_pcx_471.upper_bound_normal hm hT hdvd
    let A : Fin T → X →ₗ[F] (Fin 2 → F) := fun i => (A' i).comp π
    let out : Fin T → (Fin 2 → F) → F := fun i w => out' i (w + A' i t0) + c0
    refine ⟨A, out, ?_⟩
    intro x
    have hy := hpred (π x + t0)
    have hcard_eq : Nat.card {i : Fin T // out' i (A' i (π x + t0)) = PEqualNP.Outside.L_pcx_471.f0 (π x + t0)} =
        Nat.card {i : Fin T // out i (A i x) = f x} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
      rw [hfx x]
      simp only [A, out, LinearMap.comp_apply, map_add]
      constructor
      · intro h; rw [h]
      · intro h
        have := congr_arg (fun z => z + c0) h
        simpa [add_assoc, PEqualNP.Outside.L_pcx_471.f2_add_self] using this
    rw [hcard_eq] at hy
    exact hy
