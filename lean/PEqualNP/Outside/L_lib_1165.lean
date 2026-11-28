import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1165

open Finset

def Fits (a b : ℕ) {r n : ℕ} (x : Fin r → Fin n) (S : Finset (Fin r)) : Prop :=
  ∀ j, ((x j).val < a → j ∈ S) ∧ (a ≤ (x j).val → (x j).val < a + b → j ∉ S)

open Classical in
noncomputable def U (a b r n : ℕ) (M : Finset (Finset (Fin r))) : Finset (Fin r → Fin n) :=
  univ.filter (fun x => ∃ S ∈ M, Fits a b x S)

lemma mem_U {a b r n : ℕ} {M : Finset (Finset (Fin r))} {x : Fin r → Fin n} :
    x ∈ U a b r n M ↔ ∃ S ∈ M, Fits a b x S := by
  classical
  simp [U]

def Down {α : Type*} [DecidableEq α] (D : Finset (Finset α)) : Prop :=
  ∀ S ∈ D, ∀ j ∈ S, S.erase j ∈ D

def bw : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + bw ((n + 1) / 2)
decreasing_by omega

lemma bw_eq (n : ℕ) : bw n = n % 2 + bw (n / 2) := by
  cases n with
  | zero => simp [bw]
  | succ m => rw [bw]

def G (x : ℚ) (n : ℕ) : ℚ := ∑ i ∈ range n, x ^ bw i

lemma G_succ (x : ℚ) (n : ℕ) : G x (n + 1) = G x n + x ^ bw n := sum_range_succ _ _

lemma bw_even (n : ℕ) : bw (2 * n) = bw n := by
  rw [bw_eq, show (2 * n) % 2 = 0 by omega, show (2 * n) / 2 = n by omega, Nat.zero_add]

lemma bw_odd (n : ℕ) : bw (2 * n + 1) = 1 + bw n := by
  rw [bw_eq, show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega]

lemma G_two (x : ℚ) (n : ℕ) : G x (2 * n) = (1 + x) * G x n := by
  induction n with
  | zero => simp [G]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, G_succ, G_succ, G_succ, ih, bw_even, bw_odd,
      pow_add]
    ring

lemma G_odd (x : ℚ) (n : ℕ) : G x (2 * n + 1) = G x (n + 1) + x * G x n := by
  rw [G_succ, G_two, G_succ, bw_even]
  ring

lemma G_mono {x : ℚ} (hx : 0 ≤ x) (n : ℕ) : G x n ≤ G x (n + 1) := by
  rw [G_succ]
  linarith [pow_nonneg hx (bw n)]

lemma key_ineq (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ N a b : ℕ, a + b = N → b ≤ a → G x (a + b) ≤ G x a + x * G x b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b hN hab
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [G]
    have H : ∀ p q : ℕ, q ≤ p → p + q < N → G x (p + q) ≤ G x p + x * G x q :=
      fun p q h1 h2 => ih (p + q) h2 p q rfl h1
    rcases Nat.even_or_odd' a with ⟨p, rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' b with ⟨q, rfl | rfl⟩
    · rw [show 2 * p + 2 * q = 2 * (p + q) by ring, G_two, G_two, G_two]
      have := mul_le_mul_of_nonneg_left (H p q (by omega) (by omega))
        (show 0 ≤ 1 + x by linarith)
      linarith
    · rw [show 2 * p + (2 * q + 1) = 2 * (p + q) + 1 by ring, G_odd, G_two, G_odd]
      have h1 := H p (q + 1) (by omega) (by omega)
      rw [show p + (q + 1) = p + q + 1 by ring] at h1
      have h2 := mul_le_mul_of_nonneg_left (H p q (by omega) (by omega)) hx0
      linarith
    · rw [show 2 * p + 1 + 2 * q = 2 * (p + q) + 1 by ring, G_odd, G_odd, G_two]
      have h1 := H (p + 1) q (by omega) (by omega)
      rw [show p + 1 + q = p + q + 1 by ring] at h1
      have h2 := mul_le_mul_of_nonneg_left (H p q (by omega) (by omega)) hx0
      linarith
    · rw [show 2 * p + 1 + (2 * q + 1) = 2 * (p + q + 1) by ring, G_two, G_odd, G_odd]
      rcases eq_or_lt_of_le (show q ≤ p by omega) with h | hlt
      · rw [show p + q + 1 = 2 * p + 1 by omega, G_odd, h]
        linarith
      · have h1 := H (p + 1) q (by omega) (by omega)
        rw [show p + 1 + q = p + q + 1 by ring] at h1
        have h2 := H p (q + 1) (by omega) (by omega)
        rw [show p + (q + 1) = p + q + 1 by ring] at h2
        have h3 := mul_le_mul_of_nonneg_left h2 hx0
        have h4 := mul_nonneg (mul_nonneg hx0 (sub_nonneg.2 hx1))
          (sub_nonneg.2 (G_mono hx0 q))
        linarith

lemma down_sub {α : Type*} [DecidableEq α] {D : Finset (Finset α)} (hD : Down D) :
    ∀ S ∈ D, ∀ T ⊆ S, T ∈ D := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hS T hT
    by_cases h : T = S
    · rwa [h]
    obtain ⟨j, hjS, hjT⟩ := Finset.exists_of_ssubset (ssubset_of_subset_of_ne hT h)
    exact ih (S.erase j) (erase_ssubset hjS) (hD S hS j hjS) T (subset_erase.2 ⟨hT, hjT⟩)

lemma down_bound (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {α : Type*} [DecidableEq α] :
    ∀ D : Finset (Finset α), Down D → G x D.card ≤ ∑ S ∈ D, x ^ S.card := by
  intro D
  induction D using Finset.strongInduction with
  | _ D ih =>
    intro hD
    by_cases h : ∃ S ∈ D, S.Nonempty
    · obtain ⟨S, hS, j, hj⟩ := h
      have hinj : Set.InjOn (fun T : Finset α => T.erase j) (D.filter (fun T => j ∈ T)) := by
        intro A hA B hB h
        have hA' : j ∈ A := (mem_filter.1 hA).2
        have hB' : j ∈ B := (mem_filter.1 hB).2
        rw [← insert_erase hA', ← insert_erase hB']
        exact congrArg (insert j) h
      have hsub : (D.filter (fun T => j ∈ T)).image (fun T => T.erase j) ⊆
          D.filter (fun T => j ∉ T) := by
        intro T hT
        obtain ⟨A, hA, rfl⟩ := mem_image.1 hT
        obtain ⟨hAD, hjA⟩ := mem_filter.1 hA
        exact mem_filter.2 ⟨hD A hAD j hjA, by simp⟩
      have hlt : D.filter (fun T => j ∉ T) ⊂ D :=
        filter_ssubset.2 ⟨S, hS, not_not.2 hj⟩
      have hD0 : Down (D.filter (fun T => j ∉ T)) := by
        intro A hA i hi
        obtain ⟨hAD, hjA⟩ := mem_filter.1 hA
        exact mem_filter.2 ⟨hD A hAD i hi, fun h => hjA (mem_of_mem_erase h)⟩
      have hD1 : Down ((D.filter (fun T => j ∈ T)).image (fun T => T.erase j)) := by
        intro T hT i hi
        obtain ⟨A, hA, rfl⟩ := mem_image.1 hT
        obtain ⟨hAD, hjA⟩ := mem_filter.1 hA
        obtain ⟨hne, hiA⟩ := mem_erase.1 hi
        refine mem_image.2 ⟨A.erase i,
          mem_filter.2 ⟨hD A hAD i hiA, mem_erase.2 ⟨Ne.symm hne, hjA⟩⟩, ?_⟩
        exact erase_right_comm
      have hlt1 := Finset.ssubset_of_subset_of_ssubset hsub hlt
      have hc : D.card = (D.filter (fun T => j ∉ T)).card +
          ((D.filter (fun T => j ∈ T)).image (fun T => T.erase j)).card := by
        rw [card_image_of_injOn hinj, add_comm, card_eq_sum_ones, card_eq_sum_ones,
          card_eq_sum_ones]
        exact (sum_filter_add_sum_filter_not D (fun T => j ∈ T) _).symm
      have hs : ∑ T ∈ D, x ^ T.card = (∑ T ∈ D.filter (fun T => j ∉ T), x ^ T.card) +
          x * ∑ T ∈ (D.filter (fun T => j ∈ T)).image (fun T => T.erase j), x ^ T.card := by
        rw [← sum_filter_add_sum_filter_not D (fun T => j ∈ T), add_comm, sum_image hinj,
          mul_sum]
        congr 1
        apply sum_congr rfl
        intro A hA
        have hjA : j ∈ A := (mem_filter.1 hA).2
        rw [← pow_succ', card_erase_add_one hjA]
      calc G x D.card = G x ((D.filter (fun T => j ∉ T)).card +
              ((D.filter (fun T => j ∈ T)).image (fun T => T.erase j)).card) := by rw [← hc]
        _ ≤ _ := key_ineq x hx0 hx1 _ _ _ rfl (card_le_card hsub)
        _ ≤ _ := by
          rw [hs]
          exact add_le_add (ih _ hlt hD0) (mul_le_mul_of_nonneg_left (ih _ hlt1 hD1) hx0)
    · have : D ⊆ {∅} := by
        intro S hS
        rw [mem_singleton]
        by_contra hne
        exact h ⟨S, hS, nonempty_iff_ne_empty.2 hne⟩
      rcases subset_singleton_iff.1 this with rfl | rfl
      · simp [G]
      · simp [G, bw]

def sh {r : ℕ} (M : Finset (Finset (Fin r))) (j : Fin r) (S : Finset (Fin r)) : Finset (Fin r) :=
  if j ∈ S ∧ S.erase j ∉ M then S.erase j else S

lemma step (a b c r : ℕ) (hb : b ≤ a) (M : Finset (Finset (Fin r))) (j : Fin r) :
    (U a b r (a + b + c) (M.image (sh M j))).card ≤ (U a b r (a + b + c) M).card := by
  classical
  have hmain : (U a b r (a + b + c) (M.image (sh M j)) \ U a b r (a + b + c) M).card ≤
      (U a b r (a + b + c) M \ U a b r (a + b + c) (M.image (sh M j))).card := by
    have hkey : ∀ x ∈ U a b r (a + b + c) (M.image (sh M j)) \ U a b r (a + b + c) M,
        (a ≤ (x j).val ∧ (x j).val < a + b) ∧
          ∃ T ∈ M, j ∈ T ∧ Fits a b x (T.erase j) := by
      intro x hx
      obtain ⟨h1, h2⟩ := mem_sdiff.1 hx
      obtain ⟨S', hS', hf⟩ := mem_U.1 h1
      obtain ⟨T, hT, rfl⟩ := mem_image.1 hS'
      by_cases hc : j ∈ T ∧ T.erase j ∉ M
      · rw [sh, if_pos hc] at hf
        refine ⟨?_, T, hT, hc.1, hf⟩
        by_contra hr
        apply h2
        refine mem_U.2 ⟨T, hT, fun i => ?_⟩
        by_cases hi : i = j
        · rw [hi]
          exact ⟨fun _ => hc.1, fun h3 h4 => absurd ⟨h3, h4⟩ hr⟩
        · have := hf i
          simpa [mem_erase, hi] using this
      · rw [sh, if_neg hc] at hf
        exact absurd (mem_U.2 ⟨T, hT, hf⟩) h2
    refine card_le_card_of_injOn (fun x => Function.update x j
      ⟨(x j).val - a, lt_of_le_of_lt (Nat.sub_le _ _) (x j).isLt⟩) ?_ ?_
    · intro x hx
      replace hx : x ∈ U a b r (a + b + c) (M.image (sh M j)) \ U a b r (a + b + c) M := hx
      obtain ⟨⟨ha1, ha2⟩, T, hT, hjT, hf⟩ := hkey x hx
      set y : Fin r → Fin (a + b + c) := Function.update x j
        ⟨(x j).val - a, lt_of_le_of_lt (Nat.sub_le _ _) (x j).isLt⟩ with hy
      have hyj : (y j).val = (x j).val - a := by simp [hy]
      have hyi : ∀ i, i ≠ j → y i = x i := fun i hi => by simp [hy, Function.update, hi]
      show y ∈ U a b r (a + b + c) M \ U a b r (a + b + c) (M.image (sh M j))
      refine mem_sdiff.2 ⟨mem_U.2 ⟨T, hT, fun i => ?_⟩, fun hmem => ?_⟩
      · by_cases hi : i = j
        · rw [hi, hyj]
          exact ⟨fun _ => hjT, fun h3 _ => by omega⟩
        · rw [hyi i hi]
          have := hf i
          simpa [mem_erase, hi] using this
      · obtain ⟨S', hS', hg⟩ := mem_U.1 hmem
        obtain ⟨V, hV, rfl⟩ := mem_image.1 hS'
        have hjm : j ∈ sh M j V := (hg j).1 (by rw [hyj]; omega)
        by_cases hc : j ∈ V ∧ V.erase j ∉ M
        · rw [sh, if_pos hc] at hjm
          simp at hjm
        · rw [sh, if_neg hc] at hjm hg
          have hVe : V.erase j ∈ M := by
            by_contra h
            exact hc ⟨hjm, h⟩
          apply (mem_sdiff.1 hx).2
          refine mem_U.2 ⟨_, hVe, fun i => ?_⟩
          by_cases hi : i = j
          · rw [hi]
            exact ⟨fun h => absurd h (by omega), fun _ _ => by simp⟩
          · have := hg i
            rw [hyi i hi] at this
            simpa [mem_erase, hi] using this
    · intro x hx z hz h
      have h1 := (hkey x hx).1.1
      have h2 := (hkey z hz).1.1
      funext i
      by_cases hi : i = j
      · rw [hi]
        apply Fin.ext
        have := congrArg (fun w : Fin r → Fin (a + b + c) => (w j).val) h
        simp at this
        omega
      · have := congrFun h i
        simpa [Function.update, hi] using this
  have e1 := card_sdiff_add_card_inter (U a b r (a + b + c) (M.image (sh M j)))
    (U a b r (a + b + c) M)
  have e2 := card_sdiff_add_card_inter (U a b r (a + b + c) M)
    (U a b r (a + b + c) (M.image (sh M j)))
  rw [inter_comm] at e2
  omega

lemma compress (a b c r : ℕ) (hb : b ≤ a) (M : Finset (Finset (Fin r))) :
    ∃ D : Finset (Finset (Fin r)), D.card = M.card ∧ Down D ∧
      (U a b r (a + b + c) D).card ≤ (U a b r (a + b + c) M).card := by
  induction h : (∑ S ∈ M, S.card) using Nat.strong_induction_on generalizing M with
  | _ w ih =>
    by_cases hM : Down M
    · exact ⟨M, rfl, hM, le_rfl⟩
    unfold Down at hM
    push_neg at hM
    obtain ⟨T, hT, j, hj, hne⟩ := hM
    have hinj : Set.InjOn (sh M j) M := by
      intro A hA B hB h
      replace hA : A ∈ M := hA
      replace hB : B ∈ M := hB
      unfold sh at h
      split_ifs at h with h1 h2 h2
      · rw [← insert_erase h1.1, ← insert_erase h2.1, h]
      · exact absurd (show A.erase j ∈ M by rw [h]; exact hB) h1.2
      · exact absurd (show B.erase j ∈ M by rw [← h]; exact hA) h2.2
      · exact h
    have hlt : ∑ S ∈ M.image (sh M j), S.card < w := by
      rw [← h, sum_image hinj]
      apply sum_lt_sum
      · intro S _
        unfold sh
        split_ifs
        · exact card_erase_le
        · exact le_rfl
      · refine ⟨T, hT, ?_⟩
        rw [sh, if_pos ⟨hj, hne⟩]
        exact card_erase_lt_of_mem hj
    obtain ⟨D, h1, h2, h3⟩ := ih _ hlt (M.image (sh M j)) rfl
    exact ⟨D, h1.trans (card_image_of_injOn hinj), h2, h3.trans (step a b c r hb M j)⟩

lemma count (a b c r : ℕ) (D : Finset (Finset (Fin r))) (hD : Down D) :
    (U a b r (a + b + c) D).card = ∑ S ∈ D, a ^ S.card * (b + c) ^ (r - S.card) := by
  classical
  let P := fun x : Fin r → Fin (a + b + c) => univ.filter (fun j => (x j).val < a)
  have h1 : U a b r (a + b + c) D = univ.filter (fun x => P x ∈ D) := by
    ext x
    rw [mem_U, mem_filter]
    simp only [mem_univ, true_and]
    constructor
    · rintro ⟨S, hS, hf⟩
      exact down_sub hD S hS _ (fun j hj => (hf j).1 (mem_filter.1 hj).2)
    · intro h
      refine ⟨_, h, fun j => ⟨fun hj => mem_filter.2 ⟨mem_univ _, hj⟩, fun h2 _ h3 => ?_⟩⟩
      have := (mem_filter.1 h3).2
      omega
  rw [h1, card_eq_sum_card_fiberwise (s := univ.filter (fun x => P x ∈ D)) (f := P) (t := D)
    (fun x hx => (mem_filter.1 hx).2)]
  apply sum_congr rfl
  intro S hS
  have h2 : (univ.filter (fun x => P x ∈ D)).filter (fun x => P x = S) =
      Fintype.piFinset (fun j => univ.filter
        (fun v : Fin (a + b + c) => (v.val < a ↔ j ∈ S))) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨_, h⟩ j
      rw [← h]
      simp [P]
    · intro h
      have e : P x = S := by
        ext j
        simp only [P, mem_filter, mem_univ, true_and]
        exact h j
      exact ⟨e ▸ hS, e⟩
  rw [h2, Fintype.card_piFinset]
  have h3 : ∀ j : Fin r, (univ.filter
      (fun v : Fin (a + b + c) => (v.val < a ↔ j ∈ S))).card = if j ∈ S then a else b + c := by
    intro j
    have hlt : (univ.filter (fun v : Fin (a + b + c) => v.val < a)).card = a := by
      rw [Fin.card_filter_val_lt]
      omega
    split_ifs with h
    · simp only [h, iff_true]
      exact hlt
    · simp only [h, iff_false]
      have e : (univ.filter (fun v : Fin (a + b + c) => v.val < a)).card +
          (univ.filter (fun v : Fin (a + b + c) => ¬ v.val < a)).card = a + b + c := by
        rw [card_eq_sum_ones, card_eq_sum_ones, sum_filter_add_sum_filter_not,
          ← card_eq_sum_ones, card_univ, Fintype.card_fin]
      omega
  rw [prod_congr rfl (fun j _ => h3 j), prod_ite, prod_const, prod_const,
    show univ.filter (fun j => j ∈ S) = S by ext; simp,
    show univ.filter (fun j => j ∉ S) = Sᶜ by ext; simp, card_compl, Fintype.card_fin]

def idx {r : ℕ} (S : Finset (Fin r)) : ℕ := ∑ j ∈ S, 2 ^ j.val

lemma idx_eq {r : ℕ} (S : Finset (Fin r)) :
    idx S = (finFunctionFinEquiv (fun j => if j ∈ S then (1 : Fin 2) else 0)).val := by
  have : ∀ i : Fin r, ((if i ∈ S then (1 : Fin 2) else 0).val) * 2 ^ i.val
      = if i ∈ S then 2 ^ i.val else 0 := by
    intro i
    split_ifs <;> simp
  rw [finFunctionFinEquiv_apply, sum_congr rfl (fun i _ => this i), sum_ite_mem, univ_inter]
  rfl

lemma idx_lt {r : ℕ} (S : Finset (Fin r)) : idx S < 2 ^ r := by
  rw [idx_eq]
  exact Fin.isLt _

lemma idx_inj {r : ℕ} : Function.Injective (idx (r := r)) := by
  intro S T h
  rw [idx_eq, idx_eq] at h
  have h' := finFunctionFinEquiv.injective (Fin.ext h)
  ext j
  have := congrFun h' j
  by_cases h1 : j ∈ S <;> by_cases h2 : j ∈ T <;> simp_all

lemma bw_sum : ∀ (r : ℕ) (f : Fin r → Fin 2),
    bw (∑ i, (f i).val * 2 ^ i.val) = ∑ i, (f i).val := by
  intro r
  induction r with
  | zero => intro f; simp [bw]
  | succ r ih =>
    intro f
    have e : ∑ i : Fin r, (f i.succ).val * 2 ^ (i.succ).val
        = 2 * ∑ i : Fin r, (f i.succ).val * 2 ^ i.val := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [Fin.val_succ, pow_succ]
      ring
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i => (f i).val), e]
    simp only [Fin.val_zero, pow_zero, mul_one]
    have := (f 0).isLt
    rw [bw_eq, show ((f 0).val + 2 * ∑ i : Fin r, (f i.succ).val * 2 ^ i.val) % 2 = (f 0).val
        by omega,
      show ((f 0).val + 2 * ∑ i : Fin r, (f i.succ).val * 2 ^ i.val) / 2
        = ∑ i : Fin r, (f i.succ).val * 2 ^ i.val by omega, ih (fun i => f i.succ)]

lemma bw_idx {r : ℕ} (S : Finset (Fin r)) : bw (idx S) = S.card := by
  have : ∀ i : Fin r, (if i ∈ S then (1 : Fin 2) else 0).val = if i ∈ S then 1 else 0 := by
    intro i
    split_ifs <;> simp
  rw [idx_eq, finFunctionFinEquiv_apply, bw_sum, sum_congr rfl (fun i _ => this i),
    sum_ite_mem, univ_inter, card_eq_sum_ones]

lemma initial {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (hf : Function.Injective f)
    (hlt : ∀ s, f s < Fintype.card α) (k : ℕ) (hk : k ≤ Fintype.card α) :
    (univ.filter (fun s => f s < k)).image f = range k := by
  have himg : univ.image f = range (Fintype.card α) :=
    eq_of_subset_of_card_le (by
      intro n hn
      obtain ⟨s, _, rfl⟩ := mem_image.1 hn
      exact mem_range.2 (hlt s))
      (by rw [card_range, card_image_of_injective _ hf, card_univ])
  ext n
  constructor
  · intro hn
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hn
    exact mem_range.2 (mem_filter.1 hs).2
  · intro hn
    have hnk := mem_range.1 hn
    have : n ∈ univ.image f := by
      rw [himg]
      exact mem_range.2 (lt_of_lt_of_le hnk hk)
    obtain ⟨s, _, rfl⟩ := mem_image.1 this
    exact mem_image.2 ⟨s, mem_filter.2 ⟨mem_univ _, hnk⟩, rfl⟩

lemma exch {α : Type*} (A B : Finset α) (f : α → ℕ) (h : A.card = B.card)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, f x ≤ f y) : ∑ x ∈ A, f x ≤ ∑ y ∈ B, f y := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  obtain ⟨m, hm, hmax⟩ := exists_max_image A f hA
  calc ∑ x ∈ A, f x ≤ A.card • f m := sum_le_card_nsmul A f _ hmax
    _ = B.card • f m := by rw [h]
    _ ≤ ∑ y ∈ B, f y := card_nsmul_le_sum B f _ (fun y hy => hAB m hm y hy)

def kk {r : ℕ} (S : Finset (Fin r)) : ℕ := S.card * 2 ^ r + idx S

def rk {r : ℕ} (S : Finset (Fin r)) : ℕ :=
  (univ.filter (fun V : Finset (Fin r) => kk V < kk S)).card

lemma lex_iff {r : ℕ} (V S : Finset (Fin r)) :
    (V.card < S.card ∨ (V.card = S.card ∧ idx V < idx S)) ↔ kk V < kk S := by
  have hV := idx_lt V
  have hS := idx_lt S
  unfold kk
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · have := Nat.mul_le_mul_right (2 ^ r) (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at this
      omega
    · rw [h1]
      omega
  · intro h
    rcases lt_trichotomy V.card S.card with h1 | h1 | h1
    · exact Or.inl h1
    · rw [h1] at h
      exact Or.inr ⟨h1, by omega⟩
    · have := Nat.mul_le_mul_right (2 ^ r) (Nat.succ_le_of_lt h1)
      rw [Nat.succ_mul] at this
      omega

lemma kk_inj {r : ℕ} : Function.Injective (kk (r := r)) := by
  intro S T h
  apply idx_inj
  have := congrArg (· % 2 ^ r) h
  simpa [kk, Nat.mul_add_mod', Nat.mod_eq_of_lt (idx_lt _)] using this

lemma rk_mono {r : ℕ} {S T : Finset (Fin r)} (h : kk S < kk T) : rk S < rk T := by
  unfold rk
  apply card_lt_card
  have hsub : univ.filter (fun V : Finset (Fin r) => kk V < kk S)
      ⊆ univ.filter (fun V : Finset (Fin r) => kk V < kk T) := by
    intro V hV
    exact mem_filter.2 ⟨mem_univ _, lt_trans (mem_filter.1 hV).2 h⟩
  exact (ssubset_iff_of_subset hsub).2
    ⟨S, mem_filter.2 ⟨mem_univ _, h⟩, fun h' => lt_irrefl _ (mem_filter.1 h').2⟩

lemma rk_inj {r : ℕ} : Function.Injective (rk (r := r)) := by
  intro S T h
  rcases lt_trichotomy (kk S) (kk T) with h1 | h1 | h1
  · exact absurd (rk_mono h1) (by omega)
  · exact kk_inj h1
  · exact absurd (rk_mono h1) (by omega)

lemma rk_lt {r : ℕ} (S : Finset (Fin r)) : rk S < Fintype.card (Finset (Fin r)) := by
  rw [← card_univ]
  unfold rk
  exact card_lt_card (filter_ssubset.2 ⟨S, mem_univ _, lt_irrefl (kk S)⟩)

end PEqualNP.Outside.L_lib_1165

theorem PEqualNP.Outside.L_lib_1165 : (∀ (r k a b c : Nat), b ≤ a → k ≤ 2 ^ r →
  let Kind := Finset (Fin r)
  let kinds := (Finset.univ : Finset Kind)
  let positions := (Finset.univ : Finset (Fin r))
  let omega := (Finset.univ : Finset (Fin r → Fin (a + b + c)))
  let sees := fun (M : Finset Kind) => (omega.filter (fun x =>
    M.toList.any (fun S => positions.toList.all (fun j =>
      if (x j).val < a then decide (j ∈ S) else
      if (x j).val < a + b then decide (j ∉ S) else true)))).card
  let index := fun (S : Kind) => S.sum (fun j => 2 ^ j.val)
  let weightOrder := fun (S : Kind) => (kinds.filter (fun V =>
    V.card < S.card ∨ (V.card = S.card ∧ index V < index S))).card
  let best := kinds.filter (fun S => (if a ≤ b + c then index S else weightOrder S) < k)
  best.card = k ∧ sees best =
    best.sum (fun S => a ^ S.card * (b + c) ^ (r - S.card)) ∧
    ∀ M : Finset Kind, M.card = k → sees best ≤ sees M) := by
  intro r k a b c hb hk Kind kinds positions omega sees index weightOrder best
  open PEqualNP.Outside.L_lib_1165 Finset in
  have hsees : ∀ M : Finset (Finset (Fin r)), sees M = (U a b r (a + b + c) M).card := by
    intro M
    show (omega.filter _).card = _
    congr 1
    ext x
    rw [mem_filter, mem_U, List.any_eq_true]
    simp only [omega, mem_univ, true_and, mem_toList]
    apply exists_congr
    intro S
    apply and_congr_right'
    rw [List.all_eq_true]
    simp only [positions, mem_toList, mem_univ, true_implies, Fits]
    apply forall_congr'
    intro j
    split_ifs with h1 h2
    · simp only [decide_eq_true_eq]
      exact ⟨fun h => ⟨fun _ => h, fun h3 _ => by omega⟩, fun h => h.1 h1⟩
    · simp only [decide_eq_true_eq]
      exact ⟨fun h => ⟨fun h3 => absurd h3 h1, fun _ _ => h⟩,
        fun h => h.2 (by omega) h2⟩
    · simp only [true_iff]
      exact ⟨fun h3 => absurd h3 h1, fun _ h4 => absurd h4 h2⟩
  have hN : Fintype.card (Finset (Fin r)) = 2 ^ r := by simp
  by_cases h : a ≤ b + c
  · have hbest : best = univ.filter (fun S : Finset (Fin r) => idx S < k) :=
      filter_congr (fun S _ => by rw [if_pos h]; exact Iff.rfl)
    have himg := initial idx (idx_inj (r := r)) (fun S => by rw [hN]; exact idx_lt S) k
      (by rw [hN]; exact hk)
    have hcard : (univ.filter (fun S : Finset (Fin r) => idx S < k)).card = k := by
      rw [← card_image_of_injective _ idx_inj, himg, card_range]
    have hdown : Down (univ.filter (fun S : Finset (Fin r) => idx S < k)) := by
      intro S hS j hj
      exact mem_filter.2 ⟨mem_univ _,
        lt_of_le_of_lt (sum_le_sum_of_subset (erase_subset _ _)) (mem_filter.1 hS).2⟩
    have hs := count a b c r _ hdown
    rw [hbest]
    refine ⟨hcard, (hsees _).trans hs, fun M hM => ?_⟩
    obtain ⟨D, hD1, hD2, hD3⟩ := compress a b c r hb M
    rw [hsees, hsees]
    refine le_trans ?_ hD3
    rw [hs, count a b c r D hD2]
    have hDk : D.card = k := by
      rw [hD1]
      exact hM
    rcases Nat.eq_zero_or_pos (b + c) with h0 | h0
    · have ha : a = 0 := by omega
      have e : ∀ S : Finset (Fin r), a ^ S.card * (b + c) ^ (r - S.card) = 0 ^ r := by
        intro S
        rw [ha, h0, ← pow_add]
        congr 1
        have := card_le_univ S
        rw [Fintype.card_fin] at this
        omega
      rw [sum_congr rfl (fun S _ => e S), sum_congr rfl (fun S _ => e S), sum_const, sum_const,
        hcard, hDk]
    · have hβ : (0 : ℚ) < (b : ℚ) + c := by exact_mod_cast h0
      set x : ℚ := (a : ℚ) / ((b : ℚ) + c) with hx
      have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hβ.le
      have hx1 : x ≤ 1 := (div_le_one hβ).2 (by exact_mod_cast h)
      have e : ∀ S : Finset (Fin r),
          ((a ^ S.card * (b + c) ^ (r - S.card) : ℕ) : ℚ) = ((b : ℚ) + c) ^ r * x ^ S.card := by
        intro S
        have hle : S.card ≤ r := by
          have := card_le_univ S
          rwa [Fintype.card_fin] at this
        have hp : ((b : ℚ) + c) ^ r
            = ((b : ℚ) + c) ^ (r - S.card) * ((b : ℚ) + c) ^ S.card := by
          rw [← pow_add]
          congr 1
          omega
        have hne : ((b : ℚ) + c) ^ S.card ≠ 0 := pow_ne_zero _ hβ.ne'
        rw [hp, hx, div_pow]
        push_cast
        field_simp
      apply (Nat.cast_le (α := ℚ)).1
      rw [Nat.cast_sum, Nat.cast_sum, sum_congr rfl (fun S _ => e S),
        sum_congr rfl (fun S _ => e S), ← mul_sum, ← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hβ.le _)
      have e1 : ∑ S ∈ univ.filter (fun S : Finset (Fin r) => idx S < k), x ^ S.card = G x k := by
        unfold G
        rw [← himg, sum_image (idx_inj.injOn)]
        exact sum_congr rfl (fun S _ => by rw [bw_idx])
      rw [e1, ← hDk]
      exact down_bound x hx0 hx1 D hD2
  · have h' : b + c ≤ a := by omega
    have hbest : best = univ.filter (fun S : Finset (Fin r) => rk S < k) :=
      filter_congr (fun S _ => by
        rw [if_neg h]
        show (univ.filter (fun V : Finset (Fin r) =>
          V.card < S.card ∨ (V.card = S.card ∧ idx V < idx S))).card < k ↔ rk S < k
        unfold rk
        rw [filter_congr (fun V _ => lex_iff V S)])
    have himg := initial rk (rk_inj (r := r)) rk_lt k (by rw [hN]; exact hk)
    have hcard : (univ.filter (fun S : Finset (Fin r) => rk S < k)).card = k := by
      rw [← card_image_of_injective _ rk_inj, himg, card_range]
    have hdown : Down (univ.filter (fun S : Finset (Fin r) => rk S < k)) := by
      intro S hS j hj
      exact mem_filter.2 ⟨mem_univ _, lt_trans
        (rk_mono ((lex_iff _ _).1 (Or.inl (card_erase_lt_of_mem hj)))) (mem_filter.1 hS).2⟩
    have hs := count a b c r _ hdown
    rw [hbest]
    refine ⟨hcard, (hsees _).trans hs, fun M hM => ?_⟩
    obtain ⟨D, hD1, hD2, hD3⟩ := compress a b c r hb M
    rw [hsees, hsees]
    refine le_trans ?_ hD3
    rw [hs, count a b c r D hD2]
    have hDk : D.card = k := by
      rw [hD1]
      exact hM
    set B := univ.filter (fun S : Finset (Fin r) => rk S < k) with hB
    rw [← sum_inter_add_sum_sdiff B D, ← sum_inter_add_sum_sdiff D B, inter_comm D B]
    apply Nat.add_le_add_left
    apply exch
    · exact card_sdiff_comm (by rw [hcard, hDk])
    · intro S hS T hT
      have hS' : rk S < k := (mem_filter.1 (mem_sdiff.1 hS).1).2
      have hT' : ¬ rk T < k := fun hh =>
        (mem_sdiff.1 hT).2 (mem_filter.2 ⟨mem_univ _, hh⟩)
      have hk' : kk S < kk T := by
        rcases lt_trichotomy (kk S) (kk T) with h1 | h1 | h1
        · exact h1
        · rw [kk_inj h1] at hS'
          exact absurd hS' hT'
        · have := rk_mono h1
          omega
      have hle : S.card ≤ T.card := by
        rcases (lex_iff S T).2 hk' with h1 | h1
        · exact h1.le
        · exact h1.1.le
      have hTr : T.card ≤ r := by
        have := card_le_univ T
        rwa [Fintype.card_fin] at this
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, show r - S.card = d + (r - (S.card + d)) by omega, pow_add, pow_add, ← mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h' d))
