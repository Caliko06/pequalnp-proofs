import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45401

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def fullMask : Nat := 0xffffffffffffffff

abbrev Masked (mask w : Nat) : Prop := w &&& mask = w

def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c

theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl

theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h

theorem masked_zero (mask : Nat) : Masked mask 0 := by
  unfold Masked; simp

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

theorem masked_xor {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (a ^^^ b) := by
  unfold Masked at ha hb ⊢
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_xor] at ea eb ⊢
  cases hm : mask.testBit i <;> simp_all

theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all

theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all

def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)

theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]

theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]

theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]

theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩

theorem canon_masked (mask w : Nat) : Masked mask (canon mask w) := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0]; exact masked_zero mask
  · rw [h1]; exact masked_land_right mask w
  · rw [h2]; exact masked_xor (masked_self mask) (masked_land_right mask w)

theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]

theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w

theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]

theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne

theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]

def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))

theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _

theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩

theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp

theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]

theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h

theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1

def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank

def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b

def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs

def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length

theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)

theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩

theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)

theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2

def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S

theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _

theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega

inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S

theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0

theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega

theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1

theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩

theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))

def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w

theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl

def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k

theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]

def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws

theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢

theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha

theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq

def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)

theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]

theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega

theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit

def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws

theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]

def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w

theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]

def recipeGateBin (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  availB bank ac && availB bank bc &&
    (Nat.beq vc (binOp cut 0 ac bc) || Nat.beq vc (binOp cut 1 ac bc) ||
     Nat.beq vc (binOp cut 2 ac bc) || Nat.beq vc (binOp cut 3 ac bc))

theorem recipeGateBin_spec {cut : Nat} {bank : List Nat} {vc ac bc : Nat}
    (h : recipeGateBin cut bank vc ac bc = true) : GateBin cut bank vc := by
  unfold recipeGateBin at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, availB_spec] at h
  obtain ⟨⟨ha, hb⟩, ((h0 | h1) | h2) | h3⟩ := h
  · exact ⟨ac, bc, 0, by omega, ha, hb, h0⟩
  · exact ⟨ac, bc, 1, by omega, ha, hb, h1⟩
  · exact ⟨ac, bc, 2, by omega, ha, hb, h2⟩
  · exact ⟨ac, bc, 3, by omega, ha, hb, h3⟩

def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l

def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws

def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed

def replayRec (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canon cut w
      if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
        v :: next (v :: bank)
      else next bank) hist bank

theorem replayRec_builds (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    BuildsBin cut bank (replayRec cut needed hist bank) := by
  induction hist generalizing bank with
  | nil => trivial
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    change BuildsBin cut bank
      (if needed.contains (canon cut w) && !(availB bank (canon cut w)) &&
          recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) then
        canon cut w :: replayRec cut needed hist (canon cut w :: bank)
      else replayRec cut needed hist bank)
    split
    · rename_i hyes
      exact ⟨recipeGateBin_spec (Bool.and_eq_true_iff.mp hyes).2, ih _⟩
    · exact ih _

def boundCloses (target : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, goal) := bound
  let (fuel, ws, hist) := state
  Nat.beq (canon cut target) goal && !(Nat.beq goal 0) &&
    forceW (fuel - flatCount cut ws) (fun rem =>
      if Nat.blt rem lower then
        forceWs (recipeStart cut stock ws) (fun start =>
          if Nat.blt (start.length + rem) lower then
            forceWs (recipeClose cut stock hist start) (fun needed =>
              if Nat.blt (needed.length + rem) lower then
                forceWs (replayRec cut needed hist.reverse stock) (fun replay =>
                  Nat.blt (replay.length + rem) lower &&
                    ws.all (fun w => availB (replay ++ stock) (canon cut w)))
              else false)
          else false)
      else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => boundCloses target state b || rest) bounds

def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1

theorem boundCloses_sound {mask goal : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    boundCloses goal state bound = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hlow sub nd hk hlive
  apply Bool.eq_false_iff.mpr
  intro hc
  unfold boundCloses at hc
  simp only [forceW_eq, forceWs_eq, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨hgeq, hgnz⟩, scan⟩ := hc
  have hgnz' : bgoal ≠ 0 := ne_of_beq_false hgnz
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  simp only [Bool.and_eq_true, Nat.blt_eq] at scan
  obtain ⟨hlen, hsrc⟩ := scan
  set replay := replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock
  have hgnf : canon cut goal ≠ 0 := hgeq.symm ▸ hgnz'
  have hsup : ∀ w ∈ ws.toFinset, Avail (replay ++ stock) (canon cut w) := by
    intro w hw
    exact availB_spec.mp (List.all_eq_true.mp hsrc w (List.mem_toFinset.mp hw))
  obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (replay ++ stock) hsup
  rw [← flatCount_card cut nd] at hylen
  have hboth := builds_append (replayRec_builds cut _ hist.reverse stock) hybd
  have hfinal : Avail ((replay ++ ys) ++ stock) bgoal := by
    rw [← hgeq]
    exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
  have heno := hlow (replay ++ ys) hboth hfinal
  simp only [List.length_append] at heno
  omega

theorem knownCloses_sound {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    knownCloses goal bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change (boundCloses goal state b || knownCloses goal bs state) = false
    rw [boundCloses_sound (hknown b List.mem_cons_self) (hsub b List.mem_cons_self) nd hk hlive]
    exact ih (fun x hx => hknown x (List.mem_cons_of_mem _ hx)) (fun x hx => hsub x (List.mem_cons_of_mem _ hx))

def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l

theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]

theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩

def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l

theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩

theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2

theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]

def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits

theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)

theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)

theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩

def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])

def makeToken (a b op keep : Nat) : Nat := ((a * 16 + b) * 4 + op) * 4 + keep

def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)

theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)

def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i

theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2

def dagLocal (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Nat.blt (fuel + 1) ws.length ||
    !(dagPart ws goal (mask ^^^ goal)) ||
    knownCloses goal bounds state

theorem dagLocal_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    dagLocal mask goal bounds state = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  dsimp only at nd hk hlive
  unfold dagLocal
  have hcard : ws.length ≤ fuel + 1 := by
    have := liveBin_card_le hlive
    rw [List.toFinset_card_of_nodup nd] at this; omega
  have h1 : Nat.blt (fuel + 1) ws.length = false := by
    cases h : Nat.blt (fuel + 1) ws.length; rfl; have := Nat.blt_eq.mp h; omega
  have h2 : dagPart ws goal (mask ^^^ goal) = true := dagPart_live hgm hlive
  have h3 : knownCloses goal bounds (fuel, ws, hist) = false :=
    knownCloses_sound hknown hsub nd hk hlive
  simp [h1, h2, h3]

def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi

theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2

theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Nat.blt dest count &&
      match states dest with
      | none => false
      | some saved => Nat.beq saved.1 state.1 && (saved.2.1 == state.2.1)

def dagCheckChildren (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := ws.length
  !(ws.contains goal) &&
    (Nat.beq fuel 0 ||
      (Nat.blt n 17 &&
        treeBlock 0 n (fun a =>
          let x := ws.getD a 0
          treeBlock (a + 1) n (fun b =>
            let y := ws.getD b 0
            treeBlock 0 4 (fun op =>
              forceW (binOp mask op x y) (fun z =>
                Nat.beq z 0 || ws.contains z ||
                  treeBlock 0 4 (fun keep =>
                    let keepA := Nat.beq (keep &&& 1) 1
                    let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
                    let newLen := n - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0)
                    Nat.blt fuel newLen ||
                      forceWs (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))) (fun ws' =>
                        let ch := (fuel - 1, ws', (z, x, y) :: hist)
                        dagLocal mask goal bounds ch || ref (makeToken a b op keep) ch))))))))

def dagCheckNode (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (dagRef count states links (i + 1)) st

def dagCheckRoots (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ stock.length) (fun token =>
    forceWs (subsetWords stock token) (fun ws =>
      let st := (fuel, ws, [])
      dagLocal mask goal bounds st || ref token st))

theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]

theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega

theorem dagAllNodes {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNode at hchk
    rw [htr] at hchk
    unfold dagCheckChildren at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hchk
    obtain ⟨hnohit, hstep⟩ := hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hnohit; exact Bool.noConfusion hnohit
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      rcases hstep with hrem0 | ⟨hn17, hblock⟩
      · exact hrem_pos hrem0
      · have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
        have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
        obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
        obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
        have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
        have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
            ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
              ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
              ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
              binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
              LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
          by_cases hlt : ia0 < ib0
          · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
              by simp only [hlt, ite_true]; exact hea0,
              by simp only [hlt, ite_true]; exact heb0,
              by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
          · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
            have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
              ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
            exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
              by simp only [hlt, ite_false]; exact heb0,
              by simp only [hlt, ite_false]; exact hea0,
              by rw [hea0, heb0, hopEq],
              by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
        set x := ws.getD a 0
        set y := ws.getD b 0
        set z := binOp mask op x y
        set keep := (if keepA then 1 else 0) + (if keepB then 2 else 0)
        have hkeep_lt : keep < 4 := by cases keepA <;> cases keepB <;> simp [keep]
        have hkA : Nat.beq (keep &&& 1) 1 = keepA := by cases keepA <;> cases keepB <;> decide
        have hkB : Nat.beq ((keep >>> 1) &&& 1) 1 = keepB := by cases keepA <;> cases keepB <;> decide
        have hkA' : (keep &&& 1 = 1) ↔ keepA = true := by cases keepA <;> cases keepB <;> decide
        have hkB' : ((keep >>> 1) &&& 1 = 1) ↔ keepB = true := by cases keepA <;> cases keepB <;> decide
        have hA := treeBlock_at hblock (Nat.zero_le a) ha_lt
        have hB := treeBlock_at hA (by omega : a + 1 ≤ b) hb_lt
        have hO := treeBlock_at hB (Nat.zero_le op) hop_lt
        simp only [forceW_eq, Bool.or_eq_true, Nat.beq_eq] at hO
        have hznz : z ≠ 0 := hzeq.symm ▸ hz0
        have hznm : ws.contains z = false := by
          cases h : ws.contains z
          · rfl
          · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
        rcases hO with (hz' | hcm) | hK
        · exact hznz hz'
        · rw [hznm] at hcm; exact Bool.noConfusion hcm
        · have hKe := treeBlock_at hK (Nat.zero_le keep) hkeep_lt
          simp only [hkA, hkB, hkA', hkB', forceWs_eq, Bool.or_eq_true, Nat.blt_eq] at hKe
          set ws' := insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))
          have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
          have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
          have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
          have hzNotW : z ∉ ws := fun hm => by
            have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
          have hnd' : ws'.Nodup :=
            insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
          have hset' : ws'.toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
            ext w; simp only [ws', List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
          have hlive' : LiveBin mask goal k' ws'.toFinset := by rwa [hset']
          have hlen' := list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
          have hcard' : ws'.length ≤ rem := by
            have := liveBin_card_le hlive'
            rw [List.toFinset_card_of_nodup hnd'] at this; omega
          rcases hKe with hwide | hloc | href
          · change ws'.length = _ at hlen'; rw [← hlen'] at hwide; omega
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm hknown hsub hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · unfold dagRef at href
            split at href
            · contradiction
            · rename_i dest _
              simp only [Bool.and_eq_true, Nat.blt_eq] at href
              obtain ⟨hdest, hst⟩ := href
              cases htr2 : dagTrace mask stock fuel forest dest with
              | none => rw [htr2] at hst; contradiction
              | some saved =>
                rw [htr2] at hst
                simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
                obtain ⟨hfEq, hwEq⟩ := hst
                have hbelow : rem - 1 < cap := by omega
                exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive')

theorem lowerDag {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  have hchk := treeBlock_at hroots (Nat.zero_le tok) htok
  simp only [forceWs_eq, Bool.or_eq_true] at hchk
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  rcases hchk with hloc | href
  · have hopen := dagLocal_open (state := (fuel, subsetWords stock tok, [])) hgm hknown hsub hnd (k := k) (by omega) hlive'
    rw [hopen] at hloc; exact Bool.noConfusion hloc
  · unfold dagRef at href
    split at href
    · contradiction
    · rename_i dest _
      simp only [Bool.and_eq_true, Nat.blt_eq] at href
      obtain ⟨hdest, hst⟩ := href
      cases htr : dagTrace mask stock fuel forest dest with
      | none => rw [htr] at hst; contradiction
      | some saved =>
        rw [htr] at hst
        simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
        obtain ⟨hfEq, hwEq⟩ := hst
        exact dagAllNodes hgm hknown hsub snd hnodes fuel dest saved hdest htr hfEq k (by omega) (hwEq ▸ hlive')

def unpack (data width idx : Nat) : Nat :=
  (data >>> (idx * width)) &&& ((1 <<< width) - 1)

def unpackForest (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := pBits + tBits
  let code := unpack data w i
  (code >>> tBits, code &&& ((1 <<< tBits) - 1))

def unpackLinks (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpack index idxW parent
    let sz := entry &&& ((1 <<< sizeBits) - 1)
    let off := entry >>> sizeBits
    let w := tokBits + destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        if Nat.blt lo hi then
          let mid := (lo + hi) / 2
          let code := unpack data w mid
          let key := code &&& ((1 <<< tokBits) - 1)
          if Nat.beq tok key then some (code >>> tokBits)
          else if Nat.blt tok key then next lo mid else next (mid + 1) hi
        else none) steps) off (off + sz)

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k

def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide

theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]

theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]

theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]

def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]

theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)

theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)

theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])

theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel

theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l

theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]

def allN (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun w _ ih => Bool.rec false ih (p w)) l

theorem allN_eq (p : Nat → Bool) (l : List Nat) : allN p l = l.all p := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec false (allN p ws) (p w) = (p w && ws.all p)
    rw [ih]; cases p w <;> rfl

def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l

theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]

def appN (l r : List Nat) : List Nat :=
  List.rec r (fun w _ ih => w :: ih) l

theorem appN_eq (l r : List Nat) : appN l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons w ws ih => change w :: appN ws r = w :: (ws ++ r); rw [ih]

def revAccN {α : Type} (l acc : List α) : List α :=
  (List.rec (motive := fun _ => List α → List α) (fun a => a) (fun w _ ih a => ih (w :: a)) l) acc

theorem revAccN_eq {α : Type} (l acc : List α) : revAccN l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    change revAccN ws (w :: acc) = (w :: ws).reverse ++ acc
    rw [ih, List.reverse_cons, List.append_assoc]; rfl

def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i

theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl

def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1

theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]

def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)

theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl

def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)

theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl

def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws

theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl

def flatCountF (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt =>
    let v := Nat.land w cut
    Bool.rec (Bool.rec cnt (Nat.add cnt 1) (Nat.beq v cut)) (Nat.add cnt 1) (Nat.beq v 0)) ws

theorem flatCountF_eq (cut : Nat) (ws : List Nat) : flatCountF cut ws = flatCount cut ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (flatCountF cut ws) (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) cut))
      (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) 0) =
      bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws)
    rw [ih]
    rcases canon_cases cut w with ⟨h0, h1 | h2⟩ | ⟨hne, _⟩
    · have hb : Nat.beq (Nat.land w cut) 0 = true := Nat.beq_eq.mpr h1
      rw [h0, hb, Nat.beq_refl]; rfl
    · have hb : Nat.beq (Nat.land w cut) cut = true := Nat.beq_eq.mpr h2
      rw [h0, hb, Nat.beq_refl]; cases Nat.beq (Nat.land w cut) 0 <;> rfl
    · have h1 : Nat.beq (Nat.land w cut) 0 = false := beq_false_ne (fun e => by
        change w &&& cut = 0 at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      have h2 : Nat.beq (Nat.land w cut) cut = false := beq_false_ne (fun e => by
        change w &&& cut = cut at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      rw [h1, h2, beq_false_ne hne]; rfl

def availBF (bank : List Nat) (w : Nat) : Bool :=
  Bool.rec (memN w bank) true (Nat.beq w 0)

theorem availBF_eq (bank : List Nat) (w : Nat) : availBF bank w = availB bank w := by
  unfold availBF availB; rw [memN_eq]; cases Nat.beq w 0 <;> rfl

def recipeGateBinF (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  Bool.rec false
    (Bool.rec false
      (Bool.rec
        (Bool.rec
          (Bool.rec (Nat.beq vc (binOpF cut 3 ac bc)) true (Nat.beq vc (binOpF cut 2 ac bc)))
          true (Nat.beq vc (binOpF cut 1 ac bc)))
        true (Nat.beq vc (binOpF cut 0 ac bc)))
      (availBF bank bc))
    (availBF bank ac)

theorem recipeGateBinF_eq (cut : Nat) (bank : List Nat) (vc ac bc : Nat) :
    recipeGateBinF cut bank vc ac bc = recipeGateBin cut bank vc ac bc := by
  unfold recipeGateBinF recipeGateBin
  simp only [availBF_eq, binOpF_eq]
  cases availB bank ac <;> cases availB bank bc <;>
    cases Nat.beq vc (binOp cut 0 ac bc) <;> cases Nat.beq vc (binOp cut 1 ac bc) <;>
    cases Nat.beq vc (binOp cut 2 ac bc) <;> cases Nat.beq vc (binOp cut 3 ac bc) <;> rfl

def addUniqF (w : Nat) (l : List Nat) : List Nat :=
  Bool.rec (w :: l) l (memN w l)

theorem addUniqF_eq (w : Nat) (l : List Nat) : addUniqF w l = addUniq w l := by
  unfold addUniqF addUniq; rw [memN_eq]; cases l.contains w <;> rfl

def recipeStartF (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canonF cut w
    Bool.rec (addUniqF v acc) acc (availBF stock v)) ws

theorem recipeStartF_eq (cut : Nat) (stock ws : List Nat) : recipeStartF cut stock ws = recipeStart cut stock ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (addUniqF (canonF cut w) (recipeStartF cut stock ws)) (recipeStartF cut stock ws) (availBF stock (canonF cut w)) =
      (if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    rw [ih, canonF_eq, availBF_eq, addUniqF_eq]; cases availB stock (canon cut w) <;> rfl

def recipeCloseF (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canonF cut w
      Bool.rec (next acc)
        (let va := canonF cut a
         let vb := canonF cut b
         let acc1 := Bool.rec (addUniqF va acc) acc (availBF stock va)
         let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
         next acc2)
        (memN v acc)) hist needed

theorem recipeCloseF_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseF cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : recipeCloseF cut stock ((w, a, b) :: hist) needed =
        Bool.rec (recipeCloseF cut stock hist needed)
          (let va := canonF cut a; let vb := canonF cut b
           let acc1 := Bool.rec (addUniqF va needed) needed (availBF stock va)
           let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
           recipeCloseF cut stock hist acc2)
          (memN (canonF cut w) needed) := rfl
    have hR : recipeClose cut stock ((w, a, b) :: hist) needed =
        (if needed.contains (canon cut w) then
          let va := canon cut a; let vb := canon cut b
          let acc1 := if availB stock va then needed else addUniq va needed
          let acc2 := if availB stock vb then acc1 else addUniq vb acc1
          recipeClose cut stock hist acc2
        else recipeClose cut stock hist needed) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, addUniqF_eq]
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only; rw [ih]
      cases availB stock (canon cut a) <;> cases availB stock (canon cut b) <;> rfl

def replayRecF (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canonF cut w
      Bool.rec (next bank)
        (Bool.rec
          (Bool.rec (next bank) (v :: next (v :: bank))
            (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
          (next bank) (availBF bank v))
        (memN v needed)) hist bank

theorem replayRecF_eq (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    replayRecF cut needed hist bank = replayRec cut needed hist bank := by
  induction hist generalizing bank with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : replayRecF cut needed ((w, a, b) :: hist) bank =
        let v := canonF cut w
        Bool.rec (replayRecF cut needed hist bank)
          (Bool.rec
            (Bool.rec (replayRecF cut needed hist bank) (v :: replayRecF cut needed hist (v :: bank))
              (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
            (replayRecF cut needed hist bank) (availBF bank v))
          (memN v needed) := rfl
    have hR : replayRec cut needed ((w, a, b) :: hist) bank =
        (let v := canon cut w
         if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
           v :: replayRec cut needed hist (v :: bank)
         else replayRec cut needed hist bank) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, recipeGateBinF_eq]
    rw [ih bank, ih (canon cut w :: bank)]
    cases needed.contains (canon cut w) <;> cases availB bank (canon cut w) <;>
      cases recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) <;> rfl

def boundClosesF (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, _) := bound
  let (fuel, ws, hist) := state
  forceW (Nat.sub fuel (flatCountF cut ws)) (fun rem =>
    Bool.rec false
      (forceWs (recipeStartF cut stock ws) (fun start =>
        Bool.rec false
          (forceWs (recipeCloseF cut stock hist start) (fun needed =>
            Bool.rec false
              (forceWs (replayRecF cut needed (revAccN hist []) stock) (fun replay =>
                Bool.rec false
                  (allN (fun w => availBF (appN replay stock) (canonF cut w)) ws)
                  (Nat.blt (Nat.add (lenN replay) rem) lower)))
              (Nat.blt (Nat.add (lenN needed) rem) lower)))
          (Nat.blt (Nat.add (lenN start) rem) lower)))
      (Nat.blt rem lower))

theorem boundClosesF_eq {target : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hg : canon bound.1 target = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0) :
    boundClosesF state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hg hnz
  unfold boundClosesF boundCloses
  simp only [forceW_eq, forceWs_eq, flatCountF_eq, recipeStartF_eq, recipeCloseF_eq,
    replayRecF_eq, revAccN_eq, List.append_nil, lenN_eq, allN_eq, appN_eq, availBF_eq, canonF_eq,
    hg, Nat.beq_refl, beq_false_ne hnz, Bool.not_false, Bool.and_true, Bool.true_and]
  cases Nat.blt (fuel - flatCount cut ws) lower
  · rfl
  · cases Nat.blt ((recipeStart cut stock ws).length + (fuel - flatCount cut ws)) lower
    · rfl
    · cases Nat.blt ((recipeClose cut stock hist (recipeStart cut stock ws)).length + (fuel - flatCount cut ws)) lower
      · rfl
      · cases Nat.blt ((replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock).length + (fuel - flatCount cut ws)) lower <;> rfl

def knownClosesF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => Bool.rec rest true (boundClosesF state b)) bounds

theorem knownClosesF_eq {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    knownClosesF bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change Bool.rec (knownClosesF bs state) true (boundClosesF state b) =
      (boundCloses target state b || knownCloses target bs state)
    have h0 := hgoals b List.mem_cons_self
    rw [boundClosesF_eq h0.1 h0.2, ih (fun x hx => hgoals x (List.mem_cons_of_mem _ hx))]
    cases boundCloses target state b <;> rfl

def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l

theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl

def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop

theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl

def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits

theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl

def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)

theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl

def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i

theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl

theorem knownCloses_of_mem {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)} {b : Nat × List Nat × Nat × Nat}
    (hmem : b ∈ bounds) (hb : boundCloses target state b = true) :
    knownCloses target bounds state = true := by
  induction bounds with
  | nil => cases hmem
  | cons x xs ih =>
    change (boundCloses target state x || knownCloses target xs state) = true
    rcases List.mem_cons.mp hmem with rfl | htl
    · rw [hb]; rfl
    · rw [ih htl]; cases boundCloses target state x <;> rfl

theorem treeBlock_mono {lo hi : Nat} {f g : Nat → Bool}
    (hf : treeBlock lo hi f = true)
    (himp : ∀ i, lo ≤ i → i < hi → f i = true → g i = true) :
    treeBlock lo hi g = true := by
  unfold treeBlock at hf ⊢
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      (∀ i, a ≤ i → i < b → f i = true → g i = true) →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then g x else next x m && next m y
          else true) steps) a b = true from
    this (hi - lo + 1) lo hi hf himp
  intro steps
  induction steps with
  | zero => intro a b _ _; rfl
  | succ s ih =>
    intro a b h hfg
    dsimp only at h ⊢
    cases hlt : Nat.blt a b
    · rfl
    · simp only [hlt, ite_true] at h ⊢
      have hab : a < b := Nat.blt_eq.mp hlt
      cases heq : Nat.beq a ((a + b) / 2)
      · simp only [heq, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h ⊢
        exact ⟨ih a ((a + b) / 2) h.1 (fun i h1 h2 => hfg i h1 (by omega)),
               ih ((a + b) / 2) b h.2 (fun i h1 h2 => hfg i (by omega) h2)⟩
      · simp only [heq, ite_true] at h ⊢
        exact hfg a (Nat.le_refl a) hab h

def nthBound (bounds : List (Nat × List Nat × Nat × Nat)) (i : Nat) :
    Option (Nat × List Nat × Nat × Nat) :=
  (List.rec (motive := fun _ => Nat → Option (Nat × List Nat × Nat × Nat))
    (fun _ => none)
    (fun b _ ih k => Nat.rec (some b) (fun m _ => ih m) k) bounds) i

theorem nthBound_mem {bounds : List (Nat × List Nat × Nat × Nat)} {i : Nat} {b : Nat × List Nat × Nat × Nat}
    (h : nthBound bounds i = some b) : b ∈ bounds := by
  induction bounds generalizing i with
  | nil => simp [nthBound] at h
  | cons x xs ih =>
    cases i with
    | zero => cases h; exact List.mem_cons_self
    | succ m => exact List.mem_cons_of_mem _ (ih h)

def knownClosesTopF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match bounds with
  | [] => false
  | b0 :: rest =>
    Bool.rec
      (match rest with
       | [] => false
       | b1 :: rest1 =>
         Bool.rec
           (match rest1 with
            | [] => false
            | b2 :: _ => boundClosesF state b2)
           true (boundClosesF state b1))
      true (boundClosesF state b0)

theorem knownClosesTopF_imp {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : knownClosesTopF bounds state = true) :
    knownCloses target bounds state = true := by
  cases bounds with
  | nil => exact Bool.noConfusion h
  | cons b0 rest =>
    unfold knownClosesTopF at h; dsimp only at h
    have h0 := hgoals b0 List.mem_cons_self
    cases hb0 : boundClosesF state b0
    · rw [hb0] at h; dsimp only at h
      cases rest with
      | nil => exact Bool.noConfusion h
      | cons b1 rest1 =>
        dsimp only at h
        have h1 := hgoals b1 (List.mem_cons_of_mem _ List.mem_cons_self)
        cases hb1 : boundClosesF state b1
        · rw [hb1] at h; dsimp only at h
          cases rest1 with
          | nil => exact Bool.noConfusion h
          | cons b2 rest2 =>
            dsimp only at h
            have h2 := hgoals b2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            rw [boundClosesF_eq h2.1 h2.2] at h
            exact knownCloses_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) h
        · rw [boundClosesF_eq h1.1 h1.2] at hb1
          exact knownCloses_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) hb1
    · rw [boundClosesF_eq h0.1 h0.2] at hb0
      exact knownCloses_of_mem List.mem_cons_self hb0

def edgeAxis (mask goal stride lm : Nat) : Nat :=
  let neg := Nat.xor mask goal
  Nat.land (Nat.lor (Nat.land (Nat.shiftRight goal stride) neg)
    (Nat.land goal (Nat.shiftRight neg stride))) lm

def edgePack (mask goal : Nat) : Nat :=
  Nat.lor (edgeAxis mask goal 1 0x5555555555555555)
    (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 2 0x3333333333333333) 64)
      (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f) 128)
        (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 8 0x00ff00ff00ff00ff) 192)
          (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 16 0x0000ffff0000ffff) 256)
            (Nat.shiftLeft (edgeAxis mask goal 32 0x00000000ffffffff) 320)))))

def sepAxis (stride lm w : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.shiftRight w stride) w) lm

def sepPack (w : Nat) : Nat :=
  Nat.lor (sepAxis 1 0x5555555555555555 w)
    (Nat.lor (Nat.shiftLeft (sepAxis 2 0x3333333333333333 w) 64)
      (Nat.lor (Nat.shiftLeft (sepAxis 4 0x0f0f0f0f0f0f0f0f w) 128)
        (Nat.lor (Nat.shiftLeft (sepAxis 8 0x00ff00ff00ff00ff w) 192)
          (Nat.lor (Nat.shiftLeft (sepAxis 16 0x0000ffff0000ffff w) 256)
            (Nat.shiftLeft (sepAxis 32 0x00000000ffffffff w) 320)))))

def orSep (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ ih => Nat.lor (sepPack w) ih) ws

theorem edgeAxis_live {mask goal stride lm k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset)
    {n : Nat} (he : (edgeAxis mask goal stride lm).testBit n = true) :
    ∃ w ∈ ws, (sepAxis stride lm w).testBit n = true := by
  unfold edgeAxis at he
  change (((goal >>> stride &&& (mask ^^^ goal)) ||| (goal &&& ((mask ^^^ goal) >>> stride))) &&& lm).testBit n = true at he
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Bool.and_eq_true, Bool.or_eq_true] at he
  obtain ⟨hcases, hlm⟩ := he
  have hpm : ∀ j, goal.testBit j = true → mask.testBit j = true := fun j hg => by
    have e := congrArg (fun x => x.testBit j) hgm
    simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
  have hnm : ∀ j, (mask ^^^ goal).testBit j = true → mask.testBit j = true ∧ goal.testBit j = false := fun j hn => by
    rw [Nat.testBit_xor] at hn
    cases hm : mask.testBit j <;> cases hg : goal.testBit j <;> simp_all
  have hsep : ∃ w ∈ ws, w.testBit (stride + n) ≠ w.testBit n := by
    by_contra! hall
    rcases hcases with ⟨hg1, hn0⟩ | ⟨hg0, hn1⟩
    · have h1 := hpm (stride + n) hg1
      have h0 := hnm n hn0
      have eq := liveBin_agrees h1 h0.1 hlive (fun w hw => hall w (List.mem_toFinset.mp hw))
      rw [hg1, h0.2] at eq; exact Bool.noConfusion eq
    · have h0 := hpm n hg0
      have h1 := hnm (stride + n) hn1
      have eq := liveBin_agrees h0 h1.1 hlive (fun w hw => (hall w (List.mem_toFinset.mp hw)).symm)
      rw [hg0, h1.2] at eq; exact Bool.noConfusion eq
  obtain ⟨w, hw, hne⟩ := hsep
  refine ⟨w, hw, ?_⟩
  unfold sepAxis
  change (((w >>> stride) ^^^ w) &&& lm).testBit n = true
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hlm, Bool.and_true]
  cases hb1 : w.testBit (stride + n) <;> cases hb2 : w.testBit n <;> simp_all

theorem orSep_testBit {ws : List Nat} {w j : Nat}
    (hw : w ∈ ws) (hb : (sepPack w).testBit j = true) : (orSep ws).testBit j = true := by
  induction ws with
  | nil => cases hw
  | cons x xs ih =>
    change (sepPack x ||| orSep xs).testBit j = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | htl
    · exact Or.inl hb
    · exact Or.inr (ih htl)

theorem sepPack_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    Nat.beq (Nat.land (edgePack mask goal) (orSep ws)) (edgePack mask goal) = true := by
  apply Nat.beq_eq.mpr
  apply Nat.eq_of_testBit_eq; intro j
  change ((edgePack mask goal) &&& (orSep ws)).testBit j = (edgePack mask goal).testBit j
  rw [Nat.testBit_and]
  cases he : (edgePack mask goal).testBit j
  · rfl
  · simp only [Bool.true_and]
    have hlane (stride lm shift : Nat)
        (hl : (edgeAxis mask goal stride lm <<< shift).testBit j = true)
        (hs : ∀ w, (sepAxis stride lm w <<< shift).testBit j = true → (sepPack w).testBit j = true) :
        (orSep ws).testBit j = true := by
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive hl.2
      apply orSep_testBit hw
      apply hs w
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl.1, hsw⟩
    unfold edgePack at he
    change (edgeAxis mask goal 1 0x5555555555555555 |||
      ((edgeAxis mask goal 2 0x3333333333333333 <<< 64) |||
        ((edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f <<< 128) |||
          ((edgeAxis mask goal 8 0x00ff00ff00ff00ff <<< 192) |||
            ((edgeAxis mask goal 16 0x0000ffff0000ffff <<< 256) |||
              (edgeAxis mask goal 32 0x00000000ffffffff <<< 320)))))).testBit j = true at he
    simp only [Nat.testBit_or, Bool.or_eq_true] at he
    rcases he with h0 | h1 | h2 | h3 | h4 | h5
    · obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive h0
      exact orSep_testBit hw (by
        unfold sepPack
        change (sepAxis 1 0x5555555555555555 w ||| _).testBit j = true
        simp [Nat.testBit_or, hsw])
    · exact hlane 2 0x3333333333333333 64 h1 (fun w hw => by
        unfold sepPack
        change (_ ||| ((sepAxis 2 0x3333333333333333 w <<< 64) ||| _)).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 4 0x0f0f0f0f0f0f0f0f 128 h2 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| ((sepAxis 4 0x0f0f0f0f0f0f0f0f w <<< 128) ||| _))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 8 0x00ff00ff00ff00ff 192 h3 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| ((sepAxis 8 0x00ff00ff00ff00ff w <<< 192) ||| _)))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 16 0x0000ffff0000ffff 256 h4 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| ((sepAxis 16 0x0000ffff0000ffff w <<< 256) ||| _))))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 32 0x00000000ffffffff 320 h5 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| (_ ||| (sepAxis 32 0x00000000ffffffff w <<< 320)))))).testBit j = true
        simp [Nat.testBit_or, hw])

def mapSep (ws : List Nat) : List (Nat × Nat) :=
  List.rec [] (fun w _ ih => (w, sepPack w) :: ih) ws

def forceSepPairs : List Nat → (List (Nat × Nat) → Bool) → Bool
  | [], k => k []
  | w :: ws, k => forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest)))

theorem forceSepPairs_eq (ws : List Nat) (k : List (Nat × Nat) → Bool) :
    forceSepPairs ws k = k (mapSep ws) := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest))) = _
    rw [forceW_eq, ih]; rfl

def orSepAll (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Nat.lor p.2 ih) ps

def orSepSkip (x : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 x)) ps

def orSepSkip2 (x y : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 y)) ih (Nat.beq p.1 x)) ps

theorem orSepAll_mapSep (ws : List Nat) : orSepAll (mapSep ws) = orSep ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => change Nat.lor (sepPack w) (orSepAll (mapSep ws)) = Nat.lor (sepPack w) (orSep ws); rw [ih]

theorem orSepSkip_mapSep (x : Nat) (ws : List Nat) :
    orSepSkip x (mapSep ws) = orSep (dropVal true x ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Nat.lor (sepPack w) (orSepSkip x (mapSep ws))) (orSepSkip x (mapSep ws)) (Nat.beq w x) =
      orSep (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws))
    rw [ih]
    cases Nat.beq w x <;> rfl

theorem dropVal_comm (x y : Nat) (l : List Nat) :
    dropVal true y (dropVal true x l) = dropVal true x (dropVal true y l) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    change dropVal true y (bsel (Nat.beq u x) (dropVal true x us) (u :: dropVal true x us)) =
      dropVal true x (bsel (Nat.beq u y) (dropVal true y us) (u :: dropVal true y us))
    cases hux : Nat.beq u x <;> cases huy : Nat.beq u y
    · simp only [bsel_false]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) =
        bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [huy, hux, bsel_false, bsel_false, ih]
    · simp only [bsel_false, bsel_true]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) = _
      rw [huy, bsel_true, ih]
    · simp only [bsel_true, bsel_false]
      change _ = bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [hux, bsel_true, ih]
    · simp only [bsel_true]; exact ih

theorem orSepSkip2_mapSep (x y : Nat) (ws : List Nat) :
    orSepSkip2 x y (mapSep ws) = orSep (dropVal true y (dropVal true x ws)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (Nat.lor (sepPack w) (orSepSkip2 x y (mapSep ws))) (orSepSkip2 x y (mapSep ws)) (Nat.beq w y))
      (orSepSkip2 x y (mapSep ws)) (Nat.beq w x) =
      orSep (dropVal true y (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws)))
    rw [ih]
    cases hx : Nat.beq w x
    · rw [bsel_false]
      change Bool.rec (Nat.lor (sepPack w) (orSep (dropVal true y (dropVal true x ws))))
        (orSep (dropVal true y (dropVal true x ws))) (Nat.beq w y) =
        orSep (bsel (Nat.beq w y) (dropVal true y (dropVal true x ws)) (w :: dropVal true y (dropVal true x ws)))
      cases Nat.beq w y <;> rfl
    · rw [bsel_true]

def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi

theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

def forceWC (w : Nat) (k : Nat → Bool × List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem forceWC_eq (w : Nat) (k : Nat → Bool × List (Nat × Nat)) : forceWC w k = k w := by
  cases w <;> rfl

def closeFallbackV4 (mask goal ep : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (st : Nat × List Nat × List (Nat × Nat × Nat)) (sp : Nat) : Bool :=
  Bool.rec true
    (Bool.rec
      (Bool.rec true false (dagPartF st.2.1 goal (Nat.xor mask goal)))
      true (knownClosesTopF bounds st))
    (Nat.beq (Nat.land ep sp) ep)

theorem closeFallbackV4_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (nd : st.2.1.Nodup) {k : Nat} (hk : k ≤ st.1)
    (hlive : LiveBin mask goal k st.2.1.toFinset) :
    closeFallbackV4 mask goal (edgePack mask goal) bounds st (orSep st.2.1) = false := by
  unfold closeFallbackV4
  have hsp : Nat.beq (Nat.land (edgePack mask goal) (orSep st.2.1)) (edgePack mask goal) = true :=
    sepPack_live hgm hlive
  have hkt : knownClosesTopF bounds st = false := by
    cases h : knownClosesTopF bounds st
    · rfl
    · have hk1 := knownClosesTopF_imp hgoals h
      have hk0 := knownCloses_sound hknown hsub nd hk hlive
      rw [hk0] at hk1; exact Bool.noConfusion hk1
  have hdp : dagPartF st.2.1 goal (Nat.xor mask goal) = true := by
    have heq : dagPartF st.2.1 goal (Nat.xor mask goal) = dagPart st.2.1 goal (mask ^^^ goal) :=
      dagPartF_eq st.2.1 goal (mask ^^^ goal)
    rw [heq]; exact dagPart_live hgm hlive
  rw [hsp, hkt, hdp]

def stepLeafV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  match cur with
  | (t, code) :: tl =>
    Bool.rec
      (closeFallbackV4 mask goal ep bounds (fuel1, z :: rest, hist1) (Nat.lor spZ baseSp), cur)
      (Bool.rec
        (match nthBound bounds (Nat.shiftRight code 1) with
         | none => (false, tl)
         | some b => (boundClosesF (fuel1, z :: rest, hist1) b, tl))
        (let dest := Nat.shiftRight code 1
         let ok := Bool.rec false
           (match states dest with
            | none => false
            | some saved => Bool.rec false (eqListN saved.2.1 (insertSortedF z rest)) (Nat.beq saved.1 fuel1))
           (Nat.blt dest count)
         (ok, tl))
        (Nat.beq (Nat.land code 1) 0))
      (Nat.beq tok t)
  | [] =>
    (closeFallbackV4 mask goal ep bounds (fuel1, z :: rest, hist1) (Nat.lor spZ baseSp), [])

theorem stepLeafV4_ref {mask goal count fuel1 z tok : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (h : (stepLeafV4 mask goal (edgePack mask goal) count bounds states fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur).1 = true) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hfb : closeFallbackV4 mask goal (edgePack mask goal) bounds (fuel1, z :: rest, hist1) (Nat.lor (sepPack z) (orSep rest)) = false :=
    closeFallbackV4_open (st := (fuel1, z :: rest, hist1)) hgm hknown hsub hgoals nd hk hlive
  unfold stepLeafV4 at h
  cases cur with
  | nil => dsimp only at h; rw [hfb] at h; exact Bool.noConfusion h
  | cons hd tl =>
    obtain ⟨t, code⟩ := hd
    dsimp only at h
    cases ht : Nat.beq tok t
    · rw [ht] at h; dsimp only at h; rw [hfb] at h; exact Bool.noConfusion h
    · rw [ht] at h; dsimp only at h
      cases hev : Nat.beq (Nat.land code 1) 0
      · rw [hev] at h; dsimp only at h
        cases hb : nthBound bounds (Nat.shiftRight code 1) with
        | none => rw [hb] at h; exact Bool.noConfusion h
        | some b =>
          rw [hb] at h; dsimp only at h
          have hmem := nthBound_mem hb
          have hg := hgoals b hmem
          rw [boundClosesF_eq hg.1 hg.2] at h
          have h0 := boundCloses_sound (state := (fuel1, z :: rest, hist1)) (hknown b hmem) (hsub b hmem) nd hk hlive
          rw [h0] at h; exact Bool.noConfusion h
      · rw [hev] at h; dsimp only at h
        cases hlt : Nat.blt (Nat.shiftRight code 1) count
        · rw [hlt] at h; exact Bool.noConfusion h
        · rw [hlt] at h; dsimp only at h
          cases hst : states (Nat.shiftRight code 1) with
          | none => rw [hst] at h; exact Bool.noConfusion h
          | some saved =>
            rw [hst] at h; dsimp only at h
            cases hf : Nat.beq saved.1 fuel1
            · rw [hf] at h; exact Bool.noConfusion h
            · rw [hf] at h; dsimp only at h
              rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at h
              exact ⟨Nat.shiftRight code 1, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, h⟩

def checkKeepsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  let (ok0, c1) : Bool × List (Nat × Nat) := Bool.rec
    (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur)
    (true, cur) (Nat.blt fuel (Nat.sub n 1))
  Bool.rec (false, c1)
    (let (ok1, c2) : Bool × List (Nat × Nat) := Bool.rec
       (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1)
       (true, c1) (Nat.blt fuel n)
     Bool.rec (false, c2)
       (let (ok2, c3) : Bool × List (Nat × Nat) := Bool.rec
          (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2)
          (true, c2) (Nat.blt fuel n)
        Bool.rec (false, c3)
          (Bool.rec
            (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3)
            (true, c3) (Nat.blt fuel (Nat.add n 1)))
          ok2)
       ok1)
    ok0

theorem checkKeepsV4_at {mask goal ep count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (h : (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur).1 = true)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c).1 = true
    | true, false => Nat.blt fuel n = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c).1 = true
    | false, true => Nat.blt fuel n = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c).1 = true
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c).1 = true := by
  unfold checkKeepsV4 at h
  generalize hp0 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur)
    (true, cur) (Nat.blt fuel (Nat.sub n 1)) : Bool × List (Nat × Nat)) = p0 at h
  obtain ⟨ok0, c1⟩ := p0
  dsimp only at h
  cases ok0
  · exact Bool.noConfusion h
  · dsimp only at h
    generalize hp1 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1)
      (true, c1) (Nat.blt fuel n) : Bool × List (Nat × Nat)) = p1 at h
    obtain ⟨ok1, c2⟩ := p1
    dsimp only at h
    cases ok1
    · exact Bool.noConfusion h
    · dsimp only at h
      generalize hp2 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2)
        (true, c2) (Nat.blt fuel n) : Bool × List (Nat × Nat)) = p2 at h
      obtain ⟨ok2, c3⟩ := p2
      dsimp only at h
      cases ok2
      · exact Bool.noConfusion h
      · dsimp only at h
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, congrArg Prod.fst hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, congrArg Prod.fst hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, congrArg Prod.fst hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at h; exact Or.inr ⟨c3, h⟩
          · exact Or.inl rfl

def checkOpV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  forceWC (canonF mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWC (sepPack z) (fun spZ =>
          checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur))
        (true, cur) (memN z ws0))
      (true, cur) (Nat.beq z 0))

def check4OpsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  let (o0, c1) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur
  Bool.rec (false, c1)
    (let (o1, c2) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1
     Bool.rec (false, c2)
       (let (o2, c3) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2
        Bool.rec (false, c3)
          (checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3) o2) o1) o0

theorem check4OpsV4_at {mask goal ep count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (hop : op < 4)
    (h : (check4OpsV4 mask goal ep count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur).1 = true) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c, (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z (sepPack z) spAll spNoA spNoB spNoAB
        ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c).1 = true := by
  unfold check4OpsV4 at h
  generalize hp0 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur = p0 at h
  obtain ⟨o0, c1⟩ := p0; dsimp only at h
  cases o0
  · exact Bool.noConfusion h
  · dsimp only at h
    generalize hp1 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 = p1 at h
    obtain ⟨o1, c2⟩ := p1; dsimp only at h
    cases o1
    · exact Bool.noConfusion h
    · dsimp only at h
      generalize hp2 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 = p2 at h
      obtain ⟨o2, c3⟩ := p2; dsimp only at h
      cases o2
      · exact Bool.noConfusion h
      · dsimp only at h
        have extract (rawZ op' : Nat) (c0 : List (Nat × Nat))
            (hz : canon mask rawZ = binOp mask op' x y)
            (hok : (checkOpV4 mask goal ep count bounds states fuel fuel1 n x y rawZ op' spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0).1 = true) :
            binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
              ∃ c, (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n (binOp mask op' x y) (sepPack (binOp mask op' x y))
                spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c).1 = true := by
          unfold checkOpV4 at hok
          rw [forceWC_eq, canonF_eq, hz] at hok
          cases h0 : Nat.beq (binOp mask op' x y) 0
          · rw [h0] at hok; dsimp only at hok
            cases hm : memN (binOp mask op' x y) ws0
            · rw [hm] at hok; dsimp only at hok
              rw [forceWC_eq] at hok
              exact Or.inr (Or.inr ⟨c0, hok⟩)
            · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
          · exact Or.inl (Nat.beq_eq.mp h0)
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur rfl (congrArg Prod.fst hp0)
        · exact extract _ 1 c1 rfl (congrArg Prod.fst hp1)
        · exact extract _ 2 c2 rfl (congrArg Prod.fst hp2)
        · exact extract _ 3 c3 rfl h

def loopB_V4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, b, cur =>
    let y := getDN ws0 b
    let wsNoB := dropValF true y ws0
    let wsNoAB := dropValF true y wsNoA
    forceWC (orSepSkip y ps) (fun spNoB =>
      forceWC (orSepSkip2 x y ps) (fun spNoAB =>
        let tokAB := Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2
        let (ok, cur1) := check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur
        Bool.rec (false, cur1) (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1) ok))

theorem loopB_V4_at {mask goal ep count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b : Nat} {cur : List (Nat × Nat)}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (h : (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur).1 = true) :
    let y := getDN ws0 b
    ∃ c, (check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c).1 = true := by
  induction rem generalizing b0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopB_V4 at h; dsimp only at h
    rw [forceWC_eq, forceWC_eq] at h
    cases hp : check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : b = b0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) h

def loopA_V4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, a, cur =>
    let x := getDN ws0 a
    let wsNoA := dropValF true x ws0
    forceWC (Nat.xor mask x) (fun nx =>
      forceWC (orSepSkip x ps) (fun spNoA =>
        let (ok, cur1) := loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur
        Bool.rec (false, cur1) (loopA_V4 mask goal ep count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1) ok))

theorem loopA_V4_at {mask goal ep count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a : Nat} {cur : List (Nat × Nat)}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (h : (loopA_V4 mask goal ep count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur).1 = true) :
    let x := getDN ws0 a
    ∃ c, (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c).1 = true := by
  induction rem generalizing a0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopA_V4 at h; dsimp only at h
    rw [forceWC_eq, forceWC_eq] at h
    cases hp : loopB_V4 mask goal ep count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : a = a0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) h

def dagCheckNodeV4 (mask goal ep : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      let n := lenN ws0
      Bool.rec
        (Bool.rec
          (Bool.rec false
            (forceSepPairs ws0 (fun ps =>
              forceW (orSepAll ps) (fun spAll =>
                (loopA_V4 mask goal ep count bounds states fuel (Nat.sub fuel 1) n spAll ws0 ps hist n 0 (cursors (Nat.add i 1))).1)))
            (Nat.blt n 17))
          true (Nat.beq fuel 0))
        false (memN goal ws0))

def stepRootV4 (mask goal ep count fuel : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  Bool.rec
    (match cur with
     | (t, code) :: tl =>
       Bool.rec
         (closeFallbackV4 mask goal ep bounds (fuel, ws, []) (orSep ws), cur)
         (Bool.rec
           (match nthBound bounds (Nat.shiftRight code 1) with
            | none => (false, tl)
            | some b => (boundClosesF (fuel, ws, []) b, tl))
           (let dest := Nat.shiftRight code 1
            let ok := Bool.rec false
              (match states dest with
               | none => false
               | some saved => Bool.rec false (eqListN saved.2.1 ws) (Nat.beq saved.1 fuel))
              (Nat.blt dest count)
            (ok, tl))
           (Nat.beq (Nat.land code 1) 0))
         (Nat.beq tok t)
     | [] =>
       (closeFallbackV4 mask goal ep bounds (fuel, ws, []) (orSep ws), []))
    (true, cur) (Nat.blt (Nat.add fuel 1) (lenN ws))

def loopRootsV4 (mask goal ep count fuel : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, tok, cur =>
    let ws := subsetWordsF stock tok
    let (ok, cur1) := stepRootV4 mask goal ep count fuel bounds states ws tok cur
    Bool.rec (false, cur1) (loopRootsV4 mask goal ep count fuel bounds states stock rem (Nat.add tok 1) cur1) ok

def dagCheckRootsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (stock : List Nat) (fuel : Nat) : Bool :=
  (loopRootsV4 mask goal ep count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur).1

theorem loopRootsV4_at {mask goal ep count fuel : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok : Nat} {cur : List (Nat × Nat)}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (h : (loopRootsV4 mask goal ep count fuel bounds states stock rem t0 cur).1 = true) :
    ∃ c, (stepRootV4 mask goal ep count fuel bounds states (subsetWordsF stock tok) tok c).1 = true := by
  induction rem generalizing t0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV4 at h; dsimp only at h
    cases hp : stepRootV4 mask goal ep count fuel bounds states (subsetWordsF stock t0) t0 cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : tok = t0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) h

theorem dagAllNodesV4 {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV4 mask goal (edgePack mask goal) bounds count
      (dagTrace mask stock fuel forest) cursors i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV4 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, lenN_eq, memN_eq] at hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hchk; exact Bool.noConfusion hchk
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      cases hcg : ws.contains goal
      · rw [hcg] at hchk; dsimp only at hchk
        have hrem0 : Nat.beq rem 0 = false := beq_false_ne hrem_pos
        rw [hrem0] at hchk; dsimp only at hchk
        cases h17 : Nat.blt ws.length 17
        · rw [h17] at hchk; exact Bool.noConfusion hchk
        · rw [h17] at hchk; dsimp only at hchk
          rw [forceSepPairs_eq, forceW_eq] at hchk
          have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
          have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
          obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
          obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
          have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
          have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
              ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
                ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
                ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
                binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
                LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                  (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
            by_cases hlt : ia0 < ib0
            · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
                by simp only [hlt, ite_true]; exact hea0,
                by simp only [hlt, ite_true]; exact heb0,
                by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
            · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
              have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                  dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
                ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
              exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
                by simp only [hlt, ite_false]; exact heb0,
                by simp only [hlt, ite_false]; exact hea0,
                by rw [hea0, heb0, hopEq],
                by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
          obtain ⟨cA, hB⟩ := loopA_V4_at (a := a) (Nat.zero_le a) (by omega) hchk
          obtain ⟨cB, hO⟩ := loopB_V4_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
          simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
          set x := ws.getD a 0
          set y := ws.getD b 0
          set z := binOp mask op x y
          have hznz : z ≠ 0 := hzeq.symm ▸ hz0
          have hznm : ws.contains z = false := by
            cases h : ws.contains z
            · rfl
            · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
          rcases check4OpsV4_at hop_lt hO with hz' | hcm | ⟨cK, hK⟩
          · exact hznz hz'
          · rw [hznm] at hcm; exact Bool.noConfusion hcm
          · have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
            have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
            have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
            have hzNotW : z ∉ ws := fun hm => by
              have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
            have hdropComm : dropVal true y (dropVal true x ws) = dropVal true x (dropVal true y ws) :=
              dropVal_comm x y ws
            set rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
            have hnd_u : (z :: rest).Nodup :=
              List.nodup_cons.mpr ⟨fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1,
                dropVal_nodup (dropVal_nodup nd)⟩
            have hset_u : (z :: rest).toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
              ext w; simp only [rest, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, ← dropVal_toFinset]
            have hlive_u : LiveBin mask goal k' (z :: rest).toFinset := by rwa [hset_u]
            have hset_s : (insertSorted z rest).toFinset = (z :: rest).toFinset := by
              ext w; simp only [List.mem_toFinset, insertSorted_mem, List.mem_cons]
            have hlive_s : LiveBin mask goal k' (insertSorted z rest).toFinset := by rwa [hset_s]
            have hlen' : (insertSorted z rest).length =
                ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) :=
              list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
            have hcard' : (insertSorted z rest).length ≤ rem := by
              have hnd_s : (insertSorted z rest).Nodup :=
                insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
              have := liveBin_card_le hlive_s
              rw [List.toFinset_card_of_nodup hnd_s] at this; omega
            have h2len : 2 ≤ ws.length := by
              have hsub2 : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
                intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
                · exact List.mem_toFinset.mpr hxM
                · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hyM
              have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
              have hc := Finset.card_le_card hsub2
              rw [List.toFinset_card_of_nodup nd] at hc; omega
            have hka := checkKeepsV4_at hK keepA keepB
            have finish {tok' : Nat} {c' : List (Nat × Nat)}
                (hstep : (stepLeafV4 mask goal (edgePack mask goal) count bounds (dagTrace mask stock fuel forest)
                  (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c').1 = true) : False := by
              obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                stepLeafV4_ref hgm hknown hsub hgoals hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
              exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
            cases keepA <;> cases keepB
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
              · rw [hdropComm] at hst
                exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
              · exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
              · exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
              · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk

theorem lowerDagV4 {mask goal ep fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hep : ep = edgePack mask goal)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsV4 mask goal ep count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV4 mask goal ep bounds count
      (dagTraceF mask stock fuel forest) cursors i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  subst hep
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  unfold dagCheckRootsV4 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  obtain ⟨c, hsr⟩ := loopRootsV4_at (tok := tok) (Nat.zero_le tok) (by omega) hroots
  rw [subsetWordsF_eq] at hsr
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  have hcard : (subsetWords stock tok).length ≤ fuel + 1 := by
    have := liveBin_card_le hlive'
    rw [List.toFinset_card_of_nodup hnd] at this; omega
  have hnw : Nat.blt (Nat.add fuel 1) (lenN (subsetWords stock tok)) = false := by
    rw [lenN_eq]
    cases h : Nat.blt (Nat.add fuel 1) (subsetWords stock tok).length
    · rfl
    · have hlt' : fuel + 1 < (subsetWords stock tok).length := Nat.blt_eq.mp h
      omega
  have hfb := closeFallbackV4_open (st := (fuel, subsetWords stock tok, [])) hgm hknown hsub hgoals hnd (k := k) (by omega) hlive'
  unfold stepRootV4 at hsr
  rw [hnw] at hsr; dsimp only at hsr
  cases c with
  | nil => dsimp only at hsr; rw [hfb] at hsr; exact Bool.noConfusion hsr
  | cons hd tl =>
    obtain ⟨t, code⟩ := hd
    dsimp only at hsr
    cases ht : Nat.beq tok t
    · rw [ht] at hsr; dsimp only at hsr; rw [hfb] at hsr; exact Bool.noConfusion hsr
    · rw [ht] at hsr; dsimp only at hsr
      cases hev : Nat.beq (Nat.land code 1) 0
      · rw [hev] at hsr; dsimp only at hsr
        cases hb : nthBound bounds (Nat.shiftRight code 1) with
        | none => rw [hb] at hsr; exact Bool.noConfusion hsr
        | some b =>
          rw [hb] at hsr; dsimp only at hsr
          have hmem := nthBound_mem hb
          have hg := hgoals b hmem
          rw [boundClosesF_eq hg.1 hg.2] at hsr
          have h0 := boundCloses_sound (state := (fuel, subsetWords stock tok, [])) (hknown b hmem) (hsub b hmem) hnd (k := k) (by omega) hlive'
          rw [h0] at hsr; exact Bool.noConfusion hsr
      · rw [hev] at hsr; dsimp only at hsr
        cases hltc : Nat.blt (Nat.shiftRight code 1) count
        · rw [hltc] at hsr; exact Bool.noConfusion hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest (Nat.shiftRight code 1) with
          | none => rw [htr2] at hsr; exact Bool.noConfusion hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; exact Bool.noConfusion hsr
            · rw [hf] at hsr; dsimp only at hsr
              rw [eqListN_eq, beq_iff_eq] at hsr
              exact dagAllNodesV4 hgm hknown hsub hgoals snd hnodes fuel (Nat.shiftRight code 1) saved
                (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (hsr ▸ hlive')

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    let code := Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask
    unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc)

def unpackCursorV4 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    let entry := Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask
    let sz := Nat.land entry sizeMask
    let off := Nat.shiftRight entry sizeBits
    unpackListAux data off w wMask tokBits tokMask sz []

def m_0 : Nat := 0xaa000000aa
def s_0 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_0 : Nat := 0x20000002a
def ep_0 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
theorem epk_0 : ep_0 = edgePack 0xaa000000aa g_0 := by decide +kernel
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, 0xaa000000aa &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_0] at hb
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV4 m_0 g_0 ep_0 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 (dagCheckNodeV4 m_0 g_0 ep_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0) = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_0 g_0 ep_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0) i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_0 kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0xcc000000cc
def s_1 : List Nat := [0x4400000044, 0xc0000000c, 0xcc]
def g_1 : Nat := 0x40000004c
def ep_1 : Nat := 0x4800000000000000000000000000000000000000040000000800000000000000000000000400000040
theorem epk_1 : ep_1 = edgePack 0xcc000000cc g_1 := by decide +kernel
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, 0xcc000000cc &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_1] at hb
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV4 m_1 g_1 ep_1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 (dagCheckNodeV4 m_1 g_1 ep_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1) = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_1 g_1 ep_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1) i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_1 kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0xf0000000f0
def s_2 : List Nat := [0x5000000050, 0x3000000030, 0xf0]
def g_2 : Nat := 0x1000000070
def ep_2 : Nat := 0x6000000000000000000000000000000000000000000000000000000010000000200000001000000040
theorem epk_2 : ep_2 = edgePack 0xf0000000f0 g_2 := by decide +kernel
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, 0xf0000000f0 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_2] at hb
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV4 m_2 g_2 ep_2 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 (dagCheckNodeV4 m_2 g_2 ep_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2) = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_2 g_2 ep_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2) i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_2 kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0xaa00aa
def s_3 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_3 : Nat := 0x2002a
def ep_3 : Nat := 0x280000000000000000000000000002000800000000000200200000000000000000
theorem epk_3 : ep_3 = edgePack 0xaa00aa g_3 := by decide +kernel
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, 0xaa00aa &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_3] at hb
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV4 m_3 g_3 ep_3 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 (dagCheckNodeV4 m_3 g_3 ep_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3) = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_3 g_3 ep_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3) i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_3 kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0x55005500
def s_4 : List Nat := [0x11001100, 0x5000500, 0x5500]
def g_4 : Nat := 0x1001500
def ep_4 : Nat := 0x14000000000000000000000000000100040000000000010010000000000000000000
theorem epk_4 : ep_4 = edgePack 0x55005500 g_4 := by decide +kernel
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, 0x55005500 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_4] at hb
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV4 m_4 g_4 ep_4 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 (dagCheckNodeV4 m_4 g_4 ep_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4) = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_4 g_4 ep_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4) i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_4 kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0xaa00aa00
def s_5 : List Nat := [0x22002200, 0xa000a00, 0xaa00]
def g_5 : Nat := 0x2002a00
def ep_5 : Nat := 0x28000000000000000000000000000200080000000000020020000000000000000000
theorem epk_5 : ep_5 = edgePack 0xaa00aa00 g_5 := by decide +kernel
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, 0xaa00aa00 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_5] at hb
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV4 m_5 g_5 ep_5 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 (dagCheckNodeV4 m_5 g_5 ep_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5) = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_5 g_5 ep_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5) i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_5 kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0x5500550000000000
def s_6 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_6 : Nat := 0x100150000000000
def ep_6 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
theorem epk_6 : ep_6 = edgePack 0x5500550000000000 g_6 := by decide +kernel
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, 0x5500550000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_6] at hb
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV4 m_6 g_6 ep_6 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 (dagCheckNodeV4 m_6 g_6 ep_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6) = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_6 g_6 ep_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6) i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_6 kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0x5555000000000000
def s_7 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_7 : Nat := 0x115000000000000
def ep_7 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
theorem epk_7 : ep_7 = edgePack 0x5555000000000000 g_7 := by decide +kernel
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, 0x5555000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_7] at hb
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV4 m_7 g_7 ep_7 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 (dagCheckNodeV4 m_7 g_7 ep_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7) = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_7 g_7 ep_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7) i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_7 kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0x3333000000000000
def s_8 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_8 : Nat := 0x113000000000000
def ep_8 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
theorem epk_8 : ep_8 = edgePack 0x3333000000000000 g_8 := by decide +kernel
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, 0x3333000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_8] at hb
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV4 m_8 g_8 ep_8 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 (dagCheckNodeV4 m_8 g_8 ep_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8) = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_8 g_8 ep_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8) i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_8 kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0xf0f000000000000
def s_9 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_9 : Nat := 0x107000000000000
def ep_9 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
theorem epk_9 : ep_9 = edgePack 0xf0f000000000000 g_9 := by decide +kernel
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, 0xf0f000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_9] at hb
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV4 m_9 g_9 ep_9 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9) = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9) i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_9 kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0xff00000000
def s_10 : List Nat := [0x5500000000, 0x3300000000, 0xf00000000]
def g_10 : Nat := 0x1700000000
def ep_10 : Nat := 0x60000000000000012000000000000001400000000
theorem epk_10 : ep_10 = edgePack 0xff00000000 g_10 := by decide +kernel
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, 0xff00000000 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV4 m_10 g_10 ep_10 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 (dagCheckNodeV4 m_10 g_10 ep_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10) = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_10 g_10 ep_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10) i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_10 kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0xff000000000000
def s_11 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_11 : Nat := 0x17000000000000
def ep_11 : Nat := 0x600000000000000120000000000000014000000000000
theorem epk_11 : ep_11 = edgePack 0xff000000000000 g_11 := by decide +kernel
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, 0xff000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV4 m_11 g_11 ep_11 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 (dagCheckNodeV4 m_11 g_11 ep_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11) = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_11 g_11 ep_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11) i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_11 kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xaa00aa00aa00aa
def s_12 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_12 : Nat := 0x200020002002a
def ep_12 : Nat := 0x2800000000000000280000000000000000000200020002000800020002000200200000000000000000
theorem epk_12 : ep_12 = edgePack 0xaa00aa00aa00aa g_12 := by decide +kernel
def bds_12 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_3, s_3, 4, g_3)]
theorem kn_12 : KnownBin bds_12 := by
  intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_0
  · exact lb_3
theorem sub_12 : ∀ b ∈ bds_12, 0xaa00aa00aa00aa &&& b.1 = b.1 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_12 : Nat → List (Nat × Nat) := fun _ => []
def f_12 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV4 m_12 g_12 ep_12 0 bds_12 (dagTraceF m_12 s_12 4 f_12) (cur_12 0) s_12 4 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_12 g_12 ep_12 bds_12 0 (dagTraceF m_12 s_12 4 f_12) cur_12 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_12 : LowerBin m_12 s_12 g_12 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_12 kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xaa00aa00aa00aa00
def s_13 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_13 : Nat := 0x2002a00
def ep_13 : Nat := 0x2002a0000000000000028000000000000000000000000000200080000000000020020000000000000000000
theorem epk_13 : ep_13 = edgePack 0xaa00aa00aa00aa00 g_13 := by decide +kernel
def bds_13 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_13 : ∀ b ∈ bds_13, 0xaa00aa00aa00aa00 &&& b.1 = b.1 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_13 : Nat → List (Nat × Nat) := fun _ => []
def f_13 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV4 m_13 g_13 ep_13 0 bds_13 (dagTraceF m_13 s_13 4 f_13) (cur_13 0) s_13 4 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_13 g_13 ep_13 bds_13 0 (dagTraceF m_13 s_13 4 f_13) cur_13 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_13 kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xcc00cc00cc00cc
def s_14 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_14 : Nat := 0x400040044004c
def ep_14 : Nat := 0x40004800000000000000080000000000000000000400040000000800000000000000000004000400440040
theorem epk_14 : ep_14 = edgePack 0xcc00cc00cc00cc g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_14 : ∀ b ∈ bds_14, 0xcc00cc00cc00cc &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_14 : Nat → List (Nat × Nat) := fun _ => []
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 0 bds_14 (dagTraceF m_14 s_14 4 f_14) (cur_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_14 g_14 ep_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) cur_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xf000f000f000f0
def s_15 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_15 : Nat := 0x10001000500070
def ep_15 : Nat := 0x40006000000000000000200000000000000000000000000000000000100010000000200010001000500040
theorem epk_15 : ep_15 = edgePack 0xf000f000f000f0 g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_15 : ∀ b ∈ bds_15, 0xf000f000f000f0 &&& b.1 = b.1 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_15 : Nat → List (Nat × Nat) := fun _ => []
def f_15 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 0 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) s_15 4 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_15 g_15 ep_15 bds_15 0 (dagTraceF m_15 s_15 4 f_15) cur_15 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xaaaa0000aaaa
def s_16 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_16 : Nat := 0x200002a2a
def ep_16 : Nat := 0x2a2800000000000000000000000200000000000000020000080800000002000020200000000000000000
theorem epk_16 : ep_16 = edgePack 0xaaaa0000aaaa g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_16 : ∀ b ∈ bds_16, 0xaaaa0000aaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_16 : Nat → List (Nat × Nat) := fun _ => []
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 0 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_16 g_16 ep_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) cur_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x5555000055550000
def s_17 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_17 : Nat := 0x115000001550000
def ep_17 : Nat := 0x40000000000000000000000014000000540000010400000100000001100000010000000000000000000000
theorem epk_17 : ep_17 = edgePack 0x5555000055550000 g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_17 : ∀ b ∈ bds_17, 0x5555000055550000 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_17 : Nat → List (Nat × Nat) := fun _ => []
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 0 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_17 g_17 ep_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) cur_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xcccc0000cccc
def s_18 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_18 : Nat := 0x40400000c4c
def ep_18 : Nat := 0x848000000000000000000000000000000400000040400000c0800000000000000000000040400000040
theorem epk_18 : ep_18 = edgePack 0xcccc0000cccc g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_18 : ∀ b ∈ bds_18, 0xcccc0000cccc &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_18 g_18 ep_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0x3333000033330000
def s_19 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_19 : Nat := 0x113000003130000
def ep_19 : Nat := 0x200000000000000000000000012000000100000010200000302000000000000000000000110000000100000
theorem epk_19 : ep_19 = edgePack 0x3333000033330000 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_19 : ∀ b ∈ bds_19, 0x3333000033330000 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_19 : Nat → List (Nat × Nat) := fun _ => []
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 0 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_19 g_19 ep_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) cur_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xf0f00000f0f0
def s_20 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_20 : Nat := 0x101000003070
def ep_20 : Nat := 0x206000000000000000000000000000000040000000000000000000001010000030200000101000000040
theorem epk_20 : ep_20 = edgePack 0xf0f00000f0f0 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_20 : ∀ b ∈ bds_20, 0xf0f00000f0f0 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_20 g_20 ep_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xf0f00000f0f0000
def s_21 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_21 : Nat := 0x107000003070000
def ep_21 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040000
theorem epk_21 : ep_21 = edgePack 0xf0f00000f0f0000 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_21 : ∀ b ∈ bds_21, 0xf0f00000f0f0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_21 g_21 ep_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xff000000ff
def s_22 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_22 : Nat := 0x170000007f
def ep_22 : Nat := 0x6800000000000000000000000000000000000000060000000800000012000000200000001400000040
theorem epk_22 : ep_22 = edgePack 0xff000000ff g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_10, s_10, 4, g_10)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_1
  · exact lb_2
  · exact lb_10
theorem sub_22 : ∀ b ∈ bds_22, 0xff000000ff &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x943282054007c4f81e130c600c0178ad25a0ac9582a13d8780f01d13a0740e09a2304600b89702c22b00c801 0x3e4d236950b4681233c519d07a1c39201a870c5104a30150e2020090388028140fa736935448ad23564a696515826a1c390e151e0983834201654a60710100681c300c0a204d16694a3464d23078f9227a4135449287128f08c1c290e0d04058c4984b480e200a0d038601824141a06090d4945a46291d108d8728c31360e9707128408c1c3a081b07066846f21377093870ed706e1c2b38138706c102e000f 11 2047 4 15 10 1023 17 131071
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc0601d4e068b407430180480200 0xa8a6c2516626b0125a42687125408a1c41681aa6095f2493a4d8522cc8d5e24d284d0e24961143882c0351c0ac41303880f934 9 511 4 15 10 1023 17 131071
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_22_1 (Nat.sub p 32)) (cc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 43 bds_22 (dagTraceF m_22 s_22 6 f_22) (cur_22 0) s_22 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 43 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22) = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22) i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xff000000ff0000
def s_23 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_23 : Nat := 0x17000000570000
def ep_23 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
theorem epk_23 : ep_23 = edgePack 0xff000000ff0000 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_23 : ∀ b ∈ bds_23, 0xff000000ff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0x55555555
def s_24 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_24 : Nat := 0x1551555
def ep_24 : Nat := 0x14000000000000540040000000000100040000000000010010000000000000000000
theorem epk_24 : ep_24 = edgePack 0x55555555 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_24 : ∀ b ∈ bds_24, 0x55555555 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_24 g_24 ep_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0x5555555500000000
def s_25 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_25 : Nat := 0x115151500000000
def ep_25 : Nat := 0x1400000000000014000000000000010404040000000001101010000000000000000000000000
theorem epk_25 : ep_25 = edgePack 0x5555555500000000 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_6
  · exact lb_7
theorem sub_25 : ∀ b ∈ bds_25, 0x5555555500000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_25 g_25 ep_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x3333333300000000
def s_26 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_26 : Nat := 0x113111300000000
def ep_26 : Nat := 0x1000000000000012000200000000010200020000000000000000000000000110111000000000
theorem epk_26 : ep_26 = edgePack 0x3333333300000000 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_26 : ∀ b ∈ bds_26, 0x3333333300000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xf0f0f0f00000000
def s_27 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_27 : Nat := 0x107050700000000
def ep_27 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
theorem epk_27 : ep_27 = edgePack 0xf0f0f0f00000000 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_27 : ∀ b ∈ bds_27, 0xf0f0f0f00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xff00ff
def s_28 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_28 : Nat := 0x57007f
def ep_28 : Nat := 0x280000000000000000000000000002000800000000000200200000000000540040
theorem epk_28 : ep_28 = edgePack 0xff00ff g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_28 : ∀ b ∈ bds_28, 0xff00ff &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xff00ff0000000000
def s_29 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_29 : Nat := 0x100150000000000
def ep_29 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
theorem epk_29 : ep_29 = edgePack 0xff00ff0000000000 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_29 : ∀ b ∈ bds_29, 0xff00ff0000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_29 g_29 ep_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xffff00000000
def s_30 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_30 : Nat := 0x151700000000
def ep_30 : Nat := 0x200000000000004060000000000001012000000000000151400000000
theorem epk_30 : ep_30 = edgePack 0xffff00000000 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_30 : ∀ b ∈ bds_30, 0xffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_30 g_30 ep_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xffff000000000000
def s_31 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_31 : Nat := 0x117000000000000
def ep_31 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_31 : ep_31 = edgePack 0xffff000000000000 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_11, s_11, 4, g_11)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_8
  · exact lb_9
  · exact lb_11
theorem sub_31 : ∀ b ∈ bds_31, 0xffff000000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x945282053e2784f01e030c5c4b09602b1560ac150aa03d8708d11a0322640c09803005c4b81702c22b00c801 0x7c0c0705236850a4280a73c509506260210e0eba064382a101150a0074d0b2601d246da0b49043a9a1d3e4c99074b8a2441c4d641f200c9805c282250a0074d092601d2451a0220b16684aa310ea7265083a7a1d2e20912413900841c3d3c1704088b2801d24249807490b4804a30181e06130d48462320ea7145083a7c41320e968e1385084203e0819070b6846721337091870fd70661c2f38118707c1026000f 11 2047 4 15 10 1023 17 131071
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb85c1b4c1603005411080040000 0x4e506326351297890b610560621c2da41487095004312409da0c28ca627cf13268209a084383b28190e0a8a04624811340 9 511 4 15 10 1023 17 131071
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 43 bds_31 (dagTraceF m_31 s_31 6 f_31) (cur_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0x5555555555555555
def s_32 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_32 : Nat := 0x115151501551555
def ep_32 : Nat := 0x40004000001400000014000014000000540040010404040100040001101010010010000000000000000000
theorem epk_32 : ep_32 = edgePack 0x5555555555555555 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 5, g_17), (m_24, s_24, 5, g_24), (m_25, s_25, 5, g_25), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_24
  · exact lb_25
  · exact lb_4
  · exact lb_6
  · exact lb_7
theorem sub_32 : ∀ b ∈ bds_32, 0x5555555555555555 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV4 0xc06030162a1502633090b903a01 0x6340815c523431345344334464543a3842342134a34f934b734713433a4f3a4b3a473a433a3f3a3b3a373a333926001f 9 511 4 15 11 2047 16 65535
def f_32 : Nat → Nat × Nat := unpackForestF 0x2d3c5a5c15c168e51515a21234368844d05a1801f 4 11
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 11 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 11 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 11 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 11 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xaaaaaaaaaaaaaaaa
def s_33 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_33 : Nat := 0x2000202022a2a
def ep_33 : Nat := 0x2002a2800000000000028280002000200000000000200020202080800020002020220200000000000000000
theorem epk_33 : ep_33 = edgePack 0xaaaaaaaaaaaaaaaa g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 5, g_12), (m_13, s_13, 5, g_13), (m_16, s_16, 5, g_16), (m_0, s_0, 4, g_0), (m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_13
  · exact lb_16
  · exact lb_0
  · exact lb_3
  · exact lb_5
theorem sub_33 : ∀ b ∈ bds_33, 0xaaaaaaaaaaaaaaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_33 : Nat → List (Nat × Nat) := unpackCursorV4 0xc0602e361924824102803883a01 0x5340434033408150485c70505140404034542138a34f934b63471343484f484b48474843483f483b483748334811001f 9 511 4 15 11 2047 16 65535
def f_33 : Nat → Nat × Nat := unpackForestF 0xb4f2d2f950e140b47850204051511382d0c01f 3 11
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 11 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33 : treeBlockF 0 11 (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 11 (dagTraceF m_33 s_33 6 f_33) cur_33) = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 11 (dagTraceF m_33 s_33 6 f_33) cur_33) i = true := fun _ h1 h2 => treeBlockF_at nb_33 h1 h2
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0x3333333333333333
def s_34 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_34 : Nat := 0x113111303133333
def ep_34 : Nat := 0x200222000001000000030200012000200100000010200020302000000000000000000000110111000100000
theorem epk_34 : ep_34 = edgePack 0x3333333333333333 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 5, g_19), (m_26, s_26, 5, g_26), (m_8, s_8, 4, g_8)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl
  · exact lb_19
  · exact lb_26
  · exact lb_8
theorem sub_34 : ∀ b ∈ bds_34, 0x3333333333333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 5 f_34) (cur_34 0) s_34 5 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 5 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xcccccccccccccccc
def s_35 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_35 : Nat := 0x4040400440c4c
def ep_35 : Nat := 0x4008480000040000000c0800040000004400400004040400000c0800000000000000000004040400440040
theorem epk_35 : ep_35 = edgePack 0xcccccccccccccccc g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 5, g_14), (m_18, s_18, 5, g_18), (m_1, s_1, 4, g_1)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl
  · exact lb_14
  · exact lb_18
  · exact lb_1
theorem sub_35 : ∀ b ∈ bds_35, 0xcccccccccccccccc &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 5 f_35) (cur_35 0) s_35 5 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 5 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xf0f0f0f0f0f0f0f
def s_36 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_36 : Nat := 0x107050703070f0f
def ep_36 : Nat := 0x2000a080000040000000c080006000200040000000000000000000001020002030200000104050400040000
theorem epk_36 : ep_36 = edgePack 0xf0f0f0f0f0f0f0f g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 5, g_21), (m_27, s_27, 5, g_27), (m_9, s_9, 4, g_9)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl
  · exact lb_21
  · exact lb_27
  · exact lb_9
theorem sub_36 : ∀ b ∈ bds_36, 0xf0f0f0f0f0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 5 f_36) (cur_36 0) s_36 5 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 5 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xf0f0f0f0f0f0f0f0
def s_37 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_37 : Nat := 0x10101000503070
def ep_37 : Nat := 0x40206000001000000030200010000000500040000000000000000000101010000030200010101000500040
theorem epk_37 : ep_37 = edgePack 0xf0f0f0f0f0f0f0f0 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 5, g_15), (m_20, s_20, 5, g_20), (m_2, s_2, 4, g_2)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl
  · exact lb_15
  · exact lb_20
  · exact lb_2
theorem sub_37 : ∀ b ∈ bds_37, 0xf0f0f0f0f0f0f0f0 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 5 f_37) (cur_37 0) s_37 5 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 5 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xff00ff00ff00ff
def s_38 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_38 : Nat := 0x1700170057007f
def ep_38 : Nat := 0x40006800000000000000280000000000000000000600060002000800120012000200200014001400540040
theorem epk_38 : ep_38 = edgePack 0xff00ff00ff00ff g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_14, s_14, 5, g_14), (m_15, s_15, 5, g_15), (m_12, s_12, 5, g_12), (m_23, s_23, 5, g_23), (m_28, s_28, 5, g_28), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_22
  · exact lb_14
  · exact lb_15
  · exact lb_12
  · exact lb_23
  · exact lb_28
  · exact lb_0
  · exact lb_1
  · exact lb_2
  · exact lb_3
  · exact lb_10
  · exact lb_11
theorem sub_38 : ∀ b ∈ bds_38, 0xff00ff00ff00ff &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 7 f_38) (cur_38 0) s_38 7 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 7 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xff00ff00ff00ff00
def s_39 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_39 : Nat := 0x100150003003f00
def ep_39 : Nat := 0x2002a000000140000003c0000000000000000000100040003000c0001001000030030000100150000000000
theorem epk_39 : ep_39 = edgePack 0xff00ff00ff00ff00 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 5, g_13), (m_29, s_29, 5, g_29), (m_6, s_6, 4, g_6), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_29
  · exact lb_6
  · exact lb_4
  · exact lb_5
theorem sub_39 : ∀ b ∈ bds_39, 0xff00ff00ff00ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 5 f_39) (cur_39 0) s_39 5 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 5 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xffff0000ffff
def s_40 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_40 : Nat := 0x151700003f7f
def ep_40 : Nat := 0x2a68000000000000000000000002000000400000040600000c0800001012000030200000151400000040
theorem epk_40 : ep_40 = edgePack 0xffff0000ffff g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_18, s_18, 5, g_18), (m_20, s_20, 5, g_20), (m_16, s_16, 5, g_16), (m_30, s_30, 5, g_30), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_10, s_10, 4, g_10), (m_0, s_0, 4, g_0)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_22
  · exact lb_18
  · exact lb_20
  · exact lb_16
  · exact lb_30
  · exact lb_1
  · exact lb_2
  · exact lb_10
  · exact lb_0
theorem sub_40 : ∀ b ∈ bds_40, 0xffff0000ffff &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 7 f_40) (cur_40 0) s_40 7 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 7 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xffff0000ffff0000
def s_41 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_41 : Nat := 0x117000003570000
def ep_41 : Nat := 0x240000000000000000000000016000000540000010600000302000001120000030200000114000000540000
theorem epk_41 : ep_41 = edgePack 0xffff0000ffff0000 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31), (m_19, s_19, 5, g_19), (m_21, s_21, 5, g_21), (m_23, s_23, 5, g_23), (m_17, s_17, 5, g_17), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_11, s_11, 4, g_11), (m_7, s_7, 4, g_7)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_31
  · exact lb_19
  · exact lb_21
  · exact lb_23
  · exact lb_17
  · exact lb_8
  · exact lb_9
  · exact lb_11
  · exact lb_7
theorem sub_41 : ∀ b ∈ bds_41, 0xffff0000ffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 7 f_41) (cur_41 0) s_41 7 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 7 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xffffffff
def s_42 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_42 : Nat := 0x3573f7f
def ep_42 : Nat := 0x3c2800000000005400400000000003020c0800000000030230200000000000540040
theorem epk_42 : ep_42 = edgePack 0xffffffff g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 5, g_24), (m_28, s_28, 5, g_28), (m_5, s_5, 4, g_5), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_28
  · exact lb_5
  · exact lb_3
  · exact lb_4
theorem sub_42 : ∀ b ∈ bds_42, 0xffffffff &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 5 f_42) (cur_42 0) s_42 5 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 5 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xffffffff00000000
def s_43 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_43 : Nat := 0x117151700000000
def ep_43 : Nat := 0x1400000000000016000200000000010604060000000001121012000000000114151400000000
theorem epk_43 : ep_43 = edgePack 0xffffffff00000000 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_25, s_25, 5, g_25), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_31
  · exact lb_26
  · exact lb_27
  · exact lb_29
  · exact lb_30
  · exact lb_25
  · exact lb_6
  · exact lb_7
  · exact lb_8
  · exact lb_9
  · exact lb_10
  · exact lb_11
theorem sub_43 : ∀ b ∈ bds_43, 0xffffffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 7 f_43) (cur_43 0) s_43 7 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 7 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def g_44 : Nat := 0x117151703573f7f
def ep_44 : Nat := 0x2402a680000140000003c2800160002005400400106040603020c0801121012030230200114151400540040
theorem epk_44 : ep_44 = edgePack fullMask g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_38, s_38, 8, g_38), (m_40, s_40, 8, g_40), (m_41, s_41, 8, g_41), (m_43, s_43, 8, g_43), (m_32, s_32, 7, g_32), (m_33, s_33, 7, g_33), (m_22, s_22, 7, g_22), (m_31, s_31, 7, g_31), (m_34, s_34, 6, g_34), (m_39, s_39, 6, g_39), (m_35, s_35, 6, g_35), (m_36, s_36, 6, g_36), (m_42, s_42, 6, g_42), (m_37, s_37, 6, g_37), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_13, s_13, 5, g_13), (m_14, s_14, 5, g_14), (m_15, s_15, 5, g_15), (m_16, s_16, 5, g_16), (m_17, s_17, 5, g_17)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_38
  · exact lb_40
  · exact lb_41
  · exact lb_43
  · exact lb_32
  · exact lb_33
  · exact lb_22
  · exact lb_31
  · exact lb_34
  · exact lb_39
  · exact lb_35
  · exact lb_36
  · exact lb_42
  · exact lb_37
  · exact lb_26
  · exact lb_27
  · exact lb_28
  · exact lb_29
  · exact lb_30
  · exact lb_13
  · exact lb_14
  · exact lb_15
  · exact lb_16
  · exact lb_17
theorem sub_44 : ∀ b ∈ bds_44, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_44 : Nat → List (Nat × Nat) := unpackCursorV4 0x317194c58b24b5c6720160001 0x5d6f4d6b4d675d635c6f5c6e4c6b4c6a4c674c665c635c62ac5fac5eac5d5b6f4b6b4b675b638b5b8b5abb598b578b56ab53ab518b478b468b45386f386b38673863385f385b38573853384f384d384b38493847384538433841383f383b383738335d6f4d6b4d675d635c6f4c6b4c675c638c5f8c5ebc5d8c578c558c538c525b6f5b6e4b6b4b6a4b674b665b635b628b578b568b558b4fab4e8b4d386f386b38673863385f385b38573853384f384b38473843383f383d383b383938373835383338315d6f5d6e4d6b4d6a4d674d665d635d625c6f4c6b4c675c638c5f8c5e8c5d5b6f4b6b4b675b638b5f8b5eab5d8b4f8b4e8b4b8b498b438b42bb412340386f386b38673863385f385d385b38593857385538533851384f384b38473843383f383b383738335c5f4c5b4c575c535b5f4b5b4b575b538b4f8b4eab4d385f385b38573853384f384b38473843383f383b383738335d6f4d6b4d675d635c6f4c6b4c675c63ac5fac5d8c5b8c5a8c578c56bc5524545b6f5b6e4b6b4b6a4b674b665b635b62ab5fab5eab5d8b4f8b4e8b4d386f386b38673863385f385b38573853384f384b38473843383f383d383b383938373835383338315c5f4c5b4c575c535b5f4b5b4b575b53534f434b33471343385f385b38573853384f384b38473843383f383b38373833003f 14 16383 6 63 11 2047 16 65535
def f_44 : Nat → Nat × Nat := unpackForestF 0x169eb4b5a3d15168603f 2 11
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 fullMask g_44 ep_44 6 bds_44 (dagTraceF fullMask rootStock 9 f_44) (cur_44 0) rootStock 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44 : treeBlockF 0 6 (dagCheckNodeV4 fullMask g_44 ep_44 bds_44 6 (dagTraceF fullMask rootStock 9 f_44) cur_44) = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 6 → (dagCheckNodeV4 fullMask g_44 ep_44 bds_44 6 (dagTraceF fullMask rootStock 9 f_44) cur_44) i = true := fun _ h1 h2 => treeBlockF_at nb_44 h1 h2
theorem lb_44 : LowerBin fullMask rootStock g_44 10 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def wg : List Gate := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [2, 1]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [11, 8]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.or, [14, 7]⟩, ⟨GateOp.and, [15, 13]⟩]
theorem wfits : Monotone2 ⟨wg, 16⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 16⟩ (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4238917760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677352 * 2 ^ 32 + 4238917760)) (11 - 1) := by
  rw [show canon fullMask (4276677352 * 2 ^ 32 + 4238917760) = g_44 by decide]
  exact lb_44

end PEqualNP.Outside.L_meta_45401

theorem PEqualNP.Outside.L_meta_45401 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4238917760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4238917760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_45401.table2_from_lowerBin (4276677352 * 2 ^ 32 + 4238917760) 11 PEqualNP.Outside.L_meta_45401.root_lb PEqualNP.Outside.L_meta_45401.wg 16 rfl PEqualNP.Outside.L_meta_45401.wfits PEqualNP.Outside.L_meta_45401.weval
