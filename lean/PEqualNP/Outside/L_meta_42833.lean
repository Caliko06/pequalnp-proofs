import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42833

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

def m_0 : Nat := 0x5500000055000000
def s_0 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_0 : Nat := 0x100000015000000
def ep_0 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
theorem epk_0 : ep_0 = edgePack 0x5500000055000000 g_0 := by decide +kernel
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, 0x5500000055000000 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
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

def m_1 : Nat := 0x3300000033000000
def s_1 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_1 : Nat := 0x100000013000000
def ep_1 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
theorem epk_1 : ep_1 = edgePack 0x3300000033000000 g_1 := by decide +kernel
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, 0x3300000033000000 &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
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

def m_2 : Nat := 0xf0000000f000000
def s_2 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_2 : Nat := 0x100000007000000
def ep_2 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
theorem epk_2 : ep_2 = edgePack 0xf0000000f000000 g_2 := by decide +kernel
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, 0xf0000000f000000 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
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

def m_3 : Nat := 0x4444444400000000
def s_3 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_3 : Nat := 0x4044400000000
def ep_3 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
theorem epk_3 : ep_3 = edgePack 0x4444444400000000 g_3 := by decide +kernel
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, 0x4444444400000000 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
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

def m_4 : Nat := 0x5050505000000000
def s_4 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_4 : Nat := 0x10105000000000
def ep_4 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
theorem epk_4 : ep_4 = edgePack 0x5050505000000000 g_4 := by decide +kernel
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, 0x5050505000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
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

def m_5 : Nat := 0x5500550000000000
def s_5 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_5 : Nat := 0x100150000000000
def ep_5 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
theorem epk_5 : ep_5 = edgePack 0x5500550000000000 g_5 := by decide +kernel
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, 0x5500550000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
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

def m_6 : Nat := 0x3300330000000000
def s_6 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_6 : Nat := 0x100130000000000
def ep_6 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
theorem epk_6 : ep_6 = edgePack 0x3300330000000000 g_6 := by decide +kernel
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, 0x3300330000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
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

def m_7 : Nat := 0xf000f0000000000
def s_7 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_7 : Nat := 0x100070000000000
def ep_7 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
theorem epk_7 : ep_7 = edgePack 0xf000f0000000000 g_7 := by decide +kernel
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, 0xf000f0000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
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

def m_8 : Nat := 0x5555000000000000
def s_8 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_8 : Nat := 0x115000000000000
def ep_8 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
theorem epk_8 : ep_8 = edgePack 0x5555000000000000 g_8 := by decide +kernel
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, 0x5555000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
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

def m_9 : Nat := 0x3333000000000000
def s_9 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_9 : Nat := 0x113000000000000
def ep_9 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
theorem epk_9 : ep_9 = edgePack 0x3333000000000000 g_9 := by decide +kernel
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, 0x3333000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
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

def m_10 : Nat := 0xf0f000000000000
def s_10 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_10 : Nat := 0x107000000000000
def ep_10 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
theorem epk_10 : ep_10 = edgePack 0xf0f000000000000 g_10 := by decide +kernel
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, 0xf0f000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
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

def m_11 : Nat := 0xff00
def s_11 : List Nat := [0x5500, 0x3300, 0xf00]
def g_11 : Nat := 0x1700
def ep_11 : Nat := 0x60000000000000012000000000000001400
theorem epk_11 : ep_11 = edgePack 0xff00 g_11 := by decide +kernel
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, 0xff00 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
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

def m_12 : Nat := 0xff0000
def s_12 : List Nat := [0x550000, 0x330000, 0xf0000]
def g_12 : Nat := 0x170000
def ep_12 : Nat := 0x6000000000000001200000000000000140000
theorem epk_12 : ep_12 = edgePack 0xff0000 g_12 := by decide +kernel
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, 0xff0000 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV4 m_12 g_12 ep_12 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 (dagCheckNodeV4 m_12 g_12 ep_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12) = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_12 g_12 ep_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12) i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_12 kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xff000000
def s_13 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_13 : Nat := 0x17000000
def ep_13 : Nat := 0x600000000000000120000000000000014000000
theorem epk_13 : ep_13 = edgePack 0xff000000 g_13 := by decide +kernel
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_13 : KnownBin bds_13 := by intro b hb; simp [bds_13] at hb
theorem sub_13 : ∀ b ∈ bds_13, 0xff000000 &&& b.1 = b.1 := by intro b hb; simp [bds_13] at hb
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_13] at hb
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV4 m_13 g_13 ep_13 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 (dagCheckNodeV4 m_13 g_13 ep_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13) = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_13 g_13 ep_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13) i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_13 kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xff0000000000
def s_14 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_14 : Nat := 0x170000000000
def ep_14 : Nat := 0x6000000000000001200000000000000140000000000
theorem epk_14 : ep_14 = edgePack 0xff0000000000 g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, 0xff0000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14) = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14) i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xff000000000000
def s_15 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_15 : Nat := 0x17000000000000
def ep_15 : Nat := 0x600000000000000120000000000000014000000000000
theorem epk_15 : ep_15 = edgePack 0xff000000000000 g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, 0xff000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15) = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15) i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0x4444444444444444
def s_16 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_16 : Nat := 0x4044404040444
def ep_16 : Nat := 0x400000000000440000000400004004000000040000404000404040000000000000000000000000000000000
theorem epk_16 : ep_16 = edgePack 0x4444444444444444 g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_16 : ∀ b ∈ bds_16, 0x4444444444444444 &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_16 : Nat → List (Nat × Nat) := fun _ => []
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 0 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_16 g_16 ep_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) cur_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x5050505050505050
def s_17 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_17 : Nat := 0x10105010101050
def ep_17 : Nat := 0x1000000000001040000000400010004000000040000000000000000000101000101010000000000000000000
theorem epk_17 : ep_17 = edgePack 0x5050505050505050 g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_17 : ∀ b ∈ bds_17, 0x5050505050505050 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_17 : Nat → List (Nat × Nat) := fun _ => []
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 0 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_17 g_17 ep_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) cur_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0x5500550055005500
def s_18 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_18 : Nat := 0x100150015001500
def ep_18 : Nat := 0x1400000000001400000000000000000000000000010004000400040001001000100010000000000000000000
theorem epk_18 : ep_18 = edgePack 0x5500550055005500 g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_5, s_5, 4, g_5)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_0
  · exact lb_5
theorem sub_18 : ∀ b ∈ bds_18, 0x5500550055005500 &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_18 g_18 ep_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0x3300330033003300
def s_19 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_19 : Nat := 0x100130013001300
def ep_19 : Nat := 0x1200000000001200000000000000000000000000010002000200020000000000000000000100100010001000
theorem epk_19 : ep_19 = edgePack 0x3300330033003300 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_6, s_6, 4, g_6)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_1
  · exact lb_6
theorem sub_19 : ∀ b ∈ bds_19, 0x3300330033003300 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_19 : Nat → List (Nat × Nat) := fun _ => []
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 0 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_19 g_19 ep_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) cur_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xf000f000f000f00
def s_20 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_20 : Nat := 0x100070007000700
def ep_20 : Nat := 0x600000000000600000000000000000000000000000000000000000001000200020002000100040004000400
theorem epk_20 : ep_20 = edgePack 0xf000f000f000f00 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_2
  · exact lb_7
theorem sub_20 : ∀ b ∈ bds_20, 0xf000f000f000f00 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_20 g_20 ep_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0x5555000055550000
def s_21 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_21 : Nat := 0x115000015150000
def ep_21 : Nat := 0x1400000000000000000000000014000000000000010400000404000001100000101000000000000000000000
theorem epk_21 : ep_21 = edgePack 0x5555000055550000 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_8, s_8, 4, g_8)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_0
  · exact lb_8
theorem sub_21 : ∀ b ∈ bds_21, 0x5555000055550000 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_21 g_21 ep_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0x3333000033330000
def s_22 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_22 : Nat := 0x113000013130000
def ep_22 : Nat := 0x1200000000000000000000000012000000000000010200000202000000000000000000000110000010100000
theorem epk_22 : ep_22 = edgePack 0x3333000033330000 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_9, s_9, 4, g_9)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_1
  · exact lb_9
theorem sub_22 : ∀ b ∈ bds_22, 0x3333000033330000 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_22 g_22 ep_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xf0f00000f0f0000
def s_23 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_23 : Nat := 0x107000007070000
def ep_23 : Nat := 0x600000000000000000000000006000000000000000000000000000001020000020200000104000004040000
theorem epk_23 : ep_23 = edgePack 0xf0f00000f0f0000 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_10, s_10, 4, g_10)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_2
  · exact lb_10
theorem sub_23 : ∀ b ∈ bds_23, 0xf0f00000f0f0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xff000000ff000000
def s_24 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_24 : Nat := 0x100000017000000
def ep_24 : Nat := 0x1600000000000000000000000000000000000000010000000600000001000000120000000100000014000000
theorem epk_24 : ep_24 = edgePack 0xff000000ff000000 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_13, s_13, 4, g_13)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_1
  · exact lb_2
  · exact lb_13
theorem sub_24 : ∀ b ∈ bds_24, 0xff000000ff000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_24_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x945282053e2784f01e030c5c4b09602b1560ac150aa03d8708d11a0322640c09803005c4b81702c22b00c801 0x7c0c0705236850a4280a73c509506260210e0eba064382a101150a0074d0b2601d246da0b49043a9a1d3e4c99074b8a2441c4d641f200c9805c282250a0074d092601d2451a0220b16684aa310ea7265083a7a1d2e20912413900841c3d3c1704088b2801d24249807490b4804a30181e06130d48462320ea7145083a7c41320e968e1385084203e0819070b6846721337091870fd70661c2f38118707c1026000f 11 2047 4 15 10 1023 17 131071
def cc_24_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb85c1b4c1603005411080040000 0x4e506326351297890b610560621c2da41487095004312409da0c28ca627cf13268209a084383b28190e0a8a04624811340 9 511 4 15 10 1023 17 131071
def cur_24 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_24_1 (Nat.sub p 32)) (cc_24_0 p) (Nat.blt p 32)
def f_24 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 43 bds_24 (dagTraceF m_24 s_24 6 f_24) (cur_24 0) s_24 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_0 : treeBlockF 0 32 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_1 : treeBlockF 32 43 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) = true := by decide +kernel
theorem nj_24_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_24_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_24_1 h1 h2)
theorem nc_24 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) i = true := nj_24_1
theorem lb_24 : LowerBin m_24 s_24 g_24 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0x5555555500000000
def s_25 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_25 : Nat := 0x115155500000000
def ep_25 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_25 : ep_25 = edgePack 0x5555555500000000 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_8, s_8, 4, g_8)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_4
  · exact lb_5
  · exact lb_8
theorem sub_25 : ∀ b ∈ bds_25, 0x5555555500000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x943282054007c4f81e130c600c0178ad25a0ac9582a13d8780f01d13a0740e09a2304600b89702c22b00c801 0x3e4d236950b4681233c519d07a1c39201a870c5104a30150e2020090388028140fa736935448ad23564a696515826a1c390e151e0983834201654a60710100681c300c0a204d16694a3464d23078f9227a4135449287128f08c1c290e0d04058c4984b480e200a0d038601824141a06090d4945a46291d108d8728c31360e9707128408c1c3a081b07066846f21377093870ed706e1c2b38138706c102e000f 11 2047 4 15 10 1023 17 131071
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc0601d4e068b407430180480200 0xa8a6c2516626b0125a42687125408a1c41681aa6095f2493a4d8522cc8d5e24d284d0e24961143882c0351c0ac41303880f934 9 511 4 15 10 1023 17 131071
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 43 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 43 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x3333333300000000
def s_26 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_26 : Nat := 0x113131300000000
def ep_26 : Nat := 0x1200000000000012000000000000010202020000000000000000000000000110101000000000
theorem epk_26 : ep_26 = edgePack 0x3333333300000000 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_9, s_9, 4, g_9)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_6
  · exact lb_9
theorem sub_26 : ∀ b ∈ bds_26, 0x3333333300000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xcccccccc00000000
def s_27 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_27 : Nat := 0x4044400000000
def ep_27 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_27 : ep_27 = edgePack 0xcccccccc00000000 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_27 : ∀ b ∈ bds_27, 0xcccccccc00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf0f0f0f00000000
def s_28 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_28 : Nat := 0x107070700000000
def ep_28 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
theorem epk_28 : ep_28 = edgePack 0xf0f0f0f00000000 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_10, s_10, 4, g_10)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_7
  · exact lb_10
theorem sub_28 : ∀ b ∈ bds_28, 0xf0f0f0f00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xf0f0f0f000000000
def s_29 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_29 : Nat := 0x10105000000000
def ep_29 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
theorem epk_29 : ep_29 = edgePack 0xf0f0f0f000000000 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_29 : ∀ b ∈ bds_29, 0xf0f0f0f000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_29 g_29 ep_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff00ff
def s_30 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_30 : Nat := 0x170057
def ep_30 : Nat := 0x400000000000000000000000000006000200000000001200020000000000140054
theorem epk_30 : ep_30 = edgePack 0xff00ff g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_30 : ∀ b ∈ bds_30, 0xff00ff &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_30 g_30 ep_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xff00ff00000000
def s_31 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_31 : Nat := 0x17005700000000
def ep_31 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
theorem epk_31 : ep_31 = edgePack 0xff00ff00000000 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_31 : ∀ b ∈ bds_31, 0xff00ff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xff00ff0000000000
def s_32 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_32 : Nat := 0x100170000000000
def ep_32 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_32 : ep_32 = edgePack 0xff00ff0000000000 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_14, s_14, 4, g_14)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_6
  · exact lb_7
  · exact lb_14
theorem sub_32 : ∀ b ∈ bds_32, 0xff00ff0000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x945282053e2784f01e030c5c4b09602b1560ac150aa03d8708d11a0322640c09803005c4b81702c22b00c801 0x7c0c0705236850a4280a73c509506260210e0eba064382a101150a0074d0b2601d246da0b49043a9a1d3e4c99074b8a2441c4d641f200c9805c282250a0074d092601d2451a0220b16684aa310ea7265083a7a1d2e20912413900841c3d3c1704088b2801d24249807490b4804a30181e06130d48462320ea7145083a7c41320e968e1385084203e0819070b6846721337091870fd70661c2f38118707c1026000f 11 2047 4 15 10 1023 17 131071
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb85c1b4c1603005411080040000 0x4e506326351297890b610560621c2da41487095004312409da0c28ca627cf13268209a084383b28190e0a8a04624811340 9 511 4 15 10 1023 17 131071
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xffff
def s_33 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_33 : Nat := 0x1757
def ep_33 : Nat := 0x40000000000000060200000000000012020000000000001454
theorem epk_33 : ep_33 = edgePack 0xffff g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_33 : ∀ b ∈ bds_33, 0xffff &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xffff00000000
def s_34 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_34 : Nat := 0x175700000000
def ep_34 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
theorem epk_34 : ep_34 = edgePack 0xffff00000000 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_34 : ∀ b ∈ bds_34, 0xffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xffff000000000000
def s_35 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_35 : Nat := 0x117000000000000
def ep_35 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_35 : ep_35 = edgePack 0xffff000000000000 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10), (m_15, s_15, 4, g_15)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_9
  · exact lb_10
  · exact lb_15
theorem sub_35 : ∀ b ∈ bds_35, 0xffff000000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x945282053e2784f01e030c5c4b09602b1560ac150aa03d8708d11a0322640c09803005c4b81702c22b00c801 0x7c0c0705236850a4280a73c509506260210e0eba064382a101150a0074d0b2601d246da0b49043a9a1d3e4c99074b8a2441c4d641f200c9805c282250a0074d092601d2451a0220b16684aa310ea7265083a7a1d2e20912413900841c3d3c1704088b2801d24249807490b4804a30181e06130d48462320ea7145083a7c41320e968e1385084203e0819070b6846721337091870fd70661c2f38118707c1026000f 11 2047 4 15 10 1023 17 131071
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb85c1b4c1603005411080040000 0x4e506326351297890b610560621c2da41487095004312409da0c28ca627cf13268209a084383b28190e0a8a04624811340 9 511 4 15 10 1023 17 131071
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_35_1 (Nat.sub p 32)) (cc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 43 bds_35 (dagTraceF m_35 s_35 6 f_35) (cur_35 0) s_35 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 43 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0x5555555555555555
def s_36 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_36 : Nat := 0x115155515151555
def ep_36 : Nat := 0x1400000000001440000000400014004000000040010404000404040001101000101010000000000000000000
theorem epk_36 : ep_36 = edgePack 0x5555555555555555 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25), (m_17, s_17, 5, g_17), (m_18, s_18, 5, g_18), (m_21, s_21, 5, g_21), (m_16, s_16, 5, g_16), (m_0, s_0, 4, g_0), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_8, s_8, 4, g_8)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_25
  · exact lb_17
  · exact lb_18
  · exact lb_21
  · exact lb_16
  · exact lb_0
  · exact lb_3
  · exact lb_4
  · exact lb_5
  · exact lb_8
theorem sub_36 : ∀ b ∈ bds_36, 0x5555555555555555 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 7 f_36) (cur_36 0) s_36 7 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 7 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0x3333333333333333
def s_37 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_37 : Nat := 0x113131313131313
def ep_37 : Nat := 0x1200000000001200000000000012000000000000010202020202020200000000000000000110101010101010
theorem epk_37 : ep_37 = edgePack 0x3333333333333333 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 5, g_19), (m_22, s_22, 5, g_22), (m_26, s_26, 5, g_26), (m_1, s_1, 4, g_1), (m_6, s_6, 4, g_6), (m_9, s_9, 4, g_9)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_22
  · exact lb_26
  · exact lb_1
  · exact lb_6
  · exact lb_9
theorem sub_37 : ∀ b ∈ bds_37, 0x3333333333333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 5 f_37) (cur_37 0) s_37 5 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 5 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xcccccccccccccccc
def s_38 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_38 : Nat := 0x4044404040444
def ep_38 : Nat := 0x400000000000440000000400004004000000040000404000404040000000000000000000004044404040444
theorem epk_38 : ep_38 = edgePack 0xcccccccccccccccc g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 5, g_16), (m_27, s_27, 5, g_27), (m_3, s_3, 4, g_3)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl
  · exact lb_16
  · exact lb_27
  · exact lb_3
theorem sub_38 : ∀ b ∈ bds_38, 0xcccccccccccccccc &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 5 f_38) (cur_38 0) s_38 5 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 5 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xf0f0f0f0f0f0f0f
def s_39 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_39 : Nat := 0x107070707070707
def ep_39 : Nat := 0x600000000000600000000000006000000000000000000000000000001020202020202020104040404040404
theorem epk_39 : ep_39 = edgePack 0xf0f0f0f0f0f0f0f g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 5, g_20), (m_23, s_23, 5, g_23), (m_28, s_28, 5, g_28), (m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7), (m_10, s_10, 4, g_10)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_23
  · exact lb_28
  · exact lb_2
  · exact lb_7
  · exact lb_10
theorem sub_39 : ∀ b ∈ bds_39, 0xf0f0f0f0f0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 5 f_39) (cur_39 0) s_39 5 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 5 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xf0f0f0f0f0f0f0f0
def s_40 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_40 : Nat := 0x10105010101050
def ep_40 : Nat := 0x1000000000001040000000400010004000000040000000000000000000101000101010000010105010101050
theorem epk_40 : ep_40 = edgePack 0xf0f0f0f0f0f0f0f0 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 5, g_17), (m_29, s_29, 5, g_29), (m_4, s_4, 4, g_4)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl
  · exact lb_17
  · exact lb_29
  · exact lb_4
theorem sub_40 : ∀ b ∈ bds_40, 0xf0f0f0f0f0f0f0f0 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 5 f_40) (cur_40 0) s_40 5 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 5 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xff00ff00ff00ff00
def s_41 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_41 : Nat := 0x100170017001700
def ep_41 : Nat := 0x1600000000001600000000000000000000000000010006000600060001001200120012000100140014001400
theorem epk_41 : ep_41 = edgePack 0xff00ff00ff00ff00 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24), (m_32, s_32, 7, g_32), (m_20, s_20, 5, g_20), (m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_7, s_7, 4, g_7), (m_11, s_11, 4, g_11), (m_13, s_13, 4, g_13), (m_14, s_14, 4, g_14), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_32
  · exact lb_20
  · exact lb_18
  · exact lb_19
  · exact lb_7
  · exact lb_11
  · exact lb_13
  · exact lb_14
  · exact lb_0
  · exact lb_1
  · exact lb_2
  · exact lb_5
  · exact lb_6
theorem sub_41 : ∀ b ∈ bds_41, 0xff00ff00ff00ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 7 f_41) (cur_41 0) s_41 7 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 7 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xffff0000ffff0000
def s_42 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_42 : Nat := 0x117000017170000
def ep_42 : Nat := 0x1600000000000000000000000016000000000000010600000606000001120000121200000114000014140000
theorem epk_42 : ep_42 = edgePack 0xffff0000ffff0000 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24), (m_35, s_35, 7, g_35), (m_23, s_23, 5, g_23), (m_21, s_21, 5, g_21), (m_22, s_22, 5, g_22), (m_10, s_10, 4, g_10), (m_12, s_12, 4, g_12), (m_13, s_13, 4, g_13), (m_15, s_15, 4, g_15), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_35
  · exact lb_23
  · exact lb_21
  · exact lb_22
  · exact lb_10
  · exact lb_12
  · exact lb_13
  · exact lb_15
  · exact lb_0
  · exact lb_1
  · exact lb_2
  · exact lb_8
  · exact lb_9
theorem sub_42 : ∀ b ∈ bds_42, 0xffff0000ffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 7 f_42) (cur_42 0) s_42 7 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 7 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xffffffff
def s_43 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_43 : Nat := 0x17171757
def ep_43 : Nat := 0x400000000000000040000000000606060200000000121212020000000014141454
theorem epk_43 : ep_43 = edgePack 0xffffffff g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 5, g_30), (m_33, s_33, 5, g_33), (m_13, s_13, 4, g_13), (m_11, s_11, 4, g_11), (m_12, s_12, 4, g_12)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_30
  · exact lb_33
  · exact lb_13
  · exact lb_11
  · exact lb_12
theorem sub_43 : ∀ b ∈ bds_43, 0xffffffff &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 5 f_43) (cur_43 0) s_43 5 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 5 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xffffffff00000000
def s_44 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_44 : Nat := 0x117175700000000
def ep_44 : Nat := 0x1640000000000016004000000000010606020000000001121202000000000114145400000000
theorem epk_44 : ep_44 = edgePack 0xffffffff00000000 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25), (m_32, s_32, 7, g_32), (m_35, s_35, 7, g_35), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_31, s_31, 5, g_31), (m_26, s_26, 5, g_26), (m_34, s_34, 5, g_34), (m_27, s_27, 5, g_27), (m_15, s_15, 4, g_15), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10), (m_14, s_14, 4, g_14)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_25
  · exact lb_32
  · exact lb_35
  · exact lb_28
  · exact lb_29
  · exact lb_31
  · exact lb_26
  · exact lb_34
  · exact lb_27
  · exact lb_15
  · exact lb_3
  · exact lb_4
  · exact lb_5
  · exact lb_6
  · exact lb_7
  · exact lb_8
  · exact lb_9
  · exact lb_10
  · exact lb_14
theorem sub_44 : ∀ b ∈ bds_44, 0xffffffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_44_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x91a9114a1c1c3028487090212040487822ca998a2b1406202c2097052e005a08b30546823d43ea47a0cf011d433a807500da417111b4c14880298001 0x6b4f01ed3807b4302ad080aa4f02a90c07a3f01a8ec06a3701e8cc0a94e02213c0884301e0fc0783e0220f40882f0220ac0882702208c05b4a01ed240cb48016d1805b4101693406a450165341194503a4f4079350161440583e0160b8058290220880582102a0801b2500608c00393400e8d00694406d1401814001a4d01914e060508058390160c4058290160840581901604407c5e07114805a5e06894805a4e01692407a420169041724001a8e805a3600e534039450160e4058310160640581101b17c07c5e01f14c2645201ad7c0db5309497c1f25301e93c0ea4d01a92c06a4701e91407a430368fc06a3b01a8dc0da3301657c0795301653c0794e0164fc0793e01a4ec0793901e4cc0893201e4c41e1300164bc0792b01649c079230741780784e01a0d81602600ed7006b5001ad200b9200161700492003cd4004820038d800db5804cd2003b4404892003a440445200594402e4800584400ed1003a4403c5200b93003a5700e45100ed7403a5d01a92806a4601e5440493e01e4e40493201e4c40b93001e4a40792101c118038360340b80bb4f02ed0c03a4f01e93807a4302e90803a3f01e8ec03a3701e8cc0b94e01213c048430120fc0483b0120dc048330120bc0782e0120b405b4d042d1405a4a01e9240ca4801691805a410368e807a3600e534039450161440482e012078058190120480581102e040082500148c00393400e8d0069440211400514001a4d00614e014508058390160c4058290160840581901604405c5e02514807a5e01c94805a4e01692405a4201e9040424001a8e806a3600e534039450160e4058310160640581105117c1045300ed7c07b5e01ed4c0c35200ed3c07b4b036d2803b4701ed1807b4300e97c0ea5300e93c0ea4b00e91c0ea4301657c0795301653c0794b01651c079430164fc0493e0164bc0492e00e4ac0792901e48c0492201e4840b1200281780304601e0f80382662517d7e4535e8d7d6f35359cd3d5e34b560d1d3034301697d2425e47c94cd925201693cd824e33c92cbf24a01691cae24628490c9f2420168fc9e23e2388ec7e23a0168dc6d2361608cc5623212c578401460d44d82805e05411802036fb8d3fd5343f4093fb7243ea48ff9523be1c8df53233d0453f3313fbac4dedb12fa3849e7204f96c0fe030377a80bd8d02700405c0001f 15 32767 6 63 11 2047 22 4194303
def cc_44_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe603941e30b64ad903544d407110b0522a68a021068401f867d05dc67701d817409ac959491d2278098116404450d103400c043000a0800a 0x12483a35012483936042d63e3480ed13d2480e913c14816510b9201e1103b440e913a1482e4c0995ce51443b5d0e9746a4a1a9185951124f85939124c859312e4c0592916485a0460e0db802e2ed3cbb430e93c5a4e1690cba420e8fc5a3b0e8dc5a331253c4943124fc493b124dc4933124bc592e124b4b84efd17fb4530ed7c5b5e16d4f73520ed3c5b4b42d283b4716d185b430e97d1a530e93d1a4b0e91d1a431657c59531653c594b1651c5943164fc493e164bc492e0e4ac59291648c4922164876120a41796046160f838261ed70fb54d04e059342e48058341e970fa542a5032128164905824b88c03c5c0f152d23016533014016112e130224c04920b4d12c26c1e970fa54225004930124b04920160907b4a16d24fb4816d185b411a9346a451e534e945464f4593516144583e160b858292208858212a0807b4d36d147a4a16924fa48169185a41428e85a360e534394516144482e1207858191204858112e0407b4f1ed347b4b1ed1cdb451ed0c7a4f1e9347a4b1e91cea451e90f323fc48eef237ac8cc7951164fc793e1e4ec59371e4cca932164bc792e1e4ac59271e48cb9221e11aa036a4098da5c1b1746b5d909443a3d0e8d479511e53879492250879412a50079391e4c468469c0f9c0260f1703c500e930a930161706a540e910a950844a0893085140883091580eb5c8c9706a54889306a442a5020128164905824 14 16383 6 63 11 2047 18 262143
def cc_44_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x80070001f043e007c00f609a52318c52c2a5013e327c04c8c9805243248048828f090c499a032825540a02930426004b0496012421f942b500b30005 0x1805706caa5f13cba4b0229402d260ea480b4880e9002ca207844b62d9684f362376b462d48bda51482db7673620b6bd94d682dab633520969c16d3425a60eb4a0b68c16d142da205a6e0b4ac169182d226116ebc2c5705786cad0d956b22a4165382ca68593e1d27a0e4f03c37078560f08c1e1105daf0bb520969c12d345d2f0b95e092a41252834a30e9360926a2e1785e2f8bc53096be2ed7825a984b520969f5cd3825a584b470968612d085d2f04a366c4681257c5caf04953092a41253c44a70494b092941251c34a30494309284124fc249f0493d170bc120d8581a05b5c196a9544e02c9a0b9200f06816970652a0a940a6250164903c124f230078b80f15271180594ca22801e1127898089300924138d12693605a5c194a82250024980492c092401e0902da785b4d0b69616d1c85a285b430b49e169342d2585a472348a1690ea11fd223ba046f308cc2ca88593f0b27c164ec2c9b8593315264164bc2c970592b0b24e1648c5c91058463a06c280984d2e06c5d0b6bb1c9441d1e83a350b2a2165382ca4889420b2822a5002c9c859310d08d280f8481303c5c078a00e93054980785c0d4a80e91054a8441281126111140449847560236b9189702d2a4524c0d4882a5021894059240f04816d3c2da705b43156842a93c552185a3f0b476168dc2d198894f11286164fc2c9f0893d1125e224ac4493889231509c1717c2e2f05c53928a41ad7c85a9c825f844a61693c8d2685a4b0b48e169142d2190a3f0d4761a8dc85198595f0b2a61653c2ca70593f0b27c164ec2c9c8593311264164c608980592f0b2561649c2c91aa05e0b09c1a0d8181303b5c0d6a01ad205c900785c 15 32767 6 63 11 2047 19 524287
def cc_44_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xad6e987a602980a30e60b9706485882a20088021438502044762db8866211a04114ec63614b492c048c91f1050b110c10d04000040000000 0x8c45f8a45303b5f03b5e03b538735203b4f03b4e03b4b03b4703b43813420395f7f15e03953039520394f0894e0394b0394a039470694603943039420393703936039357836003b5c0ab5803b5406b5006b4808b407235008b407b23c7736006b5808b5003b4c7c34803b4408b407a24803a44059440784403a547234803b4403a4405944078447845d7745103b5d03b5103a5d08a4e06a4a06a4608a4203a3a03b5c0595c0785c7224c03a44059240782403b4f03b4b03b4703b437524f7424b732477124303a3b03a3703a3303b4f03b4306a4f06a4303a3f03a3b03a3703a3303b4f03b4308a4f08a4303a3f03a3b03a3703a337d45f7945303b5f03b5e03b5903b537635203b517035003b4f03b4e03b4b06b4a03b496f34803b4703b4603b4308b4203b416e34003a5f03a5303a4f03a4b03a4703a4303a3f03a3e03a3d0393e0383e05b5c05b5405a5c0393c0785c6836004b4c05b4405a440393c0784405b4c05b4405a440393c07844663586435004b4c05b4405a440d954059440393c0784405a446846005b6c05b4404a4c0ea446216c0392c0786c0784405b44059440392c078446645005b4404a4c0ea445d15c069540392c049280e924049200784405a44059440d9246445005b5405b4404a4c0ea440895c0d9540392c049280d9240492007854078446226003a500595c0785c 14 16383 6 63 11 2047 20 1048575
def cc_44_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x9d765c68f223038c021c586061807d25e447901b8b6c09a0468018083c90f003324c81272c9c027007c81e047411d00683190428f0904009 0xbc5f0bc5304b5f04b5304b4f04b4b04b4704b4304a5f0ba5e04a5304a5204a4f08a4e04a4b04a4a04a4706a4604a4304a4204a3f04a3e04a3d0595e04936049260785e04836048269b36005b4c05b4405a440493c07844983589535005b4c05b4405a440d9580493c0784405b4403944078449b4609226c9a14c039440492803920984509025c06a549714c039440392c049285a1240392005b44039440392c078449545005b5408a5c0da549414c039440392c049280d924039200785405a54078549226004a5005954078549025808a5005a4c5a24805a4404a4005944078440ec6e9d4620ec5e9c45205b6e9936205b5e9635a05b569335205b4e05b4d05b4c03b4605b4503b440eb4205a6e05a5603a4605a449116e0e9628f15e0d95a0d9560e95205946059450593e0e93d0493c0786e0785603846078448d35803b54863400695c039580a954039500894c0694403a3c8535003b4c8334005a440895c069540894c039488b144039400784403b5d8934e83342039510894e039428813603935039400394805a347b1340783403b488645e854528435e8335203b4e03b4d8015e039520394a03949039480694603941821360393506b4403c5d06b4d08b4906b4508b4103a5d03a4d03a3e80232 14 16383 6 63 11 2047 20 1048575
def cc_44_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xe02b800e003743d91338bcd07187c117040c103040be0eccbab228c88381f857819cc56a25a4160258005c117005c016435120b642130021 0x6c5d06c5105b5d06b4ab825db625103a3d04a3903a3504a3106c580594c0784cb425c06a54059240782406b4b06b4706b4306a4f06a4b06a4706a43bd23fbc23bbb237ba23304b54b846003c5c0bc5805c5403c5003a4c04a40b425c06a5403a440592407824b4450b334c04a40b656003b5c04b50b525c04a5805a5404a50b224c06a44059240782406b4f06b4303a4f03a4303a3f03a3b03a3703a3306b4f06b4304a4f04a4304a3f04a3b04a3704a3305c5f05c5e05c5905c53be45205c51b945006b5f06b5305b4f05b4e06b4db725fb125305a4f05a4e03a4db024c05a4b04a4905a4703a4505a4305a4204a41af24006a3f06a3b06a3706a330594e0584e05b5c05b5405a5c0693c0785ca936005b5c05b5405a540693c0785405b4c05b4405a440693c07844953586435005b4c05b4405a440e954059440693c0784405a54a956005b6c05b5408a5c0da54a716c0692c0786c07854a726006a500595c0785ca514c0e944a413c9424804a4004a3c0da3803a3404a300593407834ad56eac562ab459aa45105b6ea836205b5e05b5d05b5c0db5a05b5605b5505b5405b4e9334a05b466334205a6e05a5605a5405a46a616ea31620595e0595da214e0e94a0e946591420593e0d93d0693c0786e0785607854078460ab5e0ab5208b4e08b4d0aa5e0a95e089520394a039460d936089350a85e08c5f0ac5e08c5308c520ab5f0ab5308b4f08b4ba034908b4708b4308b410aa5e08a46412440895f0a95e08953089520594f0594e0594d0893f0493e0893b0393a089370393608933049320a85e088461e044 14 16383 6 63 11 2047 20 1048575
def cc_44_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xdc03700db07642d31af179f7664691223838e02245870a0c47b215e457015c04f213c046251413a2ce413804e00350cd01253c9011b2401b 0x6e9180124f1b826804a4c6f9221885b1bc2b8db15401c964691462a6a31034f859a5c1cd1df66860595d7c8a7822539ee2960694a790a381a519d6286089427489f8124f9ce2760393a7109b80e4d9b4266049320462f82314c0b6be0ab5e02da9816d480b69e08b4e02da682a97c154a608a4f0452582291c1148605a3f01d1e8168ec0947205a3701d1a8168cc094620595e02ca30164d80f0bc0784602c1b354d800b6b805b5402d2a0224f00f0a898358331a8016d300b68805a4406cac0224f00f08805b5402caa01e151aaac0d226c6a0ae01a5501125005a5403c2a348980114a00595403c2a25c9200948004a3c2d11c00e8d0094600593403c1a0375b9aeac40dc596b228816db9a66c405b5e02dae816d700b6ac05b5502daa036d480b69c9634a02da3194d080b4dc05a5602d2a016919a22dc0d96202cab016555a029c0d94a074a30365080b27c0d93d0449e01e1b80d0ac0785403c2301b1759c692c4341034a8b345180d28a0493e0249932d1600d8a8c734001cae01a560172a8039500249e00e4d00b490c6450035ac310d400b4680494c01ca20124f00d270c91340249801e0d0072800694802d1a2cc4d00f06803b4863a2f3191498a6bcc4352035a701ad35822bc0695201ca501a5240729003946034a0b0c4d80d26a03b440362e81ad740b69a03a4d0252480e9140948206a396091881b17c0d8bc06c5366229328d7d906a606b4f035a581ad240d68e06b43611a081a57d802bc06953034a901651c0b28c059450349f8124f80d2760393a0349b80e4d80d26604932 14 16383 6 63 11 2047 21 2097151
def cc_44_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xa414465b3fc7e0e95c8b54682d01a03135129c5382434808c5091b6360594a891422038c700d10920c418003 0x1ba460ff4507f1a83f4d100b4a003a40025184195820a8c102454809b001a560112a003948024a00124f200270fc134024983e95800b8c0f8158044a801a511e0288f825c0352a3485b011258f43507a22801a521e228005d607b2303d4d71e66a005a5c044ae01a521de2800785c6e89a3c4d01e0298ed1346e918022531da28808a5c7792a29c5b1dc298ec144034963a91800b6c0e8148024a000e4d1c0268e824c01d222485b009258e445001ca4384501c88a005c607322c395141c66c005a4c024a600e4e1be2600784c6e89a384d01b8288e013c 11 2047 4 15 11 2047 21 2097151
def cc_44_8 : Nat → List (Nat × Nat) := unpackCursorV4 0xc00be1be0bc19b19a09819809617517217207016e156c56054152150138c3043002a316a141121120101065003000000 0x8e01a4704d21e6b3063518f1a4c04d063a48c05a447d0ae81a5680d2acf615502ca681a5280d28c0594502ca246c1180f089170248b89244d17a0a8a51935e809a94608d80b468ea14d01ca500e519c628a0593d01c9d00e4d80b26a039348b01b01e0d0072a80494c01d1e4511b2266c005a44044ae01a5500729912148888a200e500072700493003c220125500927803a4887ab0438db00b46806958044a8012530072880493c8689c4304d00926007834821a80169100728807844819a0012510072690a560811a0424570072b003954840a80225300d2880493c01c9a3fc4d1fc268dd1348222800e522062800493c7e89a0168d00b26807834 12 4095 5 31 11 2047 21 2097151
def cc_44_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xcf0304ec102f83be02f41b61ed80b40ab86ae02b02aa0a9066dddb4065219405d2170157155c05509501540128a335cb07251c8051b1401b 0x50917a828a54035e9f9a94f857a002a40394e02ca5016518072840493e01c9d00e4d8092653a35001da44f0d02748a93b4549c9b001ad60076a003b48025a01688f26e280049209b22a022540092800492c024904c80926828004920044200120c2668a808950024a00124b00924132024abab755558aa88dd524620762e8371681b8ac0ec55a522a524dba8e6c40eb5e075ae836d381b69b2526e7d9310229780d4b4d62596112c01a958114a4aa25104528012938074949c2494092400e9180948469241025200128f80b47a04a3ca211d50c8e67a4713823602d1a8168d00946459231025181305b8212ac119469a89b0164d0560dc0d856074234c40d80f06805b5c01dac4bcd50076a004a5801d2a0164d00f06808c580362a016970094b12d254025280164900f0492924001e2e4ad160078a805c50941184a4d200768804c540462c01b150096b003b54941a249c9b00b4b804a589312a0129400b8ba05b4f02da6816d2c1169205b47035a2816d0c0b68205a4f01d2681692c0949205a4701d2281690c094832e23f9611dca88de4a4660594602c23354da1526c005b5c02daa0169500b2a8078544d9ac1a0d400b69805b4402d220165100f088d4258045280169100b288078444d124012900074680593403c1a48d586448c205b6d02db6016d79a66b405b56541a9016d393269405b46339a10169b00b4ac05a4602cb6c845781b2b40d956518a94805381d2940e9462f0a101e1b00f0ac07846 14 16383 6 63 11 2047 21 2097151
def cc_44_10 : Nat → List (Nat × Nat) := unpackCursorV4 0xb3c2c81aa22a02a70649567ad8075f055c8501d3c147211c0440d10042090414100e48216050d140024b09001c2011800100000000000000 0x375bacaac40dc5e0762e8371541b8a56436e06db1036d581b6ab6334e06da6cb09ba164c408a5e0352d0369640d4b006a56045292ac945404a004a4e01d2500e9180948404a3e02d1e8128f01b47562239af91c0368d80b46a05a34025190368c4094605216e034ab0465181b26c059341883701a1581d08c0d83603c1a544d02a06a10a26002d265749200b4890824002ca201e1129a8a00393ca6118036d381b6920db42075a0d2cd00a24bc06a4601d1b56857a102a40594e024a50125180b2840493e01c9d00e4d8092643005e0342300e0d81badd5c56206e2f0371741b6bc0eb5d06da7036d241b6840eb41a51a04a89ba0e4c40da5e02d2e816970074b40da5901d2c00e9580b4aa03a5406d2956c946b24a008a4e0352501a9181148404a3e01d1d00e8d8094645016e01cab0165500d28c039361783700e1580f0a80684601c1b037170154b006a50431240129028447004a3001ca403b1520c4c15625804528214920094814123802518037170174b003a50639240229028047004a30034a40371520a4c0c62580452854c920094813f23802518410942a249103240a7924518900072784f24e9b91b53053a062854613a9e09b0b813a6806c0dc5ea8229036d3a9c69b2825e81129036938074940da4901d2400e9181b4854d241a59200128fa8a4753b236025191385780728d361361682f00e11a6606d2726c02d2e02a9600b4a900250629240229010847004a30268b6016570580d80785c80930310960114a083248025200128f29047005a34025180164d00f06803948a30a05151500d2b00395001ca40125000b2680493c 14 16383 6 63 11 2047 21 2097151
def cc_44_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x82550401f453e4168d0d005866b0426002b7256e02c85568aac054e29f6a3a127400de29b8137006e00b890b30160027143c484cb090212002400012 0x1bada0dc6db29acd54d441d69b87349075a2d1cd06464c31a2600452f01a969ae4b2cc2580352b022949584a208a50045270169340b4998624ac2924e109230448c05a4502d220229094648208a4005d1f2288e8f246c0ba32084ab6045180b2883b13606c2b5fc1180f088100366592c0229400b4997d24802d22022900074700ba3002ca201e110072780ed6d06e2edf11641b8aa0ec51075b083ad3aa868403a5e02d2e80e970174b57b25905d2c02e9580b4aa05a5401d2903a944074a00aa4e651252dc9181548404a3e01d1d03a8e40747003a36025191b08c4174600395e02cae1205180726c0385e03c2e0941180706c0494c8c930022971644a805a4cbc9240169101148089238025181145500b2882205403c2200e5800b2680493cb69a754cd088648c0894e034a501a51811284039361002300ed82e86b00ab5001da417c8f2302c00494002496012482e2049170508b0b00125000925804920b881203b1b6d88bd52452075b6de0d781b6b40db56a39a94889862a4c00aa5e6412d2c4958154a404a4e01d252749250e49003a46025211ac9040948004a3e02d1e8128f2ee47576239ba91c5cc8d80b46a05a34025191788c4094604215608ca35c84d80b2681f056074235c00d80f0691426002d2e02a9600b4a91225001d1c02e8c00b2b80785c899305a8920074816d2380251800e4f01d6bd6a352075a483ad04aa4bc03a36b48af4485480929c0594a02ca30125080927c0393a01c9b0124c8680bc03836b723703b18ac68bc0ec5d075b75b0d881b6b40eb5906dab03ad441b68c0db4597137440988114bc06a5a0352b0229480749c05a4d01d2603a92ad649368248075230169140b48803a420752080e9000947c03a3a0751c80e8e00746c04a323511895c8c0a82dc10956074a30165100726c3306e06c2b03a1180f0880383687930598960114a161238025184389800b4b80ba5802d2a4349400d4900aa4002cae01e1701b8a806a580452800e9200948004a3c2d11c0168d0094600593403c1a0124f01b8bd6145206da7036d08a64bc06a46b00af4345480b29c0394a01ca30165080927c0393a01c9b0124c8640bc06846 15 32767 6 63 11 2047 21 2097151
def cc_44_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x9403202202fc0407c12f411e803ac97502e70dc03b0dd5f0abe016c427983ec25d80ba014ca29022aa0520870d0d0419042048400058a06140a08005 0x3a54cf2360229700d4a805a4c06d240369100b4800592ccfa370271881d6dd9d362045af01ad680d6ac08b5202da700ed340769809b4a075a4836d201368c03b4501da2016d081368205b4001d268129240748a04a4104cb70265581328c0993e02c9e03a0f81d05d9936001da666cd2007689953400252400e9100f0880901401da201a9500748808014ccab06609700b4b005a54ca9280229300d488059240380a0180500b248048240280a65897b2a4a403a4e0251f0265381d07c0401404eb76695881d6dd9736204daf00ed74076b805b5a04dac816d600b6ac03b5501daa026d481d6a394350045a701ad280d68c08b4201d2e812964074aa04a5104caf0265381d07c0e82e0180a01a9700b4b00aa5402d280165532269003b44045260169201d48805a4002ca601e113248bf9045301daf83ad4c0769e0eb4b01da383ad0c0b4be0ea5e02d298169480b49e08a4e02d258169280b48e06a4602d218169080b2bc0594e01c9b00e498178be0bc5301daf80ed78076a60bb5201da780ed2c0768e03b4301d2f80e94c0749e03a4b01d2380e90c092be04953024a781252c0928e0494305c2f83a13c1d08e0383f01c1b80e0bc0704e0481f0240e81205c1d02be845feda2980ed7fb46bdd7353e21a900ed3f8669dbc34bdc1a500ed1f6868dab343d51a100e97f4c4a603a4fd212580e91f46487a015fce0a7e4c51c1d27f8f13d01c9b9b44d41d25e03927c701f6380b80402c06a58055282349200948004a3cc611c0168d0094600593403c1a01a4f01bada0dc6106daee2cd641d6aa0db5106da4d5cd040d4bc05a5d02d2e02a96b144b20aa580552b0169540b4a806a5206d2881a9401149c06a4a06d2481a9200d48c08a425692082a9001747c8c23a3e91b02e8c80d2bc0595c034a30fc4d80d0bc0785c034230500d8092791e2606712c022940094987a2440251e6208e00b46804a301e8a20164d02408807834034b00165101127966349ab1a08f08d80b28c0493e01c9d00e4d809264110360363001b161486998324c05d20474580112a00593c044986000d2380a11b160044a801e4f01126180034 15 32767 6 63 11 2047 21 2097151
def cc_44_13 : Nat → List (Nat × Nat) := unpackCursorV4 0xc0037b16bee57c0ab914d2a5ef490b8a21053dc7138036d0cd905a82b5006904d2019c22c9c4aba8e1d1c02206392c672c98d8b201600251c0cf8006 0x3b54df1b0022d40094b003a5403c2a0435bb84ac403c6edfa3100f178078ba03c5c01e2b00f154078a810c5201dae80ed577a4dc10a6201d2b00e9540749c10a4d0452600e8f81d29a0394504c968264940709c0383e03c0b01b1740769a03b4503528eec9180d48a04a3e06c0b01b1740d6ba03b4d01d268129240748a04a4102ca68165141b02c06c5f0362f01b14f748a403b5fd49a980ed3c0769a03b4701da281ad0c0d4bfb925e0352981a9480748e03a4601d2281a8fc0947c0d95f034a781a51c1b27e03937034978164b40d24e0592506c0b01b1740d8a203b5d035a500e974074a203a3d06cae8164f40b26a07816035a581ad1c0d68603a4f01d2580e90c0747e03a3701d1981a53c0d28e0d93f06c9b80e4bc0724e0781602da7816d0c0d49e06a4302d1f8168dc0b4660394f01ca180e4fc0726e0393301c9780e4ac0724603c5f01e2f00f164078a7b745201e28ed91400d6be06b5301da780ed380d69a03a5f01d2980e93c0749c03a4d01d1f80e8ec074660d95f01ca780e5380b29bb514c01ca380e514072840693f0349b80e4bc0724e0384e03c0b00f170078a806a4cd8a3000f170078a803b540352601e150076a9b1560045ae042d535e4d806a3cd79b001ad435a49804a3c04c9201209366addb256201e376c1188078bc03c5d01e2e043168078ac03c5501e2a00ed74076abae26ed613100e978074ba03a4e0852681a9300747c0e94d01ca28264b41324a0384e01c1f01e058118be0ac5e04629823148076be0ab5301da780ed341169603b4701da282297c154bc08a530452900e93c0749c03a4d0451f8128f8152be0894f044a383a4fc0726e0892f02c9682249c0b24a04b4cd412e01a9500d47804a3807d1a0128c3506b008b5001da603ed200768808b4001e2f6a5168078ac0ac5201db680ed78096a403a6dd392f012968214ac04a5201d270129341f4980e94d01ca28124b41324a0384e01c1f03a058178bc0bc5201da680ed14174bc0ba5201d270164b40b24a0383e0740b02f5b817ac403c6e05e3100f178078ac08c5201daf00ed74076aa04b5205d37012988074ac03a5501d270129374a49803a3e0251e83a5340728a0492d04c9280e1380707c0e81605eb702f588078dc0bc6201e2f01b168078ac03b6e025b100ed74096b403b5601daa80ed50174dc04a6201d2f00e9740749c04a4d0852600e8f80947a0e94d01ca28124f40726a0492d04c9280e1380707c0e81606dac022d4007699a234801da2022d000b27809c5dd0a2c843154138a205b5e01dae80ed70136b40eb59065ac026d58076aa03b5402da9026d440b6a00ab4e06da5036d181568403a5d0252c80e954094a20994e04c9f0164f01325c0b83e05c170280533c6c003b5c055ac00ed501b6a00593c 15 32767 6 63 11 2047 21 2097151
def cc_44_14 : Nat → List (Nat × Nat) := unpackCursorV4 0xe40b8c1dc1ec6b966e3888b0dd957505d40750189362017455c05604580160050214004e093804c09147420d041286435b07181420500005 0x1148004a3004490750980114a008a4003d1e0228c3bc271dd134086b68431b7b26c3d3360045af01ad6b846b3ba358035ab022d4b646a208b50045a700ed3407699e734af31a4f94d23c668c03b4501da2022d0b5868208b4005d2c82e9440749be224a02524f80923be48c03a4501d220129041329a09945c809e9e44d7b808c0784405c1f02e0b82002c03c5d01da780ed340769608b4901da381ad140768603b4101d2380e9180748a03a3f01d1d80e8dc074660394f01ca680e51c0b28a0e93f0749b80e4bc0724e0384601c1701e05b828d1b146001e2e00f150076a803a5403c2a02e133806b008b5001da2765584078da03c6c01e2f6fd168078adb045201db680e9b7b04bc10a5a0852b6b09481d29a0394504c968264940709c0b84c01c1f01e058076880bb5905da880ed37ac695d534601da280ed13a44ba06a5a0352b7389540749a06a4a0352300e91407489d404605c1f03805ba4ac003c60e812c0229400d489cb244e81ae01ad537c4d808a3c01eb0739180076b808a5c035247289039a2b80785ce592672449011499c9244045ae728d535e4d80ba4c0351e7204900f0480ea6c02c9a0340500b259d345101dae80ed3c1769603b4705da180e977a249e08a4ee792581a92b9848e06a46e392182290b3a29f9714705c9f80e4df8c25e0592de28938164941707c0c0160462f82314c076be0ab5e01da980ed480769e08b4e01da680e97c074a603a4b01d2380e90c0746e03a3601d1a82a57c1129e0894701c9f80e4f40726e0593501c9780e49c0706dc146001e2e00f150076a808a4c03c2a00f150074a9c1560df1b67009700d4a808a38 14 16383 6 63 11 2047 21 2097151
def cc_44_15 : Nat → List (Nat × Nat) := unpackCursorV4 0xda2d9b66fee591bac973e6e44e47457fbcfb11ee2365e6890d0059432adf5388a01d10c19a22340450445188020f0419143200544078c0f000c48006 0x131740bb4f01ad340bb4b022d240bb4701ad140bb43022d0404a5102e8fc04a3b02e8dc04a3302e53c0594d02e51c059457d04fdf01370124bc0b927012d3c04b4b012d1c04b4301297404a4f02293804a4b01292804a4701a91804a4301290804a3f0128f804a3d04a53c129470124fc049370124bc0492d01249c0592501209808c5f02314c08b5f02ad7808b53022d4804b4f012d3804b4d02a97c04a5301292c04a4902291c04a4301290408a3700e8d40a95f02253c089470224fc0593d0224dc059350124bc1192702a17806c5f01b14c04b5f012d4c04b4f012d1c04b4301297c0ba5e01294c04a5201291c06a4601291404a3f0128f804a3d02e57c0694f01a51c0493f0124dc0492f0124b4049270164940482601b17406b5d012d2804a4901290403a3d0128e403a350128c40593d0164d406c5f01b17806c537e914806b5f01ad4c04b4f012d3804b4d02e97c04a5301a93c03a4d01a8fc04a3b0128e404a330128c40d95f01a53c0594d01a51c0594501a4fc069370124bc0d92702317c08c53012d7c04b53012d3c04b4b012d1c04a5f02a97804a5301294804a4f02293804a4d0128fc04a3e0128f40a95f02253c089470124fc049370124bc0492d01249c0592501e1780482602293004a4804691004a4001e11009c5d7dd16410c5502714403b5d012d6403b55012d4405a5e02697405a5c02696804a5901296009a5602e9540ca5401694804a510129400aa4e02e9280da4602a9080994e0124f80492e0164b00b83602e0980da5c0129600aa540129400db5c016d600bb54016d41f546e02718803b4d012d2403b45012d05f426e04a98808a5e01a96806a5602294805a4e02693405a4c02692804a4901292009a460469140da4401690804a410129000996e0265580994604a1b80e83603a09804b4800ed11f126c04693004a4804691004a4001e13004b547c518005c5c02f16005c540471400784c0275b9f256200ed7404b5900ed5404b517c09b812a6202697811a5d04697005a5a01296404a5801695809a5501695009a5201294404a5002293806a4a01a91808a420265780994e04a1b80985e01e1700e83603a09805b5c02ad6005b5401ad4005b4c04ad2005b44022d0004a4803a910059447b917ded453016d7c05b5e016d4c12b52016d3c05b4e016d2c06b4a016d1c05b46016d0c08b4202e97c04a5303a93c04a4b03a91c04a430124f80492e04a1780e82601ed3c07b4b01ed1c07b4301e93c03a4d01292c07a4a01e91c07a4600e9140ba3f0128ec0ba370128cc0795d01e53c0394d01e4fc0a93e0124ec079370124cc0793201e13c0784704a0fc128370120bc0b82701207c0781d01e05c1281580917dff45302ed7c04b53046d3c04b4b046d1c04b4302e97dfe25e01294dfd25204693dfc24e01292dfb24a04691df924601290df82427d857df314f7bc51c0493f0464dc0492f2784b4119277b0495eb05e6380d98e02601a93010d6d04318406b5e00ed7403b5c02ad69e935902ad600ab5600ed5403b5401ad4810b5101ad4008b4e01ad2810b4901ad2006b46022d09b334102ad0003a5d01296403a550129440ba4902e9040995d0265559213d1f44d40b83e02e0b81401601a98003a440229300482c00e91804a3e0164b40592504c05806c6001b161ad34c790531d6360022d4008b4c022d0003a4477811008b4e022d09e123e0128f59113d1e84d40483e0120b812016012d31d526002294003a3c0228c1dd034 15 32767 6 63 11 2047 22 4194303
def cc_44_16 : Nat → List (Nat × Nat) := unpackCursorV4 0xdd899f7304eddcbae373c827804d478b3f1116220424878b0e921d00b88661bec301744ad845b00ad25580aa43510e8574c909120133c230c4408022 0x21f25c0229300992401e09006d6e89558a2436e888d8811b5d01ad6804b59012d6006b5601ad5406b5401ad2806b468809ba1e26201a97811a5d00e97006a4e01a8f806a3d036574069550264b40992501a1780684e01e05806c5f02f14c04b5f02ed7804b53012d4804b4f012d2c04b4a012d1c06b4601297c0ba5e01294c04a5201293c03a4e0128fc04a3e0128f40b95f03653c069470124fc049370124bc0492d01249c0592502ad780ab5201ad2806b4602a9780aa520128f80592d0164940684e03605806d6e02b5880ab6e022d8806b5e022d761b35c01ad3808b4d02a9b80aa6201296403a5501294406a4a01a92406a4602290406a3601a8d40d95d01a5540893d0264d40685e01a1380d81601b5b80ad6201b1b808c6202adb80ab6200ed7404b5900ed5408b4d01ad2806b4601ad1406b4402a9b808a6201a97808a5d04697006a4e02293406a3e01a8f40d95d01a5540894d01a5140892d0264940685e01a1380d81603ad7004b5086097004a5801a95004a5001657005c5e01b17405c5c0271680dc5903316009c5601b15406c5401714809c5101714006b5d022d6406b55022d4409a5d85c96411a550269440ea4d02e9240da4502e9040994e0165300993e0264b80a84e02a0f81d01400ed7005b5802ed5003b500165521425c01a95005a4c0129200da440129000592c01e09006c5f03714c05b5f036d7805b53016d4a1525f84c94c0da4f01a92c06a4703690c05a3f00e8f405a3b0128e405a3700e8d405a330128c40595e016518059360164b804b4800ed121026c03a93004a4803a91004a4001653004b5484118006c5c02f16006c5403b1400594c0375ba1156200ed7404b5900ed5404b5183c9b809a6203697809a5d03a97006a5a01296404a5801a95809a5501a95009a5201294404a5002293806a4a01a91808a420265b80995e016570099360264980d85e03613a0b36000ed320d34800ed120734001292003a440165101c01400ed1006a5400e9101b01482d5820a25c01a96006a5481c94008a4c01a9100782406805019014012490078240600520825e81c94803a4e0128f80993e036138170140375ba0c562026dba09362026d7803b5d00ed7006b5a026d6406b5801ad5803b5500ed500db52026d4606350022d3806b4a01ad1808b4200e97404a5900e95404a510264f80992e0361780d84e05805006c5f01b17806c5302b14806b5f01ad4c07a5f01e94c0a95f02a54c0694f01a52c0694701a50c0693f01a4ec0693701a4cc0792f01e4ac0792701e48c0a85f01a13c0684701a0fc0683701e0bc0782d01e09c0d82503607c0d81701b17e5a45e96114e4b45201ad7e4935391c97e332538b093e2624d01a92dfb24901a91db424587490e1c2418688fc06a3b01a8de1923385857c0d94f848534069472b85140d93f01a4de0e12f81449e0404e8100f8150160435b410c6100ed7404b5900ed5404b51012d2404b4101a9780ba5d01a9700aa5a01296404a5802a9580ba5502a95006a5201294404a5002293806a4a01a91808a420265740995502e4b5ee12502e0d80b826012d3008a3c0228c004b4c0435b410c6d012d6404b5100ed340bb4a012d2404b48804d1803b45046d1004b4102297806a5a01a95808a520229380ba4d0229300ba4a01292404a488009180ba4504691008a4201290404a400265340994502e4b5ed12502e0d80b826 15 32767 6 63 11 2047 22 4194303
def cc_44_17 : Nat → List (Nat × Nat) := unpackCursorV4 0xc213041bb1aec0b226c80ac1ab00aa0aa41a21ddeb7701c857105b056a099064871200411cdca3700bc81178305090c20102180800008000 0xf58003b5c87c9723f15c01a9523d560012d4004a5801294006a448d80923b34e022d3404a490129061414d2c85140884e0220f8220168e518004b4002297004a4801290235024012900049400124c237560012d4004a50012560049508d85323514491958643560046db62d35e00ed762735c012d6403b55888d4804b51012d400ab4e02ad0811a6d90897a4125d90097006a5a01296404a5801a95a3e25501a9521e25201294404a5002293a3c24d8e893006a4a01a91a3824501a91008a4284c574b11550264b40992502a1780a84e8d00980782407c05a3046c012d222e2608c88e003a3401b1523046001314008b5801ad500785401a95003a348b958004b5c01a96006a5401a9100782401b5ba315628bcdb811b6201ad7811b5d012d7006b4e0469ba2d26201a96806a5901a96006a5600e95403a5404694406a4a01a91806a3601a8d40d95d01a5540993d0264d40685e01a1380781601317003b4c012d200fb4400ed022b23800e8d003c5d01ad3404b4901ad1404b4100e97403a4d0165340594503a05803b51012d3803a5d01a92806a4600e8da2823503a05806c5f8a914c03b5f8a4d7803b5300ed4803b4f012d3803a5f00e97803a5389c94803a4b01a92803a4700e91803a4300e8dc03a3600e8d40e95f03653c0694700e4fc0393d00e4dc0593500e4bc0392703a05a23360012d2011b448849b003a4c01b17006c5400e93006b4488d58004b5801ad5006b4400e9700783488518003c50 14 16383 6 63 11 2047 22 4194303
def cc_44_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x9911137de3134605b36b30d3caa6844c829415280230846008a091402202408e7e0cfa099192f0c48588e089230e101c003800253038405080028000 0x97d1b008a5c01a95007a4c04292010a4401e9000782c9811b812c62026dba5e362022d7806b5a01ad5808b5201ed3803b4d00ed3010b4a026d2410b48026d1803b4500ed1007b42026d0407b4000e93404a4900e91404a410264f80992e04a1b80d8560361180983e01e0f007b4f01ad3407b4b01ed2807b4701ed1806b4501e97407a4f01a9340794f01e52c0794701e50c0893f02a4ec0a9370224cc0792f01e4ac0b92901e49c0792301e4840784f01e11c0883f02a0dc0782f01e0b40782704a0941281f04a05c0ac5f02314c0ab5f9c4d7807b539c0d4a6f25f9b094c08a4f04292c10a4702290c07a3f70c8f410a3b9ac8e410a379a48d407a337e08c66715f02253c1094701e4fcd813d0424de641359844be5d12797017a040468100d806c5d01ad1c06b4601ad1406a4f00e93406a4b01292406a4700e91406a4301290406a3f01a8ec06a3701a8cc0694f016534069470165140693f01a4dc0d92f03649c0684601a0f8078168c8d7004b5000e95006d6d01b5b006c6d01adb6462618c497406a5901a956252510468f6592390468d61e231036574069550264f40993501a1780a85c01a138078168c0db004b4c95892003a449488d245360958d3004b4001a98003a4401b18006c58012d324426000e8f2512309505300784c9488f2501240128e250234012d22513448849b00aa5c00e9324f12401e0900db6c016510270140164f006c5d01ad764325102a93c06a4b01a91c0aa4395c8fc03a3d9548ec04a3994c8dc03a359388cc04a3102a53c069479344fc0593d9304dc059358444be0c12702a138260168acd7004b5003e97004a5800e95004a5001b1b406b6d01ad7808b5d03ed722a25d01a96406a5502e94406a4902290408a3d9288e411a350228c40d95d01a5540893d0264d40685e01a1380d81600ed7011d6d00f17806c5d00f1700bc5a9211640bc5802f15806c5501b15003c5204714403c5001ad7408b5901ad5408b5104698411a4e00e93403a4c01292403a4589090804a4102e9000aa3e02a8c80995d0265561514d2dc5140a84e02a0f8250168b8db22336001a9a006a6401a95006a4402a1b00782402ad780ab5200ed364534a910d1803b458f497406a5a01a95a3925501a95003a4d01a92806a4600e91403a4402a17a3702609005804b5c01e0f003c6001a91004b4e00e8d40593d0164d423016 15 32767 6 63 11 2047 22 4194303
def cc_44_19 : Nat → List (Nat × Nat) := unpackCursorV4 0xf70fd957a82ed9edb01af1f20fe2c5b6bd6d02cc3d1df943f1259f2cb6de6c06d7056b1265c4716736cdc2941e2608451c5ac0a44128807780230001 0x28034404a9b004a6801699004a609fc97005924016d7c06b5d016d6c05b59016d5c05b55016d4c08b5101697c03a5d01696c04a5901695c03a5501694c04a51a0c8fe8223ba048de7e23301657805a4c0129200da440129000592401b17408c5901b15408c5101ed7809b5d01ed7009b5a016d6405b5803ed5809b55036d5007b52016d4405b5003a9767c25903a95412a510268f40ba390468d409a31026518099360221380583e01e0f01282e046d7004b509e897004a5801695004a5001e17007c5e01717405c5c03f16809c5903f16009c5601715405c5401f14809c5101f14006b5d022d6406b55022d440ea5d9e49640ea5504a94411a4d02692409a4502e9040994e0264f80984e01e1300a83e04a0b82a01402293004a4803a91004a400165100dc5d9dd1640dc5504b14403b5d012d6403b55012d4407a5e02697407a5c02696804a590129600fa560269540ea5401e94804a510129400aa4e02692810a46026908099360264981284e0120f80482e01e0b010b58022d4003b4c9d4d2003b44022d000783c0371767445903715412c5101ed7803b5d00ed700fb5a026d640fb58026d5803b5500ed5007b52026d4407b50026d3810b4a026d180ab4200e97404a5900e95404a510264f80992e04a1380983e01e0f00b82e0a405007b4f968d340fb4ba34d240fb47a30d1407b439c0d0407a4f7689340fa4ba2c9240fa47a2891407a437f49068923fa208ee87237a108cc0794f4905340f9479f45167b13f9e04de7612f9cc49e5c03e7ac0b82801601f17408b5102a93c03a4d02a92c04a4902a91c03a4502a90c04a410228fc0aa3b02a8dc08a3302a53c0594d02a51c059450224fc0a93798c4be6012701ed7407b4f022d3807b4d02293c08a4b02291c08a4301e8fc03a3d01e8ec04a3901e8dc03a3501e8cc04a3102253c0894701e4fc0593d01e4dc0593504a4bc1292701e0d811d6d01b17408c5901b15408c5100ed780ab5d00ed700ab5a01ed6407b5802ed580ab5502ed5003b5201ed4403b5004698408a4e02290803a3d0128e403a350128c40995d0265540a93d9984d40a84602a0d808a5c01292004a4001e97011b6d022d7808b5200ed3404b4900ed1404b410469b408a5e02a97408a5c01a96806a569b895410a5402294807a4e02a93407a4c02a92804a490129200aa469b491410a4401e90804a410129000a94d9945140992d0264940a85602a1180ac5f02314c04b5f012d4c04b4f022d3804b47012d0c04b4201297c0ba5e01294c04a5201291c03a460128fc04a3e0128f40b95f02253c109470124fc049370124bc0492d01249c0592502e17803b5d022d3804b4a012d1808b4200e97403a4e02290803a3d0164f40593500f17c03c5e00f14e6a45202ad7c08b5300ed3c04b4d00e97c03a5300e93c03a4e00e93403a3f00e8f803a3b00e8cc08a3203a57c0394f0165340394700e5140893f03a4dc0392f00e49c07a4c01292010a440129000782401b17408c5901b15408c51016d7809b5d016d7009b5a01ed6407b58026d580ab55032d5005b5201ed4405b500269766825904695409a5102a8f40ba3903a8d40aa310225380793e0164f00992e02a1180a83600f1700bc5801715003c5004a97004a5801695004a500229300da4401649005c5f01717805c5304b1480ab5f022d4e6625f99494c05a4f00e93405a4b01292405a4700e91405a4301290408a3f0368ec0da370228cc0594e0164f81285e0360d80ea5c0129600aa540129400eb5c01ed600bb5401ed426346e04b18803b4d012d2403b45012d066226e02698808a5e01a96806a5602294807a4e02693407a4c02692804a4901292010a460269140ea4401e90804a410129000996e0264d80992604a1b80d85603611a5f36000ed700ab5800ed5010b5001e0f003a54 15 32767 6 63 11 2047 22 4194303
def cc_44_20 : Nat → List (Nat × Nat) := unpackCursorV4 0x8bc08ac483dc7c9d7ac77ac0794673d6710b6a5b62605a2158c558c056c850d848e043173cd9371730d927a51e6514e610d00e0b042802c50185000600000000 0x29e24c0128f00492404a092a456ea8d58803c6ea8518803c5e00f17403c5c03716803c5600f15403c5400ed7403b55a7c9ba9d26200e97803a5d00e9380da4d01a93003a3e00e5380393e026134038450260b40982501605408c5f02b17808c5302314803b5f02ad4c03b4f00ed3408b4b00ed1c03b4502297c0aa5e02294c08a5200e93c03a4e00e93408a3f0128f80a85f02213c088470460fc038370220bc0782d02209c07825012d329925c01a95006a3c0128e00ca340128c299358022d4003b4c032d2003b44022d0003c5ea6916803c5602b14803b6d00ed7804b5200e9b69825e0129680da5601294803a4e0129340ca4c00e5380393e046134038450120b4118250460540bc5e02f14803b4d00ed140ba5e02e94803a4e00e4f80782d01e0941181502f5b80bd6200f1b80bc6200f17803c5602314803b5e00ed7403b55012d480ba6e01298803a5600e95403a4e0129369624c00e8f804a3d00e5380393e046134038450120b4118250460540bd6e02f58803c6e02f18803c5e01b16803c5600edb804b6200ed7404b5a00ed5803b5500ed500ba6e01298803a5e00e97403a4e0129340da4c00e8f804a3d00e5380393e046134038450120f4038350120b4118250460540bc5f02f14c03b5f00ed7803b5302ed4803b4f00ed2c03b4700ed0c03a5f00e94c03a4f00e92c03a4700e90c0495f01254c0494f01252c0494701250c0985f02613c0984700e0fc0383700e0bc0382701207c0481d01205c0981501ad7007b58026d5006b5001e15008b4c01ed2009b4401ed029124800e9100594401e1329245fa4114c07b5f026d7807b5301ed4807b4f022d3807b4b01ad2807b4701ad1807b4301ed0803a5f04694c03a4f04692c03a4704690c0785e01e1380383600e09ad945fb3114c03b5fb2cd7ac8353ad4d4803b4fad0d3aad34baa4d2803b47a94d1a9c343a6cd0803a5fa5c94c03a4fa5492c03a47a5090e9313ea4c4ba7305f97413e050470260fe8f03d00e0dc6d0350460bc038270d405407b4f01ed3807b4d02293c08a4b02291c08a430228fc03a3d0228ec04a390228dc03a350228cc04a3102253c089470224fc0593d0224dc059359dc4be7412701ad7c06b5e01ad7406a5f00e97406a5b01296406a5700e95406a5301294406a3f01a8ec06a3701a8cc0695f016574069570165540693f01a4dc0d92f03649c0683e03605804b4f012d2c04b47012d0c04a4f02293804a4b01292804a4701a91804a4301290804a3f0128f804a3d9f053e791470124fc049370124bc0492d01249c0592500ed7c06b5d00ed6c03b5900ed5c03b5500ed4c08b5100e97c03a5e00e97403a3f00e8ec03a3700e8cc0395f0165740395700e5540e93f03a4dc0392f00e49c0382e03a05806c5d02316406c5502314407b5e02ad7407b5c02ad6803b5900ed600fb5602ad540fb5401ed4803b5100ed400ab4e02ad3403a5d01296403a550129440aa4a02e9240aa4602a9040aa360428d52e15da0c5540993d0264d40884e02a0d80783402e0b83301601b17408c5901b15408c5100ed7404b5900ed5404b5102ad380bb4d02ed140ab4201e9780ba5d01e9700ba5a01296404a5803e9580ba5503e95007a5201294404a500429180ba4502a8f80aa3d4b0576821550264b40992502a1380483e02e098078240c405807c5e00f17403c5c03f16810c5903f1600fc5600f15403c5401f14810c5101f14006b5d022d6406b55022d440bb4e02ed3403a5d01296403a550129440aa4e02a9340aa3e02e8e40aa3202e8c6862304a857681155026534099450421380784c02a0f80b82e0bc05803b4d042d2403b45042d040aa5d02a93404a4902a91404a410428f80aa3d4a0536801450420f80482e0b405804c5d022d6408b5101296404a5149c5767f15502a1180883e0120b82c01601b17408c5901b15408c5100ed7404b5900ed5404b5102ad340ab4a02ad180bb45a18d100aa6da149b007a5e02a97407a5c02a96804a590129600fa5602a9540fa5401e94804a510129400aa4e02a9340ba3e02a8f52515d9f85540992d0264940884e0120f80482e01e0b02b01604adb003b68016d9003b6001e0d012a6c0129a005a640129800782400f1b005c6800f19012c60a008c00594c 16 65535 6 63 11 2047 22 4194303
def cc_44_21 : Nat → List (Nat × Nat) := unpackCursorV4 0x8380ff21fe03f427e80fb09e83bc437802d76578dad865a04b4015e2ab81548a8d711a021483d945d78a459090199e11881c18206038202140400002 0x3d60afd18003b5c02297006a48aec9000595caf8172bc24cae809008a4cae891008b5caecd52a026c02e93006a3c016492b90240269b0078340e00500782cb1114403b5d00ed3c0bb4b00ed1c0bb4300e976c224f02293ac024b01a92abd24701a91ab82430229080b93e97813e0904702e0fc03837adc0bc0782dad809c078250dc05408c5f02314c03b5f02ad7803b5300ed4803b4f022d3803b4d00e97c03a5300e92c03a4700e90c03a3700e8d803a3500e4d80985f02213c0884700e0fc0383d00e0dc0783500e0bc03827ac918003c5c00f15003b540229300595400f15003a54ac9582af36cac497006a540228e003b54abcd8008b5001296003a540165500dd6eacd58803c6eac118803c5e00f17403c5c00f15803c5500f1500dc5200ed7403b55ab89b80da6200e95803a5500e9380da4d02293003a3e00e5380393e026134038450260b40982501605406c5d00ed3403b4501a946ac24601a91404a3e04205406c5d01ad7403b4d00e93404a4900e91404a4101e1340784504205406c5f01b17806c53aad14803b5fa68d4c03b4f00ed3403b4700ed1406b4301a97eaa25e01a94c06a5200e91c03a4600e91406a3f0128f81085f01a13c068470420fc0383701a0bc0682d01a09c0782504205406c5d01b14403b5d01ad2803a5d00e94403a3d0261740783d01e0d40581501ad2c06b4701ad0c03a4f00e92c03a4300e8fc03a3700e8cc0684f01a11c0983f0260dc0382f00e09c0581501ed3c07b4301a93c06a4301a8fc06a3701a8cc0394f00e50c0393f00e4dc0393300e4bc0392b00e48c03c5f00f17803c5900f14ea845200f146a745001ad7c06b5300ed3c03b4e01ad3403a5f00e94c03a4f00e93803a4d00e8fc03a3b00e8cc0394e02617c0384f00e1380784da981300384700e1140384201a0fc0683700e0bc0382701605403c5c00f15006a4ca8918003c5c00f15003b5401a9300595400ed52a2560022d700db54a809b006a3ca80d8006b50 15 32767 6 63 11 2047 22 4194303
def cc_44_22 : Nat → List (Nat × Nat) := unpackCursorV4 0x89890c1de8c35206982b08d5c12b02538aa70146227464e8094251c323024582841cb358f9b1b10330c3ca87410e801d001498280028a04040020000 0x6a5c02696007a5401a94004b4803ad1007a4c02692007a4402290007844b7917edd45302ed7c04b5303ad3c04b4b03ad1c04b4301e97c07a5e01e94c09a5201e93c07a4e01e92c06a4a01e91c06a4601e90c08a42026578099360120f80482eba917ee745302ed7c04b5303ad3c04b4b03ad1c04b4302e97ee625e01294ee525203a93ee424e01292ee324a03a91ee124601290ee0242b7c57a93136a4c49a7605f98413e0e0470120fc0e8370120bc9e02d02609edc02501a9300dd6d03718406b5e00ed7403b5c02ad6ada35902ad600ab5600ed5403b5401ad480db5101ad4008b4e01ad280db4901ad2006b46022d0aa434102ad0003a5d01296403a550129440ba4902e9040b93e02e4b80d85d04a1569203d1f40d43f01501a98003a440229300492c00e91804a3e01e0b4078250f805406c6001b1629e34cb54132c7360022d4008b4c022d0003a44b3c51008b4e022d0ad223e0128f40493e0124ba9103d1e80d43d015012d32c626002294003a3c0228c2ce13402290004a30022482c526002294008a400168f008a30b3c4e2ce1340375b40dc6db28d86c4360022d7806b5aaccd66ab35801ad5808b52a8cd4408b50022d3803b4d00ed32d834ab5cd26d6348b50d1803b4500ed1008b42a74d0408b4002e9640ba5100e936d324a012926d1248b4091803a4500e91004a41b345180594402e4f80b92e04a13412845a400f4790350ec05403c5d00ed3c03b4d00ed2c08b4900ed1c06b4500ed0c03b4100e91c03a4600e91403a3f00e8ec03a3700e8cc0394600e4b80384f00e1340384701e1140983f0260dc0382f00e09c05815ac91a2a246000f17003c5400ed5003a540165500b94cac4d6008b5000ed12ca56100f1b403c6c00f17ab045a00f15aa145200edb403a6db249780da5a03695a9d25200e5380b94c00e4f80984d00e1140982d0260940581500ed100bb5902ed4403b4db1cd2ac634600ed1403b44b0c97406a5a01a95abf25500e93406a4a01a91803a4500e912c514602e4f839015b0d58003c60b0496008a5001a912bc244b04d7006b54abc9b008a3c 15 32767 6 63 11 2047 22 4194303
def cc_44_23 : Nat → List (Nat × Nat) := unpackCursorV4 0x821e80c580037fc17e467e407dc27dc07cc475dc6e9d6bcb651b5d2054e15385538051884b9843a03c1e3b433b0132a22d1626d91fdc191b164b0f9b089c0022 0x1b17f0245300ed7f0135e00ed4c03b5200ed3c04b4e00e97c03a5e00e94eff25200e92c06a4a00e91c03a4600e90c03a3700e8d803a3504617c1084f01a11c0383f00e0f40383701e0d40382f00e09c11815becd8004b4803ad12f926c00e93005c5c01715003a4c016d12fb560012d6005b5401ad1003a5c0164d2f946000f142f725c0229300592404a09005d6ebf558afc36ebe8d880eb5d016d6804b59012d6005b56016d5405b5401ad2806b46be09baf62620169780ea5d00e97006a4e0168f805a3d0165780594e026174058550260b40982501605406c5f02f14c04b5f02ed7804b53012d4804b4f012d2c04b4a012d1c06b4601297c0ba5e01294c04a5201293c03a4e0128fc04a3e0128f40b85f04213c068470120fc048370120bc0482d01209c0782502ad780ab5201ad2806b4602a9780aa520128f80694e01e0b40782504205406d6e02b5880ab6e022d8806b5e022d76f335c01ad3808b4d02a9b80aa6201296403a5501294406a4a01a92406a4602290406a3601a8d40695e01a5381085d01a1540883d0420d41081501b5b80ad6201b1b808c6202adb80ab6200ed7404b5900ed5408b4d01ad2806b4601ad1406b4402a9b808a6201a97808a5d03a97006a4e02293406a3e01a8f40695e01a5381085d01a1540884d01a1140882d0420941081501717c05c5e01714c0ac5201ad7c06b5301697c05a5302a57c0a95301653c0594b01651c0594301a4fc0693b01a4dc069330164bc0592b01649c0592302617c0584f01611c0683f01a0dc0582f0160b4058270260940981f02605c03c5c01f16009c5400f1400785401e97004a5802695004a50bb893006a440164900782c01f17c09c5e01f14c07c5201ad7c10b53bbc97eed25301e93c03a4d01e92c04a4901e91c03a4501e90c04a410428fc06a3b01a8dc10a3301e1780584601a0d80782e01717f3245ecc114f2345201ad7f21353c7c97f0b253c1093efe24d01692ee324901691ea5245bd490ef4241bc88fc06a3b01a8def1233bc053af013e9e017c0984fbb0134058472b81141083f01a0ddef02f64c09c400150375b40dc6100ed7404b5900ed5404b51012d2404b4101a9780ba5d01a9700aa5a01296404a5802a9580ba5502a95006a5201294404a5002293806a4a01a91808a4202e4d80b9260361741285502e0b6de025012d3008a3c0228c004b4c0375b40dc6d012d6404b5100ed340bb4a012d2404b48ba4d1803b4503ad1004b4102297806a5a01a95808a520229380ba4d0229300ba4a01292404a48ba09180ba4503a91008a4201290404a4002e4d80b92604a1341284502e0b6dd0250131740bb4f01ad340bb4b022d240bb4701ad140bb43022d0404a5102e8fc04a3b02e8dc04a3302e13c0784d02e11c078459880fe0f0370120bc0b827012d3c04b4b012d1c04b4301297404a4f02293804a4b01292804a4701a91804a4301290804a3f0128f804a3d0124980984f02611c0483f0120dc0482f0120b40482701e09408c5f02314c08b5f02ad7808b53022d4804b4f012d3804b4d02a97c04a5301292c04a4902291c04a4301290408a3700e8d40a95e02a17c0884f02211c0883f01e0f40883701e0d40482f03a09c06c5f01b14c04b5f012d4c04b4f012d1c04b4301297c0ba5e01294c04a5201291c06a4601291404a3f0128f804a3d0124980985f01a13c068470120fc048370120bc0482d01209c0782501b17406b5d012d2804a4901290403a3d0128e403a350128c40783d01e0d406c5f01b17806c53b8914806b5f01ad4c04b4f012d3804b4d02e97c04a5301a93c03a4d01a8fc04a3b0128e404a330128c41085f01a13c0784d01a11c0684501a0fc068370120bc0e82702317c08c53012d7c04b53012d3c04b4b012d1c04a5f02a97804a5301294804a4f02293804a4d0128fc04a3e0128f40595e0124980985f02213c088470120fc048370120bc0482d01209c07825016d3c05b4b016d1c05b4301693c03a4d01292c05a4a01691c05a4600e9140ba3f0128ec0ba370128cc0595d01653c0394d0164fc0a93e0124ec059370124cc0593201613c058470260fc098370120bc0982701207c0581d01605c09815 16 65535 6 63 11 2047 22 4194303
def cc_44_24 : Nat → List (Nat × Nat) := unpackCursorV4 0xb322cc0b3028139e0a70297165c093124818c1a30083260c07d19f407b09e81731d22b48010c54204f453b08d461970640121c20a0800008 0x30636cbecd8005a6801699006a540169100a96c0164900ab5e02ad4803b4dc74d2b1c34600ed171525d01a96806a56c4495406a5400e93405a4a01691803a4500e9100a95ec3c49847015012d700593c00f18005a44012d3803a3501e0f40783511805403d6000ed72f725cc5c17006a54c5558004b5001296004a5001a9130e124c4cd3808b4d01292404a410225380893ebb8134b204511405711460012d0008a5c01292004a40c3449004a4001250004930c3d58004b50012940049580125430e14cc345131e561c6d5800eb6dc14d7803b5dbfcd7004b5900ed56fa352012d4404b5002ad380ab4203a9b71a25ec649771825c01696804a5901296005a56c5895405a54bd894804a5101294008a4ec509371224c01a92806a46c4091406a440229080a95e02a53b0c126016492ed05d2c41541282d04a09442015c211b004b48c189830a23800e8d006c54c2118004c50022d6006b5401655006a5400e8d306560012d7005a5801695006a4401649005d6ec2558b0736e03ad8805b5e03ad7404b5c01ad380ea6ec1498805a5a01696405a5801695803a5500e9500ea5101a92806a460168d805a350165780594e026174058550260f40983501605404c5c00ed3004b48032d1003b40c0c8e003a3400f17406b4d012d2406b45012d0403a5d00e9340784d01e1141181500ed4404b4e00e97406a4a01a91803a36c008d411815 14 16383 6 63 11 2047 22 4194303
def cc_44_25 : Nat → List (Nat × Nat) := unpackCursorV4 0xbd3d770eec0d5229c392d2e24dbc227608e51d9ac2b6049368f0cf4a9d843a827014e001a0834006608cc019022e8e5a0cb2090191d0c24584608023 0x3b5b406c5d02316406c5502314403b5e02ad7403b5c02ad6805b59016d600bb5602ad540bb5400ed4805b5100ed400ea6102293808a4200e8f404a3900e8d404a3102a5180a93603a1741285502a0f73603502297004a4801290005a5c03adb408b5e022d4803b4d012d2403b45012d040ea6d0229780aa5d02297006a5a01a95b3d25503695008a520169380aa4d0169300aa4a01292404a4802a91b3c24503691005a4201290404a4002a5580a94602a1373504504a0b41282502b17c08c53012d7c04b53012d3c08b4e012d1c04b43012d0804a5f02e97804a5301294804a4700e91804a3f0128f804a3d02e5780b85f02213c0d8470120fc048370120bc0482d01209c0782500ed7408b4e012d2804b46022d0803a5d00e93808a4200e8f40783d01e0d403c5f00f17803c53ce51480ab5f022d4c03b4f012d3403a5f00e94c03a4f00e93803a4d00e8fc03a3e00e8ec03a330228c81185f00e13c0784d00e11c038450220fc0d83700e0bc03827016d3c05b4d016d2c05b4a016d1c05b4601ad1405a5d01693c05a4d01653c0594b01651c059430224fc0a93b02a4dc089330164bc0592b02e4a40592701648c0592101613c058470220fc098370160bc0582d01609c0982502607c0981700ed7009b5801ed5003b500229700da5402693004a4801e91004a4001e0900ac5f02314c07b5f01ed7807b53026d4b3625fcd494c08a4f03692c0da4702290c07a3f00e8f407a3b0128e407a3700e8d407a330128c40995e0265180784e0160f80ac5f02314c0ab5fd00d7805b53cfcd4b3e25fcec94c08a4f03692c0da4702290c05a3fad08f40da3bce88e40da37ce08d405a33b808c73715ebc051af01369ec17c0884f03611c0583f3600f409837cd00d5f302f67009c05c5d016d1c05b4601ad1405a4f00e93405a4b01292405a4700e91405a4301290406a3f01a8ec06a3701a8cc059460164f80584f0161340584701e1140683f01a0dc0982f02609c05815c28d7004b5000e95005d6d0175b006c6d016db71e261c2497405a59016956fd25103a8f73123903a8d6f62310165780a95c0165380985d0161540983d0260d405815c20db004b4ccb892003a44ca88d31d360cb8d3004b4001698003a4401718006c58012d331c26000e8f3292300165332c04cca88f3280240128e328234012d2329344be49b00aa5c00e93005924c9c09009b6c01e1104a01401e0f006c5d016d771b25102a93c06a4b01a91c0aa43cbc8fc03a3dcb48ec04a39cac8dc03a35c988cc04a3102a5380a84f01a11f2503f01e0f72403701e0d5f202f66809c49015c0cd7004b5003297004a5800e95004a5001b1b406b6d01ad7808b5d032d730225d01a96406a5502e94406a4902290408a3dc888e40ea350228c40695e01a5381085d01a1540883d0420d41081500ed700ed6d00f17805c5d00f1700bc5ac811640bc5802f15805c5501715003c5203b14403c5001ad7408b5901ad5408b5103a9840ea4e00e93403a4c01292403a45bf090804a4102e9000aa3e02a8c80a94e02a4f80e85d04a156ef04d2dc11448015 15 32767 6 63 11 2047 22 4194303
def cc_44_26 : Nat → List (Nat × Nat) := unpackCursorV4 0x93828c5d8a48835c800d80007f827ec3779d75886e9c636d5d97575951974b59422538e52f662b50288b1ea81d451c051a861a801a8018c713950bdf06560019 0xd7d1500782402b5b808d6202b1b804c6201317404c5a02315804c55d811500ab6e02ad8803b5e012d380aa6e01298808a5e01297404a4e0129340895e0125380493e0124b80492cd780f5380350120b7570254d405405a5d02293804a3e0165380493e01e0b4078250160540ac5f02314c0bb5f012d4c08b4f012d2c0db4701697c05a5e01694f5c25201693c03a4e0128fc04a3e0165380493e0124b80985f02213c098470120fc098370160bc0782d01609c058250160540ac5e02b1480ab5e02ad4810b4e04293804a4dd644f53b1350421380483e0120b933016d65150059340164b00783c4c80500ad6e0235880ac6e01318804c5d01316808c560131575a45402adb80ab6200ed7804b4e02a9b804a6202297804a5d01293804a4dd604f5381350124b7571250221780484e0120f80482e0120b13101601e97408a4e0128f80592d0164940784e0120f80781602b17c08c5302ed7c04b53022d3c04b4b042d1c07a5f01e97807a53d5494807a4f00e93804a3f0128f81295f02253c109470124fc1193701e4bc0592d01e49c0592501e1380483e0120b80781602b17f8645e02314f8445202ed7f8335e012d4f81352022d3f6434d012d2f6134adfcd1f7d346decd176a34402a97f6925e01294f6625202293f6524ed9093404a3fd8c8fb6123dd2457c0894fbc451c0493fa504dc0492fb804b75d127d6c4968405f02213e190470120fda30370120bdf802dd5809f540254c005c05b4f016d3805b4d02293c08a4b02291c08a430228fc03a3d0228ec04a390228dc03a350228cc04a3102213c088470220fc0783d0220dc078357dc0bda1027016d7c05b5e016d7406a5f00e97406a5b01296406a5700e95406a5301294406a3f01a8ec06a3701a8cc0693e01a17c0785d01a15c0685501a0fc068370420bc1082704205404b4f012d2c04b47012d0c04a4f02293804a4b01292804a4701a91804a4301290804a3f0128f804a3d9a013e170470120fc048370120bc0482d01209c0782500ed7c06b5d00ed6c03b5900ed5c03b5500ed4c08b5100e97c03a5e00e97403a3f00e8ec03a3700e8cc0392e00e17c0785d00e15c038550460fc1183700e0bc0382704605406c5d02316406c5502314405b5e02ad7405b5c02ad6803b5900ed600cb5602ad540cb54016d4803b5100ed400ab4e02ad3403a5d01296403a550129440aa4a02e9240aa4602a9040aa360368d40894e02a4d80593402e4b92e05dd201540a83d04a0d45401501b17408c5901b15408c5100ed7404b5900ed5404b5102ad380bb4d02ed140ab420169780ba5d0169700ba5a01296404a580329580ba5503295005a5201294404a500369180ba4502a8f80aa3d02a5380493e02e498059244b01774705502e0b41282514805405c5e00f17403c5c0331680dc590331600cc5600f15403c540171480dc5101714006b5d022d6406b55022d440bb4e02ed3403a5d01296403a550129440aa4e02a9340aa3e02e8e40aa3202e8c74b2300365380594c02a4f80b92e4a81774605504a1340d84514005403b4d036d2403b45036d040aa5d02a93404a4902a91404a410368f80aa3d0364f80492e4a01374504513805404c5d022d6408b5101296404a5102a5180893e0124b92705dd101544d01501b17408c5901b15408c5100ed7404b5900ed5404b5102ad340ab4a02ad180bb45d2cd100aa6dd289b005a5e02a97405a5c02a96804a590129600ca5602a9540ca5401694804a510129400aa4e02a9340ba3e02a8f40894e0124f80492e0164b12505dd0c1540a82d04a0944c015026d7003b5801ed5003b500164d009a5c01296007a540129400592400f17007c5800f15009c50d148c00784cd14d134426c02697004a5801e95004a5001e09007b4f01ad3407b4b01ed2407b4701ad1407b43022d0407a4f00e93407a4b01292407a4700e91407a430129074823fd1c8ef46237d0c8cc0584e016d3f3234d032d2f52349032d1f51345016d0f3f34101693ecb24d03292f5024903291f4f24501690ee5241d388ff4d23bd308df49233cdc4fadf12e01613d2404d02611f4204599c0fe160377d80bda002712c05405c5d022d440aa4f00e9340aa4b0129240aa4700e9140aa4301290408a3f02a8ec0aa370228cc0a84f01e1340a84701e1140883f02a0ddf502f67c09c05b5d016d3c08b4e016d3408a4f02292c08a4702290c05a3f00e8f405a3b0128e405a3700e8d405a330128c40593602213c088470160fc0583d0160dc078350260bc09827 16 65535 6 63 11 2047 22 4194303
def cc_44_27 : Nat → List (Nat × Nat) := unpackCursorV4 0xf7abc89f66ae327bf9b703ede0dbc0b7036e02c26d3d2a7814f027a94f409e813d027a04a548aa8f875d27b68f5cc28fa8db110ea17a80d880068000 0x2ad3c0ab4301a93c06a430128fc04a3b0128e803a3700e8d803a3302a53c0d93f0364dc0692f01a49c0a84f0420fc1083701a0bc0682703605c03c5f01b17806c5302b14806b5f01ad7806b53022d4804b4f012d3804b4d02297c04a5301a93c06a4e0229377e24c00e8fc03a3e00e8f40a95f01a53c0394701a4fc0893d01a4dc069350124bc0892702a17c0684f00e11c0683f0220f40683701a0d40482f02209c0d81702ed3c0bb4300e93c03a4300e8fc03a3b0128e803a3700e8d803a3302e53c0e93f03a4dc0392f00e49c0b84f0460fc1183700e0bc0382703a05c03c5f00f17803c5302f14803b5f00ed7803b53012d4803b4f00ed3803b4d01297c04a5300e93c03a4e0129377c24c00e8fc03a3e0128f40b95f00e53c0394700e4fc0493d00e4dc039350124bc0492702e17c0384f00e11c0383f0120f40383700e0d40482f01209c0e81700ed3403a3700e8d80aa3500e4fc039370124bc0a92700e0fc038370120bc0a82703605c03c5d00f17003b5d02a97403a4e02a9340aa3d036534039450364f40d935042134038450420f410835036d7010b5c00ed340aa4d02a8fc0aa3dde04ff771370124bc0a927dd80ff750370120bc0a82754005c03c5e02b1480ab5e02ad480aa5e0129480d94d00e5140d93d0364d40492d0364941084d00e1141083d0420d40482d04209403b4f00ed0f7224fdc490c03a3f00e8f804a3d03653c0393f00e4dc0d92f03649c1084f00e0fc038370420bc1082703605c0ab4f02ad380ab4302ad0804a4f01290c03a3700e8d803a3502a53f6f13fdb84dc0492f01249c0a84fdb40ff6c0370120bc0482753805c03b4fde8d3b79343dd0d080aa4f01290f7323fdc08fb6b23dd2c53c0d93f00e4dc0492fd8049e8604f0420fc038370120bf5a02752805c04c5d022d4408b4300ed0404a5101290c04a410228fc04a3b02a8df4a15d02a53c0594d02a51c059450224fc0a9370124bc0b927a141740a84f01e1340a84701e1140883f02a0dc0482f02e09d490170128fc04a3b0128dc0593f0164dc059330124bc0492701248c0883f0220dc0482f01209c0581f01605c04a3f0128ec04a3701e4fc0793701e4cc0492f01249c049230220fc088370120bc0482701e07c07817012d3c04b4b012d1c04a5d01293c08a4e01293404a3f0128f804a3d02253c089470124fc049370124bc0492d0124a80492701249805925da04900884f02211c0483f0120dc0482f0120b40482a01209c0482601e0976702451c05c06c5f02314c03b5f02ad7803b5300ed4803b4f012d3803b4d00e97c03a5e00e94c0aa5200e92c06a4a00e92403a4700e91803a4300e90403a3700e8d803a3502a57c0894f01a51c0393f00e4f4039370164d40392f00e49c0a85f02213c0684700e0fc0383d00e0dc0783500e0bc0382703a05c03c5f02b17803c5300f14803b5f00ed7803b53012d4803b4700ed1803b45d88d1004a5f01294c03a4700e91803a3f00e8f804a3d02a57c0394f00e51c0393f00e4dc0492f01249c0a85f00e13c0384700e0fc038370120bc0482703a05c06c5f01b17806c5302f14803b5f012d4c03b4f01ad3803b4d00ed1c03b45012d0c04b4201297c0ba5e01294c04a5200e91c03a4600e91404a3f0128f804a3d02e57c0694f01a51c0493f00e4dc0492f0124b4049270164940b85f01a13c068470120fc038370120bc0482d01209c0782503605c03b4f00ed3803b4302ad0804a4f01290c03a3f00e8f804a3d02a53c0393f00e4dc0492f01249c0a84f00e0fc038370120bc0482703605c06c5f01b17806c5302314804b5f02ad7804b53012d4804b4701ad1804b45d88d1004a5f01294c04a4f01a93804a4d0128dc04a3602a57c0694f01a51c0493f0124dc0492f01249c0a85f01a13c068470120fc048370120bc0482703605c0ac5e02b1480ab5e02ad480db4e03693804a4d0365380493e0124bb5f03d4ec0d536015 15 32767 6 63 11 2047 22 4194303
def cc_44_28 : Nat → List (Nat × Nat) := unpackCursorV4 0xcd61c521bdddb69db38ca9699e2d96dd8f9d852a7d20769a75c37542748374026c20659a5f1a575f4f9f489c419c3769305c2d4c265c1f5c1c4c155c0a6c0029 0x1b17c06c53022d7c03b53012d3c04b4e012d3406a5f02a97804a5301a94803a4700e91803a4501a8dc08a3601a8d77e23402a57c0694f01a51c0393f0224dc0492f01a49c0a85f01a13c0684700e0fc088370120bc0682703605c03c5f02f17803c5300f14803b5f00ed4c03b4700ed1803b4501297c04a5300e91c03a460129177c24400e8fc03a3e0128f40b95f00e53c0394700e4fc039370124bc0492702e17c0384f00e11c0383f00e0dc0482f01209c0e81701317406b5d01ad3c03b4d01294404a430129040aa3f02a8f806a370128cc0aa3202e53c0594d02e51c0594502a4fc069370124bc0b92702e13c0784d02e11c0784502a0fc068370120bc0b82759005c04b4f01ad3804b47012d0c04b4201297404a4701a91804a450128fc04a3e0128f40694f01a51c0493f0124dc0492f0124b4049270164940684f01a11c0483f0120dc0482f0120b40482701e0940d81701b17403b5d00e97403a4e01a90803a4102a90003a3d0164f40593501e0f40783500f17c03c5e00f14f9a45201ad7c06b5300ed3c03b4e012d3403a5f00e94c03a4f00e93803a4d00e8fc03a3e00e8ec03a3900e8cc06a3200e8c76223003657c0394f0165340394700e5140693f01a4dc0392f00e49c1085f00e13c0784d00e11c0384501a0fc0683700e0bc0382703605c06c5f02b17808c5302314803b5f02ad7804b53012d4803b4f00ed3404b4b012d2803b4701ad1803b45d88d1004a5f02a97804a5301294803a4f00e93803a4d0128fc04a3e0128f40a95f02253c069470124fc039370124bc0492d01249c0592502a17c0884f01a11c0483f00e0dc0482f0120b40482701e0956301701b17c0dc5302ed7c04b53036d3c06b47012d0c05a5f01697805a5303694805a4700e91804a3f0128f80595e0165180493e0124b80985f02613c068470120fc098370160bc0782d01609c0582501605406c5f04314c0bb5f012d4c10b4f01ad1c04b4301e97c07a5e01e94c10a5201a91c03a460128fc04a3e04a57c0d94f01a51c0493f0464dc0792f0164b4079270164940785e01a1180483e0120b80781601b17fa845ee9914fa045202ed7c04b53e7cd3f9e34ee74d3406b47e28d1404b43d84d080ba5fe7097804a53e6c94806a47e6491b8a2450128ff9823ed848f74d15f03653c069470124fe951370124bee312d03649f97125a2017c1084f01a11c0483f6900dc0482f7ec0b410827e580955e01700f17403b4700ed1806b4500e91c03a4600e91403a3f00e8f803a3b00e8e403a3301a8c803a31de88c00394f00e534039470165140693f01a4dc0392f00e49c0384f00e1340384701e1140683f01a0dc0382f00e09c0d81700f5b403d6c01b1b403c5e01b1740bc5c00edb404b4a00e9b403a5e00e9740aa5c00e93803a4901a90803a41de490003a3d036574039550364f40d935042174038550420f410835036db378250016513772500164f010b6cdd894007844dd49400783c01b17403b5d01ad2c04b4a00e97403a4f02a93806a4b02e9240aa4302a9080ba41dd090003a3f00e8f40a94f01a51f9213f0164f7911370164d40b92f00e49c0a84f01a11f9003f01e0f78f03701e0d40b82f00e09d5c01701b1b406c5e01b1740bc5c01adb406b5e022d740bb5c01a97808a5d01a93806a4901a90808a4102290003a3d0128e404a31036574069550224f40d935042174068550220f41083500f17804c5d00edb403b5e00ed740ab5c00ed3803b49012d0803b41012d0003a6d00e97804a5d02a97008a4e01292804a4203a574039550124b40e925046174038550120b41182500f17c03c5e00f14c0ac5201ad7c06b5300ed3c03b4e01ad3403a5f00e94c03a4f00e8fc06a3e00e8f76223c02a57c0394f00e51c0693f01a4dc0392f00e49c0a85f00e13c0384701a0fc0683700e0bc0382703605c03c5f00f17803c5302f14803b5f00ed4c03b4f00ed3803b4d01297c04a5300e93c03a3f00e8f804a3dd888f00b95f00e53c0394700e4fc039370124bc0492702e17c0384f00e11c0383f00e0dc0482f01209c0d81701717c0dc5e01714c05c5201ad7c0db53016d3c04b4d00e97c0ea5300e93c03a4d00e8fc06a3b0368cc0595e00e5180593600e4980985f01613c0584d01611c078450260fc068370260bc0382701f17c10c5e01f14c07c5201ad7c10b5301ad3c04b4d00e97c11a5300e93c03a4d00e8fc06a3b0428cc1295f01e53c0594d01e51c059450364fc0693703a4bc0392701e1780384601a0d80382600f17f9445ee4d14f8e45201ad7f8d35301ad3f8a34ed8cd3403a5fe3094c03a4fe2c93b6524d00e8ff8b23e01a8ef8a239dfc8cf7d232dec8c76a230d3057c0d94fe2453403947a945140d93f01a4dc0e92f00e49e8705f04213f8804d00e11db40450420fc068370460bc0382756005c08c5d01ad3c06b4e00ed377a34c02ad1c03b45012d0c06b4202a91c0aa4602a91404a3f01a8f806a3d01a53c0a9470124fc0b9370124bc0a92701a13c0a8470120fc0b8370120bc0a82755c05c03a3f00e8f808a3d00e4fc039370124bc0892700e0fc038370120bc0882703a05c08c5d022d3c03b4d012d2c08b4a022d1c08b4600ed178534402297408a4f00e93404a3f02e8f808a3d02253c089470124fc0b9370124bc0892702213c088470120fc0b8370120bc0882755405c04c5d00ed3c03b4e01ad377a34c02ad1c06b4500ed0c03b4202a91c0ba4602a91403a3f00e8f803a3d00e53c0b9470224fc0a9370124bc0a92700e13c0b8470220fc0a8370120bc0a82755005c04a3f01a8f804a3d01a4fc069370124bc0492701a0fc068370120bc0482703605c04b5d012d3c04b4d012d2c04b4a012d1c06b46012d178234401297404a4f02a93804a4d0128fc04a3d02253c0a9470124fc049370124bc0492702213c0a8470120fc048370120bc0482754805c0ac5e02b14806b5e022d4803b4e00ed3403b4a00ed2403b4600ed1403b4200ed0403a5e01294803a4e00e93404a4a00e92403a4600e91404a4200e90403a3e00e8f404a3a00e8e403a3600e8d403a340128c803a310128c00594d0165140893d01a4d40492d00e4940784d01e1140883d01a0d40482d00e09403d6e02b58806c6e02318803c5e01317403b6e012d8803b5e00ed7403b4e00ed3403b4c012d2803b49012d200aa6e01298803a5e0129778025c00e93803a4d00e8f804a3d03657403955022534069450124f4039350124b40d92504217403855022134068450120f4038350120b410825 16 65535 6 63 11 2047 22 4194303
def cc_44_29 : Nat → List (Nat × Nat) := unpackCursorV4 0xfb81f217d837ac1f407d25b74c6661be3b5f7688dcd8e8bbf111a220440188010f05eccb65d5e3a92a8eed9a4e253e441888010c12180420452c8029 0x3be25802294006a448d815007844012d0007a5c01a9200aa4001e172350440164d00592c01e0f1710140131b7ad45e0131480ab5eefcd6a3e35602ad4804a6def497804a5aef095804a52eec4f5731350124b7ba1258d01580484e0120f80482e0120b170016046d3c04b4b046d1c04b4301e93c07a4e01e92c06a4a01e91c06a4601e90c08a4204a53c129470124fc1193701e4bc0592d01e49c0592501e1180483e0120b807816f3cd77b234feb0d3804b4be30d1c04b43e04d0bcf25df3093fcb24e01292f9b24af2091fc724601290f66242cec53f0b1470124fe971370124bee512df0449fc01259b013e330470120fda60370120bdfd02dee409fb80255bc05c03c5d022d4408b43012d0403a5d00e93c03a4d02a8ec0ba3900e8dc08a3302a8c40a94f0165340a9470165140893f02a4dc0b92f00e49c0a84f01e1340a84701e1140883f02a0dc0b82f00e09d6e01700ed7403b4f022d3803b4d00e92c03a4900e91c03a4300e90403a3700e8d803a3502253c0894700e4fc0393d00e4dc0593500e4bc0392702213c0884700e0fc0383d00e0dc0783500e0bc0382703a05c03c5d00ed3c03b4d00ed2c03b4a00ed1c03b4601ad1403a5d00e93c03a4d00e8fc0aa3e00e8f40394f00e51c0893f02a4dc0392f00e49c0384f00e11c0883f02a0dc0382f00e09c0e817012d3403a5d00e8e404a3200e8c404a30016534059450124b40392501e134078450120b40382501317803c5d00edb403b6c012d6803b5900ed5804b5200ed4404b5000ed1803b4500e9b404a5a01a95804a5200e91804a45ecc9100394d03a5140493d00e4d40492d03a4940384d0461140483d00e0d40482d04609403a5d0128c80492dec04940482deb8097b0244eb891004b4f012d3804b4d00e97404a4b01a9280aa4701a91804a4302a8dc0aa36ec48d40894f02a51c0393f02a4dc0492febc49c0884f02a11c0383f02a0dc0482feb409d6c01702b17c08c53016d7c05b5e016d4c0eb52016d3c04b4e00e97c0ea5303692c03a4702290c03a3700e8d40595e0165380393e00e4980985f02213c098470160fc0783d0160dc058350260bc038270160540ac5f02314c07b5f01ed7807b53046d4807b4f012d3803a5f04694c10a4b00e91c08a4300e8dc03a3504a57c0894f04251c0793f0164f4079370164d40e92f00e49c0785e01e1380383e00e0980781602b17c08c5302ad7fb635e00ed4fb5352022d3f9834ed90d3403a5fed097bb2253eb094b9f24be7892b9d24900e91f8b24602290f6424100e8df8b236e648d74e15f02253ef214700e4feb413d03a4dfab13503a4bc03927a2417c0884f86811c0383f70c0f411837ea80d41182f00e09d6701701b17406b4f00ed3404b4b01ad2806b4701ad1803b4501a97406a4f00e93404a3f02a8f806a3d01a53c069470124fc0b9370124bc0692701a13c068470120fc0b8370120bc0682703605c06c5d01a93806a4201290408a4000e8f40894d01a5140593d0164d40884d01a1140783d01e0d406d6d01b5b006c6d01ad7808b5d01ad5406b52012d4408b5000ed3403b45012d0406a5601a95408a4601a917a72440228f806a3d022574069550225340d94501a4b40d925022174068550221341084501a0b41082501ad7404a310224f7a41350220f7a2035e90913a224401b17408b4f00ed340bb4700ed1404b4302e91fa524602e91404a3f0228f808a3d02253fa31470124fc0b9370124bc0b92702213fa10470120fc0b8370120bc0b82759405c06d6e0235880ac6e00f18804c5e00f17403b6e012d8803b5600ed5403b54012d4803b51012d4003b4600ed140aa6e01298803a5600e95403a460129178024400e8f804a3d0225740695500e5340d9450124f4039350124b40d9250221740685500e134108450120f4038350120b410825 15 32767 6 63 11 2047 22 4194303
def cc_44_30 : Nat → List (Nat × Nat) := unpackCursorV4 0xed31d613ac07445e58dca078e1ec56ccb17886badcfde94ad1359e50b4df670ac91554fa2df44848708cb110a31f083e007228cc619021c5808c0004 0x2293c0da4b03691c08a430168fc03a3d0168ec04a390168dc03a350168cc04a310165380593e0164980884f02611c0583f01e0f4058370160d40982f02609c05815022d7004b4cf7092003a44f70d3004b4000e911de03401e09004b4c02294003a3c02e8c00784c774090059440164f00784c60005008d6d022db7a1259022947dd24d02e925e324502e90408a3df6c8e7da2350228c7d914d6085140893df604d40885e0221380883e01e0f1dc0265fc05808a4f04292c10a4702290c07a3f00e8f407a3b0128e407a3700e8d407a330128c40894f04251c0793f0164f4079370164d41292f04a49c0784e01e0f80782601e05bed45dfb4d7408a4fe9892fa0249e3491c08a43e1090408a3fed48f7ea23bfa48e7e6237f948d408a33d988c40894fc8451c0893fcfc4f7df137f784d6e712fb3049c0884f92411c0883f9c00f7d7037f580d5ff02f76c09d7e01700ed3c03b4e00ed3403a4f00e93408a4b00e91c03a450228ec04a3902253c089470224fc0593d0224dc0593502e4bc0392702213c088470220fc0783d0220dc0783502e0bc038275f005c03b5f00ed7803b5d01a94c06a5201294403a3f01a8f803a3d00e8dc03a3501a8cc06a3201a57c0595d01a55c0595501a4fc0693702e4bc0392701a17c0785d01a15c0685501a0fc0683702e0bc0382703605c05b4f01ad3405b4b016d2405b47016d1405b43022d0403a3f02e8ec03a3702e8cc0394e00e4980584f01e134058470161140983f0260dc0982f00e09c07b4f01ad3407b4b01ed2407b4701ad1407b43022d0403a3f02e8ec03a3702e8cc0794f016534079470165141293f04a4dc0b92f00e49c0384e00e09bcf45d00ed3f9434d02ed2fd434902ed1fd334500ed0fb5341f3c94403a3fed08f80ba3b00e8dc0ba33e0c8c80394fb2c5340b947f485173e13fc7c4dc0b92f00e49c0384f7681340b847f441166f03f91c0dc0b82f00e09d7a01700f17c03c5b00f15c03c5300ed3c03b4e00ed2c03b4700ed0c04b4201293c04a4b01291c04a4300e57c0395703a53c0e94700e4fc039370124bc0492700e17c0385704613c1184700e0fc038370120bc0482703a05c0ec6000ed3004b400169100592404718003b4c012d0006a4401e09004c5e01317404b6d012d6404b52012d4404b5000ed1404a6d01296804a590129600aa5601294804a510129400aa4601291406a4402a5771415502a537ce1450124b7c412502a1763c05502a137cd0450120b7bd025012d3c04b4e012d3404a4b01292408a4701290c04a410228dc03a3502253c0894d02251f121450224fc0593d0224dc059350124be9812702213c0884d02211e3a0450220fc0783d0220dc078350120bda70275e005c05a5c01649007a5c01e09004c5e01317404b6d02ad7803b5d02ad700ab4e012d2404b42012d0404b400129b40aa5e01297408a5c02a93804a4a01292404a4801290804a41012903ca15dc585573d14dc405140492df0c497c905d8f81566e04d8e01140482def009404b4f012d3804b4d01a93c06a4e00e93406a3f01a8f804a3b0128e404a3301a8c804a31e088c00694f016534069470165140693f0364f40693701a4d40492f03649c0684f01e1340684701a1140683f0420f40683701a0d40482f04209c0d817f14d7006b5401293004a3cf1496008a500169130e15401651004b4001697006a4802a9000595cc34510078240131b7af45e0131480ab5ef18d6b1635602ad4804a6df1097804a5af0c95804a52c305580494e0124f80492e0124b3c203d5cc0d40482dee80957201503ad3c04b4b03ad1c04b4301693c05a4e01692c06a4a01691c05a4601690c08a420165180493e0124b80984f02611c0483f0260dc0582f01e0b40582701609405815ef8d7006b5401293004a3c 15 32767 6 63 11 2047 22 4194303
def cc_44_31 : Nat → List (Nat × Nat) := unpackCursorV4 0xa0b7237a1ab3dd66b42b77d642ab45473e6f7cda11ac224c4268c44208800e8a17182c08016 0x12d3c04b4b012d2804b4701ad1804a4f00e93804a3f0128f804a3d02a53c069470124fc049370124bc0492d01249c0592502a13c068470120fc048370120bc0482d01209c0782562c05c03b4300ed0804b4100e93c03a4e00e93403a3b01a8e803a3900e8dc03a3600e8cc03a3100e53c0594d00e51c0394502a4fc0693700e4bc0392700e13c0784d00e11c0384502a0fc0683700e0bc0382703a05c05a4f00e93405a4b01292405a4700e91405a430129040aa3f01a8ec06a3702a8cc0594e0164d80584f01e134058470161140983f01a0dc0982f02609c07a4f00e93407a4b01292407a4700e91407a430129040aa3f01a8ec06a3702a8cc0794f016534079470165140a93f01a4dc1292f04a49c0684e01a0dbed45dfb4d4406a4fe509340aa4bfc89240aa47fc491406a43e6c9040aa3f01a8efa823901a8dc0aa33e188c40694fcc85340a947fc05140a93f01a4deea12fb6449c0684f9681340a847fbc1140a83f01a0de0202f7a009d8901701a97c06a5b01a95c06a5301a93c06a4b01a92406a4701a90c08a410228fc08a3b0228dc08a3301a57c0695701a53c069470224fc089370364bc0d92701a17c0685701a13c068470220fc088370420bc1082703605c0da6001a96008a5000e9100594404298006a5802294003a4401e11008d6d0231b408b5e022d4804b51022d4008b4e022d3408b4c02ed1408b42012d0404b4001a95808a4602e91403a440228f808a3d022537e214502e4f6d313502e4b7ec125022137db04502e0f5e203502e0b7eb025012d3c08b4e012d1c04b43012d0804a4700e91804a3f0128f804a3d02253f221470124fc0493d0124ded11350124bc0492d01249c0592502213e4a0470120fc0483d0120dde00350120bc0482d01209c0782561c05c04b4c0164d004b4c01e0d008d6d01b1680bc5902f16008b6d02ed3808b4d012d3008a5e02e96408a5202294408a5002293808a4d0228f803a3d00e8f00ba390228c808a310228c3e814db505140893df844d6e912db40497e704d78c1140883df680d60102d77c09403b4b012d2803b4900e93c03a4e00e92c03a4900e90c08a4200e9078524000e8fc03a3e00e8f40894f03a51c0393f0164f40393700e4d40392f03a4b40392700e4940884f04611c0383f01e0f40383700e0d40382f0460b40382700e0940e817022d7004b4cf8c92003a44f8cd3004b4000e912cf13401649004b4c02294003a3c02e8c00594cb38490078340235b408b6de8c96408a51f909340ba49b509140ba410228f7e2239f848d408a310225780894e0224f80593cb3449be004d6081140883df600d581015 15 32767 6 63 11 2047 22 4194303
def cur_44 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_44_31 (Nat.sub p 992)) (cc_44_30 (Nat.sub p 960)) (Nat.blt p 992)) (cc_44_29 (Nat.sub p 928)) (Nat.blt p 960)) (cc_44_28 (Nat.sub p 896)) (Nat.blt p 928)) (cc_44_27 (Nat.sub p 864)) (Nat.blt p 896)) (cc_44_26 (Nat.sub p 832)) (Nat.blt p 864)) (cc_44_25 (Nat.sub p 800)) (Nat.blt p 832)) (cc_44_24 (Nat.sub p 768)) (Nat.blt p 800)) (cc_44_23 (Nat.sub p 736)) (Nat.blt p 768)) (cc_44_22 (Nat.sub p 704)) (Nat.blt p 736)) (cc_44_21 (Nat.sub p 672)) (Nat.blt p 704)) (cc_44_20 (Nat.sub p 640)) (Nat.blt p 672)) (cc_44_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_44_18 (Nat.sub p 576)) (Nat.blt p 608)) (cc_44_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_44_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_44_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_44_14 (Nat.sub p 448)) (Nat.blt p 480)) (cc_44_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_44_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_44_11 (Nat.sub p 352)) (Nat.blt p 384)) (cc_44_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_44_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_44_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_44_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_44_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_44_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_44_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_44_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_44_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_44_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_44_0 p) (Nat.blt p 32)
def f_44 : Nat → Nat × Nat := unpackForestF 0x7de927ef48bf7945fbc22802d3fd66bbf5925fac12fac8efd6473f394df9c26fac8dfd646bf024df8da67c08e7e046bf004df589bfac4d7d849bee34cf611cfb08d7d829bec135f581bfac0d401687e8b49f45a2fa2517d108a00a4fee12ef9a517cd08bdc24fee127792577c90bbdc247ee123784d6bc54b1e125ef092b7840f7b824fdc125ee9ad77c963ba4bddd256ee89ef74497b804fdc02500521f54d7baa6a5d525eecd2275494fad46bd8244eb493f5c913ad04fd5252ea89af540d40147fcb45ee9d2272d14fa148dd2244e84a3f44913a108fcb452e59a7f2cd3b9669bcb25ee592973514b9648dcb23ee5892f2c09401477c445ee2229f1e4ff8f26fc783fe3c1bf1114b886a7c4253e211f7108e78829bc404d0051bea917b85689aa452d51af704d13546a5c025cd51a3efc9335468dbe24cd51a2ed6d3b6b687ba93fdd49beea0ff7506fb5b42dad1fee293f71487b5a3edb09fed84df6c07fb6037dad1eea8d13544bdb3924d9c126a894b5449daa24dd511f6c4d135447baf454d7e2a6bc0f75424fae252d5092eaf153598a9ab93dd5c92ea809f554a5aa02500519e84d274268ba1249d0922e848ff42477a1237d29a26949b342467a1a3fd0d1de868df44689a226cd0d19e841140129f9a35ecd1a966897f3c4ab9e245cd129e688e7398a59a235cd0af66a97f354a79a0350049fdd917b3147376453c911fe5cd33244779604cc911be548f32768994234c9c126488cf2407f92037bb2296448e6ec6a790459bb12fe195871c6958e346c32b061897b0c4bb8625cc5c2e61895715ac18624dc4da7618933118c186245c36b061a5330d28986126bb129e148e305ac584460c15b760d583054c57624fc0d1c5ff14eff6bd80235bfd295d8936f6ac57b36ebeeb05ecd8af98c17b26ebdd2e5ec98aec48776241bcdae5d88feec4677613ebb52fddc932ed4a77604d0049bdb917ee868d74246b7229db897adc4a56e24eb71255c514adc48d6e242b70af5bb17edd8a76e02500497db4d668f8bf66b4ab35a4d9ad22d509966b46b35255a48facd49166a46b389c59c4d2cd28d47c53a3daf593586c94bd47b53b15a558ad1ac528d5b451b0eb056c93ec16b95b24bafa3057c172b648f5e24cae5aa574912b90495b243ad817d6c09e8f6a547b4eabab1563582b14b957462abdb055c9ba8f69756246aaa2955497a8f69553452a9a2854c1328f68d4ed6ea76b15455829d8c550360a753753c9329d4c547b43a3da153116a996b14c25ea3d29d2c9328f49747a43a3c9752117e9149148453a3c1e80249e7369339b459cd24ce69167347f39a3b9cd1bd0ad12854d939a339f91fcfc8ee7e46f3fb449fd2e4fc8ce7328b3e2599cc9fcf4972794b3399379de2cce64be756913a4599cc9380213e5c6bd2e3529712fcda9566d48b2e2539711ccd514a5c46b34259970afcca97e654a72e13598a374c49ba5c25f2f46e97e364bcd8a5c24f2e05e0041fc0917a59473024539311fcacd324c4772a14c9311bca48f24f6892823493c924988ce4c27f26137812294948e6046a7244598112fc6958644695223468d2b046897a344bb1a25c8fcae4689563dac11a24d8eda7468932398c11a2458d6b046a532352891a02681129c648e22dac5184608b5b745d5822d4c50224f8ad1c44f14e276bd1423589d294089361eac50f36e88eb043cd8a218c10f26e87d2e43c98a044870224186dae4088fe044670c25c85d2cc0857e134bf0a25c84d29c085360fac50846083d374084be0d6910356282ab0414972066c503a5e81d2940cd420424f0203e0041bbd717e0068d002467ae29bd6979eb4a4f5a4e7ad253f5149eb48cf5a427de2cbd657df48dcfa26e7aca7be1589f18c0f826e7aca3bdb17ded8a6f59257ac2f0020bde96b2c745f771a53b8d25dc690f214c771a33b8929e147cee248771233ba4e1dd268ee04663a29b1cd79d8ac2ec25e639a9ba8d29d468cea04671628ba5581c549ee835c71525b9b181cd2b8e2a4772d26390d51c9488e412471521b8a4bdc524ec7352639a737b589c0ac0e025c6f63137cd81bd4dcc734b6ed23373149b94bcc734a6d62936b141b5298c73466b2b7359589b1ac0d64626bdb03589b9ad498d6262639a1b1cd09a78b4d435869d2f31c94da5498c724b63921b44d21a18b2c715f6763733d1b19d6c4c714f66da432958998ac0cc25c651b132a979954a4ca350638a3b2117d91690c84536389eb1c0b80104ec6238629acb14964028bec42385fda4afe9297f492bfa4860d262fe9197f28cc00345fc2300514d7d490bdc595ed2c804d7d79490b835e5c11d2e08e570470ba3585c11b2e04d971048b8036009a9ad11b96d470b43625a124ad2d49692bcb4248009a7acc9615fac4afb6e57da72be8e5608a4b015e57d1c004d2d5d490acd6256528ab4579594a0013474c6b72ac96131ac498c6e54d2426318951490a5c5253d24296d354b482a614e52d20263151316dca42384c5b128c501458a898a3a4c51ca7d1793e8a49f35e4f9a927c579314709e3404e62a275151396c098a364dca026d1513126c9a1404ca2a2640913106c013434bdaa24a8fd2d4a892a3b4ae2c24a8dd29690933444993624c951254660125e482b0a41185202bc9014e00929a36d251b48c8e13446c231b5145166bc8b23645c9222c0d8da6a288c6c445b0222521112886d34f432b0218db10c27086134369a5a11581082b884150369a39f9580fc8c081c5040ca01f9150fc6c07e1383f6281fad40fd6887e134369a19f5580da29e7c25c368a59e7180f36b87a4503cda81b451cf06807814c3b12a1d8530ed28876144368a19d5180da27e7424c3689d9c7160e38a07245038db01b44dce06807013c36d221b6570dd4606e13436caa1b44cc024a40124e342b11a1144d4ac06a15c341b11a4980d02dc6814e0092599ad24cd28c6045232e2c180d7cc92686035330e2f187148c36bc61b5230c9b180d04c14626015e0092515f148ba47e5d23b2e91b9748ccaf8a05c4602bd2f965580b24b859c502cda6164930af4a657a4c2bd20004918a2adc5156228a2c945144a9ac05136229d301445b8a42985213c288b11445380248650349009210048f88f8c447c5226a301345308f6c44bc5025ca611ed68948a04a14c23da91249808f2dc4825823caf0048ec8d6b03fc5f22ca20ff14c8869c441361fda9105178828a44135e209a91044d87f684402321fcaf0048e86e8be3d3481ed1e0f49206e8a63bc5d1de288dcd487149e38a4b1c5238e493071486373501b9a40dcd000246c2cc6e166310b3178598a434460165b10cd140596b432450165a90c4980592dc2f95c17c9e0b25885d4b02c95e168b60b44f0592a40123315da70048c8552702623f14c940988ec512802623713c9809ad104d4d826233008af0940f8418a420a5f10eb0086970434982245010c9408294c41260011460da2f878d203c4901e1480da29874520388a21c02e0d9a906c4800226c1a1380a51f8644a029476181400a51b85c4c02c6881626c0a5198520d82904c0105e09c1f02d148164be105600812e040930218a0101280592982c4c0160bc0bc5206e2802e9481829c0c14205d2002c0980208c01c5f045a40229201129001c5303ca401b1440d05c01b5200c90006178048a4044500112900a538052840224000c230040d80102e0001f 10 11
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 1011 bds_44 (dagTraceF m_44 s_44 9 f_44) (cur_44 0) s_44 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 64 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_2 : treeBlockF 64 96 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_3 : treeBlockF 96 128 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_4 : treeBlockF 128 160 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_5 : treeBlockF 160 192 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_6 : treeBlockF 192 224 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_7 : treeBlockF 224 256 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_8 : treeBlockF 256 288 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_9 : treeBlockF 288 320 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_10 : treeBlockF 320 352 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_11 : treeBlockF 352 384 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_12 : treeBlockF 384 416 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_13 : treeBlockF 416 448 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_14 : treeBlockF 448 480 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_15 : treeBlockF 480 512 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_16 : treeBlockF 512 544 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_17 : treeBlockF 544 576 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_18 : treeBlockF 576 608 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_19 : treeBlockF 608 640 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_20 : treeBlockF 640 672 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_21 : treeBlockF 672 704 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_22 : treeBlockF 704 736 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_23 : treeBlockF 736 768 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_24 : treeBlockF 768 800 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_25 : treeBlockF 800 832 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_26 : treeBlockF 832 864 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_27 : treeBlockF 864 896 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_28 : treeBlockF 896 928 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_29 : treeBlockF 928 960 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_30 : treeBlockF 960 992 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_31 : treeBlockF 992 1011 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nj_44_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_1 (fun _ h1 h2 => treeBlockF_at nb_44_2 h1 h2)
theorem nj_44_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_2 (fun _ h1 h2 => treeBlockF_at nb_44_3 h1 h2)
theorem nj_44_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_3 (fun _ h1 h2 => treeBlockF_at nb_44_4 h1 h2)
theorem nj_44_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_4 (fun _ h1 h2 => treeBlockF_at nb_44_5 h1 h2)
theorem nj_44_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_5 (fun _ h1 h2 => treeBlockF_at nb_44_6 h1 h2)
theorem nj_44_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_6 (fun _ h1 h2 => treeBlockF_at nb_44_7 h1 h2)
theorem nj_44_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_7 (fun _ h1 h2 => treeBlockF_at nb_44_8 h1 h2)
theorem nj_44_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_8 (fun _ h1 h2 => treeBlockF_at nb_44_9 h1 h2)
theorem nj_44_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_9 (fun _ h1 h2 => treeBlockF_at nb_44_10 h1 h2)
theorem nj_44_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_10 (fun _ h1 h2 => treeBlockF_at nb_44_11 h1 h2)
theorem nj_44_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_11 (fun _ h1 h2 => treeBlockF_at nb_44_12 h1 h2)
theorem nj_44_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_12 (fun _ h1 h2 => treeBlockF_at nb_44_13 h1 h2)
theorem nj_44_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_13 (fun _ h1 h2 => treeBlockF_at nb_44_14 h1 h2)
theorem nj_44_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_14 (fun _ h1 h2 => treeBlockF_at nb_44_15 h1 h2)
theorem nj_44_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_15 (fun _ h1 h2 => treeBlockF_at nb_44_16 h1 h2)
theorem nj_44_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_16 (fun _ h1 h2 => treeBlockF_at nb_44_17 h1 h2)
theorem nj_44_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_17 (fun _ h1 h2 => treeBlockF_at nb_44_18 h1 h2)
theorem nj_44_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_18 (fun _ h1 h2 => treeBlockF_at nb_44_19 h1 h2)
theorem nj_44_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_19 (fun _ h1 h2 => treeBlockF_at nb_44_20 h1 h2)
theorem nj_44_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_20 (fun _ h1 h2 => treeBlockF_at nb_44_21 h1 h2)
theorem nj_44_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_21 (fun _ h1 h2 => treeBlockF_at nb_44_22 h1 h2)
theorem nj_44_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_22 (fun _ h1 h2 => treeBlockF_at nb_44_23 h1 h2)
theorem nj_44_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_23 (fun _ h1 h2 => treeBlockF_at nb_44_24 h1 h2)
theorem nj_44_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_24 (fun _ h1 h2 => treeBlockF_at nb_44_25 h1 h2)
theorem nj_44_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_25 (fun _ h1 h2 => treeBlockF_at nb_44_26 h1 h2)
theorem nj_44_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_26 (fun _ h1 h2 => treeBlockF_at nb_44_27 h1 h2)
theorem nj_44_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_27 (fun _ h1 h2 => treeBlockF_at nb_44_28 h1 h2)
theorem nj_44_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_28 (fun _ h1 h2 => treeBlockF_at nb_44_29 h1 h2)
theorem nj_44_30 : ∀ i, 0 ≤ i → i < 992 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_29 (fun _ h1 h2 => treeBlockF_at nb_44_30 h1 h2)
theorem nj_44_31 : ∀ i, 0 ≤ i → i < 1011 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := block_join nj_44_30 (fun _ h1 h2 => treeBlockF_at nb_44_31 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 1011 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1011 (dagTraceF m_44 s_44 9 f_44) cur_44) i = true := nj_44_31
theorem lb_44 : LowerBin m_44 s_44 g_44 10 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def g_45 : Nat := 0x117175717171757
def ep_45 : Nat := 0x1600000000001640000000400016004000000040010606020606060201121202121212020114145414141454
theorem epk_45 : ep_45 = edgePack fullMask g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_44, s_44, 10, g_44), (m_41, s_41, 8, g_41), (m_42, s_42, 8, g_42), (m_36, s_36, 8, g_36), (m_24, s_24, 7, g_24), (m_25, s_25, 7, g_25), (m_32, s_32, 7, g_32), (m_35, s_35, 7, g_35), (m_40, s_40, 6, g_40), (m_37, s_37, 6, g_37), (m_38, s_38, 6, g_38), (m_43, s_43, 6, g_43), (m_39, s_39, 6, g_39), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_31, s_31, 5, g_31), (m_18, s_18, 5, g_18), (m_33, s_33, 5, g_33), (m_34, s_34, 5, g_34), (m_19, s_19, 5, g_19), (m_20, s_20, 5, g_20), (m_21, s_21, 5, g_21), (m_22, s_22, 5, g_22), (m_23, s_23, 5, g_23)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_44
  · exact lb_41
  · exact lb_42
  · exact lb_36
  · exact lb_24
  · exact lb_25
  · exact lb_32
  · exact lb_35
  · exact lb_40
  · exact lb_37
  · exact lb_38
  · exact lb_43
  · exact lb_39
  · exact lb_29
  · exact lb_30
  · exact lb_31
  · exact lb_18
  · exact lb_33
  · exact lb_34
  · exact lb_19
  · exact lb_20
  · exact lb_21
  · exact lb_22
  · exact lb_23
theorem sub_45 : ∀ b ∈ bds_45, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 fullMask g_45 ep_45 0 bds_45 (dagTraceF fullMask rootStock 9 f_45) (cur_45 0) rootStock 9 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 fullMask g_45 ep_45 bds_45 0 (dagTraceF fullMask rootStock 9 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin fullMask rootStock g_45 10 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def wg : List Gate := [⟨GateOp.and, [4, 3]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.and, [7, 0]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [9, 1]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [7, 0]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [10, 15]⟩]
theorem wfits : Monotone2 ⟨wg, 16⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 16⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3907578024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3907578024)) (11 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3907578024) = g_45 by decide]
  exact lb_45

end PEqualNP.Outside.L_meta_42833

theorem PEqualNP.Outside.L_meta_42833 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3907578024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3907578024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_42833.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3907578024) 11 PEqualNP.Outside.L_meta_42833.root_lb PEqualNP.Outside.L_meta_42833.wg 16 rfl PEqualNP.Outside.L_meta_42833.wfits PEqualNP.Outside.L_meta_42833.weval
