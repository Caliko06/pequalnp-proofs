import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45425

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

def m_0 : Nat := 0x55005500
def s_0 : List Nat := [0x11001100, 0x5000500, 0x5500]
def g_0 : Nat := 0x1001500
def ep_0 : Nat := 0x14000000000000000000000000000100040000000000010010000000000000000000
theorem epk_0 : ep_0 = edgePack 0x55005500 g_0 := by decide +kernel
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, 0x55005500 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
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

def m_1 : Nat := 0x5500550000000000
def s_1 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_1 : Nat := 0x100150000000000
def ep_1 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
theorem epk_1 : ep_1 = edgePack 0x5500550000000000 g_1 := by decide +kernel
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, 0x5500550000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
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

def m_2 : Nat := 0x5555000000000000
def s_2 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_2 : Nat := 0x115000000000000
def ep_2 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
theorem epk_2 : ep_2 = edgePack 0x5555000000000000 g_2 := by decide +kernel
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, 0x5555000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
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

def m_3 : Nat := 0x33330000
def s_3 : List Nat := [0x11110000, 0x3030000, 0x330000]
def g_3 : Nat := 0x1130000
def ep_3 : Nat := 0x120000000000000102000000000000000000000000000001100000
theorem epk_3 : ep_3 = edgePack 0x33330000 g_3 := by decide +kernel
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, 0x33330000 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
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

def m_4 : Nat := 0x3333000000000000
def s_4 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_4 : Nat := 0x113000000000000
def ep_4 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
theorem epk_4 : ep_4 = edgePack 0x3333000000000000 g_4 := by decide +kernel
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, 0x3333000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
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

def m_5 : Nat := 0xf0f0000
def s_5 : List Nat := [0x5050000, 0x3030000, 0xf0000]
def g_5 : Nat := 0x1070000
def ep_5 : Nat := 0x60000000000000000000000000000010200000000000001040000
theorem epk_5 : ep_5 = edgePack 0xf0f0000 g_5 := by decide +kernel
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, 0xf0f0000 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
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

def m_6 : Nat := 0xf0f000000000000
def s_6 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_6 : Nat := 0x107000000000000
def ep_6 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
theorem epk_6 : ep_6 = edgePack 0xf0f000000000000 g_6 := by decide +kernel
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, 0xf0f000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
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

def m_7 : Nat := 0xff00000000
def s_7 : List Nat := [0x5500000000, 0x3300000000, 0xf00000000]
def g_7 : Nat := 0x1700000000
def ep_7 : Nat := 0x60000000000000012000000000000001400000000
theorem epk_7 : ep_7 = edgePack 0xff00000000 g_7 := by decide +kernel
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, 0xff00000000 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
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

def m_8 : Nat := 0xff000000000000
def s_8 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_8 : Nat := 0x17000000000000
def ep_8 : Nat := 0x600000000000000120000000000000014000000000000
theorem epk_8 : ep_8 = edgePack 0xff000000000000 g_8 := by decide +kernel
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, 0xff000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
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

def m_9 : Nat := 0xaaaa0000aaaa
def s_9 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_9 : Nat := 0x200002aaa
def ep_9 : Nat := 0x2aa800000000000000000000000200000080000000020000080000000002000020000000000000000000
theorem epk_9 : ep_9 = edgePack 0xaaaa0000aaaa g_9 := by decide +kernel
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, 0xaaaa0000aaaa &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_9] at hb
def cc_9_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb49682d05a0b4149290520a4148290520949282504a09410921042084108210420748e81d03a0740c901c001 0x1124c852040531f280e83c701a360b1a048b34855a0284f13260884c40221e0b0e04852482520108e07460284c1022060f02069ea3fe91df28df7467a13fc49de04dee267592fa095ce49e5247203f8c1dbc0dd9066c02f5c15a409cd046601f2c0d8c05c1026000f 11 2047 5 31 10 1023 17 131071
def cc_9_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x910a04074d5a3160c15285088e9c3260c12204050508040000000000 0x3f271f134f094764938461c344d91c6a8d332799134bc985e912d4996244a8a65251262413234 7 127 2 3 10 1023 17 131071
def cc_9_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x0 0x0 1 1 1 1 1 1 2 3
def cur_9 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_9_2 (Nat.sub p 64)) (cc_9_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_9_0 p) (Nat.blt p 32)
def f_9 : Nat → Nat × Nat := unpackForestF 0xf938f934063fed28ed24063b0637e3440633d638d634053fc93cc934053b0537be440533b24cb244052fa54ca544052b05279a340523043f043b7e4c7e407d4c7d400437683c6834682c68240433042f042b4f484f404d3c4d300427384c3844382c38240423041f041b1e481e401e381e300417084c0844083c08340413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV4 m_9 g_9 ep_9 64 bds_9 (dagTraceF m_9 s_9 5 f_9) (cur_9 0) s_9 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9_0 : treeBlockF 0 32 (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 64 (dagTraceF m_9 s_9 5 f_9) cur_9) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9_1 : treeBlockF 32 64 (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 64 (dagTraceF m_9 s_9 5 f_9) cur_9) = true := by decide +kernel
theorem nj_9_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 64 (dagTraceF m_9 s_9 5 f_9) cur_9) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_9_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_9_1 h1 h2)
theorem nc_9 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 64 (dagTraceF m_9 s_9 5 f_9) cur_9) i = true := nj_9_1
theorem lb_9 : LowerBin m_9 s_9 g_9 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_9 kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0x5555000055550000
def s_10 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_10 : Nat := 0x115000001550000
def ep_10 : Nat := 0x40000000000000000000000014000000540000010400000100000001100000010000000000000000000000
theorem epk_10 : ep_10 = edgePack 0x5555000055550000 g_10 := by decide +kernel
def bds_10 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_10 : KnownBin bds_10 := by
  intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_10 : ∀ b ∈ bds_10, 0x5555000055550000 &&& b.1 = b.1 := by intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_10 : Nat → List (Nat × Nat) := fun _ => []
def f_10 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV4 m_10 g_10 ep_10 0 bds_10 (dagTraceF m_10 s_10 4 f_10) (cur_10 0) s_10 4 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_10 g_10 ep_10 bds_10 0 (dagTraceF m_10 s_10 4 f_10) cur_10 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_10 : LowerBin m_10 s_10 g_10 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_10 kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0xff000000ff
def s_11 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_11 : Nat := 0x17000000ff
def ep_11 : Nat := 0xe800000000000000000000000000000000000000060000000000000012000000000000001400000000
theorem epk_11 : ep_11 = edgePack 0xff000000ff g_11 := by decide +kernel
def bds_11 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_11 : KnownBin bds_11 := by
  intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_11 : ∀ b ∈ bds_11, 0xff000000ff &&& b.1 = b.1 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_11 : Nat → List (Nat × Nat) := fun _ => []
def f_11 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV4 m_11 g_11 ep_11 0 bds_11 (dagTraceF m_11 s_11 4 f_11) (cur_11 0) s_11 4 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_11 g_11 ep_11 bds_11 0 (dagTraceF m_11 s_11 4 f_11) cur_11 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_11 : LowerBin m_11 s_11 g_11 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_11 kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xff000000ff0000
def s_12 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_12 : Nat := 0x17000000570000
def ep_12 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
theorem epk_12 : ep_12 = edgePack 0xff000000ff0000 g_12 := by decide +kernel
def bds_12 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_12 : KnownBin bds_12 := by
  intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_12 : ∀ b ∈ bds_12, 0xff000000ff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_12 : Nat → List (Nat × Nat) := fun _ => []
def f_12 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV4 m_12 g_12 ep_12 0 bds_12 (dagTraceF m_12 s_12 4 f_12) (cur_12 0) s_12 4 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_12 g_12 ep_12 bds_12 0 (dagTraceF m_12 s_12 4 f_12) cur_12 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_12 : LowerBin m_12 s_12 g_12 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_12 kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0x55555555
def s_13 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_13 : Nat := 0x1551555
def ep_13 : Nat := 0x14000000000000540040000000000100040000000000010010000000000000000000
theorem epk_13 : ep_13 = edgePack 0x55555555 g_13 := by decide +kernel
def bds_13 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_13 : ∀ b ∈ bds_13, 0x55555555 &&& b.1 = b.1 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_13 : Nat → List (Nat × Nat) := fun _ => []
def f_13 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV4 m_13 g_13 ep_13 0 bds_13 (dagTraceF m_13 s_13 4 f_13) (cur_13 0) s_13 4 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_13 g_13 ep_13 bds_13 0 (dagTraceF m_13 s_13 4 f_13) cur_13 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_13 kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xaaaaaaaa
def s_14 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_14 : Nat := 0x22aaa
def ep_14 : Nat := 0x2aa80000000000020080000000000002080000000000000220000000000000000000
theorem epk_14 : ep_14 = edgePack 0xaaaaaaaa g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, 0xaaaaaaaa &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def cc_14_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb49682d05a0b4149290520a4148290520949282504a09410921042084108210420748e81d03a0740c901c001 0x1124c852040531f280e83c701a360b1a048b34855a0284f13260884c40221e0b0e04852482520108e07460284c1022060f02069ea3fe91df28df7467a13fc49de04dee267592fa095ce49e5247203f8c1dbc0dd9066c02f5c15a409cd046601f2c0d8c05c1026000f 11 2047 5 31 10 1023 17 131071
def cc_14_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x910a04074d5a3160c15285088e9c3260c12204050508040000000000 0x3f271f134f094764938461c344d91c6a8d332799134bc985e912d4996244a8a65251262413234 7 127 2 3 10 1023 17 131071
def cc_14_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x0 0x0 1 1 1 1 1 1 2 3
def cur_14 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_14_2 (Nat.sub p 64)) (cc_14_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_14_0 p) (Nat.blt p 32)
def f_14 : Nat → Nat × Nat := unpackForestF 0xf938f934063fed28ed24063b0637e3440633d638d634053fc93cc934053b0537be440533b24cb244052fa54ca544052b05279a340523043f043b7e4c7e407d4c7d400437683c6834682c68240433042f042b4f484f404d3c4d300427384c3844382c38240423041f041b1e481e401e381e300417084c0844083c08340413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 64 bds_14 (dagTraceF m_14 s_14 5 f_14) (cur_14 0) s_14 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14_0 : treeBlockF 0 32 (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) cur_14) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14_1 : treeBlockF 32 64 (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) cur_14) = true := by decide +kernel
theorem nj_14_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) cur_14) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_14_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_14_1 h1 h2)
theorem nc_14 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) cur_14) i = true := nj_14_1
theorem lb_14 : LowerBin m_14 s_14 g_14 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x5555555500000000
def s_15 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_15 : Nat := 0x115151500000000
def ep_15 : Nat := 0x1400000000000014000000000000010404040000000001101010000000000000000000000000
theorem epk_15 : ep_15 = edgePack 0x5555555500000000 g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2)]
theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_1
  · exact lb_2
theorem sub_15 : ∀ b ∈ bds_15, 0x5555555500000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_15 : Nat → List (Nat × Nat) := fun _ => []
def f_15 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 0 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) s_15 4 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_15 g_15 ep_15 bds_15 0 (dagTraceF m_15 s_15 4 f_15) cur_15 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0x33333333
def s_16 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_16 : Nat := 0x1133333
def ep_16 : Nat := 0x32200000000000120000000000000102000000000000000000000000000001100000
theorem epk_16 : ep_16 = edgePack 0x33333333 g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_16 : ∀ b ∈ bds_16, 0x33333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_16 : Nat → List (Nat × Nat) := fun _ => []
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 0 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_16 g_16 ep_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) cur_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x3333333300000000
def s_17 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_17 : Nat := 0x113111300000000
def ep_17 : Nat := 0x1000000000000012000200000000010200020000000000000000000000000110111000000000
theorem epk_17 : ep_17 = edgePack 0x3333333300000000 g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_17 : ∀ b ∈ bds_17, 0x3333333300000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_17 : Nat → List (Nat × Nat) := fun _ => []
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 0 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_17 g_17 ep_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) cur_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xf0f0f0f
def s_18 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_18 : Nat := 0x1070f0f
def ep_18 : Nat := 0xe080000000000060000000000000000000000000000010200000000000001040000
theorem epk_18 : ep_18 = edgePack 0xf0f0f0f g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_18 : ∀ b ∈ bds_18, 0xf0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_18 g_18 ep_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xf0f0f0f00000000
def s_19 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_19 : Nat := 0x107050700000000
def ep_19 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
theorem epk_19 : ep_19 = edgePack 0xf0f0f0f00000000 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_19 : ∀ b ∈ bds_19, 0xf0f0f0f00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_19 : Nat → List (Nat × Nat) := fun _ => []
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 0 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_19 g_19 ep_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) cur_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xff00ff00
def s_20 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_20 : Nat := 0x1003f00
def ep_20 : Nat := 0x3e0000000000000000000000000001000c0000000000010030000000000001000000
theorem epk_20 : ep_20 = edgePack 0xff00ff00 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_20 : ∀ b ∈ bds_20, 0xff00ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_20 g_20 ep_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xff00ff0000000000
def s_21 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_21 : Nat := 0x100150000000000
def ep_21 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
theorem epk_21 : ep_21 = edgePack 0xff00ff0000000000 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_21 : ∀ b ∈ bds_21, 0xff00ff0000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_21 g_21 ep_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xffff0000
def s_22 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_22 : Nat := 0x1570000
def ep_22 : Nat := 0x560000000000000102000000000000010200000000000001540000
theorem epk_22 : ep_22 = edgePack 0xffff0000 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_3
  · exact lb_5
theorem sub_22 : ∀ b ∈ bds_22, 0xffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_22 g_22 ep_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xffff00000000
def s_23 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_23 : Nat := 0x151700000000
def ep_23 : Nat := 0x200000000000004060000000000001012000000000000151400000000
theorem epk_23 : ep_23 = edgePack 0xffff00000000 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_23 : ∀ b ∈ bds_23, 0xffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xffff000000000000
def s_24 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_24 : Nat := 0x117000000000000
def ep_24 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_24 : ep_24 = edgePack 0xffff000000000000 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_4
  · exact lb_6
  · exact lb_8
theorem sub_24 : ∀ b ∈ bds_24, 0xffff000000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
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

def m_25 : Nat := 0x5555555555555555
def s_25 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_25 : Nat := 0x115151501551555
def ep_25 : Nat := 0x40004000001400000014000014000000540040010404040100040001101010010010000000000000000000
theorem epk_25 : ep_25 = edgePack 0x5555555555555555 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 5, g_10), (m_13, s_13, 5, g_13), (m_15, s_15, 5, g_15), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_10
  · exact lb_13
  · exact lb_15
  · exact lb_0
  · exact lb_1
  · exact lb_2
theorem sub_25 : ∀ b ∈ bds_25, 0x5555555555555555 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_25 : Nat → List (Nat × Nat) := unpackCursorV4 0xc06030162a1502633090b903a01 0x6340815c523431345344334464543a3842342134a34f934b734713433a4f3a4b3a473a433a3f3a3b3a373a333926001f 9 511 4 15 11 2047 16 65535
def f_25 : Nat → Nat × Nat := unpackForestF 0x2d3c5a5c15c168e51515a21234368844d05a1801f 4 11
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 11 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25 : treeBlockF 0 11 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 11 (dagTraceF m_25 s_25 6 f_25) cur_25) = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 11 (dagTraceF m_25 s_25 6 f_25) cur_25) i = true := fun _ h1 h2 => treeBlockF_at nb_25 h1 h2
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xaaaaaaaaaaaaaaaa
def s_26 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_26 : Nat := 0x2000200022aaa
def ep_26 : Nat := 0x2aa80000000000002aa80002000200020080000200020002080000020002000220000000000000000000
theorem epk_26 : ep_26 = edgePack 0xaaaaaaaaaaaaaaaa g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 6, g_9), (m_14, s_14, 6, g_14)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_9
  · exact lb_14
theorem sub_26 : ∀ b ∈ bds_26, 0xaaaaaaaaaaaaaaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 6 f_26) (cur_26 0) s_26 6 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 6 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x3333333333333333
def s_27 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_27 : Nat := 0x113111301133333
def ep_27 : Nat := 0x222000001000000032200012000200120000010200020102000000000000000000000110111001100000
theorem epk_27 : ep_27 = edgePack 0x3333333333333333 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 5, g_16), (m_17, s_17, 5, g_17), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_17
  · exact lb_3
  · exact lb_4
theorem sub_27 : ∀ b ∈ bds_27, 0x3333333333333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV4 0x1e0f0783c1c2e07038193c86432190b95c2e170a1d02813190c824111883503801 0xca5cc250b238aa34a134835c7b506a4c6244592432302244223433442a5c1a541124db4fd34bbb479b43924f8a4b724752434a3f423b3a370a33001f 9 511 4 15 10 1023 16 65535
def f_27 : Nat → Nat × Nat := unpackForestF 0xe9e1d2f12e62500e8f48e291a51340e86193c325bf5c7ea0191d7262e445a48190c31f863b0c6e2d1052e123414a82490319801f 5 10
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 28 bds_27 (dagTraceF m_27 s_27 6 f_27) (cur_27 0) s_27 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 28 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 28 (dagTraceF m_27 s_27 6 f_27) cur_27) = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 28 (dagTraceF m_27 s_27 6 f_27) cur_27) i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xcccccccccccccccc
def s_28 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_28 : Nat := 0x4040400440ccc
def ep_28 : Nat := 0x4008c80000040000000c8800040000004400c00004040400000c0000000000000000000004040400440000
theorem epk_28 : ep_28 = edgePack 0xcccccccccccccccc g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_28 : KnownBin bds_28 := by intro b hb; simp [bds_28] at hb
theorem sub_28 : ∀ b ∈ bds_28, 0xcccccccccccccccc &&& b.1 = b.1 := by intro b hb; simp [bds_28] at hb
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_28] at hb
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xec0ec0ec0ec0ec0ec0ec0ec0d46d40d40d40cc2cc0cc0c42c40c40c40bc2bc0bc0b42b40b40ac2ac0ac0ac0a42068001 0x71160da281a24c3248060530b8a0141282624844170802a0d04c18088284f0489a0704c0c0880c170102a6234fbe69778d1ed9a1d824faa4975091e8921d023f9e477208de3919c614f8a296f851de8a1ba13f6e276d84dd9899b212f62256a849d4891a804f4e0968011cf8219e03f3a076580dca8199202f1e0563809c58118801f0a0361005c08098001f 12 4095 6 63 11 2047 19 524287
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x9690909082808072707070626060606060606060363030303030303030300600 0x88d721b50849720a5080171f850780e1d83472571c1546a4f1a13460d617b505cd216b40580f158304cd712b50489711a50445710950 8 255 3 7 10 1023 18 262143
def cc_28_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xe1c3862c182950a10a04080c983060c183060c030000000000000000 0x2e81c5c034b409164112b92656244a625148492722c4d450982992c502502649040 7 127 3 7 11 2047 19 524287
def cc_28_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x21052102 0xc85231944c28e30234 5 31 2 3 10 1023 18 262143
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_28_3 (Nat.sub p 96)) (cc_28_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_28_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0x31948c65100b4fc08e3023402d2c0b47b80e2e03402d0ec848b21100a4fac932b2440292c0a47a44a291240290c0a3f028ee4c5893142494c92502484c921000a37028cc094f0252dfb5c7ed41fa5c7e941f85c7e14009470250dd838760d0093f70571c154024ec0937684f1a134024cc092f024ad5b5856d415b4856d01583c560c009270248c084f0212d0b5c42d410a5c42941095c4254008470210c083f020ecbc582f140ba4c2e900b94c2e5000837020cc992826490082f201708054020ac08271813060440208c493c124d0081f0c13030440206c08170417010540204c001f 7 11
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 101 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 101 (dagTraceF m_28 s_28 6 f_28) cur_28) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 64 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 101 (dagTraceF m_28 s_28 6 f_28) cur_28) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_2 : treeBlockF 64 96 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 101 (dagTraceF m_28 s_28 6 f_28) cur_28) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_3 : treeBlockF 96 101 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 101 (dagTraceF m_28 s_28 6 f_28) cur_28) = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 101 (dagTraceF m_28 s_28 6 f_28) cur_28) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nj_28_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 101 (dagTraceF m_28 s_28 6 f_28) cur_28) i = true := block_join nj_28_1 (fun _ h1 h2 => treeBlockF_at nb_28_2 h1 h2)
theorem nj_28_3 : ∀ i, 0 ≤ i → i < 101 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 101 (dagTraceF m_28 s_28 6 f_28) cur_28) i = true := block_join nj_28_2 (fun _ h1 h2 => treeBlockF_at nb_28_3 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 101 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 101 (dagTraceF m_28 s_28 6 f_28) cur_28) i = true := nj_28_3
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xf0f0f0f0f0f0f0f
def s_29 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_29 : Nat := 0x107050701070f0f
def ep_29 : Nat := 0xa080000040000000e080006000200060000000000000000000001020002010200000104050401040000
theorem epk_29 : ep_29 = edgePack 0xf0f0f0f0f0f0f0f g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_19
  · exact lb_5
  · exact lb_6
theorem sub_29 : ∀ b ∈ bds_29, 0xf0f0f0f0f0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV4 0x1e0f0783c1c2e07038193c86432190b95c2e170a1d02813190c824111883503801 0xca5cc250b238aa34a134835c7b506a4c6244592432302244223433442a5c1a541124db4fd34bbb479b43924f8a4b724752434a3f423b3a370a33001f 9 511 4 15 10 1023 16 65535
def f_29 : Nat → Nat × Nat := unpackForestF 0xe9e1d2f12e62500e8f48e291a51340e86193c325bf5c7ea0191d7262e445a48190c31f863b0c6e2d1052e123414a82490319801f 5 10
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 28 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 28 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 28 (dagTraceF m_29 s_29 6 f_29) cur_29) = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 28 (dagTraceF m_29 s_29 6 f_29) cur_29) i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xf0f0f0f0f0f0f0f0
def s_30 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_30 : Nat := 0x101010005030f0
def ep_30 : Nat := 0x4020e000001000000030a000100000005000c0000000000000000000101010000030000010101000500000
theorem epk_30 : ep_30 = edgePack 0xf0f0f0f0f0f0f0f0 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_30 : KnownBin bds_30 := by intro b hb; simp [bds_30] at hb
theorem sub_30 : ∀ b ∈ bds_30, 0xf0f0f0f0f0f0f0f0 &&& b.1 = b.1 := by intro b hb; simp [bds_30] at hb
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_30] at hb
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xec0ec0ec0ec0ec0ec0ec0ec0d46d40d40d40cc2cc0cc0c42c40c40c40bc2bc0bc0b42b40b40ac2ac0ac0ac0a42068001 0x71160da281a24c3248060530b8a0141282624844170802a0d04c18088284f0489a0704c0c0880c170102a6234fbe69778d1ed9a1d824faa4975091e8921d023f9e477208de3919c614f8a296f851de8a1ba13f6e276d84dd9899b212f62256a849d4891a804f4e0968011cf8219e03f3a076580dca8199202f1e0563809c58118801f0a0361005c08098001f 12 4095 6 63 11 2047 19 524287
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x9690909082808072707070626060606060606060363030303030303030300600 0x88d721b50849720a5080171f850780e1d83472571c1546a4f1a13460d617b505cd216b40580f158304cd712b50489711a50445710950 8 255 3 7 10 1023 18 262143
def cc_30_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xe1c3862c182950a10a04080c983060c183060c030000000000000000 0x2e81c5c034b409164112b92656244a625148492722c4d450982992c502502649040 7 127 3 7 11 2047 19 524287
def cc_30_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x21052102 0xc85231944c28e30234 5 31 2 3 10 1023 18 262143
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_30_3 (Nat.sub p 96)) (cc_30_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0x31948c65100b4fc08e3023402d2c0b47b80e2e03402d0ec848b21100a4fac932b2440292c0a47a44a291240290c0a3f028ee4c5893142494c92502484c921000a37028cc094f0252dfb5c7ed41fa5c7e941f85c7e14009470250dd838760d0093f70571c154024ec0937684f1a134024cc092f024ad5b5856d415b4856d01583c560c009270248c084f0212d0b5c42d410a5c42941095c4254008470210c083f020ecbc582f140ba4c2e900b94c2e5000837020cc992826490082f201708054020ac08271813060440208c493c124d0081f0c13030440206c08170417010540204c001f 7 11
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 101 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 101 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 64 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 101 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_2 : treeBlockF 64 96 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 101 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_3 : treeBlockF 96 101 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 101 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 101 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nj_30_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 101 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := block_join nj_30_1 (fun _ h1 h2 => treeBlockF_at nb_30_2 h1 h2)
theorem nj_30_3 : ∀ i, 0 ≤ i → i < 101 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 101 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := block_join nj_30_2 (fun _ h1 h2 => treeBlockF_at nb_30_3 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 101 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 101 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := nj_30_3
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xff00ff00ff00ff
def s_31 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_31 : Nat := 0x170017005700ff
def ep_31 : Nat := 0x4000e800000000000000a80000000000000000000600060002000000120012000200000014001400540000
theorem epk_31 : ep_31 = edgePack 0xff00ff00ff00ff g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 5, g_11), (m_12, s_12, 5, g_12), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_12
  · exact lb_7
  · exact lb_8
theorem sub_31 : ∀ b ∈ bds_31, 0xff00ff00ff00ff &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_31 : Nat → List (Nat × Nat) := unpackCursorV4 0x1e0f0783c1c2e07038193c86432190b95c2e170a1d02813190c824111883503801 0xca5cc250b238aa34a034835c7b506a4c6244582432302244223433442a5c1a541024db4fd34bbb479b43924f8a4b724752434a3f423b3a370a33001f 9 511 4 15 10 1023 16 65535
def f_31 : Nat → Nat × Nat := unpackForestF 0xe9e1d2f12e62500e8f48e291a50340e86193c325bf5c7ea0191d7262e445848190c31f863b0c6e2d1052e123414a82090319801f 5 10
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 28 bds_31 (dagTraceF m_31 s_31 6 f_31) (cur_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31 : treeBlockF 0 28 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 28 (dagTraceF m_31 s_31 6 f_31) cur_31) = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 28 (dagTraceF m_31 s_31 6 f_31) cur_31) i = true := fun _ h1 h2 => treeBlockF_at nb_31 h1 h2
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xff00ff00ff00ff00
def s_32 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_32 : Nat := 0x100150001003f00
def ep_32 : Nat := 0x2a000000140000003e0000000000000000000100040001000c0001001000010030000100150001000000
theorem epk_32 : ep_32 = edgePack 0xff00ff00ff00ff00 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 5, g_20), (m_21, s_21, 5, g_21), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_21
  · exact lb_0
  · exact lb_1
theorem sub_32 : ∀ b ∈ bds_32, 0xff00ff00ff00ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV4 0x1e0f0783c1d1ca6430371b85c2e170b850e814091482412090481e6f0783483801 0x2a4619450a11860532e2815130a1a241141e498e240609e2c4d0e6a0634829a00c5304289b23fd11dd88de6467213f889db44dd4266912f40959049c2246001f 9 511 4 15 11 2047 17 131071
def f_32 : Nat → Nat × Nat := unpackForestF 0xa3f0a3bbc50b94cb9400a37a930a3440a33093f093b7450724c72400937593c59340933092f092b2b502b482b400927114c11440923001f 5 11
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 28 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 28 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 28 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 28 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xffff0000ffff
def s_33 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_33 : Nat := 0x151700003fff
def ep_33 : Nat := 0x2ae8000000000000000000000002000000c00000040600000c0000001012000030000000151400000000
theorem epk_33 : ep_33 = edgePack 0xffff0000ffff g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 6, g_9), (m_11, s_11, 5, g_11), (m_23, s_23, 5, g_23), (m_7, s_7, 4, g_7)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_9
  · exact lb_11
  · exact lb_23
  · exact lb_7
theorem sub_33 : ∀ b ∈ bds_33, 0xffff0000ffff &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) s_33 6 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 6 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xffff0000ffff0000
def s_34 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_34 : Nat := 0x117000001570000
def ep_34 : Nat := 0x40000000000000000000000016000000560000010600000102000001120000010200000114000001540000
theorem epk_34 : ep_34 = edgePack 0xffff0000ffff0000 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24), (m_12, s_12, 5, g_12), (m_22, s_22, 5, g_22), (m_10, s_10, 5, g_10), (m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_12
  · exact lb_22
  · exact lb_10
  · exact lb_6
  · exact lb_8
  · exact lb_2
  · exact lb_3
  · exact lb_4
  · exact lb_5
theorem sub_34 : ∀ b ∈ bds_34, 0xffff0000ffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 7 f_34) (cur_34 0) s_34 7 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 7 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xffffffff
def s_35 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_35 : Nat := 0x1573fff
def ep_35 : Nat := 0x3ea800000000005600c00000000001020c0000000000010230000000000001540000
theorem epk_35 : ep_35 = edgePack 0xffffffff g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 6, g_14), (m_13, s_13, 5, g_13), (m_16, s_16, 5, g_16), (m_18, s_18, 5, g_18), (m_20, s_20, 5, g_20), (m_22, s_22, 5, g_22), (m_0, s_0, 4, g_0), (m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_13
  · exact lb_16
  · exact lb_18
  · exact lb_20
  · exact lb_22
  · exact lb_0
  · exact lb_3
  · exact lb_5
theorem sub_35 : ∀ b ∈ bds_35, 0xffffffff &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xeb00ea02ea00e902e900dc99dc80dc80d986d980d980d48aca94bb9ebb80bb80bb80b807b781b603b581b384a1a480c2739a62a2579646a234a411c600a20001 0x788d00592401649004814022d381d3420548f403a3a00e8d808a350705381b1420224f81a13d00e4b80392d0164a8059260224940592400e4880885d0221540883d0220d40481d00e0640481500e0441825001e93005a4001a1900584805c11003a4805490008a3c00e8e003a340168c00393401a190058380500d007a4e01e90808a3e00e8e803a360228c80794a01e5180893a0224d80592e0164b40585501a1500482e0120b40481e0160640481201604407a4e01e90808a3e00e8e803a360228c80695e01a5480694a01e5180693a0224d80592e0164b40784e016128078460161080883e0160e8088360160c80482e0120b40481e016068058190160600481201604407b440404a00f12401e110088340120a00e02401e0d007a4401e5100581402209008a340224d00381c01605006b4f01ad0c06a4f01a90c08a3f01e8ec07a370348cc069430304fc0793b01e4dc0b1330284bc0892b02249c0912301a13c0684e01210c0684201a0fc0483b01a0e80683701e0d80483301a0bc0482b01a0a8068270220980482301607c0581e01607406c5b01b15c06b5b01ad5c08b4f01ed2c07b470bcd0c06a5b01a95c2e24f0ac93807a4b01e91c2a2430949082423f0808f808a3b00e8e808a3700e8d81f2330648c80495b01a55c1614f01252c0794a01e51c0794601250c1313f0124ec0893a0224dc089360124cc0592f0164b80592d0481740585b01a1680685701a158110550201500784f01612c0784701610c0883f0160ec088370160cc0482f0120b80482d01207c0481e01606c0581901204c0481201604407a3f01e8ec07a3701e8cc0493f0124ec049370124cc0492f0124ac0492701248c0583f0160ec058370160cc0582f0160ac0582701608c0481f01206c0481a01205c0481601204c06b4b01ad1c06a4b01a91c07a3f01e8ec07a3701e8cc0494b01251c0493f0124ec049370124cc0492f0124ac0492701248c0584d01612c058470161140583f0160ec058370160cc0582f0160ac0582701608c0481f01206c0481701204c06a4b01a91c0494b01251c0492f0124ac0492701248c0584d01612c058470161140582f0160ac0582701608c0481f0120740481b01205c0581501204c06b4b01ad1c06a4b01a91c07a3f01e8ec07a3701e8cc0494b01251c0493f0124ec049370124cc0492f0124ac0492701248c0584d01612c058470161140583f0160ec058370160cc0582f0160ac0582701608c0481f01206c0481701204c06b4b01ad1c03a4b00e91c03a3f00e8ec03a3700e8cc0494b01251c0493f0124ec049370124cc0392f00e4ac0392700e48c0584d01612c058470161140583f0160ec058370160cc0382f00e0ac0382700e08c0481f0120740481b01205c0581501204c06c5b01b15c06b5b01ad5c07b4f01ed2c07b4701ed0c04a5b01295c04a4f01292c04a4701290c04a3f0128ec04a370128cc0595d01656c059570165540594f01652c0594701650c0593f0164ec059370164cc0492f0124b40492b0124a804927012498059250121740485b01215c048550181500484f01e1380484d0141300484b01211c04845010110048430121080483f0220f80483d00c0f00483b00e0e80483700e0d8048350080d0048330120c80482f0120b80482d01207c0581e0120764d34b92cd1e4624b91091e4023f8ec8ee392378188cdec14b72c51daf13f6ac4eda61376644cd6e12f5a84ad5c12753048d3d04d4ec12d2f04744c1150203f3e80ecc50372b80cc9802f2400ac5b02711008c3801f0d006c0701700404c0001f 16 65535 7 127 11 2047 22 4194303
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xaf96af80af80af01a19b981378bf68a05c98511730c130012f022d042b04238f2105210021001b0c188518801684168016800c940986098009800980038c0007 0x6c5a0d8ac12d3825a687a49804820e8f5f91c83a35764621252424a08493a09272124e024988785d0d0aa1e1343c228783d0f06a124a035ad06b561169cf4d09e1273b2420947c128f41c9d049390726c124c41c968492a09252124a01c93039250924222174342a8883d1106a220b41c148882507042129283d2304a3a1146c1e53824a10893e072740e4d824990492e0925a161542415058290904c12084240b058150d8b61b15c35ad86b571169e1ed2c3da3c1343094b61295c252784a4b094941291c3d2304a430947e128ec251d04a371146c128cc24ad849570929ef853824a5849470928612508249fba13e092760e4e8249b8393609266124c824978492e0925ae41742c2d868570d0aa1e13c2c25878470b086220fc2c1d888370b066120ac2415058290904e120982411848210902e12059a80a86b4f0d6861a93c352187a3f0f4761e8dc3d198694f092861a4fc249d86937092661a4bc249586927092461613c34270584d0b07e160ec2c1b858330b05e160ac2c13858230b02e1a0582c0a87a3f0f4761e8dc3d198693f092761a4dc24998692f092561a49c24918583f0b076160dc2c198582f0b0561609c2c118481f0b0361605c240987a4e0f484228f81d1d03a3611464125283ca30493a1126c164b824968585d0b0b41a1582c2a868540905c120b4240f058190902412044362d86c570d6b61ad5c3da787b4b0f68e1ed0c252d86a570f49e1292c3d2384a431147e128ec451b84a330b2ba1656c2cad059570d2ac16555b8aa0594f0b2961651c2ca18593f0b276164dc2c998492f0925c164b42c938592509246124882c2e8585b0b0ae16155b02a0584f0f09c1612c2c23858430b084160fc441f0583b07074160dc1c1b058330b0641609da813058250903e12078240e90054074803c15148a01e1300b240381503da2049200f088220d03e2a282500749074901111e33238644686c8c03caa0894409270c44d0683205838600681e961392807944180c85c1103da72734d0747ab48e41d1aa22310f26c1e4d43c2e878555806c1e0d539ae07b540f4a816490583229234072880e4d02c9207b4950682609343d228794e4e29a984f81c9d0393636264164a82c93079250b2481e1743c2a8784d0f08a12074240a88a48344800e8d0449a0a064280688c939112108a3e3447a0e4e81c9b089261124a22174442aa10261104a68d3045a208a44072780e4b02c9209064 16 65535 7 127 11 2047 19 524287
def cc_35_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xbc09bc00b391924392008f068e028e008a087e187e007e006d226d006d006c0261165022500050004f023f203f003f003e022b26074807000700010c00020000 0x7a3503936039356012a5f1260884d08845058390583103b4e03b496134203b415e34003a3e5d23d039390493103926039250885d088550383e0883d05829058218d45b07c5703b5b03b5703b4f03b4e03b4b03b498c34803b4703b438934203b417b34003a5b03a5703a4f03a4b07a4a03a4703a4603a4303a3f03a3e03a3d7515b711576c14f0794b07947651430393f6213d0393b03939039370393503933049310392f5c12d0392b0392703925039230885d0585b08857088550784f0584b07847058430383f0383e0883d0382f0382e0382b038290382303822058210881f0581b08817058135405c510540483c4c034058285a024500444b02403b6c583605706c058605304c4f0440482c4a02403a3f07a3b03a3707a330693f0693b06937069330692f0392b03927069230583f0583b05837058330582f0382b03827058230581f0581b058170581307b4b07b4708a4b03a4703a3f07a3b03a3707a335414b531470793f0793b07937079330892f0392b03927089230584d0584b05847058450583f0583b05837038330582f0382b03827058230581f0581b058170581303a5c5025008a4b03a475114b4f1470892f0392b03927089230584d0584b05847058450582f0582d0382b0382705825058230581f0581b058170581306b4b06b4706a4b03a4703a3f07a3b03a3707a330494b049470493f0493b04937049330492f0392b03927049230584d0584b05847058450583f0583b05837058330582f0382b03827058230481f0481b048170381303a5c4b25007b4e07b4207a4e07a4208a3e03a3a03a3608a324c15a4a1560794e0794a07946079420893e0393a03936089320592e0592d0585d058550583d058350482d0382904825038210581d05819058150581103a5c4725007b4b07b4708a4b03a4703a3f07a3e07a3b03a3707a3307a324814b461470793f0793b07937079330892f0392b03927089230584d0584b05847058450583f0583b05837058330582f0582d0382b0382705825058230581f0381b058170581307c5b07c5708b5b03b5703b4f07b4e07b4b03b4707b4307b425925b5625707a4f07a4b07a4707a4308a3f03a3b03a3708a330595d0595b05957059550594f0594b05947059430593f0593d0393b0393a0393703936059350592f0592b05927059230585d0585b0585705855550540584f0784e0584d5204c0584b05847058454e04405843058420583f0883e0583d0582f0482e0582d4d02c0582b0582a0582749026058254502405823048220381f0381e0381d07c5407a5408a4404a38432344015c3d14c039443b13c04938421340493003b4403a44 16 65535 7 127 11 2047 20 1048575
def cc_35_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xd806b0728cf687a03b09d80ec0740b419a00d006803011686b405a02c052109003e29f00f807813a09424a004c10290004000000 0x7e124812347f1546814c03944058187d01403b4b03b478724b8624703a3f07a3d03a3b03a3703a3503a337914b721470393f5e13d0393b0393703935039338512f8412b821277c1230884d0584b08847088450383f0383b038390383703833058310882f0582b08827058230881f0581b08817058137714c03944773407a458794507814c039447613c0393403b6c7436073348723406e34803b4403a446e3407035003b4c6f34803b446334007a586d24803a446b2346814c03944039340581868340048306a4506914c0394803944049406713c03934058186601403a346424e6324203a3e03a3a03a3603a320393a0393603926039250885d088550882d0482908825048210881d0881507a34 13 8191 6 63 11 2047 20 1048575
def cc_35_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x900190008d068c818c018195623f62006102610061005f045318471827402700268124051a141902180207220700060206000502038303800184008200800001 0x4a349e14c039449d13c04938089340493004a340381408b4e9b34204a3d05a3a05a3604a3504a340893a04939089360493103926039250885d0885503836038350882a058299a02605821ab45b07c5708b5b03b5703b4f07b4b07b4a03b4707b4608b4308a5b08a5708a4f08a4e07a4b07a4708a43a824205a3f05a3e05a3da515ba31579f14f0794b079479c1430893f9913d0393b0393708935089330892f2012d0892b04929089270892508923049210885d0585b08857088550784f0584b07847058430383b0383a05839038370383605833058310382703826038250881f0581b0881705813038289702403b6c953609406c0386003a3f03a3b03a3703a330693f0693b06937069330392f0392b03927039230583f0583b05837058330382f0382b03827038230581f0581b058170581303b4e07b4207a4e07a4203a3e03a3a03a3603a320794a079460393a039360392e0392d0585d058550583d038350482d058290482505821058190581107c5b07c5703b5b03b5703b4f03b4e03b4b03b4703b4307b429625b9325707a4f07a4b07a4707a4303a3f03a3b03a3703a330595d0595b05957059550594f0594b05947059430393f0393e0593d039370393503933039320592f0592b05927059230385d0385b0385703855920540384f0784e0384b0384703843038420383703836038350382f0482e0382b0382a038279102603823038220381f0581e0381d883408b3508f34803b448e24803a4403b4b03b477a14b731470393f0393b03937039330784d0584b07847078450383f0383b03837038330781f0581b07817058138834803b4403a406b1408b45a07c5603b4d03b4907b4803b4503b4403b4103a4e03a4d03a3a03a3603a3503a347014d07949079456a1416113d039356312d049298a125049210785d078550784d05849078450584103839058310782d078258824c03a446e24c03a446024c0794c039448335803b445f14c81120801447e01480124 16 65535 7 127 11 2047 20 1048575
def cc_35_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xfa03e80e06b800e0037c1c17a9daa7029c0a60629c8a022808905ade2df8b402d00a442900a01115c44011003440d002c20a042020800008 0x7b4b08a4b08a4707a3f07a33be14bbd1470793f079330892f0892b08927089230584d0584b05847058450583f058330582f0582b058270581f0581b0581705813ba35007b4b03a4b03a4703a3f03a3903a3303a31bb14bb91470793f079330392f0392b03927039230584d0584b05847058450583f0583d05835058330382f03827038230581f0581b058170581306b4b06a4b06a4707a3f07a330494b049470493f049330492f0492b04927049230584d0584b05847058450583f058330582f0582b05827058230481f0481b04817b535007b4908b4107a4e07a4208a3e03a3a03a3608a32b615ab41560794e079420893e0893a08936089320592e0592d0585d058550584d058450482d048250581d058190581505811b135007b4b08a4b08a4707a3f07a3907a3308a31b214bb01470793f079330892f0892b08927089230584d0584b05847058450583f0583d05835058330582f0582b05827058230581f058170581307c5b08b5b08b5707b4f07b4907b4308b41c325bc025707a4f07a4308a3f08a3b08a3708a330595d0595b05957059550594f0594d059450593f0593b05937059330592f0592b05927059230585d0585b0585705855bf0540584f0784e0584d0583f0883e0583dbc03c0583b0383a058370383605835b803405833058320582f0482e0582db702c0582b0582a05827b302605825af0240582304822ad34803b44ac24808a4407b4403b4d03b4507b4407a4e08a4d07a3e07a3da114d079459b13d089352212d04929aa125049210785d0785505849058410583905831a902607825a714c03944a613c0893408a6ca426005a3403b4404a4407b58a234803b44a125008a4ca024808a4422240 14 16383 6 63 11 2047 20 1048575
def cc_35_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xf00f00f00ea3ea0d2cd20cc3cc0cc0bc8a6ba41a40a40a40a219669609039009008e18c17e743e420366322320247012 0xde460dd24cdc24003a3dda23903a35d02310785d078550783d0483907835048310781d0781503b4c03b4408a4403a3d08a35d612ad51260784d078450583905831d834dd7241d424003a3d03a35049410785d078550784d0583905831cf34ccf24003b5cd235008b4cd125cd0250ce24ccc234c914c05818c92400484003b5ccb350ca15c04950c814c05818c7014f725b08a5703a4df624cf3241e524008a3ddf15bdb157d914d04941d313dcd12f0892b08927c61230785d0585b07857078550784d058310782f0582b07827058230781f0581b0781705813be04cbb0440483cb603405828c4024ba034b5024c2460c106c05860bd03cb90340482cb402407a3f07a330693f069330692f0692b06927069230583f058330582f0582b05827058230581f0581b0581705813 12 4095 5 31 11 2047 20 1048575
def cc_35_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x9c04d0a398fd062e3101842ba449a24051c25d92e01684b405812a1150098848224011848c04411d2835c1800a10500280102004 0x7fa303f81b00d25e0692b0349381a48c0b05e0582b02c1381608c0b03e0581b02c0b81604c1168208a3e01d1d00e8d8114640893a0449b0161740b0aa0584d024168160a40904a0582102c0c816044116b608b57045a0c0096dfa4ae08a3f0451d8228dc114660595d02cad81655c0b2aa0594d02c9f8164ec0b26e0593302c978164ac0b24e059237e02a0220f80706c0482e7d813016079e448003b5c7a9a83e4971f049803a4b01d23b9052dba28e0392f01c9580e49c072460784d02c2581e11c0f08a0382f01c1580e09c070460781f02c0d81e05c0b026f234c660983d4d68116ac03b4d045a600e935ae29ad213d0449c8224d596262d012d02494bd0494092420785d03c2a8161040f07a0583903c1a8160c40f05a0382903c1280e085e4498cf24c6b126022531da6b003b4c6a8a63ac481d4288e8014750923a0491d6468e9154648a6016061ce028f124b781238228f5c6296dc1476a09ebbc4bddc256ec1277309181e1340b0960784703c228160c40f05e0582b03c1381608c0f03e0581b03c0b81604dc2298e1240721ae38cd41c42b8e014c 13 8191 5 31 11 2047 21 2097151
def cc_35_8 : Nat → List (Nat × Nat) := unpackCursorV4 0xb586d01b10ec409b5a6c09a066809a02602806182060018005d0d7405d016835a01602580115344051003c20ec13b00d8501d40400004000 0xf8bd2a452045af4a4d480769a03b4503da24a097a4c4a403a4e01d26c705340f28b1813d0449ac544b40925324125024908161240b0820583902c1881e0b40f0540582902c1448c0980f04b1f02402c1081e0681a02c03a3401da200e9123a04806b5e035a9012d380969a07a498e12080e8f63647203a358a91881a5780d2a404949024a081e1340f08a0783d02c1c81e0d40b0620681a0340b4640900b05116024045a7460d080d4bc06a528b9274549080947c04a3d034af01a548072740493901c9b0124c40724c039250441e8220d41105a05829044128160840d0340681603da7cb4d0c1149f2b2430451f81e8ec0f46f1e233034a781a50e3427e0693b03c9b81a4ce2825e0692b0449381a48c0f07e0583b03c1b8160cc1105e0582b0441381608c0d03e0581b1b80d04405c1002c058138912e4449300f4890f15c870a601e5100f6d90c360025a6816d280b68c04b45025a201e9254248203a3d01d1a81e5280929207946024a081e1740f0aa0783a02c1cc280d80b06205b44045ae00ed31366810825c8392601e9200f48822240025a2414572082980494803ca20125000f8b607b5b03dab816d3c0b69c05b4d8812d82295c0f49e08a4d03d2281e90c0f47e03a3d03d1d81e8e40f46e03a3503d19aa08c61a2b70b15703ca7c245340f28a0794303c9f8ac4f40f2760493903c9b81e4d40f26604931830978224ac1124f0312303c2e81616c0f0ae0785502c2481610c0b0820782f02c1581e09c0b0460781f02c0d81e05c0b02701024 14 16383 6 63 11 2047 21 2097151
def cc_35_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xde3f159ab6a2e08b01f4e7d01c0d6f05bc06f01bc06d09b01642115f4500cd233008131e087411c04700190c640151048311044401100011 0x4a3d01d1d00e8d80946b3f14e024a10224f80927a0392e01c9681a1540903a058190440a8120441147e07a3b03d1bd248ce8c27e0793b03c9bd104ce8025e0892b04493cf848e7808a0783f02c1d81e0dc0b0660882f02c1582209c0b0463901f02c0d84805c0b02607a3f03d1d81e8dc0f4660693f0349d81a4dc0d2660692f0349581a49c0d2460583f02c1d8160dc0b0660582f02c1581609c0b0460581f02c0d8160680b02e0681602c0981ed3c0f69607b4703da181a93c0d49606a470352181a8fc0d47606a370351981653c0b2960594702ca18164fc0b2760593702c998164bc0b2560592a02c9381a4980b2473c05403c270220f80706c0482e0341301e9266c48203a3d9d11c80e8d66446206949034a081a4f409272069350249881e1340f08a08b4e9a9a14e093a64484069390349881a4b40925206925024908220f41106a0382901da20124a26624807a349b23000edb26a6c007b449a1364c89800b051310249c9a880e9766e4a208a3f03d1d81e8de604660695d024a881a4fc0d276069370349981a4bc0d256069270349181e0fc0b0760783702c198220bc0b0560882702c1181a07c0b0360681a0340b81a0580b02607a499512080e8f65c47203a359311881a5440d292069410349e8124e40d26a0493103c2681e1140b0620681a0340b00ed741169d2934201d2ecb093a4c484069510349c81a4c40d25a04929034928124841107a0883501c148160840d0340681601da248809242048058400249449c4900b0512525002c1403c0901c02807b4401ca60164b00746807b4e911a102293a4248403a3d01d1a81e8d00b2720893102c9481e4863a07a078358c8168220964003a0f015 14 16383 6 63 11 2047 21 2097151
def cc_35_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x9601910a6e466e006b066b00678767806780678067805c965c805c805c8051965003429b253b2500248119961882188010111000098d09800980098000130000 0x4920036b401ada0076b961350b01a000e972be4a15e240024a00124800d8b606c5701dad80ed66d26b003b5701da880ed3c0769c03b4b01da380ed0ed068403a5b0352d00e95c074ac03a4f01d2700e92c0748e03a43b312100e8fc0747c03a3d024ad81a55ec429e0494bae8a381250c0727e0393ea789e80e4bc0725c0392b01c9480e48c07244049210442e81a16c0d0ae088550442782212c1108e0884301c1f8220f4070760383901c1b80e0d4070660583101c178220b4070560382701c1280e08c0903e0881d0440d82205c1102a0481301d220128e2b64695715c0249c5544d0078a804a38ac91a558572a42995013c0249801b1680d8ac04b4e025a6d5c926ac48355239a8118812524092820393901c988124b40924b3f05d0342ac141359008b0403d02c1cd500d40b06206b5a01dab00ed3aa46855124ea812100e8f80947a0393a01c9c80e4d8092620392601c928221740d0aa0883d01c1a8220b40b0520882502c1080e4d00b248048140251e80e8e80746c04a35820a75385081127c0393a01c9b0224c80725c0492a0249300e488110ba0685a0342b01a1540d0a80884a638230220f8110640482e024110120780903a06c5b0362b81ad6c076ae03b4fad1a580ed1eb068604a5b0252b81293c0949604a47025218128fc0947a03a3b01d1d00e8dc0746c04a35024ad81255c0929f5314e024a581251c09286049420249fd3c4f80927a0392f01c9700e4b67c0ba0685b0342b81a1560609e0884b6302382210c1107e0383b01c1b8220cc0905e0482b0241381208c0903e0481d0240d8160640902f4d01502409812046964b003b4d01da281ed100749c03a4da40a681e5168627a08935a08968124a69424a0492103c2a8161240b0820583902c1881e0b40b0520782502c1080ed100748804b4e025a681e9269048203a3da391c80e8d68246204949024a081a1540f09a0784503c1e8160e40f06a05831025268129140f29c0494da289f00e4e80726c049320342a8120740b0320781502408822d3a866854224ea09210128f80947a0393a0249c80e4d8092620392601c9281a1541107a08835044168160a41104a05821 16 65535 7 127 11 2047 21 2097151
def cc_35_11 : Nat → List (Nat × Nat) := unpackCursorV4 0xb200b102b081aa8caa01aa00aa00a706a700a700a700a387a0869d079c02921471c1639c51a44696264119991092108004980401038103800007000000000000 0xbf8a65f84f22c0a95124ec0926d548fb0047b7d126b0892d041762a0aa2202d02c14df00940b04203a44bd1a85e4d20076897825c01d265409000dad003b5cbb1a85d4d00074b950250ba1260549300b47803934044920220e04206804b4c01da20168f0072489a04c108160220800746804928839275c09080947c03a3a01d1b0128c8072740393601c968124a40724a049210442e8221541107c08832108170220b411034140160362d81b15c0d6b606b5a01dab81ad580769f9734ecb1a580ed1f2a687913420352d81a95f1e49f8b24ec4125e1891f044877b2420251f8128f80947a0495b034abddc53c0929773147024a180e4ec072740493901c9b80e4d8092660493101c9380e4980724b4005d0342d81a15e280ab0604f04425b3411c110860883f4c81e80e0ec0706e5c03504419dc80bc4005a0882b02c14dc409ede04a0882302c1081207c11036130170240981b1680d8ac03b4e01da680e9340749203a4501d2080e8f40746a0494d024a48125140928204939024988124b40724a0885d0342a8221341109208845044208220f40b0720883502c1881ad2c0d68e03a4b01d2380e8fc0747603a3701d1981252c0928e0493f0249d8124dc092660392f0249680e4ac0724e0392501c918221340d09606847034228220fc11076088370441980e0bc070560382701c1181207c09036048170240980e92c0748e0494b024a380e4bc072560392701c9181e1340d096068470342280e0bc070560382701c1181207c0903a0481b0240b81e0540902606c5b0362b80ed6c076ae03b4f01da580ed1c0768604a5b0252b81293c0949604a470252180e8fc0747c04a3d01d1b80e8d40746603a3201cad80e55c0729f6d14e01ca6db0530072960394701ca2dac510072860394201c9b80e4d80726a0392f0249700e4b4110ba0685b0342b81a1541109e0884b0442382210c0707e0383b01c1b80e0cc0905e0482d0241581209c1104a0482301c0f80e074070360581901c0b822054070260381101da780ed2c0768e03b43034a781252c0d28e0494301c9f80e4ec0726e039330442782212c1108e0884301c1f80e0ec0706e038330441281207c0d036068170240980ed340768a03a4e01d2680e8e80746d6514db00a2d404b6c224a0885d0442a822124110820882d02c148220940b04203b5901da880ed340768a03a4e01d2680e8face47b6414daf0a280e4faa427a0492902490822174110aa088490442080e0e40b0620882d044128220741102a03b4401d2201ada2ca6a003b4ca81a0590942c649003a44 16 65535 7 127 11 2047 21 2097151
def cc_35_12 : Nat → List (Nat × Nat) := unpackCursorV4 0xc203080ac5aa82935d8b161054504b190c843010c04108ad62b00985260094125004d212044800d143400814200070418102100410004000 0xd6b406b56cf9a7678d0aa249d502420251f0128f40929a049450249c8124c40725a03925a282e81a1553c07a670354e8168160a73a04a0582102c920120500949a04a4503ca701e5093a27c0393a01c9b66c4c8092540492603c2e81a1680d0ac068550342a01e1380f0840783a3301b0120b8090440481e0240e81b16c0d6b606b57d21a7e88d0c094b604a57025278129340948a04a3f0251d8128dc094660495b024ab81253f4029c0494d0249fe704f8092760393a0249b80e4d80926604932a202e81a16c0d0ae0685503c2781e10d3807e0783b3281b81e0cc0905e0482b0241381208c0903e0481d0240d8160640902f9a01502409812044072495234e01da680e8db3046a0493901c9880e4980724a0885d0442a8221341108a0383d0441a8160a40b0438e35ca91265408f00946804928c489200f170078a98d35c0251c5408c00728804928c189200e902320a99034dc39a280e9380749a04a3a0251b5e8536ea28a0393601c9ae504a8092539312602490d0c176300aa08849044208160e40b0629b02dc9012e40d400769804b40c512c604942fe2495034ec09a6e389271a48204a3902518de0536e828a0393d01c9ad081762e0ab0804d67022c1c0f40b0738c03502c18e14913146b806a64bb1265408f31224803b5c025a861cd02a24b984240c29265fc933026b984354bc92660c492fe2497e124 14 16383 6 63 11 2047 21 2097151
def cc_35_13 : Nat → List (Nat × Nat) := unpackCursorV4 0x9e0b3c02760cec094a52902482c900918322063a2c605898b120604832f75b2aa15516b1b5e301a5238a40109011402200344068008920f080078000 0x1c0350df9a6600d00094a003a44bf0926f4d3b7868404a4e025215408fb0047b7913db189a80e4a4072434705d8d82aa880f4da06aa002d02c14eec0940b04204c50aa9ae6e490007479b6230db9265f88e300691b6344bc12e00e9336a2481835c02da601e4d00f0902c0440262e016d32140b82c03c03c180124a00969c04b4201d1ea808e40746bb12310249c8124c40f0ba0785503c2701e1085807c0783d03c0d05c0580d8b606c5a0362b01ad6c0d6ae04b4f025a7012d340d4b606a57e5127f209278e487c3241e091f80e8f77c477ba239dc11b80e8d7684677b231024ad81a55c0929204943024a0ddc4bc092576212702491d181740d0b6068578d02a81e13e1209ad304503c21ecc0fc5607a0783b02c1cec80df6006a0783302c18a7c0bc0f0566c02703c1181207c0f036160170240981ad680d6ac0494d0249e8124e40926a0493101c968124a40724a0492103c2e81a1540f07a0783903c1a81e0c40f05a0582903c128160840d49606a47024a581251c0927a0492f0249581249c092460784d0342581a11c0d08a0782f03c1581e09c0f0460481f0240d81205c0902603a4b01d2381252c0928e0392f01c9580e49c072460784d0342581a11c0d08a0382f01c1580e09c070460481f0240e81206c0902e078150240981ad6c0d6ae04a5b0252b8129340947e04a3b0251b8128cf5c27dad13c01c9b6b04d00925c0785d0342d81a15c0d0aa0783f03c1d81e0dc0f0660482f024168120ac0904e07825024118160640f02a0692f0249581a49c092460783503c1781e0ac0f04e078230240f81a06c0d02e04813bb09ed7c4d6a025a03929b089280e4840f0ba0785503c1c81e0c40f05a0582903c128160840769ba824dd08a6dd44f6bc26a049290249081e1740f0aa0584103c1c81e0c40f05a0782503c0e81e057548b006b5a0352d81a95c0749ba9241d391881256c0d2afa014d02498dcc4bc092575d1270249181e1740d0b60685703c2a81e1340b0820783d03c1781e0ac0f04e078230240f81e0740f0360781703c0a81204c09491a524401ca6012522a228803940cf89e00e4d009471a3234d08ae678530072895013c01c9c00e4d00926003b4401d2201b1680969ba124101d1ed548e40746b50231024a081e1740d0aa0784d03c1e8160e40f06a05831 15 32767 6 63 11 2047 21 2097151
def cc_35_14 : Nat → List (Nat × Nat) := unpackCursorV4 0xfc3fc0fa1f81ee5ea2ea0e81e61e60e41de3de0d45d40ce3ce0ca2b897fd6c96c054c448440440402118100046021001 0x3b6cf01b077c9b3ac461d6230eea30770d80074d9db260ec918760973ac4a1d8234ea8127548d3ac68805828ea012764d13ae4d9d326002494748493a047003a340249c73893009251cf359861a880e9779a4b203a55521288125640d03406816f41a880e977c84a3e123fef11df688dfa24660693f0249d81a4dc092660692f0249581a49c09247cc05d02c28c2c0fdfa076db03760019a8c0bd26056710272b01181207c0d0360681702409e84d72a069803b48025a200ed037a49003a440249c7084d00769a03b45e49236848f8092520785d03c2a8161240b0820783d03c1a81e0977869003b4401d260129200748950240024946d4490076891d05401da6f00d2b7268c03b4501da200e9340949404a4601d2280e912f427b64135e30950124a78a24c04921a402ec701540b0920584103c1c81e0c54205bc4025035b2594d72a0699bf24801d227084d007689b7234 12 4095 5 31 11 2047 21 2097151
def cc_35_15 : Nat → List (Nat × Nat) := unpackCursorV4 0xda1da0da0ca8ca0c81c80c80aceac0ac0ac0ac0ac092d9018e17c943d4204203e222e22022020106d060060003000000 0x7fc531fe4540128e1fd2347e4571f414c00e511f213c7f04d003b447e8925f924100e8f5f823900e8d5f22310125240494143c134e00454380f4058397dc0d4058317d4d39f43427cc939f22420124e40493100e494a703d1d80d4a602d0160a5f1025016084059240164910e14e7bc508a613e00e4e8039367b84c80492a0120b804822810d3e0234b800d1dfb34301293c04a4b01291c04a430128fc04a3b0128dc04a337d8539f013e00e4d90d04f40012cdf04730c10ca503f2580ec750371640cc0482f0120ac0482701208c058197b405403a3c7a88c1e324d77091403a3d7ac8e403a3574c8c40694d01a514ff0493081050c03d0160e5e90350160c5e6240780d29db34679c939d324201a4f40693500e4a4950391600c4a402d0160a5e5025016085e3460788db003b60 12 4095 5 31 11 2047 22 4194303
def cc_35_16 : Nat → List (Nat × Nat) := unpackCursorV4 0xaf26bc0af02b81ae0261698024c5910a4408d123018c022c1880e1c18702181830de89731da4a68050e509e8240051014003080810008000 0x8851521f36800ed7003b440128f1c515c64c5317d12c8504821c0248749661b25100e93803a4200e8e803a367f4569d21566d4539a314260c4f9591325f44b95012d528175240558680b4058290c80940582110c074310158588d2131548605300781883c05212144838052163448445521512c834052121248488d2133440124a2111248384920e23483cd1004928834492174540128e2142348405915615c6785315013c01e0620c01401f15003b5c02297007a4c0168f0078382a40d007c5400ed4003b4800e97005a3c48c1900885001e100a902c01e0812005400ed3403b4501ed1003a4e01692403a4202290403a4000e8e805a3900e8d807a31710534079456484f4089358204b4049290c84940492101e1740785a4c41580785547c1500784e016124078420161040883e0160e4078320160c4a902e01e0b40781a0c005a3845b8dcd6c03b5700ed3c03b4d00ed16333448b896e2c25700e93c03a4e00e935fb15b74455dc714f70c535a714568850d9513f6444f40393b00e4dd661355604ce2912f5ec4b62412b0124a61e1278644960b1230124854905d01e16d300574781540784f022124078430221040883f00e0ec0783900e0dc0783301e0c60a02f2a00b40782b0160a60902781c094078230160844101f01e06c2f01701e04c0394c814511f513c00e4d1fa15c80c4d1ff2307f8d020115c 14 16383 6 63 11 2047 22 4194303
def cc_35_17 : Nat → List (Nat × Nat) := unpackCursorV4 0xb80d34a5a0f1e678a4f91c48a24501f98d543991c00d846c03601818c005c22e016088184002000e106841500a00500090040001 0x23f25c00ed3403a4d6845355213d00e4d55012d0124a5611250124840785d01e1540784100e0e40783101e0b40582901e094058215408f803a3a00e8d9552326244f95b13201e1740785501e0f40783501e0b40582901e0940582101e074078158f8d6c03b5700ed363d23e80856dde1577205359613f00e4ec039375684cc049298f04940785d01e16c0785701e1540784101e0fc0783d00e0ec0383701e0d4078330160a40782501e07c0781b01e05c0781300e93403a4900e91403a4100e8c63423000e4a80392601e1740785501e1340584901e1140584101e0f40782d00e09403a5b00e95c03a4d00e8c63323080056dda1578e85340494100e4bc0392b00e49c0392301e1740785b01e15c0785501e1340584101e0f40382f01e0b40382b00e09c0382500e08c0781f01e06c0781701e04e2f34800ed1003c548c0d722313d8d84d40784d01e114058390160c62323d89c8d62812a8884980784d01e114058390160c40782d01e0963124b8b491e3523d7f852dd91478d04f62a12f8984ae2112785c48c0784d01e12c0784701e1140583101e0bc0782d01e0ac0782701e0940782301e07c0781b01e05c078138c8932314548c09722f24c8b4d122b24c8a91518d25c6f093004a3c8944e17d1348a09322714c854492264547189719424c8948f004a3000e570039445844d22035888cd322214c85848220454 13 8191 5 31 11 2047 22 4194303
def cc_35_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x10f01fe83fc07998d969986ae535c80a941500a74b3f3e6e409ef93c02684375801b8000 0x24334e8bcd080694d01a5140693901a4c40692d0124a406925012484ad03d2380d4ac02d0160a65102501608403a3d2b08e403a3593c8c40694d01a5140693d0124e4069350124c40784e01e10a4224f8e090e5023900e8d40694f01a5340694501a50c0493901a4d40692f01a4ac0692701a48c0784f01e10c058399380d4ab02f01e0ac8d02701e08c0681f01a06c0681701a04c0694d01a4f40693501a4b40492901a4940492101e0e40783101e0b40582901e0940582100e9764c25101a5740495101a4f40692f01a4ac0692701a48c0785d0161440782f01e0ac0782701e08c0681f01a06c0681701a04e3f2498c09040694901a5040693d0124e4069350124c40692d01a4951204d3e01151103d0160e64a0350160c403a3444493a4824200e8e80693d01a4d40692d0124a4069250124840883e0220c803b4f8f8d2c03b478dcd0e4924e01a53c0694b01a51c0694301a4fc0693d00e4ec0393701a4d4069330124a40692544013c0884b3dc11c088430220fc0383b00e0dc088330160a64702501a07c0681b01a05c0681300e93403a4501a5340694501a4f40493901a4d40493101a4b403925022124088410220f4058390220d405831914d4403a3f00e8ec03a3700e8cc0695d0125440693f01a4ec0693701a4cc0392f01a4b40392b00e49c0392500e48c0885d0161440883f0220ec088370220cc0382f00e0ac0382700e08c0681f01a06c0681701a04e4323800e8d15034e544d0803a4900e90403a3900e8c5c214e6945080393e00e4f40392a00e4980885d0221540884d0221140883d0160e4088350160c40881d0220564245b00ed6c03b5700ed3e3d34e00ed3403a5b00e95c03a4900e90c03a4181056de115772853da414300e4fc0393d00e4ec0493900e4de4113500e4cc0393100e4bd9712d00e4ac0392700e494039230221740785b02215c0885501e13c0884d0221140784300e0fc0383d00e0ec0583900e0dc0883500e0cc0383100e0bc0382b00e0a40382700e08c0782102207c0781b02205c07813 15 32767 6 63 11 2047 22 4194303
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_35_18 (Nat.sub p 576)) (cc_35_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_35_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_35_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_35_14 (Nat.sub p 448)) (Nat.blt p 480)) (cc_35_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_35_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_35_11 (Nat.sub p 352)) (Nat.blt p 384)) (cc_35_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_35_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_35_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_35_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_35_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_35_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_35_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_35_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_35_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_35_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0x25104b2723993d18c9c0d40169726251005a3c940d64749d2424291c1280292e456a200a4790d1c48316e4126a00a3f8fd2e478d6e3c47d1e1250051dc745340146f03c5b81dadc6c4d63447b1a13d81da24649322f8a917a5c8bd2640e96e2d68903a578ad264551520725f13a4c89ca644b152254790392b889a64445321f8a91045487db440e49e1a4b30e02486928c340b60724b0c14c8322a42ad121525906234845a24248d21124906164835a241c8d20d2490601481c91c0e0be0704f0412d81c128028ce05288f6b4f80c9a3dad2e012b8f6b477fca63f9151fc468fe1347b5a1bee925f7482fba397dc1abda539f169cf8b427c5273e2909f104af693e7b8a13dc4c9ed02a0094b7a51cbd48c1e906ae6351795273cc901e504ae625178a303c4db1cc47eefb6077d363988eddb8c0edb6076d303988ddd2688ec234749363a8d11d5468ea024749303a4491cc466e8238735acb9c931cd4b2e605d004a3b6093dc948cd82496c121b884a9c424ce20256c120b844d1b047edfb506fda63608edbb69cddb426ec12b608e5b9480d82376dd2636ad11b5248d82336c01fb600ddb1462d80350049fb584f9ac278d61340049db4f161a7482d424d69d188024dda5488cd34f68d1a334d0da1482cd14e675a733ad099d04acd13e66c9933405401266cc2355bda72ded2d6f686c912a648933240956f684c83505bd27b189258c482c60355bd27312d7189248b7a4b61da02de91d85498c1b5460c922de90d7c49abe23d5f8a62fc4f17c24cbe0255bd212f0d4178690bc25c5bca7ae8d4174680ba24c5bca3ade0bd6f04eb82425bc128024bd6b29cb594c5aca20024ad5d6b0aeb4259d1eaba909636a0b1a5058d242ba53d5e6a0af340579282bc9015d28e0092756d1a29ad2d59468a6b4355124aa890554472aa035534a72a0d095049ca82425349f29c5094d02a0092352d2c2944953e466a3a4151d1ca7c4fd4527c9f133505a1282939414849f12f4fca727c48c0109a9e05400425a748e5306a29c24e4c128a63181316c098a6c4cc92262981310489823300423a5c8e5146869624e45121a3f1491f6a48fa5e49c9223e949254a08f92547c13240d09204849001d47c122288cd1d0488da4146d1ca284fd190488ab424552722c091154848a12f00422a229711149881a5b438ae21c531032b68636040caba140d90329a83a5c41d262064bd042b88214c40c918020fd010487da5b3fa301fc1b0fb4ae7d8543ec130020ecf84b87c24c3192d98c930f46b47a125319209e4930e649673247398979cc4aced6b07312739d1a1d4490e72a87412439c0a1cc48cc64807035c381a81c0570e14807014c318ad9b9180dc4986e240318ab9b48e4c629a6a34d351209aa4a8d524c6a2403189e99cd40ce4b86725033d2019c930c625e6623431da818e570c94806394c31c0a18c48c0106e620242bd2d983180c10d857a572bc2a17a52cbd28e5783c2e4a5974d40b928e578342bc16168568b56a05a1562bc1316052cb16a0581472bc120020ccac690562482662d952494a904c4ca42298a614c4f0992b652260264ab940d20a04a050248264a793a5309d2784c943269a11340989927a0082f25c1212296c946c04a06c2452b9221509104c0082b239a411c9205c8b62e34822a2d1144945c6844424c1f1258f891c7c25e3e12b20dac0f849c7d468401241f4aa0fc4907d0283e123171a00ed160768a03b14c1dda00ec4f05c2b6393601c9a40e4d005c2ae36b501b5a40dcd006d4902e14f1ad1a0cd14066298343401989e0cc0505c28631a4e18d210b84f45d6842f92a17c930bad005d47a2e12d004138b4090454b62bb6015c3608a95c450a82994b14ca388a1304f2962825013ca388a110450582515a12d280945584504c2314b11d2808c51c45048008231091a0844d0396861fa410fd1c8725383b6841da4e0ed210724f8390ba0081f0d4aa06a1503504c0081b0c11c0608d03026818034021a181093c2c472160360212701090c2946813341098a684c4f8084840423f085270429082104c0423e0211983c8d01a6840d14e068a10344f4084640ba5005c2201053c144800a0340209f810174080aa071280389201c090094660493f024998124bc09246040540040b80415002098010440081e0040d0010260001f 10 11
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 594 bds_35 (dagTraceF m_35 s_35 8 f_35) (cur_35 0) s_35 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 64 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_2 : treeBlockF 64 96 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_3 : treeBlockF 96 128 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_4 : treeBlockF 128 160 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_5 : treeBlockF 160 192 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_6 : treeBlockF 192 224 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_7 : treeBlockF 224 256 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_8 : treeBlockF 256 288 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_9 : treeBlockF 288 320 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_10 : treeBlockF 320 352 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_11 : treeBlockF 352 384 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_12 : treeBlockF 384 416 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_13 : treeBlockF 416 448 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_14 : treeBlockF 448 480 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_15 : treeBlockF 480 512 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_16 : treeBlockF 512 544 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_17 : treeBlockF 544 576 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_18 : treeBlockF 576 594 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nj_35_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_1 (fun _ h1 h2 => treeBlockF_at nb_35_2 h1 h2)
theorem nj_35_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_2 (fun _ h1 h2 => treeBlockF_at nb_35_3 h1 h2)
theorem nj_35_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_3 (fun _ h1 h2 => treeBlockF_at nb_35_4 h1 h2)
theorem nj_35_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_4 (fun _ h1 h2 => treeBlockF_at nb_35_5 h1 h2)
theorem nj_35_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_5 (fun _ h1 h2 => treeBlockF_at nb_35_6 h1 h2)
theorem nj_35_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_6 (fun _ h1 h2 => treeBlockF_at nb_35_7 h1 h2)
theorem nj_35_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_7 (fun _ h1 h2 => treeBlockF_at nb_35_8 h1 h2)
theorem nj_35_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_8 (fun _ h1 h2 => treeBlockF_at nb_35_9 h1 h2)
theorem nj_35_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_9 (fun _ h1 h2 => treeBlockF_at nb_35_10 h1 h2)
theorem nj_35_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_10 (fun _ h1 h2 => treeBlockF_at nb_35_11 h1 h2)
theorem nj_35_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_11 (fun _ h1 h2 => treeBlockF_at nb_35_12 h1 h2)
theorem nj_35_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_12 (fun _ h1 h2 => treeBlockF_at nb_35_13 h1 h2)
theorem nj_35_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_13 (fun _ h1 h2 => treeBlockF_at nb_35_14 h1 h2)
theorem nj_35_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_14 (fun _ h1 h2 => treeBlockF_at nb_35_15 h1 h2)
theorem nj_35_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_15 (fun _ h1 h2 => treeBlockF_at nb_35_16 h1 h2)
theorem nj_35_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_16 (fun _ h1 h2 => treeBlockF_at nb_35_17 h1 h2)
theorem nj_35_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := block_join nj_35_17 (fun _ h1 h2 => treeBlockF_at nb_35_18 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 594 (dagTraceF m_35 s_35 8 f_35) cur_35) i = true := nj_35_18
theorem lb_35 : LowerBin m_35 s_35 g_35 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xffffffff00000000
def s_36 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_36 : Nat := 0x117151700000000
def ep_36 : Nat := 0x1400000000000016000200000000010604060000000001121012000000000114151400000000
theorem epk_36 : ep_36 = edgePack 0xffffffff00000000 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24), (m_17, s_17, 5, g_17), (m_19, s_19, 5, g_19), (m_21, s_21, 5, g_21), (m_23, s_23, 5, g_23), (m_15, s_15, 5, g_15), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_17
  · exact lb_19
  · exact lb_21
  · exact lb_23
  · exact lb_15
  · exact lb_1
  · exact lb_2
  · exact lb_4
  · exact lb_6
  · exact lb_7
  · exact lb_8
theorem sub_36 : ∀ b ∈ bds_36, 0xffffffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 7 f_36) (cur_36 0) s_36 7 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 7 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def g_37 : Nat := 0x117151701573fff
def ep_37 : Nat := 0x402ae80000140000003ea800160002005600c00106040601020c0001121012010230000114151401540000
theorem epk_37 : ep_37 = edgePack fullMask g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 9, g_35), (m_34, s_34, 8, g_34), (m_36, s_36, 8, g_36), (m_28, s_28, 7, g_28), (m_29, s_29, 7, g_29), (m_30, s_30, 7, g_30), (m_31, s_31, 7, g_31), (m_32, s_32, 7, g_32), (m_33, s_33, 7, g_33), (m_25, s_25, 7, g_25), (m_26, s_26, 7, g_26), (m_27, s_27, 7, g_27), (m_24, s_24, 7, g_24), (m_14, s_14, 6, g_14), (m_9, s_9, 6, g_9), (m_11, s_11, 5, g_11), (m_12, s_12, 5, g_12), (m_13, s_13, 5, g_13), (m_10, s_10, 5, g_10), (m_15, s_15, 5, g_15), (m_16, s_16, 5, g_16), (m_17, s_17, 5, g_17), (m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_35
  · exact lb_34
  · exact lb_36
  · exact lb_28
  · exact lb_29
  · exact lb_30
  · exact lb_31
  · exact lb_32
  · exact lb_33
  · exact lb_25
  · exact lb_26
  · exact lb_27
  · exact lb_24
  · exact lb_14
  · exact lb_9
  · exact lb_11
  · exact lb_12
  · exact lb_13
  · exact lb_10
  · exact lb_15
  · exact lb_16
  · exact lb_17
  · exact lb_18
  · exact lb_19
theorem sub_37 : ∀ b ∈ bds_37, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8486bf4c1e164ed4d7155b7c39a8d6c7b36226ae3b96b1aa9b04e99246b90c5c7aed3b489afacbee45b8f275a12b3c7be838d416d68b1144d2e230e0abb821d000c00001 0xac6e09c6a09c660ac6203c5e04b4d05b4904b4505b4106a4d04a4906a4504a4108e7e09e7a08e760ae7208c6e04c6d04c6c05c6904c6505c6205c6105c6006b6d07b6906b6507b6105b4d04b4a04b4606b450aa7e05a7a09a7605a7208a6e05a6d1e26c05a6a05a6905a6808a6605a6508a6405a6205a6105a6003a5e05a5a0ba5603a5205a4e05a4d04a3e04a3d0396e0395e059260892408d6f08d6e08d6b09d6a08d6708d6608d630ad620bc6f03c6b0bc6703c630eb6f0eb6b0eb670eb6308b5f04b5d08b5b05b5908b5704b5508b5305b5103b4f0bb4b0bb4703b430ea6f0ea6b0ea670ea6308a5f06a5d08a5b07a5908a5706a5508a5307a5103a4f0ba4b0ba4703a430fa3f1f23b0fa371d2330395e0394e0ac6e09c6a09c660ac6203c5e05c5a06c5603c5204b4d05a4d03a4905a4503a410ac7e05c7a09c7605c7203c6e05c6a0bc6603c6203b6e06b6d06b6503b6205b4d07b4906b4505b410aa7e07a7a09a7607a7206a6606a6505a5e04a5a04a5605a5205a4e05a4d05a4c05a4a07a4907a4805a4607a451b24405a4205a4105a4003a3e03a3d04956049460584a0ac6e09c6a09c660ac6203c5e03c5a03c5603c5203b4d05a4d07a4905a4505a41049360ac7e05c7a09c7605c7203c6e03c6a03c6603c6203b6d03b6a03b6606b6505b4d07b4906b4505b410aa7e03a7a09a7603a7203a6e03a6d05a5e03a5a04a5603a5205a4e03a4d05a4c03a4a03a4903a4805a4603a451924403a4203a4103a4007a3e03a3d04956049460584a0ed6f0ed6b0ed670ed6304c6f05c6b04c6705c6304c5f05c5b04c5705c5305b6f0ab6e05b6b05b6a05b6709b6605b6305b6205b5f03b5e05b5b05b5a05b570bb5605b5303b520ea6f0ea6b0ea670ea630fa5f1a25b0fa571825305a4f04a4b04a4705a4305a3f05a3d05a3b07a3905a3706a3505a3305a3104946049360583a0ab6e09b6a09b660ab6203b5e06b5a04b5603b5204b4e04a3d03a3904a3503a3104d7e09d7a04d760ad7203d6e0bd6a04d690bd6804d6603d6204d6103d6003b6e06b6d06b6503b6206b5d04b5904b5507b510aa7e07a7a09a7607a7206a6606a6504a5e07a5d1625c04a5a04a5904a5804a5604a5504a5404a5207a5107a5004a4e04a4a04a4604a4203a3e03a3d0495e0494e0ab6e09b6a09b660ab6203b5e03b5a03b5603b5203b4e04a3d04a3904a3507a3104d7e09d7a04d760ad7203d6e03d6a04d690bd6803d6603d6203d6103d6003b6d03b6a03b6606b6506b5d04b5904b5507b510aa7e03a7a09a7603a7203a6e03a6d04a5e03a5d1425c03a5a03a5903a5804a5603a5504a5403a5203a5103a5004a4e03a4a04a4603a4207a3e03a3d0495e0494e03926089240ed6f0ed6b0ed670ed6304c6f04c6e04c6b09c6a04c6704c6604c630ac6204c5f03c5e04c5b0bc5a04c5704c5604c5303c5204b6f04b6b04b6704b6304b5f04b5b04b5704b530ea6f0ea6b0ea670ea630fa5f1525b0fa571325304a4f06a4d04a4b04a4904a4704a4504a4307a4104a3f04a3b04a3704a330494e0493e0ad7e03d7a09d7603d7203d6e03d6d03c6a04c6903c6603c6103c5604c5503b5d03b5a07b5907b5803b5606b5506b5403b510aa7e07a7a09a7607a7203a6e03a6a03a6603a6203a5e03a5d03a5c03a5a07a5907a5803a5607a5510a5403a5203a5103a5004a4e04a4a04a4604a42069360692603d6e04d6d04d6503d620ac7e05c7a09c7605c7204c6604c6503c5e03c5d05b4d05b4a07b4907b4805b4606b4506b4405b410aa7e07a7a09a7607a7203a6e07a6a0ba6603a6205a5e04a5a04a5605a5205a4e05a4d05a4c05a4a07a4907a4805a4607a4510a4405a4205a4105a40069360692604e7e09e7a04e760ae7204d6e05d6d03c6e03c6d03c5e04c5903c5204c510e45006b6d04b6904b6507b610aa7e07a7a09a7607a7204a6e07a6d10a6c04a6a04a6904a6804a6604a6504a6404a6207a6107a6003a5e07a5a0ba5603a5204a4e04a4a04a4604a420496e0896c069360692604c5e03c5d0aa6e07a6a09a6607a6204a5e04a5a04a5604a5203a4e03a4a03a4603a420495e069360692603d6d03d6a03d6604d650e5640ac7e03c7a09c7603c7203c6e03c6d05c5e03c5d03b4d07b4906b4503b410aa7e07a7a09a7607a7203a6e03a6a03a6603a6205a5e04a5a04a5605a5203a4e03a4d03a4c03a4a07a4907a4803a4607a4510a4403a4203a4103a4006936069260ed6f0ed6b0ed670ed630ec6f0ec6b0ec670ec631145f1045b0f4570d45306b6f07b6b06b6707b6306b5f07b5b06b5707b5306b4f07b4b06b4707b4307a6f0aa6e07a6b07a6a07a6709a6607a6307a6207a5f03a5e07a5b07a5a07a570ba5607a5303a5207a4f05a4e07a4b04a4a07a4704a4607a4305a42069360692604c5903c510aa6e09a6a09a660aa6203a5e03a5a03a5603a5204a4e04a4a04a4604a4203a3e0ad7e03d7a09d7603d7203d6e03d6d03c6a04c6903c6603c6103c5604c5506b7e09b7a06b760ab7203b6e03b6a03b6603b6203b5e03b5d03b5c03b5a06b590b35803b5606b5506b5403b5203b5103b5004b4e04b4a04b4904b4804b4604b4206b4105b4003a5d03a5a06a5907a5803a5606a5506a5403a51089760693e0692e0683203c5e03c520aa6e09a6a09a660aa6203a5e04a5a04a5603a5203a4e04a4a04a4603a4205a3e03d6e04d6d04d6503d620ac7e05c7a09c7605c7204c6604c6503c5e03c5d06b7e09b7a06b760ab7203b6e0bb6a06b690bb6806b6603b6206b6103b6005b5e04b5a04b5605b5205b4e05b4d05b4c05b4a06b490934805b4606b4506b4405b4205b4105b4005a4d05a4a06a4907a4805a4606a4506a4405a41089760693e0692e0683203c5e04c5903c5204c51054500aa6e09a6a09a660aa6203a5e05a5a05a5603a5204a4e03a4a03a4604a4204a3e089660693e04e7e09e7a04e760ae7204d6e05d6d03c6e03c6d03c5e04c5903c5204c510445006b7e09b7a06b760ab7204b6e06b6d06b6c04b6a04b6904b6804b6604b6504b6404b6206b610736003b5e0bb5a06b5603b5204b4e04b4a04b4604b4206a6d04a6904a6506a61089760693e0692e0683203a4a03a4608956039460693e04c5e03c5d06b6e09b6a06b660ab6204b5e04b5a04b5904b5804b5604b5206b510535003b4e03b4a03b4603b4208966039460693e0692e068320aa6e09a6a09a660aa6203a5e03a5a03a5603a5205a4e04a4a04a4605a4203a3e0896603d6d03d6a03d6604d65045640ac7e03c7a09c7603c7203c6e03c6d05c5e03c5d06b7e09b7a06b760ab7203b6e03b6a06b690bb6803b6603b6203b6103b6005b5e04b5a06b5904b5804b5605b5205b5105b5003b4e03b4d03b4c03b4a06b490334803b4606b4506b4403b4203b4103b4003a4d06a4906a4503a410897603946089440693e0692e068320ed6f0ed6b0ed670ed630ec6f0ec6b0ec670ec630a45f0845b064570245306b6f06b6e06b6b09b6a06b6706b6606b630ab6206b5f03b5e06b5b0bb5a06b5706b5606b5303b5206b4f05b4e06b4b04b4a06b4704b4606b4305b4206a6f06a6b06a6706a6306a5f06a5b06a5706a5306a4f06a4b06a4706a43089660693e0692e06832c845fc745bc6457c5453c435fc335bc2357c1353c034fbf34bbe347bc343b225fa725b9c2578b2538224f7924b70247672435e23f5523b4c237432333915f261572114f1c1471713f121370c12f011270003f 17 131071 6 63 11 2047 20 1048575
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8355bf0a9e354e72a6e55340c9989ec0705e47ac2c158249f734f41a6069291c86f741879dac8e69a65f63107956c8a49a44f61bfa0d23453d6264e0dd583bcc171a002e 0x3d6d07ad20f5941eb084c6d0b8d2131942e3083c5d078b40f158262abf454156fc0ede84dbb03b72116dc0edb445b603b6a076d20eda045b303b65256c80ed881db083b60076bc0ed742da703b4d0d4da1e9a4353287a610747a1e8e4351a83a31112ec2259846b683d6917aca0f584263685c69098ca1718435b687b690d6ca1ed841daf06b5d0d6aa0ed48553f07a7a134ec1e9c8453707a6d114d81e9a83d3487a68114cc1e994953207a620f4c21e980352b06a550b49c12928252305a420747c0e8f444bb0896607ada0f5a41eb283d61098da171a4263285c610d6da1eda435b287b61076ba0ed681dab06b55154fc0e9e84d3b03a72114dc0e9b4453603a6a074d20e9a0453303a65254c80e9881d3083a60074bc0e9742d2703a4a0948c0e9083d1f03a3d112ec2259846b683d6917aca0f584263684c69098ca1318435b687b690d6ca1ed8425a706b4d0968a12d08553f04a7a134ec129c8453704a6d114d8129a8253484a68114cc12994953204a62094c2129801d2f04a5a174ac0e948252304a450b47c128f444bb0896611ada0f5a45eb283d61098da171a4263285c610d6da1eda435b287b610b69a12d2825a306b45154fc169e84d3b05a72114dc169b4453605a6a0b4d2169a0453305a65254c8169882d3085a60074bc169685d2b03a520b49c16934251f04a3d112ec22598563789c6b138ce2b18c462f88c5d118b60f164462b8bc55118a60f14455b789b6b136ce2ad8c45af84b5d116b616d6445ab84b55116a616d4611a7c134b8068ef8d0c553789a6b134ce2a98c452f86a5d114b61e964452b86a55114a61e9447d27bd24b1f48ef090c7d1fbb23b1f46ee88cc44b30895607adc0f1741e2c83c55078a212d7425ac84b55096a212d241da086a5d0f4b21a9543d2883d7d07af20f5d41eb888c7e078fae11f01e3d03c79078f0231d81e3a88c74078e40f1c41e3809c6e078d4271981e3103c5e078ba12df825be84b7c096f212dd445b904b710b6e00ed6825ac83b56076a20ed1825a286a7d0f4f21a9d43d3883a4d0f4921a9141d208897e112dc22498443905d6e098ba0f164262a83c51096ba0ed6425aa83b510769c0ed08352e87a590d4aa1e94446bf0bd7d17af80f5e446ba88d7207ae20f5c0263e85c79098ea171c41e2f04c5d098aa0f14845bf05b7d6c6f816de82dbc85b78116ec16dd445ba05b720b6e216dc04db705b6a136cc16d8825ab04b550769c0ed34353e87a790d4ea1e9c42d1e87a390d46a168c444bf0896e1124c221c8263703c5e0b8b4171581e2903b5e096b20ed4825a8b23500769a12d241da284b410d49a1e924352287a4109afc135f426be08d7a09af2235e026bb04d7509ae8235c826b8b457009adc275a826b489d6809acc2758826b08ad60178fa0f1e4463a83c71098bc1717425be84b79096ea12dc41daf03b5d0769c12d241da104b41626801a9f43d3c86a750f4e21a974252c84a550f4a2225f844b70495e112b822498443903b4d0768a0e4d8263704c6d098d8131a4263288c62098c2c9180262c84c51076da0eda41db283b610969c0ed34353687a690d4ca1e98444b70895e0929c0e4d844930886207adc0f1741e2c83c55078a212d742dac84b550b6a21a9743d2c86a550f4a22249846bf03d7d17af80f5e41eba83d7207ae20f5c0463f04c7d098f8171e4263a85c720b8e2171c01e2e83c5a078ac131558a2a08b7e076fac0df01dbd03b79076f022dd81dba88b74076e40edc41db809b6e076d426d981db103b5e076ba16d381da686a7d0f4f21a9d43d3883a3d0f4721a8d41d188897e112dc0e4d8449a08926110e41f5b8362e83c590d8aa0f14425ae85b59096aa16d44352e83a590d4aa0e9441d2703a4211afc2f5f45ebe03d7911aea235c81eb883d70098fa171e4263a85c710d6fa1ede435ba87b71076bc1ad7435aa83b52114fc1e9f5713e07a7a0f4f21e9e0453b07a75114e81e9c83d3887a70134dc1e9a84d3307a620d4ac1a9542d2704a4a0948c169081d1f03a3d112fc225b8349b0792611248221c81eb703c5d078b20f1541e2884b5d0b6b212d542da886a5d0f4b21a9543d2888d7e07afa2f5f01ebc83d7507ae40f5c41eb804c7d0b8f2131d42e3888b7e0d6fa1adf03dbc86b750f6e41edc43db803b5d076b40ed5835aa88a7e074fab09f01d3d03a79074f0229d81d3a88a74074e40e9c41d3809a6e074d4269981d3103a5e074ba169381d2504a46074841e8f81d1e8897e112dc1a4d81c9308924110e4135b85e2e83c59178aa0f14425ae84b59096aa12d44352e85a590d4aa16944251f04a3217afa0f5e446ba83d71098fc131f4263e04c79098ea231c8263885c700d6fa1ede435ba87b710969c1ad3425a284b42114fc129f5513e04a7a094f2129e0453b04a75114e8129c8253884a70134dc129a84d3304a62074bc129685d2b03a520948c129142d1f04a3d112fc225b8349b0492611248221c82eb70bc5d078b22f1541e2884b5d0b6b212d542da886a5d094b21a95425288bd7d07af2235d41eb888c7e098fa131f02e3c84c750b8e4171c42e3808b7e0d6fa1adf03dbc86b750f6e41edc43db805b4d0969412d1835a288a7e0b4faa09f02d3d05a790b4f0229d82d3a88a740b4e4169c42d3809a6e0b4d4269982d3103a5e0b4b42e9581d2905a4e0b49a128f8251e8897e112dc1a4d82c9308924110e4231bc5e3688c6b078d22319c463288c63078c22717c4e2d89c57138a622dbc25b688b6b0b6d222d9c25b288b630b6c226d7c4dad89b57136a6dcd3da9a5b33475e686229bc353688a6b0f4d22299c353288a630f4c22697c4d2d89a57134a63e93d69258fa47564863e8fd491d8fa374e466225b844af08926110c42b5b84eb509d6615ac40f1741dae83b59096aa0ed441d2e85a59074aa0e94456bf03d7a13aec0f5c81e2e84c59098aa0f1441dae87b590d6aa0ed4425a706b4d0968a12d08553f04a7a134ec129c81d3703a6a074cc0e9881d2f03a5d074b80e968252c84a58074ac12955292a03a52074a20e940252304a450b47c128f41cb303956070b42b5b84eb509d6615ac40f1741dae85b59076aa0ed441d2e84a59074aa0e9441ca30ad7e07af4275d81eb903c5d0b8b2131541e2883b5d0f6b21ad541da885b4d0969412d1835a28aa7e0b4f4269d82d3903a6e074d40e9981d3103a5e074ba0e9701d2d05a590b4b00e9582d2aa3254074a40e9441d2805a4e0b49a128f8251e83966072ac0e1681eb783d6b07ace0f58c1e378ac6e078d60f1a81e3389c66078c60f18875b78eb6b1d6ce3ad8c1daf83b5b076ae0ed4c1da783b4d0769616d241da384b45076860ed0475378ea6b1d4ce3a98c1d2f83a5b074ae0e94c1d2783a4d074961e9241d2386a45074860e9047d1fa423b1f46e888cc1cab03946070942b1b84e3509c66158c40f17825a684b490968a12d04352685a490d48a16904473f09e7a11cec2b9c8263704c6d098d8131a4263288c62098c21718035b687b690d6ca1ed8425a706b4d0968a12d08553f04a7a134ec129c8453704a6d404d8129a8253484a68114cc12994453204a62094c2129801d2f04a5a174ac0e948252304a450b47c128f41cb70395e 17 131071 6 63 11 2047 19 524287
def cc_37_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x99becbb4a43e91c5687ba42759f9e8f7d474dcb69f5aaa8c97061eb2dbd163a8a3f84fa9240f501fa7bd4377a1a750b5f8555623bc103686962257d0d75041a8095e0012 0x32ab7e356bc2acf7d58c263785c6b098ce1718c262f85c5b098ae1714c2db78ab6e0b6d616da82db389b660b6c616d882daf83b5e0b6b616d682dab8bb560b6a60ed482da785b4e0b69a1a9bc353586a670d4c61a97c352d86a570d4a61292c252506a490948e129182d2185a410946e128d8251a8f96f1f2ce3e57c7cab8594f0928e164fc2c9e859371126a1a4bc349383d6e09ad4135981eb104c5d078b2271541e2884b5d096b212d5425a886a5d0b4b21a9542d288895d112aa0f9f81f3e89d7a07af2275d81eb889d6613aca131b4263484c65098c21adb43db486b650f6c212d3835a684b45096842a9f8253d09a76094e42a9b825368aa6c094d4129a425340aa66094cb74990253104a61094c00e978252e83a5c094b42e958252a8ba54074a412918252285a3e0947a225b444b28492d1124a275b81eb104c6e098d427198263103c5e078b40f1581e2903b4d0769212d141da083a4d0b4920e9141d2084a3e094642253444a289e7e07cfa0f9d41f3909d7607aea0f5b81eb683c5d078b4131642e2c03c56098aa131501e2883b5d0f6b21ad541da884b4e0d69a12d1425a109a7e094f4269d8253903a6e074d40e9981d3103a5e074ba0e9701d2d04a59094b00e958252adb254074a40e9441d2804a460948a168f8251e8395d112aa124b4449283d6d09ad20f59426b08ac6d078d2131941e3089c5e138a412db425b484b65096c21a9b42d3486a650b4c21a8f4251a8896d112ca0f9f81f3e89d7e15afa275b81eb489d6207ac2131f4263c84c75098e226df835be86b7c0f6f21add43db907b710f6e012d3835a684b4509684269f8253ed927c094f4129e4253c09a76094ea269d0253904a71094e0269b8253509a66094c40e978252d0ba56074a412918252285a3e0947a225f444ba8492d1124a2b1b8263504c66098c40f1781e2d03c56078a40ed341da484b45076820e9342d2483a45074821a8f4251a8894d1128a0f9f41f3d09e7607cea2b5f81ebe83d6e07ada0f174262c84c55078a20ed741dad07b590f6b00ed5835aa86b54076a212d3835a684b45096842a9f8253d09a76094e40e9b81d3683a6c074d40e99825328ba64074c40e9781d2e83a5c074b412964252c03a56094ab5c9501d2903a51074a012918252285a3e0947a0e57444aa8492d1124a0e16ae2b7da56bb0acf5958c263784c6b098ce1318c262f84c5b098ae1314c35b787b6b0d6ce1ed8c35af87b5b0d6ae1ed4c25a784b4e0d69a12d1c25a284b4309684129bc553704a6b094d41299c4d3304a63094c41297c1d2f04a5b094b41295c5d2b04a53074a41291c252304a450947e168f8251ebb16f522ce9057cf8ab8494f0928e1e4fc349b8492f0925a1249c449283d6907ac20edb825b504b66076c40ed784dad04b56076a412d3825a504b4609684168f4351c85a350d462224f4449a83e7e07cfa275e81ebc89d7607ae2275984eb284c7e138f4131d8563904c6e098da131b0563504c69a88d013198263284c64158c413184563003c5e178b4131581e2904b6d096d212d9425b084b4e0969a1a9b4353486a650d4c2129382d2684a3e09472128c835188896d112ca2253424a284b6e136d412d9825b103b5e076b40ed581da903b4e096940ed181da104a4e0949212908352085a3d074720e8d41d188893d1126a279f81f3e83e7507ce4275d81eba83d6e07ada131f84e3d04c79138f0131d84e3904c71158e00f1b81e3503c66078c40f1781e2e83c5c078b413166922c03c56098aa131501e2903c51078a00ed7425ac84b55076a212d3825a683a5d0d4b21a9541d2884a4e0b49a128f8251c84a320d4620e57444aa8894d0928a0f5a41eb084b6e076d40ed9825b103b5e156b412d581da904b4e0969412d1825a105a3d0d472168d435188893d1126a0f9f81f3e89d7e15afa275b81eb489d6207ac2131f8263e84c7c138f4131e44e3c04c76098ea131d04e3904c71a08e0131b84e3504c66138c40f1785e2d04c56078a412df825be84b7c096f212dd44db904b710b6e012d3825a686a7e0d4fa1a9f0353c86a75134e41a9c43d3804a4e0b49a128f8251c84a320d462225f444ba8894d0928a12db825b504b66156c40ed781dad03b56076a40ed3825a503b4607684168f41d1c83a3507462224f4449a83e7d07cf4279d81f3a8ad7e07afa0f5b81eb684c7e138f4131e44e3c04c76158e4131c4563803c6e078d40f1981e3103c5e078ba0f1701e2d04c599c8b00f158262a84c54078a40f1441e2803b5d076b412d642dac03b56096aa12d501da884b4e0969a0e9741d2d06a590f4b00e958352a86a54074a2129382d2684a3e09472128c835188395d112aa2253424a28385aa6adf455ae7ab3cd563098de131b8263589c6a098ce1319826318ac62098be0f178262d8bc5a098ae13158262983c52096de12dac25b384b63096be12d6c25ab84b530969e12d3825a686a6f0d4d61a99c353186a5f0d4b61a95c352984a4f0949c16934251f84a3e09476128e4251984a320d4623e5bc7cb38f95f1f2ae1253c44a6849470928a124fc249b8692f0d24e0f5b82eb505d6607ac4271a84e3305c5d078b2271541e2884b5d0b6b212d542da886a5d094b21a95425288895d112aa0f9f81f3e89d7a07af2275d81eb889d6613aca131b42e3484c650b8c21adb43db486b650f6c216d3425a504b460d68a2a9f82d3e8aa7c0b4f4269d82d3a89a740b4e42a9b82d368aa6c0b4d4169a42d340aa660b4cb2c9902d3105a610b4c00e9782d2d0ba56074a4169382d2684a3e0947a225b444b28592d1124a0f5b41eb285c6e0b8d4271982e3103c5e078b40f1581e2903b4d0b6920ed141da083a4d094920e9141d208894d1128a279f81f3e83e7507ce4275d81eba83d6e07ada0f1741e2d05c590b8b00f158262a84c54078a20ed741dad07b590f6b00ed5835aa86b54076a216d3425a504b460d68a269f82d3d09a760b4e40e9b81d3683a6c074d40e9982d328ba64074c40e9781d2e83a5c074b4169642d2c03a560b4ab249501d2903a51074a0169382d2684a3e0947a0e57444aa8592d1124a0f5b42eb483d650bac22b1b41e3485c65078c212db42db484b650b6c21a9b4253486a65094c2168f4251d04a360d46a225b444b283e7e07cfa275f856be89d6e07ad2275881eb084c7d0b8f2131d42e3886b7d0f6f21add43db885b4d0969412d1835a289a7e0b4fb1c9f02d3d05a790b4f0269d82d3a89a740b4e4169c42d3809a6e0b4da2a9b02d3509a660b4ca269902d3103a5e0b4ba0e9702d2d0ba560b4aa2e9501d2905a4e0b49a128f8251e8897d112ea164b4449283d6d07ad4275981eb28ac6e0b8d4171982e3103c5e078b40f1581e2903b4d0b6920ed141da083a4d094920e9141d2085a3d09474128d8351a8894d1128a0f9f41f3d09e7607cea2b5f81ebe83d6e07ada0f1742e2c84c55078a20ed743dac86b55076a216d3425a504b460d68a2a9f82d3d09a760b4e40e9b81d3503a66074c40e9781d2e83a5c074b4169642d2c03a560b4ab149501d2903a51074a0169382d2684a3e0947a0e57444aa8592d1124a0e16a52b7c856b8cacf1158c263785c6b098ce1718c262f85c5b098ae1714c35b787b6b0d6ce1ed8c35af87b5b0d6ae1ed4c2da785b4d0969612d2825a384b460d68a169bc553705a6b0b4d41699c4d3305a630b4c41697c1d2f05a5b0b4b41695c5d2b05a53074a41693c2d2705a4d0947e128f8251eba16f4e2ce8857ce8ab8594f0928e1e4fc349b8592f0b25a1649c449283d6d07ad20f5941eb08ac7e078f4271d81e3908c6e078da231b01e3503c69078d0231981e3292c64078c40f1841e3003c5e078ba12db425b484b65096c20ed6825ac83b56076a20ed1825a286a6d0f4d21a9943d3083a4d0f4921a9141d2088976112cc235b41eb48bd6507ac2131b42e3484c650b8c20f178262e84c55078a42adf82dbd09b760b6e422db82db688b6c0b6d416da42db408b660b6ca4ad902db105b610b6c012d5825aa83b4e0769a1a9b43d3486a650f4c2168f43d1c86a350b462225d844b304d7e13af4135e44ebc04d7615ae4135c456b804d6e09ada135b046b504d6925ad01359826b284d6411ac41358446b008c6d078d22f1941e3084c5e0b8ba12db425b484b65096c20ed781dae83b4e096920ed0825a0bf3400d4da1e9a4353287a610d4ba12964252a87a51112ec22598263484c61098ba13164262a84c51076ba0ed641daa83b510969c0ed34352e87a590d4aa1e94444b308956 17 131071 6 63 11 2047 19 524287
def cc_37_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x99fa4b95a42e91c54871cbfbf5f3a8edf0742b36dd1aca8c87861e92d2f54afaa05449ba23950fef879d635fc19568b26249fd22a90e1d065ac25f4102b04dd01ca80039 0x9d7e04d7d04d7505d7204c7604c7503c6e05c6d03c6c05c6a0bc6605c650bc6403c6205c5e05c5d03b6e06b6d06b6503b6205b4d07b4906b4505b4109a7e07a7a09a7607a7206a6606a6505a5e04a5a04a5605a5205a4e05a4d05a4c05a4a07a4907a4805a4607a457f24405a4205a4105a4003a3e03a3d0594d089450792d0892505d6d07d6905d6507d6106c6d03c6904c6503c6104b6d04b6904b6504b6104b5e09b5204a6d03a6904a6503a6106a4d06a450896d0896504e7e05e7d0bd7d03d7904d7503d7104c7e04c7d04c6e04c6909c6204c6104b7e06b7d06b7c04b7904b7504b7207b7107b7003b5e06b5d06b5503b5204a7e07a7d7d27c04a7a04a7904a7804a7604a7504a7404a7207a7107a7009a6e07a6a09a6607a6206a5606a5504a4e04a4a04a4604a4203a3e03a3d0897d049750792d0892504b6e07b6a07b6604b6203b5e05b5a06b5603b5205b4e04b4a04b4605b4206a5d06a5505a3d03a3905a3503a310893d0893504d7d05d7a09d7604d7504c7e04c7d03c6e05c6a0bc6603c6205c5e05c5d03b6e06b6d06b6503b6205b4d05b4a07b4907b4805b4606b4506b4405b410aa7e07a7a09a7607a7206a6606a6505a5e05a5d05a5c04a5a04a5607a5504a5405a5205a4e05a4d05a4c05a4a07a4907a4805a4607a457b24405a4205a4105a4003a3e03a3d0594d089450792d089250584a0bd6f03d6b0bd6703d638046f7e46b7c4677a46303c5f0bc5b0bc5703c5306b6f07b6b06b6707b6303b5f03b5e06b5d06b5706b5503b5303b5206b4f07b4b06b4707b4307a6f0aa6e07a6b07a6a07a6709a6607a6307a6206a5706a5606a5507a4f05a4e07a4b04a4a07a4704a4607a4305a4203a3f03a3e03a3d3d16f2d1670395f0b9571a14f151470793f069370792f0792d079270892505c6e06c6a06c6605c6203c5e07c5a04c5603c5204b6904b6104b4d04b4904b4504b4103a4d04a4903a4504a410894d0894505e7e04e7d06d7e09d7a06d760ad7204d6e04d6d04d6c04d6a06d697856804d6606d6506d6404d6204d6104d6004c6d03c690bc6503c6106c5e07c5d09b7a04b7904b7604b7104b6604b6504b5d04b5904b5504b5104a6d06a6906a6504a6103a5e03a5d03a4e06a4903a4206a410496d089650895d0695506c6e04c6a04c6606c6203c5e07c5a05c5603c5204b4d05b4904b4505b4103a5e06a5903a5206a5103a4d05a4903a4505a410894d0894506e7e09e7a06e7909e7806e7609e7206e710ae7006d6e07d6d09c7e04c7d04c7505c7204c6d05c6904c6505c6104b7604b7506b6e05b6d7636c05b6a05b6905b6806b6605b6506b6405b6205b6105b6003b5e05b5a0bb5603b5205b4e05b4d03a6e03a6d03a5e06a5903a5206a5105a3d06a3906a3505a310896d069650593d0893506c6e05c6a05c6606c6203c5e07c5a04c5603c5204b6904b6104b4d04b4904b4504b4103a4d04a4903a4504a410894d0894504e7e05e7d04d7e06d7d06d7c04d7a04d7904d7804d7604d7504d7404d7206d717457006d6e09d6a06d6609d6204c7e0bc7d0bc7c03c7904c7504c7203c7103c7006c5e07c5d04b7e04b7d04b6e04b6909b6204b6104b5d04b5904b5504b5104a7e06a7d06a7c04a7904a7504a7206a7107a7003a5e03a5d03a4e06a4903a4206a410897d049750895d0695504c6e06c6a06c6604c6203c5e07c5a05c5603c5204b4d05b4904b4505b4103a4d05a4903a4505a410894d0894506e7e09e7a06e7909e7806e760ae7206e710ae7006d6e07d6d04c7d05c7a09c7604c7504c6d05c6904c6505c6104b7e04b7d06b6e05b6d7236c05b6a05b6905b6806b6605b6506b6405b6205b6105b6003b5e05b5d03b5c05b5a0bb5605b550bb5403b5205b4e05b4d03a6e03a6d03a5e06a5903a5206a5105a3d05a3a06a3907a3805a3606a3506a3405a310896d069650593d089350583a06d6f06d6e06d6b09d6a06d6706d6606d630ad620bc6f03c6b0bc6703c6306c5f06c5e07c5d7736f7536b733677136306b5f04b5d06b5b05b5906b5704b5506b5305b5103b4f0bb4b0bb4703b4306a6f06a6b06a6706a6303a5f03a5e03a5d03a4f03a4e06a4b06a4903a4303a4206a4106a3f06a3b06a3706a330f96f0f9670695f0895d06957069550394f0b9470f93f0f9370692f0692705d6e03d6a03d6603d6203c5d03c5903c5503c5109b6a04b6603b5d03b5904b5503b5104a5d07a5904a5504a510895d0895505e7e04e7d03d6d03d6903d6503d6109c7a04c7904c7604c7104c6604c6504b6d07b6906b6504b6103b5d03b5a03b5606b550aa7e03a7d0aa7c03a7a09a7603a7509a7403a7204a6e03a6d04a6c03a6a03a6903a6804a6603a656f26403a6203a6103a6003a5e03a5d04a4e03a4a04a4603a4207a3e03a3d0496d089650392d0892504c6d04c6503b6e03b6a04b6603b6203b5e03b5a03b5603b5205b4e03b4a03b4603b4205a3d07a3905a3505a310893d0893509d7e04d7d04d7505d7204c7604c7503c6e03c6d03c6c03c6a03c6605c650bc6403c6205c5e05c5d03b6d03b6a03b6606b6505b4d05b4a07b4907b4805b4606b4506b4405b4109a7e03a7a09a7603a7203a6e03a6d05a5e03a5d05a5c03a5a04a5603a5504a5403a5205a4e03a4d05a4c03a4a03a4903a4805a4603a456d24403a4203a4103a4007a3e03a3d0594d089450392d0892505d6d03d6903d6503d6103c6d03c6903c6503c6104b6d03b6903b6503b6104a6d04a6904a6507a6103a4d03a4a03a4606a450896d0896504e7e05e7d03d7d03d7903d7503d7104c7e04c7d04c6e04c6909c6204c6106b7d04b7904b7507b7103b5d03b5a03b5606b5504a7e03a7d6b27c03a7a03a7903a7804a7603a7504a7403a7203a7103a7009a6e03a6d0aa6c03a6a09a6603a6509a6403a6203a5e03a5d04a4e03a4d05a4c03a4a04a4603a4504a4403a4207a3e03a3d0897d049750392d0892504c6d05c6a09c6604c6504b6e03b6a03b6603b6203b5e03b5a03b5603b5205b4e03b4a03b4603b4203a5d03a5a03a5606a5505a3d07a3905a3505a310893d0893504d7d05d7a09d7604d7504c7e04c7d03c6e03c6a03c6603c6205c5e05c5d03b6d03b6a03b6606b6505b4d07b4906b4505b410aa7e03a7a09a7603a7203a6e03a6d05a5e03a5a04a5603a5205a4e03a4d05a4c03a4a03a4903a4805a4603a456924403a4203a4103a4007a3e03a3d0594d089450392d089250584a03d6f03d6b03d6703d636e46f6c46b6a4676846303c5f03c5b03c5703c5306b6f07b6b06b6707b6303b5f03b5d03b5b03b5a03b5703b5606b5506b4f07b4b06b4707b4303a6f0aa6e03a6b03a6a03a6709a6603a6303a6203a5f03a5e03a5d03a4f05a4e03a4b03a4a03a4704a4603a4303a4203a3f07a3e03a3d3c16f2b1670395f039571814f131470793f069370392f0392d039270892503d6e05d6a05d6603d6205c5d03c5909c5503c5104b5d05b5904b5505b5104a5d06a5904a5506a510895d0895503e7e03e7d09d7a03d7909d7603d7109d6609d6504c6d05c6904c6505c610ab7e05b7a09b7605b720ab6e05b6d0ab6c05b6a05b6905b680ab6605b656636405b6205b6105b6003b5e05b5d03b5c05b5a0bb5605b550bb5403b5205b4e05b4d06a6d06a6906a6506a6104a4a06a4904a4605a4104a3604a350896d089650593d0893509d6e03d6205c6e05c6a09c6605c6203c5e03c5a03c5603c5203b4d05b4903b4503b4103a4d03a4904a4503a4106a3905a310894d0894509e7e03e7d03e7503e7209d7603d7503d6e03d6d03c5d05c5904c5503c5109b7e05b7a09b7605b7203b6e03b6a03b6603b6203b5e03b5d03b5c03b5a05b5905b5803b5605b556435403b5203b5103b5005b4e05b4d03a5d03a5a06a5907a5803a5606a5506a5403a5104a4a06a4904a4605a4104a3604a350395d089550593d0893503d6d05d6903d6505d610ac6d03c6905c6503c6109c5e09c5204b6d05b6904b6505b6104a6d06a6904a6506a6104a3a04a360896d0896503e7e03e7d09d7e0ad7d09d6e03d6909d6203d6109c7e04c7d04c7c05c7904c7505c7205c7105c7009b7e05b7d6237c05b7a05b7905b7809b7605b7509b7405b7205b7105b7009b6e05b6a09b6605b6203b5e05b5a0bb5603b5205b4e05b4d06a7d06a7906a7506a7104a4a06a4904a4605a4104a3604a350897d089750593d089350ac6e05c6a05c6605c6203c5e03c5a03c5603c5203b4d05b4903b4503b4103a4d03a4904a4503a4104a3a04a360894d0894503e7d03e7a09e7603e750ad7e03d7d03d6e03d6d03c5d03c5a05c5905c5803c5604c5504c5403c510ab7e05b7a09b7605b7203b6e03b6d03b6c03b6a03b6605b650bb6403b6203b5e03b5d03b5c03b5a05b5905b5803b5605b556035403b5203b5103b5005b4e05b4d03a5d06a5906a5503a5104a4a06a4904a4605a4104a3604a350395d089550593d089350385a 17 131071 6 63 11 2047 20 1048575
def cc_37_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x8e25e1c397f6f5f394758edcc146baeda59261701771d5cc21659b52ed13e1b4c26d239a4801d131a40098e04035c48bd342c85898342345873341a4504cb90b8f4251202cd00016 0x3d6e07d6a03d6603d6203c5d03c5903c5503c5104b5d05b5904b5505b5103b4d03b4a03b4604b459f34406a5d03a5903a5503a510895d0895506e7e07e7d03d7d03d7903d7503d7104c7d05c7904c7505c7103c5d03c5a03c5604c55a045406b7e03b7d9e37c03b7a03b7903b7806b7603b7506b7403b7203b7103b7009b6e03b6d0ab6c03b6a09b6603b6509b6403b6203b5e03b5d05b4e03b4d06a7e06a7d06a6e06a6909a6206a6103a3d03a3a06a3907a3803a3606a3506a3403a310897d069750393d0893506d6f06d6e07d6d06c6f0bc6d06c6b03c6906c6706c6506c6303c6109c5f09c5b09c5709c5306b6f04b6d06b6b05b6906b6704b6506b6305b6109b5f09b5b09b5709b53a534fa334ba13479d34306a6f06a6e06a6d06a5f06a5e06a5b06a5906a5309a5206a5106a4f06a4b06a4706a4306a3f06a3b06a3706a330696f0896d06967069650995f099570e94f0e9470e93f0e9370692f0692706c6e03c6a03c6603c6203c5e03c5a03c5603c5203b5a03b5604b4d04b4904b4504b4103a4d07a4903a4503a410894d089450ad7e03d7a09d7603d7203d6e03d6d03c6a04c6903c6603c6103c5604c5506b7d07b7a09b7606b7503b5d03b5a07b5907b5803b5606b5506b5403b5106a7e06a7d03a6e03a6d03a6c03a6a03a6607a650ba6403a6203a5e03a5d03a5c03a5a07a5907a5803a5607a559b25403a5203a5103a5004a4e04a4a04a4604a4207a3e07a3d0395d089550792d0792a07926089259112404c5d04c5506b6e05b6a05b6605b6203b5e04b5a04b5603b5203b4e04b4a04b4603b4205a3d07a3905a3505a310893d0893503d6e04d6d04d6503d620ac7e05c7a09c7605c7204c6604c6503c5e03c5d06b7d07b7a09b7606b7505b4d05b4a07b4907b4805b4606b4506b4405b4106a7e06a7d03a6e07a6a0ba6603a6205a5e05a5d05a5c04a5a04a5607a5504a5405a5205a4e05a4d05a4c05a4a07a4907a4805a4607a459924405a4205a4105a4007a3e07a3d0594d089450792d0792a07926089259012404d6e04d6a04d6606d6205c5d03c5905c5503c5103b5d04b5903b5504b5104a5d04a5904a5507a510895d0895504e7e09e7a04e7909e7804e760ae7204e710ae7004d6e05d6d03c6e03c6d03c5e04c5903c5204c519545006b7d07b7a09b7606b7506b6d04b6904b6507b6106a7e06a7d04a6e07a6d9726c04a6a04a6904a6804a6604a6504a6404a6207a6107a6003a5e07a5d03a5c07a5a0ba5607a550ba5403a5204a4e07a4d05a4c04a4a04a4604a4504a4404a4207a3e07a3d0896d049650792d0792a07926089258f12404d6904d6104c5e03c5d06b6d07b6a09b6606b6506a6e06a6d04a5e04a5a04a5604a5203a4e03a4d03a4c03a4a03a4607a459424403a4207a3e07a3d0792d0792a07926089258e12404c5904c5104b4e04b4206a5d07a5a09a5606a5503c5d03c5a03c5604c559445406b6e03b6a03b6603b6203b5e03b5a03b5603b5205b4e04b4a04b4605b4206a6d07a6a09a6606a6503a3d07a3903a3503a310893d0893503d6d03d6a03d6604d65955640ac7e03c7a09c7603c7203c6e03c6d05c5e03c5d06b7d07b7a09b7606b7503b4d07b4906b4503b4106a7e06a7d03a6e03a6a03a6603a6205a5e04a5a04a5605a5203a4e03a4d03a4c03a4a07a4907a4803a4607a459324403a4203a4103a4007a3e07a3d0394d089450792d0792a07926089258d1240ac6e03c6a09c6603c6203c5e03c5d03b5a04b5903b5603b5103b4604b4503a4d03a4a07a4907a4803a4606a4506a4403a410394d08949089450394104939089310881203c5e04c5d04c5503c520ab6e05b6a09b6605b6204b5604b5503b4e03b4d05a3d05a3a07a3907a3805a3606a3506a3405a3108959089510593d0893908935059310881204d6e09d6a04d6909d6804d660ad6204d610ad6004c5e05c5d03b5e03b5d03b4e04b4903b4204b418e34006a5d04a5904a5507a510895d0495904955089510881204c5904c5104b4e03b4d04949089410881203c5d03c5a03c5604c558e4540ab6e03b6a09b6603b6203b5e03b5d05b4e03b4d03a3d07a3906a3503a31089590395108949059410393d089390893503931088120ac5f09c5b09c570ac530ab5f09b5b09b570ab539134f9034b8f3478d34306a5f07a5b06a5706a4f07a4b06a4707a4306a3f07a3b06a3707a330695f08957089530894f0894b08947089430893f0893b08937089330792f0692707923088120ad6f09d6b09d670ad630ac6f09c6b09c670ac639a45f9845b964579245306b6f06b6d07b6b07b6a06b6709b6606b6506b5f07b5b06b5707b5306b4f07b4b06b4707b4306a6f06a6e06a6d07a5f03a5e07a5b07a5a07a570ba5607a5303a5207a4f05a4e07a4b04a4a07a4704a4607a4305a4207a3f07a3e07a3d0a96f099670e95f0e9570e94f0e9470793f069370792f0792d0792a0792707926089258c12403d6d05d6903d6503d6103c6d03c6903c6503c6103b6d03b6904b6503b6104a6d04a6906a6504a610896d0896505e7e04e7d03d6d03d6903d6503d610ac7e03c7a09c7603c7204c6e03c6d04c6c03c6a03c6903c6804c6603c658a46403c6203c6103c6003c5e03c5d09b7a04b7904b7604b7104b6604b6503b4d03b4a04b4905b4803b4604b4504b4403b4104a6d06a6906a6504a6103a5a06a5903a5603a5103a4606a450496d089650394d0894503d6e03d6a04d6603d6203c5d03c5903c5503c5109b6e05b6203b5d05b5903b5503b5105a5d05a5906a5505a5106a4903a410895d0895509d7e03d7a09d7603d7203d6e03d6d09c7e04c7d04c7505c7203c5d05c5904c5503c5104b7604b7503b6e03b6a03b6603b6203b5e03b5d03b5c03b5a05b5905b5803b5605b558835403b5203b5103b5005b4e05b4d03a6a06a6903a6603a6103a5606a5505a3d05a3a06a3907a3805a3606a3506a3405a310395d089550593d0893503d6e05d6a03d6603d6203c5d03c5903c5503c5104b6e09b6204b5d03b5903b5503b5106a5d04a5904a5504a5103a4a03a460895d0895504e7e05e7d04d7e03d7d0bd7c03d7903d7503d7203d7103d7004c7e03c7d8647c03c7a03c7903c7804c7603c7504c7403c7203c7103c7009c6e03c6a09c6603c6203c5e03c5d04b7e04b7d04b6e04b6909b6204b6103b4d04b4904b4503b4106a7d04a7904a7506a7103a5a06a5903a5603a5103a4606a450897d049750394d0894504d6e03d6a03d6603d6203c5d03c5903c5503c5103b5d05b5903b5503b5105a5d05a5906a5505a5103a4a03a460895d089550ad7e03d7a09d7603d7203d6e03d6d04c7d05c7a09c7604c7503c5d03c5a05c5905c5803c5604c5504c5403c5104b7e04b7d03b6e03b6d03b6c03b6a03b6605b650bb6403b6203b5e03b5d03b5c03b5a05b5905b5803b5605b558435403b5203b5103b5005b4e05b4d03a6a06a6903a6603a6103a5606a5505a3d06a3906a3505a310395d089550593d089350583a03d6f03d6b03d6703d6303c6f0ac6e03c6b03c6a03c6709c6603c6303c6203c5f03c5e03c5d8936f8736b853678336303b5f03b5b03b5703b5303b4f03b4d03b4b05b4903b4704b4503b4303b4106a6f06a6b06a6706a6303a5b03a5a06a5903a5703a5603a5303a5103a4703a4606a4506a3f06a3b06a3706a330f96f0f9670395f039570394f0394d03947089450f93f0f9370692f0692705d6e07d6a07d6605d6204c5d03c5906c5503c5104b5d04b5904b5504b5104a5d03a5904a5503a510895d0895505e7e04e7d04d6d03d690bd6503d6109c7a04c7904c7604c7104c6604c6504b6d07b6906b6504b6103b5e06b5d06b5503b520aa7e07a7a09a7607a7204a6e04a6d04a6c04a6a07a6907a6804a6607a658126404a6204a6104a6006a5606a5504a4e07a4d05a4c04a4a04a4604a4504a4404a4203a3e03a3d0496d089650792d0892509c6e05c6207b6e04b6a04b6607b6203b5e05b5a06b5603b5205b4e04b4a04b4605b4203a5e03a5205a3d03a3905a3503a310893d08935 18 262143 7 127 11 2047 20 1048575
def cc_37_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x8bbf43e7e007cfb92773aba749b96ad79465993155d80a8b2f651bf2775921e88b563f3a1e25cd6ea6a4431ae179509e7a3ffd1d2b0b5d04fac1af40aea01ee401380002 0x4d6f04d6e04d6b09d6a04d6704d6604d630ad620bc6f03c6b0bc6703c6304c5f04c5e05c5d04b6f04b6b04b6704b6303b5f03b5e03b5d03b4f03b4e04b4b04b4903b4303b4204b41bd340b626fac26ba12679626304a5f06a5d04a5b04a5904a5704a5504a5307a5103a4f0ba4b0ba4703a4304a3f04a3b04a3704a334016f331670495f0895d04957049550394f0b9470493f049370f12f0612704c5f04c5b04c5704c5303b5f03b5b03b5703b5303b4f04b4e03b4db525faa25ba02579525304a4f04a4b04a4704a4303a3f03a3b03a3703a333f15f311570494f049470393f039370e12f0412703d6f03d6b03d6703d6304c6f05c6b04c6705c6303c5f03c5d03c5b03c5a03c5703c5604c55bd45403b6f0ab6e03b6b03b6a03b6709b6603b6303b6203b5f03b5e03b5d03b4f05b4e03b4db326fa826b9d2679226303a5f03a5b03a5703a5305a4f04a4b04a4705a4303a3f03a3d03a3b07a3903a3706a3503a3303a313e16f2f1670395f039570594f049470393f0393d03937089350d12f0212703d6d07d6903d6503d6103c6d03c6903c6503c6104b6d04b6904b6504b6103a6d03a6906a6503a610896d0896507e7e06e7d03d6d03d6903d6503d610ac7e03c7a09c7603c7206c6e03c6d06c6c03c6a03c6903c6806c6603c65bb46403c6203c6103c6003c5e03c5d04b6d04b6904b6504b6103b5a04b5903b5603b5103b4604b4509a7a06a7906a7606a7106a6606a6503a4d03a4a06a4907a4803a4606a4506a4403a410696d089650394d089450686a05d6d07d6905d6505d6104c6d03c6904c6503c6104b6d03b6904b6503b6105a6d05a6906a6505a610896d0896507e7e06e7d06d6d03d690bd6503d6104c6d05c6904c6505c6103c5e04c5d04c5503c520ab7e05b7a09b7605b7206b6e05b6d06b6c05b6a05b6905b6806b6605b65b936405b6205b6105b6004b5604b5503b4e03b4d09a7a06a7906a7606a7106a6606a6505a3d05a3a06a3907a3805a3606a3506a3405a310696d089650593d089350686a04c6e04c6a04c6607c6203c5e05c5a05c5603c5203b4d04b4903b4504b4106a6906a6106a4d04a4904a4504a410894d0894507e7e06e7d04d7e09d7a04d760ad7204d6e04d6d04d6c06d6a04d69b756804d6604d6504d6406d6204d6106d6006c6d03c690bc6503c6104c5e05c5d04b6d04b6904b6504b6103b5e03b5d03b4e04b4903b4204b41b534009a7a06a7906a7606a7106a6606a6506a5d04a5904a5506a510696d089650895d049550686a07d6e06d6d04c5d04c5904c5504c5103b6d03b6503b5d03b5903b5503b5104b4e03b4d09a6a06a6906a6606a6106a5606a550695d089550685a03d6d07d6903d6503d6103c6d03c6903c6503c6104b6d05b6904b6505b6103a6d03a6906a6503a6109a5a06a560896d0896507e7e06e7d03d6d03d6903d6503d6104c6d05c6904c6505c6103c5d03c5a03c5604c55b54540ab7e03b7d0ab7c03b7a09b7603b7509b7403b7206b6e03b6d06b6c03b6a03b6903b6806b6603b65b436403b6203b6103b6003b5e03b5d05b4e03b4d09a7a06a7906a7606a7106a6606a6503a3d06a3906a3503a310696d089650393d089350686a06d6f07d6e06d6d0ac6f09c6b09c670ac6306c5f06c5d06c5b03c5906c570bc5506c5303c510ab6f09b6b09b670ab6306b5f04b5d06b5b05b5906b5704b5506b5305b51ba34fb834bb6347b334306a6b09a6a06a6906a6706a6606a6306a6106a5706a5606a5506a4f06a4b06a4706a4306a3f06a3b06a3706a330a96f099670695f0695d06957089550e94f0e9470e93f0e9370692f069270685a03c6e03c6a06c6603c6203c5e03c5a03c5603c5204b5903b5104b4d04b4904b4504b4109a6e07a6203a4d07a4903a4503a410894d0894509d7e03d7a09d7603d7203d6e03d6d03c6a04c6903c6603c6103c5604c5509b7e06b7d06b7507b7203b5d07b5906b5503b5106a7606a7503a6e03a6a03a6603a6203a5e03a5d03a5c03a5a07a5907a5803a5607a55b125403a5203a5103a5004a4e07a4d05a4c04a4a04a4604a4504a4404a4207a3e07a3d0395d089550792d0892503c5e03c5205b6e05b6a06b6605b6203b5e04b5a04b5603b5203b4e04b4a04b4603b4209a6e07a6205a3d07a3905a3505a310893d0893503d6e04d6d04d6503d6209c7e05c7a09c7605c7204c6604c6503c5e03c5d09b7e06b7d06b7507b7205b4d07b4906b4505b4106a7606a7503a6e07a6d03a6c07a6a0ba6607a650ba6403a6205a5e04a5a04a5605a5205a4e05a4d05a4c05a4a07a4907a4805a4607a45af24405a4205a4105a4007a3e07a3d0594d089450792d0892504d6e06d6a04d6604d6205c5d03c5905c5503c5103b5d04b5903b5504b5103b4e04b4903b4204b41ab34004a5d04a5904a5507a510895d0895504e7e09e7a04e7909e7804e7609e7204e710ae7004d6e05d6d03c6e03c6d03c5e04c5903c5204c51aa45009b7e06b7d06b7507b7206b6d04b6904b6507b6106a7606a7504a6e07a6dad26c04a6a04a6904a6804a6604a6504a6404a6207a6107a6003a5e07a5a0ba5603a5204a4e04a4a04a4604a4207a3e07a3d0896d049650792d0892503b4d03b4503a3a03a3604d6904d6104c5e03c5d09b6e06b6d06b6507b6203b4a03b4606a6606a6504a5e07a5dab25c04a5a04a5604a5504a5404a5203a4e03a4a03a4603a4207a3e07a3d0792d0892503b6e03b6a06b6603b6203b5e03b5a03b5603b5205b4e04b4a04b4605b4206a6d06a6503a3d07a3903a3503a310893d0893503d6d03d6a03d6604d65aa56409c7e03c7a09c7603c7203c6e03c6d05c5e03c5d09b7e06b7d06b7507b7203b4d03b4a07b4907b4803b4606b4506b4403b4106a7606a7503a6e03a6d03a6c03a6a03a6607a650ba6403a6205a5e05a5d05a5c04a5a04a5607a5504a5405a5203a4e03a4d03a4c03a4a07a4907a4803a4607a45a924403a4203a4103a4007a3e07a3d0394d089450792d0892509d6f09d6b09d6709d6309c6f09c6b09c6709c63b045fae45bac457a845306b6f09b6e06b6d06b6706b6507b6307b6206b5f07b5b06b5707b5306b4f07b4b06b4707b4306a6706a6606a6507a5f03a5e07a5b07a5a07a570ba5607a5303a5207a4f05a4e07a4b04a4a07a4704a4607a4305a4207a3f07a3e07a3d0996f099670e95f0e9570e94f0e9470793f069370792f0792d079270892503d6e07d6a03d6603d6203c5d03c5903c5503c5104b5d04b5904b5504b5103b4a03b4606a6e09a6206a5d03a5903a5503a510895d0895506e7e07e7d06d7e03d7d0bd7c03d7903d7503d7203d7103d7006c7e03c7da647c03c7a03c7903c7806c7603c7506c7403c7203c7103c7009c6e03c6a09c6603c6203c5e03c5d04b7d04b7904b7504b7103b5a04b5903b5603b5103b4604b4506a7e06a7d06a6e06a6909a6206a6103a4d06a4906a4503a410897d069750394d0894505d6e07d6a05d6605d6204c5d03c5904c5503c5104b5d03b5904b5503b5104b4d04b4506a6e09a6206a5d05a5905a5505a510895d0895506e7e07e7d0bd7d03d7906d7503d7106c7e04c7d04c7c05c7904c7505c7205c7105c7003c5e04c5d04c5503c5206b7e05b7da437c05b7a05b7905b7806b7605b7506b7405b7205b7105b7009b6e05b6a09b6605b6204b5604b5503b4e03b4d06a7e06a7d06a6e06a6909a6206a6105a3d06a3906a3505a310897d069750593d0893504c6e07c6a04c6604c6203c5e05c5a05c5603c5203b4d04b4903b4504b4106a6906a6106a4d04a4904a4504a410894d0894506e7e07e7d04d7e04d7d04d7c06d7a04d7906d7804d7604d7504d7406d7204d71a257004d6e09d6a04d6609d6206c7e0bc7d0bc7c03c7906c7506c7203c7103c7004c5e05c5d04b7e04b7d04b7c04b7904b7506b7204b7105b7003b5e03b5d03b4e04b4903b4204b41a034006a7e06a7d06a6e06a6909a6206a6106a5d04a5904a5506a510897d069750895d0495506d6e07d6d04c6d04c6904c6504c6106b6e03b6d9f36c03b6903b6503b6203b6103b6003b5d03b5504b4e03b4d06a6e06a6d06a5e06a5909a5206a5103a3a03a360896d0696504b4904b41 17 131071 6 63 11 2047 20 1048575
def cc_37_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x89fd7abd6b7d5bfe4cbd3d7d2e3d1ebe0f7d003d 0x3d6f03d6e03d6d03c6b09c6a03c6909c6709c6603c6303c6109c5709c5609c550ab6f09b6b09b670ab630ab5f04b5d0ab5b05b590ab5704b550ab5305b5103b4f0bb4b0bb4703b430aa6f09a6b09a670aa630aa5f06a5d0aa5b07a590aa5706a550aa5307a5103a4f0ba4b0ba4703a436523f5c23b532374a2330a96f099670a95f0895d0a957089550394f0b9470e93f0e9370e92f0e92703d6f09d6e03d6d03d6703d6503d6303d6203c6709c6603c6503c5f03c5e03c5d09b6f09b6b09b6709b6303b5f03b5b03b5703b5303b4f03b4d03b4b05b4903b4704b4503b4303b4109a6f09a6b09a6709a6303a5f03a5b03a5703a5303a4f03a4d03a4b07a4903a4706a4503a4303a416323f5a23b51237482330996f099670395f039570394f0394d03947089450e93f0e9370e92f0e92703d6f03d6e03d6d09c6f09c6e0ac6d09c5f09c5e03c5b03c5903c5309c5203c5109b6f04b6d09b6b05b6909b6704b6509b6305b6109b5f09b5b09b5709b5303b4f0bb4b0bb4703b4309a6f06a6d09a6b07a6909a6706a6509a6307a6109a5f09a5b09a5709a5303a4f0ba4b0ba4703a436123f5823b4f237462330996f0896d09967089650995f099570394f0b9470e93f0e9370e92f0e92703d6f03d6d03d6b03d6a03d6709d6603d6503c6f0ac6e03c6d03c5f03c5e03c5d0ab6f09b6b09b670ab6303b5f03b5b03b5703b5303b4f03b4d03b4b05b4903b4704b4503b4303b410aa6f09a6b09a670aa6303a5f03a5b03a5703a5303a4f03a4d03a4b07a4903a4706a4503a4303a415f23f5623b4d237442330a96f099670395f039570394f0394d03947089450e93f0e9370e92f0e9270384a04d6f05d6e04d6d0ac6f09c6b09c670ac6304c5f04c5d04c5b03c5904c570bc5504c5303c5104b6b09b6a04b6904b6704b6604b6304b6104b5704b5604b5504b4f04b4b04b4704b430aa6f09a6b09a670aa6304a5f04a5d04a5b07a5904a5706a5504a5304a518924f8024b772476e24304a3f04a3b04a3704a330a96f099670495f0495d04957089550e94f0e9470493f049370e92f0e92709d6f09d6b09d6709d6304c6f09c6e04c6d04c6704c6505c6305c6204c5f05c5b04c5705c5304b6704b6604b6505b5f03b5e05b5b05b5a05b570bb5605b5303b5205b4f05b4e05b4d09a6f09a6b09a6709a638725f7e25b752576c25305a4f04a4b04a4705a4305a3f05a3d05a3b07a3905a3706a3505a3305a310996f099670e95f0e9570594f049470593f0593d05937089350e92f0e92704d6f04d6e05d6d04c6f0bc6d04c6b03c6904c6704c6504c6303c6109c5f09c5b09c5709c5304b6f04b6e04b6d04b5f04b5e04b5b04b5904b5309b5204b5104b4f04b4b04b4704b4304a6f06a6d04a6b04a6904a6704a6504a6307a6109a5f09a5b09a5709a538524f7c24b732476a24304a3f04a3b04a3704a330496f0896d04967049650995f099570e94f0e9470493f049370e92f0e9270ad6f09d6b09d670ad6304c6f04c6d05c6b05c6a04c6709c6604c6504c5f05c5b04c5705c5304b6f04b6e04b6d05b5f03b5e05b5b05b5a05b570bb5605b5303b5205b4f05b4e05b4d0aa6f09a6b09a670aa638325f7a25b712576825305a4f04a4b04a4705a4305a3f05a3d05a3b07a3905a3706a3505a3305a310a96f099670e95f0e9570594f049470593f0593d05937089350e92f0e9270583a03d6f03d6b03d6703d6303c6f0ac6e03c6b03c6a03c6709c6603c6303c6203c5f03c5e03c5d04b6f04b6b04b6704b6303b5b03b5a04b5903b5703b5603b5303b5103b4703b4604b45ba26fb026ba52679a26303a5f03a5b03a5703a5303a4f03a4d03a4b07a4903a4706a4503a4303a4104a3f04a3b04a3704a334216f371670395f039570394f0394d03947089450493f049371112f0a1270bd6f03d6b0bd6703d6304c6f05c6b04c6705c6303c5f03c5e04c5d04c5704c5503c5303c5205b6f0ab6e05b6b05b6a05b6709b6605b6305b6204b5704b5604b5503b4f03b4e03b4db826fae26ba32679826303a5f0ba5b0ba5703a5305a4f04a4b04a4705a4305a3f05a3d05a3b07a3905a3706a3505a3305a314116f351670395f0b9570594f049470593f0593d05937089351012f08127 16 65535 6 63 11 2047 20 1048575
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_37_6 (Nat.sub p 192)) (cc_37_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_37_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_37_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_37_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_37_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0xc5f018b60315c062980b5f016b602d5c05a980b4f0169602d1ef62a00b43bb8c966d3ee5b259b4bb7ad166d1ed22a5a364b36860297ec52a5445faf4895116eb53654457ab4b953592a52254453014b74d1f275a7d237c9d697455c275a3cf4549f6893cdf275a180a579b4a91917e65224645b974d91915e4eb24a454934891914e35a7c6b4b8d68f1d15235a1c6124014a7151920db7c4354836d70d1f20db3c2354836c60293e05323d46f7f488f51adf53e3d4677b488f518c0525bc568716deecdb1c5b5ba570716cee4db1c5b180a476f4c8d11bdb5223446b6b4f8d119da5223446301486ccd917eb7b23545fad6c4df17eb3b03545fac6028fd75322b56f5b4a8ad5ad653e2b567574a8ad58c051daa4684dadea516136b5a84704dace9d16136b180a374b4c8895bd252a2256b474f88959d152a225630146674d3ce9a59d3473f8a874d0ce9259d2433a476748cc04af9c47c2769e6cdf09da59a5702768e65180c22a1837c276865c9f09d259627c27486549f09d1d9427c274660255c952a1123b234a8448cc04a79026c1d4763c9b07519809471b4883096c65220c2530127e2c9704d2d8a25c134a6024dc362f86c5b0d8ae1d59036298092f0b6b00517c25a40145b076c00515c15a801d64036900514c04938003f 8 11
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 fullMask g_37 ep_37 201 bds_37 (dagTraceF fullMask rootStock 10 f_37) (cur_37 0) rootStock 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_6 : treeBlockF 192 201 (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nj_37_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) i = true := block_join nj_37_1 (fun _ h1 h2 => treeBlockF_at nb_37_2 h1 h2)
theorem nj_37_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) i = true := block_join nj_37_2 (fun _ h1 h2 => treeBlockF_at nb_37_3 h1 h2)
theorem nj_37_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) i = true := block_join nj_37_3 (fun _ h1 h2 => treeBlockF_at nb_37_4 h1 h2)
theorem nj_37_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) i = true := block_join nj_37_4 (fun _ h1 h2 => treeBlockF_at nb_37_5 h1 h2)
theorem nj_37_6 : ∀ i, 0 ≤ i → i < 201 → (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) i = true := block_join nj_37_5 (fun _ h1 h2 => treeBlockF_at nb_37_6 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 201 → (dagCheckNodeV4 fullMask g_37 ep_37 bds_37 201 (dagTraceF fullMask rootStock 10 f_37) cur_37) i = true := nj_37_6
theorem lb_37 : LowerBin fullMask rootStock g_37 11 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def wg : List Gate := [⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [2, 1]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [9, 8]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [11, 7]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [14, 16]⟩]
theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4272472064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677352 * 2 ^ 32 + 4272472064)) (12 - 1) := by
  rw [show canon fullMask (4276677352 * 2 ^ 32 + 4272472064) = g_37 by decide]
  exact lb_37

end PEqualNP.Outside.L_meta_45425

theorem PEqualNP.Outside.L_meta_45425 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4272472064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4272472064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_45425.table2_from_lowerBin (4276677352 * 2 ^ 32 + 4272472064) 12 PEqualNP.Outside.L_meta_45425.root_lb PEqualNP.Outside.L_meta_45425.wg 17 rfl PEqualNP.Outside.L_meta_45425.wfits PEqualNP.Outside.L_meta_45425.weval
