import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43549

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

def m_0 : Nat := 0xa0a0a0a
def s_0 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_0 : Nat := 0x2020a
def ep_0 : Nat := 0x2080000000000020008000000000000000000000000000202000000000000000000
theorem epk_0 : ep_0 = edgePack 0xa0a0a0a g_0 := by decide +kernel
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, 0xa0a0a0a &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
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

def m_1 : Nat := 0xc0c0c0c
def s_1 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_1 : Nat := 0x4040c
def ep_1 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
theorem epk_1 : ep_1 = edgePack 0xc0c0c0c g_1 := by decide +kernel
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, 0xc0c0c0c &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
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

def m_2 : Nat := 0x55005500
def s_2 : List Nat := [0x11001100, 0x5000500, 0x5500]
def g_2 : Nat := 0x1001500
def ep_2 : Nat := 0x14000000000000000000000000000100040000000000010010000000000000000000
theorem epk_2 : ep_2 = edgePack 0x55005500 g_2 := by decide +kernel
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, 0x55005500 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
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

def m_3 : Nat := 0x33003300
def s_3 : List Nat := [0x11001100, 0x3000300, 0x3300]
def g_3 : Nat := 0x1001300
def ep_3 : Nat := 0x12000000000000000000000000000100020000000000000000000000000001001000
theorem epk_3 : ep_3 = edgePack 0x33003300 g_3 := by decide +kernel
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, 0x33003300 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
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

def m_4 : Nat := 0x3300330000000000
def s_4 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_4 : Nat := 0x100130000000000
def ep_4 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
theorem epk_4 : ep_4 = edgePack 0x3300330000000000 g_4 := by decide +kernel
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, 0x3300330000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
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

def m_5 : Nat := 0xf000f00
def s_5 : List Nat := [0x5000500, 0x3000300, 0xf00]
def g_5 : Nat := 0x1000700
def ep_5 : Nat := 0x6000000000000000000000000000000000000000000010002000000000001000400
theorem epk_5 : ep_5 = edgePack 0xf000f00 g_5 := by decide +kernel
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, 0xf000f00 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
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

def m_6 : Nat := 0xaaaa
def s_6 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_6 : Nat := 0x22a
def ep_6 : Nat := 0x28000000000000020800000000000002200000000000000000
theorem epk_6 : ep_6 = edgePack 0xaaaa g_6 := by decide +kernel
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, 0xaaaa &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
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

def m_7 : Nat := 0x55550000
def s_7 : List Nat := [0x11110000, 0x5050000, 0x550000]
def g_7 : Nat := 0x1150000
def ep_7 : Nat := 0x140000000000000104000000000000011000000000000000000000
theorem epk_7 : ep_7 = edgePack 0x55550000 g_7 := by decide +kernel
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, 0x55550000 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
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

def m_9 : Nat := 0xf0f0000
def s_9 : List Nat := [0x5050000, 0x3030000, 0xf0000]
def g_9 : Nat := 0x1070000
def ep_9 : Nat := 0x60000000000000000000000000000010200000000000001040000
theorem epk_9 : ep_9 = edgePack 0xf0f0000 g_9 := by decide +kernel
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, 0xf0f0000 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
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

def m_10 : Nat := 0xff00
def s_10 : List Nat := [0x5500, 0x3300, 0xf00]
def g_10 : Nat := 0x1700
def ep_10 : Nat := 0x60000000000000012000000000000001400
theorem epk_10 : ep_10 = edgePack 0xff00 g_10 := by decide +kernel
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, 0xff00 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
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

def m_11 : Nat := 0xa0a0a0a0a0a0a0a
def s_11 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_11 : Nat := 0x20a0002020a
def ep_11 : Nat := 0x200000000020a000002080000000800020008000000000000000000000200000202000000000000000000
theorem epk_11 : ep_11 = edgePack 0xa0a0a0a0a0a0a0a g_11 := by decide +kernel
def bds_11 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_11 : KnownBin bds_11 := by
  intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_11 : ∀ b ∈ bds_11, 0xa0a0a0a0a0a0a0a &&& b.1 = b.1 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_11 : Nat → List (Nat × Nat) := fun _ => []
def f_11 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV4 m_11 g_11 ep_11 0 bds_11 (dagTraceF m_11 s_11 4 f_11) (cur_11 0) s_11 4 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_11 g_11 ep_11 bds_11 0 (dagTraceF m_11 s_11 4 f_11) cur_11 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_11 : LowerBin m_11 s_11 g_11 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_11 kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xc0c0c0c0c0c0c0c
def s_12 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_12 : Nat := 0x4000c0004040c
def ep_12 : Nat := 0x40000000008000004080004000c00040008000000000000000000000000000000000004000000040400
theorem epk_12 : ep_12 = edgePack 0xc0c0c0c0c0c0c0c g_12 := by decide +kernel
def bds_12 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_12 : KnownBin bds_12 := by
  intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_12 : ∀ b ∈ bds_12, 0xc0c0c0c0c0c0c0c &&& b.1 = b.1 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_12 : Nat → List (Nat × Nat) := fun _ => []
def f_12 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV4 m_12 g_12 ep_12 0 bds_12 (dagTraceF m_12 s_12 4 f_12) (cur_12 0) s_12 4 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_12 g_12 ep_12 bds_12 0 (dagTraceF m_12 s_12 4 f_12) cur_12 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_12 : LowerBin m_12 s_12 g_12 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_12 kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0x5500550055005500
def s_13 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_13 : Nat := 0x100110001001500
def ep_13 : Nat := 0x40000001000000014000000000000000000010000000100040001001100010010000000000000000000
theorem epk_13 : ep_13 = edgePack 0x5500550055005500 g_13 := by decide +kernel
def bds_13 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_13 : ∀ b ∈ bds_13, 0x5500550055005500 &&& b.1 = b.1 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_13 : Nat → List (Nat × Nat) := fun _ => []
def f_13 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV4 m_13 g_13 ep_13 0 bds_13 (dagTraceF m_13 s_13 4 f_13) (cur_13 0) s_13 4 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_13 g_13 ep_13 bds_13 0 (dagTraceF m_13 s_13 4 f_13) cur_13 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_13 kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xf000f000f000f00
def s_14 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_14 : Nat := 0x100030001000700
def ep_14 : Nat := 0x40000000200000006000000000000000000000000000000000001000300010002000100000001000400
theorem epk_14 : ep_14 = edgePack 0xf000f000f000f00 g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_14 : ∀ b ∈ bds_14, 0xf000f000f000f00 &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_14 : Nat → List (Nat × Nat) := fun _ => []
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 0 bds_14 (dagTraceF m_14 s_14 4 f_14) (cur_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_14 g_14 ep_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) cur_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xaaaa0000aaaa
def s_15 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_15 : Nat := 0x20a0000022a
def ep_15 : Nat := 0x20000000000000000000000008000000280000020a0000020800000200000002200000000000000000
theorem epk_15 : ep_15 = edgePack 0xaaaa0000aaaa g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_15 : ∀ b ∈ bds_15, 0xaaaa0000aaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_15 : Nat → List (Nat × Nat) := fun _ => []
def f_15 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 0 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) s_15 4 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_15 g_15 ep_15 bds_15 0 (dagTraceF m_15 s_15 4 f_15) cur_15 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xf0f00000f0f0000
def s_16 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_16 : Nat := 0x105000001070000
def ep_16 : Nat := 0x2000000000000000000000004000000060000000000000000000001000000010200000105000001040000
theorem epk_16 : ep_16 = edgePack 0xf0f00000f0f0000 g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_16 : ∀ b ∈ bds_16, 0xf0f00000f0f0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_16 : Nat → List (Nat × Nat) := fun _ => []
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 0 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_16 g_16 ep_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) cur_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xff000000ff00
def s_17 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_17 : Nat := 0x130000001700
def ep_17 : Nat := 0x40000000000000000000000000000000000000002000000060000001300000012000000100000001400
theorem epk_17 : ep_17 = edgePack 0xff000000ff00 g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_17 : ∀ b ∈ bds_17, 0xff000000ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_17 : Nat → List (Nat × Nat) := fun _ => []
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 0 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_17 g_17 ep_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) cur_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0x55555555
def s_18 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_18 : Nat := 0x1151515
def ep_18 : Nat := 0x14000000000000140000000000000104040400000000011010100000000000000000
theorem epk_18 : ep_18 = edgePack 0x55555555 g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_2
  · exact lb_7
theorem sub_18 : ∀ b ∈ bds_18, 0x55555555 &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_18 g_18 ep_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xaaaaaaaa
def s_19 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_19 : Nat := 0x22022a
def ep_19 : Nat := 0x2080000000000220028000000000000020800000000002202200000000000000000
theorem epk_19 : ep_19 = edgePack 0xaaaaaaaa g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_6, s_6, 4, g_6)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_0
  · exact lb_6
theorem sub_19 : ∀ b ∈ bds_19, 0xaaaaaaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_19 : Nat → List (Nat × Nat) := fun _ => []
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 0 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_19 g_19 ep_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) cur_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0x5555555500000000
def s_20 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_20 : Nat := 0x115111500000000
def ep_20 : Nat := 0x1000000000000014000400000000010400040000000001101110000000000000000000000000
theorem epk_20 : ep_20 = edgePack 0x5555555500000000 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_20 : ∀ b ∈ bds_20, 0x5555555500000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_20 g_20 ep_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0x33333333
def s_21 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_21 : Nat := 0x1331333
def ep_21 : Nat := 0x12000000000000320020000000000100020000000000000000000000000001001000
theorem epk_21 : ep_21 = edgePack 0x33333333 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_21 : ∀ b ∈ bds_21, 0x33333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_21 g_21 ep_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xcccccccc
def s_22 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_22 : Nat := 0x4040c
def ep_22 : Nat := 0x4080000000000040008000000000004040c00000000000000000000000000040400
theorem epk_22 : ep_22 = edgePack 0xcccccccc g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_22 : ∀ b ∈ bds_22, 0xcccccccc &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_22 g_22 ep_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0x3333333300000000
def s_23 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_23 : Nat := 0x111131300000000
def ep_23 : Nat := 0x1202000000000010000000000000010002020000000000000000000000000111101000000000
theorem epk_23 : ep_23 = edgePack 0x3333333300000000 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_23 : ∀ b ∈ bds_23, 0x3333333300000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xf0f0f0f
def s_24 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_24 : Nat := 0x107070f
def ep_24 : Nat := 0x6080000000000060008000000000000000000000000010202000000000001040400
theorem epk_24 : ep_24 = edgePack 0xf0f0f0f g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5), (m_9, s_9, 4, g_9)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_1
  · exact lb_5
  · exact lb_9
theorem sub_24 : ∀ b ∈ bds_24, 0xf0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_24_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x943282054007c4f81e130c600c0178ad25a0ac9582a13d8780f01d13a0740e09a2304600b89702c22b00c801 0x3e4d236950b4681233c519d07a1c39201a870c5104a30150e2020090388028140fa736935448ad23564a696515826a1c390e151e0983834201654a60710100681c300c0a204d16694a3464d23078f9227a4135449287128f08c1c290e0d04058c4984b480e200a0d038601824141a06090d4945a46291d108d8728c31360e9707128408c1c3a081b07066846f21377093870ed706e1c2b38138706c102e000f 11 2047 4 15 10 1023 17 131071
def cc_24_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc0601d4e068b407430180480200 0xa8a6c2516626b0125a42687125408a1c41681aa6095f2493a4d8522cc8d5e24d284d0e24961143882c0351c0ac41303880f934 9 511 4 15 10 1023 17 131071
def cur_24 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_24_1 (Nat.sub p 32)) (cc_24_0 p) (Nat.blt p 32)
def f_24 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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

def m_25 : Nat := 0xff00ff00
def s_25 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_25 : Nat := 0x1001700
def ep_25 : Nat := 0x16000000000000000000000000000100060000000000010012000000000001001400
theorem epk_25 : ep_25 = edgePack 0xff00ff00 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5), (m_10, s_10, 4, g_10)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_3
  · exact lb_5
  · exact lb_10
theorem sub_25 : ∀ b ∈ bds_25, 0xff00ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x945282053e2784f01e030c5c4b09602b1560ac150aa03d8708d11a0322640c09803005c4b81702c22b00c801 0x7c0c0705236850a4280a73c509506260210e0eba064382a101150a0074d0b2601d246da0b49043a9a1d3e4c99074b8a2441c4d641f200c9805c282250a0074d092601d2451a0220b16684aa310ea7265083a7a1d2e20912413900841c3d3c1704088b2801d24249807490b4804a30181e06130d48462320ea7145083a7c41320e968e1385084203e0819070b6846721337091870fd70661c2f38118707c1026000f 11 2047 4 15 10 1023 17 131071
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb85c1b4c1603005411080040000 0x4e506326351297890b610560621c2da41487095004312409da0c28ca627cf13268209a084383b28190e0a8a04624811340 9 511 4 15 10 1023 17 131071
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_26 : Nat := 0xff00ff0000000000
def s_26 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_26 : Nat := 0x100130000000000
def ep_26 : Nat := 0x1200000000000000000000000000010002000000000001001300000000000100100000000000
theorem epk_26 : ep_26 = edgePack 0xff00ff0000000000 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_26 : ∀ b ∈ bds_26, 0xff00ff0000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xffff
def s_27 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_27 : Nat := 0x173f
def ep_27 : Nat := 0x28000000000000060c00000000000012300000000000001400
theorem epk_27 : ep_27 = edgePack 0xffff g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_10, s_10, 4, g_10)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_6
  · exact lb_10
theorem sub_27 : ∀ b ∈ bds_27, 0xffff &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xffff0000
def s_28 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_28 : Nat := 0x1370000
def ep_28 : Nat := 0x360000000000000104000000000000013200000000000001040000
theorem epk_28 : ep_28 = edgePack 0xffff0000 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_7
  · exact lb_9
theorem sub_28 : ∀ b ∈ bds_28, 0xffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xffff000000000000
def s_29 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_29 : Nat := 0x115000000000000
def ep_29 : Nat := 0x14000000000000010400000000000001100000000000000115000000000000
theorem epk_29 : ep_29 = edgePack 0xffff000000000000 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_29 : ∀ b ∈ bds_29, 0xffff000000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_29 g_29 ep_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0x5555555555555555
def s_30 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_30 : Nat := 0x115111501151515
def ep_30 : Nat := 0x40000001000000014000014000400140000010400040104040401101110011010100000000000000000
theorem epk_30 : ep_30 = edgePack 0x5555555555555555 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 5, g_13), (m_18, s_18, 5, g_18), (m_20, s_20, 5, g_20), (m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_18
  · exact lb_20
  · exact lb_2
  · exact lb_7
  · exact lb_8
theorem sub_30 : ∀ b ∈ bds_30, 0x5555555555555555 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV4 0x26130984c207008034c3801 0xc9714ae2550346894e089a434f76968d1c5a1a54f4a96951d2a1a53f4a7694dd299801f 9 511 4 15 10 1023 15 32767
def f_30 : Nat → Nat × Nat := unpackForestF 0x74f3a5d972ab874751a24d0e8601f 3 10
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 9 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 9 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 9 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 9 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xaaaaaaaaaaaaaaaa
def s_31 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_31 : Nat := 0x20a0022022a
def ep_31 : Nat := 0x2200200000020a0000020800000008002200280000020a0000020800000200002202200000000000000000
theorem epk_31 : ep_31 = edgePack 0xaaaaaaaaaaaaaaaa g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 5, g_11), (m_15, s_15, 5, g_15), (m_19, s_19, 5, g_19), (m_6, s_6, 4, g_6), (m_0, s_0, 4, g_0)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_15
  · exact lb_19
  · exact lb_6
  · exact lb_0
theorem sub_31 : ∀ b ∈ bds_31, 0xaaaaaaaaaaaaaaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 5 f_31) (cur_31 0) s_31 5 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 5 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0x3333333333333333
def s_32 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_32 : Nat := 0x111131301331333
def ep_32 : Nat := 0x22002000001202000012000010000000320020010002020100020000000000000000000111101001001000
theorem epk_32 : ep_32 = edgePack 0x3333333333333333 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 5, g_21), (m_23, s_23, 5, g_23), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_23
  · exact lb_3
  · exact lb_4
theorem sub_32 : ∀ b ∈ bds_32, 0x3333333333333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV4 0x1e0f0783c1c2e07038193c86432190b95c2e170a1d02813190c824111883503801 0xc95cc150b234a938a134835c7b50694c614459343130214421343244295c19541134db4fd34bbb479b43914f894b71475143493f413b39370933001f 9 511 4 15 10 1023 16 65535
def f_32 : Nat → Nat × Nat := unpackForestF 0xe9e1d2f0ae61500e8f48d289c51340e86153c2a5bf5c7ea0151d6a62d445a68150c29f853b0a6e29104ae113412a824d0299801f 5 10
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 28 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 28 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 28 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 28 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xcccccccccccccccc
def s_33 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_33 : Nat := 0x4000c0004040c
def ep_33 : Nat := 0x40000000008000004080004000c000400080004000c0004040c00000000000000000004000000040400
theorem epk_33 : ep_33 = edgePack 0xcccccccccccccccc g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 5, g_12), (m_22, s_22, 5, g_22), (m_1, s_1, 4, g_1)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl
  · exact lb_12
  · exact lb_22
  · exact lb_1
theorem sub_33 : ∀ b ∈ bds_33, 0xcccccccccccccccc &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 5 f_33) (cur_33 0) s_33 5 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 5 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xf0f0f0f0f0f0f0f
def s_34 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_34 : Nat := 0x105030f0107070f
def ep_34 : Nat := 0x204000000020a000006080004000c00060008000000000000000001000300010202000105000001040400
theorem epk_34 : ep_34 = edgePack 0xf0f0f0f0f0f0f0f g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24), (m_12, s_12, 5, g_12), (m_14, s_14, 5, g_14), (m_16, s_16, 5, g_16), (m_11, s_11, 5, g_11), (m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5), (m_9, s_9, 4, g_9), (m_0, s_0, 4, g_0)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_12
  · exact lb_14
  · exact lb_16
  · exact lb_11
  · exact lb_1
  · exact lb_5
  · exact lb_9
  · exact lb_0
theorem sub_34 : ∀ b ∈ bds_34, 0xf0f0f0f0f0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 7 f_34) (cur_34 0) s_34 7 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 7 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xff00ff00ff00ff00
def s_35 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_35 : Nat := 0x100130001001700
def ep_35 : Nat := 0x40000001200000016000000000000000000010002000100060001001300010012000100100001001400
theorem epk_35 : ep_35 = edgePack 0xff00ff00ff00ff00 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25), (m_14, s_14, 5, g_14), (m_17, s_17, 5, g_17), (m_13, s_13, 5, g_13), (m_26, s_26, 5, g_26), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_10, s_10, 4, g_10)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_25
  · exact lb_14
  · exact lb_17
  · exact lb_13
  · exact lb_26
  · exact lb_2
  · exact lb_3
  · exact lb_4
  · exact lb_5
  · exact lb_10
theorem sub_35 : ∀ b ∈ bds_35, 0xff00ff00ff00ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 7 f_35) (cur_35 0) s_35 7 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 7 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xffff0000ffff
def s_36 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_36 : Nat := 0x131f0000173f
def ep_36 : Nat := 0x42000000000000000000000000c000000280000020e0000060c00001310000012300000101000001400
theorem epk_36 : ep_36 = edgePack 0xffff0000ffff g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 5, g_15), (m_17, s_17, 5, g_17), (m_27, s_27, 5, g_27), (m_10, s_10, 4, g_10), (m_6, s_6, 4, g_6)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_17
  · exact lb_27
  · exact lb_10
  · exact lb_6
theorem sub_36 : ∀ b ∈ bds_36, 0xffff0000ffff &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xa80a42a408cc8c08c088288070c6e16e06a26a06a06436406404cc4a14a04a04a04a046246046046040340028c033001 0x1e254040280495a171421513a0485a048561d03e1003a1c0360a0320382a038261701d1913c080301714a0c1320392a0485a048561a03e0e03a18036030320382a038261701d04014141340403812054110240801c1514a021320392a0485a048561304e1004a0f0460e0420382a038260201d08014094580804006054050240401c0495a0c1420213a0485a048560b04e0a04a07046030420382a038260201dde34bd6347ce24bc4247be23fb123b922376b2335f1475513f441373412f1f1270484b1b03b160330d02b010230381b0001f 12 4095 5 31 11 2047 20 1048575
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc8320bcef0bc2c3b02b1ac292735c0701c07019364181601806018054d415012244501401003880e 0x1f22c2a14c7a080ec95130923a028700a0a84d1b01c4225a824ad00939f9253c24672484dc559a8a7241364824c0e0a41c1083819646b8c4d4180282e038568b0a85314820261244c4808808108182113c4426c844b999ad2f3565a69cb0d2941a3273424a28c904f920970383e070728c0c81c18a0030 10 1023 4 15 11 2047 19 524287
def cc_36_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xb81686d05a0b41682c0d61a44cc190320640c8161ac0580b0131a604c0981302224408041782000200000000 0x2f01c2a14c8c269184d9b0975d35ab86ad6c936d122ad23db2473608d5c918c51468a26cd44bab81d03839ac0700e0d81c18d325ca44a144142712a261249a05124942402846028a88b54115a7926bf2495048b30906591eca2358e2ad1453a289f25126070920e1041c0cc3028 11 2047 5 31 11 2047 19 524287
def cc_36_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x8c08258208207857807807807427407407407406c46c06c06c06c06253573403213013002e12e02a22a02a02a0224011 0x1fd2e3f25426248e60a00e123e15c7b2a8f0531c80c368147847aee8d5d52e3a25473250e449012ae371540425807061b40a41b4d8069520d1a39a2c6a5d894b51095a1d2ac2a548449d06936091f4023d3925afa4a9e8933c92576248e20a9c014b78286c04c0608524a231050656a8ca9018420313496148a904d8e0973535d5d6b2a0d55a5a8b4349674ba84964bd2ab32516448a8e4d8dc9701c5e038b2c61480e28b0050 12 4095 5 31 10 1023 19 524287
def cc_36_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xf81c9790720d0ba0340680d0181300600576a8131260444614c018030048c900851001082002104008000800 0x9f4589e4502a14c0384c960409c45804c500834c9b04c0384099458984509714c96140b045aaf459ae458ab456a9451a534e8234da825aa7256a624e8424da623ea5239902328e231a214ea114da014c281459d1425a13d4a1359a04e10049950429404193040862549124c8f24c771248c2547f1287c12475028048248c2548b1248a0288123c7e1287b124740286e0248123a862367812481254 11 2047 5 31 11 2047 20 1048575
def cc_36_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xaa1502a0521a0340270ce090708e1040180084100184300600c0123240214400801002004008000800000000 0xc335ac1356b534e8334dbb24aba249a624683241a6236b62355b14d4b1452d13dc0135bf0390e031912348f244b9028aa4582a14c080408c2542612404028b4020bd35abc356bb34eba34da534580342b825ab7256b6246a5245b523e8023d3f12db3125b20290a021a415c9f1509c05c99050aa45cad15cac050aa35ca315c9e1500485c98050a4458a34509b04c97040 11 2047 5 31 11 2047 20 1048575
def cc_36_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xfdbf07e07a1f41e07c0742b1d50aa0521a41406804c25a0b01602c04c6981112204028001782004000400000 0xdd455dd355d5259c323de3239e023589231681555d13ddf135048590483904831d80508c254d845cd8349c9245dd45edd349dc25db8259ab255db251c8245da15d501550485e04859d905204851d7050aa244d0028aa458c7254d0349c7245d5459c6355bd34aa8346c6255d424eb824ad3246892424212dd2125d102a04829cf02804826048218c354cc134cb0388c450c9050c7028c645ecd35dc3359ab355ca351c8345c6249bc23aa7236c515d2f15564145048590485104849c2050 11 2047 5 31 11 2047 20 1048575
def cc_36_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xccc30 0x154d63889e70830 4 15 2 3 10 1023 19 524287
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_36_7 (Nat.sub p 224)) (cc_36_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_36_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_36_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_36_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_36_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_36_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0xdf473c24f384186fa35df26a02d2f5da4eba5dd74a3ae5775c296c349d70a002d1f3e2ce7a4ecf48d9e4973c1568349cf0500292f15aee5934cb0718ad47242862b45c70518a92714ae80a47bf6b584142fdab5f935bf072028fec9ad59356b269d64d36e4145925ab24ad6491ac91f5a020b224b640a4051dc9c5a938b327162b0ae56050938ad54d724e28c9a5a934ad268fa4d1cd1c58a38a12653a4ca6c994c9e8b13d1424ca14dc589b0992613a5a2c4b450962992c5024c214984193080028de4526363468f498d8d15b12ec52548a249140a1b12d362566c4ab0c8d9b12a3624e6c49ad88fa052a3623d7e4b8fc951b0953d95c7b2a8d8499b092bba3d7746ad8491c92e3925472250e4491b015360296c050da551b40a3602601466c0d7581a8b0349604bac0945952030245600a4c2d258522b00500128ebc0e159ad2b3565649aac915591cab23556074ac0e0049fa2c5a514b8a2941442822c564549a9a951341422a414547a8a8d5212824050452ac8c0a1149f00937430506a968d52b1aa4e354947b160f4201aa463a4a8740a0d5211c050352ac6c0e0d4a70092f206b460d70c1a818050206ac5c0e081a71034a298b052530a42010346206844c90080a31012e20064424d88497100300124e3c950701f0e036010762e0f8649e0b8361703a020cc38a50a1340e09c2215044120704a0e08c1c1080415811420209c04128222c040400208c0815010120201c020840407404118001f 8 11
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 228 bds_36 (dagTraceF m_36 s_36 7 f_36) (cur_36 0) s_36 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 64 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_2 : treeBlockF 64 96 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_3 : treeBlockF 96 128 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_4 : treeBlockF 128 160 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_5 : treeBlockF 160 192 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_6 : treeBlockF 192 224 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_7 : treeBlockF 224 228 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nj_36_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) i = true := block_join nj_36_1 (fun _ h1 h2 => treeBlockF_at nb_36_2 h1 h2)
theorem nj_36_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) i = true := block_join nj_36_2 (fun _ h1 h2 => treeBlockF_at nb_36_3 h1 h2)
theorem nj_36_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) i = true := block_join nj_36_3 (fun _ h1 h2 => treeBlockF_at nb_36_4 h1 h2)
theorem nj_36_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) i = true := block_join nj_36_4 (fun _ h1 h2 => treeBlockF_at nb_36_5 h1 h2)
theorem nj_36_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) i = true := block_join nj_36_5 (fun _ h1 h2 => treeBlockF_at nb_36_6 h1 h2)
theorem nj_36_7 : ∀ i, 0 ≤ i → i < 228 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) i = true := block_join nj_36_6 (fun _ h1 h2 => treeBlockF_at nb_36_7 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 228 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 228 (dagTraceF m_36 s_36 7 f_36) cur_36) i = true := nj_36_7
theorem lb_36 : LowerBin m_36 s_36 g_36 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xffff0000ffff0000
def s_37 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_37 : Nat := 0x115000001370000
def ep_37 : Nat := 0x22000000000000000000000014000000360000010400000104000001100000013200000115000001040000
theorem epk_37 : ep_37 = edgePack 0xffff0000ffff0000 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 5, g_16), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_28
  · exact lb_29
  · exact lb_7
  · exact lb_8
  · exact lb_9
theorem sub_37 : ∀ b ∈ bds_37, 0xffff0000ffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_37 : Nat → List (Nat × Nat) := unpackCursorV4 0xc0602e361924824102803883a01 0x514041303c58845072403130534042303244213c3b4f3b4b3b473b433a42394f394b39473943a13f913b61371133001f 9 511 4 15 11 2047 16 65535
def f_37 : Nat → Nat × Nat := unpackForestF 0x93f24efc50e9009378d02230491113c24cc01f 3 11
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 11 bds_37 (dagTraceF m_37 s_37 6 f_37) (cur_37 0) s_37 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37 : treeBlockF 0 11 (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 11 (dagTraceF m_37 s_37 6 f_37) cur_37) = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 11 (dagTraceF m_37 s_37 6 f_37) cur_37) i = true := fun _ h1 h2 => treeBlockF_at nb_37 h1 h2
theorem lb_37 : LowerBin m_37 s_37 g_37 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xffffffff
def s_38 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_38 : Nat := 0x137173f
def ep_38 : Nat := 0x16080000000000360028000000000104060c00000000013212300000000001041400
theorem epk_38 : ep_38 = edgePack 0xffffffff g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24), (m_25, s_25, 7, g_25), (m_21, s_21, 5, g_21), (m_22, s_22, 5, g_22), (m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_10, s_10, 4, g_10), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_25
  · exact lb_21
  · exact lb_22
  · exact lb_18
  · exact lb_19
  · exact lb_27
  · exact lb_28
  · exact lb_10
  · exact lb_0
  · exact lb_1
  · exact lb_2
  · exact lb_3
  · exact lb_5
  · exact lb_6
  · exact lb_7
  · exact lb_9
theorem sub_38 : ∀ b ∈ bds_38, 0xffffffff &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 7 f_38) (cur_38 0) s_38 7 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 7 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xffffffff00000000
def s_39 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_39 : Nat := 0x115131f00000000
def ep_39 : Nat := 0x120a000000000014000c000000000104020e0000000001101310000000000115101000000000
theorem epk_39 : ep_39 = edgePack 0xffffffff00000000 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 5, g_20), (m_23, s_23, 5, g_23), (m_26, s_26, 5, g_26), (m_29, s_29, 5, g_29), (m_4, s_4, 4, g_4), (m_8, s_8, 4, g_8)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_23
  · exact lb_26
  · exact lb_29
  · exact lb_4
  · exact lb_8
theorem sub_39 : ∀ b ∈ bds_39, 0xffffffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xc40c02c00c00acaac0ac0aa192c9209209019009006946806806616606604ae4a048148048044244042142028d033001 0x70a0f0243ed78eb5209d382742384f8e12e360f41c390a0d41c31305302f5e0bd481f4d1e8f4ca392e8d49a31094f4253507104882e07088a1240b9782e522a9389a42078f81e3d124b491250b1781c52221381c42070e81c39160d81c31160981c250706810161c4902f5e0bd487b4e1ad081e3e078f4613d0a4d4583e070f4582e070a41c22070841d240ed403340074a02e5e0b948264e099084a3e108e82a36088c8193e074b8103e070c81c1990d0e224f7690db23f548cd314f094fd012f3449c2c4f0710cb03f070cc802f070ac50270708c1c1b0205c001f 12 4095 5 31 10 1023 18 262143
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xa80a80a238118007c27c07c066b6416406406405e35c15a15a05a05625603ae3a03a03621ec1e01e01a21a01a000d000 0x7c682f49341c94c3451846bb089760927312424625b004941c1c838310b05a160a81c14838287e04c16095e0120382107090e8111c9af383526069ac090424a68493d0926a3c0f41c1cb703507062b849198920382864048b449168a62e3425a47ad514981a6b425e624a4c093424968492a5e24c1249560921302d07052ac0941c10a805c070a012d2425a09f24d524929c9151920a212e0b09a0e1242c2283841070320e0a120122525e464a41293825212215e0929c704d8e0930902d07052840941c1083015 12 4095 5 31 11 2047 19 524287
def cc_39_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x90240902134bd2044510134310842008002 0x96279280f01c18432516a482e08f6611cc92356246212534249e849350b0ba0e1042c1e838390b06a0e0c6389a4245d8c692e0d0611289f14d8a28a161742c26838490b08a0e1041c14838217c048f4091e8ae0392c 10 1023 4 15 11 2047 19 524287
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_39_2 (Nat.sub p 64)) (cc_39_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0x24a39944f2503c928d40b438e4d22b498a5140a4f79145e25d78939e12578099eb417a935e0240290dd0446ed79bb526e0d40a3f571495a5e644919024569495a4d564996b425a8f55924560940a334e925405c4e914094f42979202442949095e42094092f36d78f02436d48d92e360f409272e8e4c14c2e8d4083f22938a12422908892522138082f16d38712416d08593d160b80827048f8123a0cd403340048d81232044f8103e0205c001f 7 11
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 77 bds_39 (dagTraceF m_39 s_39 7 f_39) (cur_39 0) s_39 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 77 (dagTraceF m_39 s_39 7 f_39) cur_39) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 64 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 77 (dagTraceF m_39 s_39 7 f_39) cur_39) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_2 : treeBlockF 64 77 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 77 (dagTraceF m_39 s_39 7 f_39) cur_39) = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 77 (dagTraceF m_39 s_39 7 f_39) cur_39) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nj_39_2 : ∀ i, 0 ≤ i → i < 77 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 77 (dagTraceF m_39 s_39 7 f_39) cur_39) i = true := block_join nj_39_1 (fun _ h1 h2 => treeBlockF_at nb_39_2 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 77 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 77 (dagTraceF m_39 s_39 7 f_39) cur_39) i = true := nj_39_2
theorem lb_39 : LowerBin m_39 s_39 g_39 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def g_40 : Nat := 0x115131f0137173f
def ep_40 : Nat := 0x2204200000120a000016080014000c003600280104020e0104060c01101310013212300115101001041400
theorem epk_40 : ep_40 = edgePack fullMask g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 8, g_34), (m_35, s_35, 8, g_35), (m_36, s_36, 8, g_36), (m_38, s_38, 8, g_38), (m_39, s_39, 8, g_39), (m_37, s_37, 7, g_37), (m_32, s_32, 7, g_32), (m_30, s_30, 7, g_30), (m_24, s_24, 7, g_24), (m_25, s_25, 7, g_25), (m_31, s_31, 6, g_31), (m_33, s_33, 6, g_33), (m_23, s_23, 5, g_23), (m_11, s_11, 5, g_11), (m_12, s_12, 5, g_12), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_13, s_13, 5, g_13), (m_14, s_14, 5, g_14), (m_15, s_15, 5, g_15), (m_16, s_16, 5, g_16), (m_17, s_17, 5, g_17)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_34
  · exact lb_35
  · exact lb_36
  · exact lb_38
  · exact lb_39
  · exact lb_37
  · exact lb_32
  · exact lb_30
  · exact lb_24
  · exact lb_25
  · exact lb_31
  · exact lb_33
  · exact lb_23
  · exact lb_11
  · exact lb_12
  · exact lb_26
  · exact lb_27
  · exact lb_28
  · exact lb_29
  · exact lb_13
  · exact lb_14
  · exact lb_15
  · exact lb_16
  · exact lb_17
theorem sub_40 : ∀ b ∈ bds_40, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x993297c58cec8b8580ac7f067c8a70b06f0662b26280614557a7574156444c6843a343413aa32eef246a2305220421c121c01fc81f811dc714a508b000610001 0x2195bc8056b1ed59c755631cd1887236f1bcd9c6c35f198d5c05a6201694805a3a0165bc5c16e0165ac0596a01659c0796601658c0596201657c5515e01656c0595a01655c0695601654c059520164ec0593a0164dc1f13600e1bc0486b00e19c0486300e17c0485b00e15c048530120ec0383700e07c0381d01206c0481900e05c0381501204c048110169001794c0165200d94401650015e7e01b9f407d7a01b5e406d7601b5c406d6601b5941d46901b18405a7a0169a805a680169080a97e0165e8079760165c80696e0165b40696c0165a8059690165a00696601659417964016588059610165800695e016568069560165480914e0165080386d0121a4038650121840381d0120640381501204405a5005e5300594803a5100594001f9f806e7d01b9d407e7201b5d806d750575b807d6d01f1e41147106d16407c510169e805a4201e5f80597a01e5d80597202e5b80596a01a5980596201e5780595d01e5700595a0165640595801e5580595505e55005952016544059500205380594200e1740485900e1540485100e0740481900e054048110169400715c05e5300594805e510059400169a805a5a0168c80596a01656807956016528069460184f80593201b9f807e7d01b5f806d7d01b5b806d6901f58806d6101b1e41947101adf81837c0169a805a4201a5f80597d05e5f00597a0165e40597801a5d80597501a5d0059720165c40597001e5b80596a01e5980596201a5780595a01a558059520145380594201a1f80387d00e1f00487900e1d4068720121c40487000e0740481900e054048110169000415c05e530059480365100594001b9f407e7a01f9d806e7501b5f806d7d01f5b807d6d0511e415c7105916415c510169e805a5a01696005a4202a5f80597a01e5d80597202e5b80596a01a5980596202a5780595d02a5700595a016564059580565580595505e550059520165440595000c5380594200e1741585a012164048580261580385500e1500485100e0740481900e054048110169600b95c0165601795401654007e790519c407d7204d1b806c6a01b19807c6201f17405a7a01690805a4001e5f80597a01e5d80597203a5b80596a01a5980596201e5380594d01e5300594a0165240594801e51805945036510059420165040594000e1340484900e1140484100e0740481900e054048110169400b95c01656017954016540116790579c407d7a0411b806c6a01b19815c6201f17405a7a01694005a4a0169200a97e0165e8079760165c80e96e0165a8069660165880a94e0165340a94c016528059490165201594601651417944016508059410165000384d012124038450121040381d0120640381501204406d620571f806c7a01f1d806c7201b17405a7a0365f80597a01e5d80597201a5b80596a01a5980596201a5380594d01a5300594a0165240594801a5180594503a510059420165040594000e1340484900e1140484100e0740481900e05404811016d3006d6a0571f807c7a01f1d815c7201b17405a7a0365f80597a01e5d80597202e5b80596a01a5980596202e5380594d02e5300594a016524059480345180594505e510059420165040594000e1340484900e1140484100e0740481900e054048110175bc05d6e0175b40ac6f01f1ac07c6702b18c0ac5f01b1740ac5b02f1640ac5701b1540ac5302b14407b6b02ad8c0ab5b036d640ab5302ad440db4b036d0c0596a0164c80386f0121ac0386701218c0385f00e1740485b02a16804859012160038570261580385500e150048530121440384f01212c0384701210c0383f0120cc06d6f02f5ac06d6702f58c0bc6f02b1b80bc6b01f1a80bc6701f1980bc6302b18805c5f01717805c5d03adac0eb6301ad6c0bb5302ed2c0eb4902ed0c0bb410164c80386f0121ac0386701218c0385f01216c0385701214c0384f00e1340484b0121240384700e114048430121040383f0120cc06b6c05eda016b6401ad800596801ed7017b5805ad5007b50016d100747005adf006b7801add017b700189f00387c0121c005b440111600ab5c05ed6016b5402ad400485800e1500956f0215ac0556700d58c16b6f02adb816b6b01eda816b6701ed9816b6302ad8816b5f02ed7816b5b01ad6816b5701ad5816b5302ed4805b4d00e1bc0486b00e19c0486300e17c0485b00e15c0485300e0fc0383d0120ec0483900e0dc038350120cc048310715bc1a56b05d59c155630491ac0f46303916c0c4530169a805a420165bc0b16e0165ac0596a01659c0796601658c0596201657c0a15e01656c0595a01655c0695601654c0595201653c0214e01650c0594200e1bc0486b00e19c0486300e17c0485b00e15c0485300e13c0484300e07c0381d01206c0481900e05c0381501204c048119a117e6345b96515e4d453920d6e26353888d2dfd3437dc97ddb25772093da524759c8fd4b15b3f454cc014b22c50c1e1330044ac0385f01216c0385701214c0384f01212c0384701210c0383f0120cc0482b00e09c0381f01204c0003f 16 65535 6 63 11 2047 22 4194303
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xfc07e03e05d86ec06e23683987c81601300158aac05602a053479a04036000fc17e03f01f80fc07623a05d00e41700b70551a02a 0x1f2b03d26c158f8f11d03d26059281109894101c1b40bb600d6a8e8950242c03854110788c0c1892a3846c0d8c81ad905d2605a381109832100441e0c8300d6d0c8d80441e0c8306ccf0d59c05db606b58606a0d09b01c360486011078320c192b03125c178d8c119171b206a4c0b46822131102006b520d4bc169642d2905a510b4a01a938352486a425c48216548441721022580a8331b14a302826c4e0d8164a1202205a340b4a0acdb951b5263664a6c48cd7865ad0cb56446a4849582d1f0383e0707a0e0f292b7ce56b96acf1d58e29b78ab6e866d61eda9f9b387b66766c62ad89c9af8bb5e6e6b61ad6999ab86b565e6a62ed49692b05a3e070de121ac1c3384863070be1216c1c2b848530707e220f81c1e8383c09076120e41c1b8383509066800c8241884830 13 8191 6 63 11 2047 19 524287
def cc_40_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xdc0748a9fce6c49b026c093223c4842d66b59015834d253404a0d2023f24f423b08cc83108b442c047cd1f005c816044450f082c40a0400a 0x48580daf81b5d036b65f5680dac82b582f1a805950090d00e1902eb785d6e0bada2b1bc563687c6b0f8cf9119456318ac5f0d8ba2b16c5e2c8ac570d8aa2b14c56288aa6f154da1e99f19328aa5f154ba2a95f112ae024fba48e0e1bc243584869070ce1218c24308385f070ba1216c542d04859090b00e15c442b03855070a81214c24288384f090960e11c24218482b0704e2b1b05e3413c64158c1691f03e3c07c74178e164dc02cb80387c090e01b1785e2e86a5e1749c2b5b83eb507d6615ac4171645d2f0ba4e070ba121641c2a848510dade2f5ac36b38bd63178de2b1b85e3587c6a178ce1f1985e318ac620b8be171782e2edb26fb04ce2e97c5d2e86a57ae4aa2e93c5d268ba47ac48a0e1bc243583867090c60e17c242d83857090a60e13c1c268484b090920e11c1c228484309082120ac1c1386c5c070b81214035b654368a66c81ad8035ac0bb500b2d00e0f0241806c6807098121002d20048200f6f02adc03dae51358a06a81ed42792a0383c09060121a01c320382c0904134df035bc06b74986e00e1f024380383c090600e0b0241006c600f8a00e130242005a400f6f02adc035b40bb60156b928d6249aa0ab50904a8121601c2a0383c0906110de055b807b648c4c8121a01c320883c56060f4992223e07c74154982213150200883c190601eda1f1b00883c52060a008212be41570156f81eda1e1b04027c070f8121c0441e26030 14 16383 6 63 11 2047 19 524287
def cc_40_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x81c981c07e4e7078704070406e876e8069555cb359cb4cb541eb3f0b3c8a30712f832ccb212f21001f471b501b40188b0cef0cc0090f060c034b02c2004a0001 0xb4e0168e268be05978272e8165c328b6079640b2701f5b42eb485d650bac21b1b42e3485c650b8c3349b7e9328386d090d20e194243086e7e0fcfa1b5f836be86d6e0dad21f58836b086c72fe8e01f18bf1be86b750b4e4169c02d3105a520b4741a5f82cbefc17c0b2f4165e42cbc069760b2ea1a5d02cb9059710b2e01e5b82cb6e416c0b2d41e5982cb2879640b2c41a5782cad069560b2a4164ea589b0687e070fa0e1f0243c838750d0e4121c424380381d090320e0542408fa4500b4a1e45702cac491540b2a1204d036b686d650d8dc171a82e3305c620f8bc171682e2b05c52156c456d83b926c92450b2c4165482c950384d090920e114242086e7d0fcf41f9d8373a86d7e0dafa1f5b83eb68ac722b8e036d77c1aa85a720b4c4169482d2805a3a152fc165e83cbb05972172dc165a834b305962152bc1657454ae0595a0b2b2165606cab05955ec2a8165482ca8859500b2751c4d81c2e8d85a090b212160442b03855070a8121441c0e848190702a1204456b707d6d0f8ac571542d3105a5a0b494168e82cae859550b2942b5bc3eb5f45690face2b58caeb095c5f158b65715c56298ab6f0f6cfb8d7f51ab8ab4f2b68e169882d2905a4a0b474165bc2cb68596b0b2d41659c3cb3059650b2be1656c2cab859530b296165282c9d85937070de121ac1c3384863070be1216c1c2b848530709e1212c1c2384843090760e0dc1c0f8481b0702e1204c36b68ed690daca37584563907b760f6cc169c82d3105a600b4a42a5f82cbe8a97c0b2f41e5d82cba879740b2e42a5b82cb68a96c0b2d4165a42cb40d9660b2ca4e5902cb1059610b2c16c5782cad069560b2a40e1b4243483865090c20e074240c8381509022169882d2905a4a0b2da165a83cb3059650f2c9645782ca90594a0bad21b1b45e3486c65178c2165081c3684869070ca1218436be87d790daea3b5c43e39714700f8c41edf83db705a720b4e0169882d290797e0b2fbc05f02cbd059790b2f01e5d82cba879740b2e4165c42cb80796e0b2db8c5b02cb5079660b2ca1e5902cb15815e0b2b41a5582ca90787e070fa0e1f0243c838750f0e4121c424380381d090320e054240885a50090b00e150563707c6a0f8cc2b1882e2d06a560b2a40e13424248384509082375f83ebd07d761bae5b91c835b306b560b4e4169882d2905a50c02fc165e83cbb05972172dc165b45cb60596a0d2cc1659434b205962172bc165745cae0595a0b2b21656074ab05955da2a8165482ca885950070ba3a168242c84858110ac0e1541c2a048510703a120641c0a848110fcf02b9c35a360ac600b4c1a05b02cb00ac6e158c41ad782d3105a520b495785b82cb10595d0b2b41a5582caa8594a0b26a1206424088ad6e0fad41f59856b105c59d06c4165881c2e84859070aa12144373f07e7a0dcec379cb523906c62d28c01adb835af05a720b4c4169802d295d17e0b2f41e5d82cb90696e0b2db9c5b02cb5059690b2d01a5982cb2869640b2c4165842cb00695e0b2bb5c5702cad069560b2aa1a5502ca9059355a2680e1b4243483865090c20e074240c83815090221b5b856b686c6e0d8da1b1643628e526d0d4ca1a1b8243486862090c212180542d088560fadc2b5b4363686c650f4dc1e1b8243487862090c212180542d088560bad21b1b45e3486c65178c22a9b8552f0386d090d20e194243084868070c82b1f03e3a0ac6c178d185190563004868070c8121201c2205c6c 16 65535 6 63 11 2047 19 524287
def cc_40_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xad095906a82d482a90149269205240a3853f227a14c4c98032f065e048cc91810e55c75abf45780a6254c0255131e45a24a83150029823e541b8800d 0x9d3780ab7007b649f264972649d47c07c7407b740aa4c05a3807b689836006d7c9b4700ab7c07b68963609a27c059700387c04870984609726c0ac7c964748e37407a4c05a34059280482803824903500ea440ab6e07b6a07b660ab6206b569034d0ba5e0ea360383d0483903835048319045c07a44914620bb5e0aa6e07a6a07a660aa620ba5e9024d0382d04829038250482107c6e07c6907c620bc610bc6007a6e05a6905a6205a6105a6007a5e07a5907a528e25105962059320786e0486907862048610486006d6f0bd6b06d670bd63a446ba046306c5b0bc539e36f0ab6e9c36b07b6a9936707b66953630ab629434f9334e923438f3428d2660ba5e05a3e059420386f0486b03867048630385f0485b03857048530384f048430383f0383d0483b04839038370383504833048310482906d6f0bd6b06d670bd63be46bb946306c5b0bc53b736fb23670bb5f06b57af34f05a5a05a420596fac16e0596b0596a059670796605963059620594fa614e05943059420593b0593a059378c1360592d0386f0486b03867048630385f0485b03857048530384f048430483b038370381f0381d0481b048190381703815048130481105a680a97c079748a16c0596853164059600386c048600ad6e05d6a05d6605d6205c5d05c5906c5505c510ab628825d53255059620592a0385d0485903855048510de7e06e7d07d7a06d7906d7606d7106d6606d650ac7206b6d8936505a7205a6a05a6805a5205a3a0a97e0597d0a97c0597a079760597507974059720696e0596d0696c0596a05969059680696605965871640596205961059600695e0595a06956059520593a521360386d0486903865048610381d04819038150481105a6205a5205a4a05a3a0596a079660b95e059520594a05a581395c0595850154059504f1340384c06d6d06d6505c6e05c6a06c6605c620ac5e05c5a05c5605c528324d50245059520884e0384d0384c048490384582042048410484007e7e06e7d06e7507e7206d7606d750dd6e07d6d07c727447007c5a8545807b5d8435505a7205a6205a5a05a5805a3a0797e0597a07976059720b96e0596a06966059620795e0595d0795c0595a05959059580795605955811540595205951059500593a4e1360385d0485903855048510381d04819038150481106d6906d6105a6205a5205a4a05a3a0596d0596a07966059650595a069560594a 15 32767 6 63 11 2047 20 1048575
def cc_40_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xbad17502d655ac0af1b379e642c3658507031e001bdc96362c601861a8234f828d48bb8140d27824a1494010490c521704203840006080a080248001 0x7e790be7107d720bc6e06c6a06c6607c6207c5d07b4dbf34505a6a0797e0597a07976059720595dab15c0794e0594d0794c0594a059490594807946059450d9440594205941059400593aa41360592d0384d0484903845048410381d04819038150481106c680bc6005a40bd14c05948a214405940a11340384c048400bd690bd6107c6a05b6a06b5abb23da22350595a059400383d0483903835048310be790be7107d7a0bc6e06c6a06c660bc6207c5d15b4dbc34505a6a05a500a97e0597a07976059720a94e0594d0a94c0594a05949059481594605945ba1440594205941059400593aa01360592d0384d0484903845048410381d048190381504811aa15c1394c059480d9440594006d6d0bd6906d650bd61b846915c6107b7607b6605a5a05a420a97e0597a07976059720a96e0596d0a96c0596a0596905968139660596513964059620596105960a914e059420592d0386d0486903865048610381d04819038150481105b40059400593005a5005a4005950a814c05948b61440594005b6c048380383405d6906c65b4369a8361059320386d04869038650486107d7e06d7d06d7c07d7906d7507d720bd710bd7007c79b547107b7e07b6e05a7205a7005a5a05a420797e0597db317c0597a05979059780797605975079740597205971059700796e0596a0796605962a714e05942059358d1340592d0787e0387d0387c04879038750787204871048700381d048190381504811b135c05b4c0ea3415c7e07c7a07c7615c720bc6e06c6a06c660bc620bb6e05a6a0d97e0597a0797605972b014e0594d9314c0594a05949059481494605945149440594205941059400592d0384d0484903845048410381d0481903815048110386c05d6906c6d0bc6906c650bc610db690db610aa6e0aa5e059320986e0386d0386c0486903865ae062048610486005d6f05d6e05d6d07c6b0bc6906c670ac630ac6106c5706c5507b6b0ab630ab5b0db590ab530ab5106b4b0bb430aa6f07a670aa5f0aa5d0aa57ad2550ba4f06a470da3f059320386f0486b03867048630385f0385d0485b04859038570385504853048510384f0484b03847048430383f048330482b0382707d690bd6107c6e0ec6d07c6507c620bb5e07b5207b4d05b4a05b4605b4505b4405b44aa4680ab6c13b680eb640ab6006d7c0bd700eb7c07b7807b74a8370059700387c0487006d6f0bd6b06d670bd63ab46a0bc520eb6f0ab6e0eb6b07b6a0eb6707b660eb630ab6205b4da926fa72670ba5f06a570ea3f9323d0ea370ea350386f0486b03867048630385f0485b03857048530383f0383d0483b04839038370383504833048310482b0382705a3007b780ab7007b4c0db480db4407b40a524407b40059300383c0483005a300483007b780ab70913500ab4ca3348a23440ab40a12440595004860 15 32767 6 63 11 2047 20 1048575
def cc_40_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xc102e48b806cc5b302c81a926a40a8068869c1a6c18c3e1c58701f0b7c01d867601d417501d407501cc27205c417101c406530e2d05cc005 0xdc3780ab7007b64de26404868038640983ccb030d7264dc47c07c740aa4c0984cca040c9020da5700ab7c07b68d6360d927c0387c048700983cc7030d726c0ac7cd647407a4c059280984cc6040d035016a4404848038440883cc5030038340ab6e07b6a07b660ab6206b5ed034d16a360383dd303a048390483808836038350383404831d045cce35c05a380884cc404006c520aa6e07a6a07a660aa6206a56d024d0382d04829038250482106b5a06b56ce24105a310882ec3022cc054c926cc806c0592808834cb36eca36ac7366c6362c534ec434206a56c324e05a3e0383e0383d0383c06d6f06d6b06d6706d63e246bdf46306c5b06c53dd36f0ab6edb36b07b6ad836707b66d53630ab62d434fd234ed1343cf34206a56cd24e05a3e0386f0486b03867048630385f0485b03857048530384f048430383f0983e0383d0383c0483b04839038370383504833c2032048310483006d6f06d6b06d6706d63fb46bf646306c5b06c53f436fee36706b5f06b57eb34f05a520596fe816e0596b0596a059670796605963059620594fe314e05943059420593b0593a05937c11360592d0386f0486b03867048630385f0485b03857048530384f048430483b038370381f0381d0481b04819038170381504813048111394c059480d94405940a5134 14 16383 6 63 11 2047 20 1048575
def cc_40_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xede3a7d34235deabb816d2ada059489cd9331a17441078200fd1dfa03d096260c4017e2a6a5461c7f348dc90842082410070483e9048c09000e10007 0x56b781f5ac0face0ad6303e3582b18e468b71f4538e9af82ed7a366b606b5a8c1ab81ad5a286a60bb52899a7c44d3a206870d3420553742895a1049c05a3e02cb5016508070de0486b01c3381218c070be0485b01c2b81214c0709e0484301c1f8260f80707a0383c0241d8120e40706e0383502419bfc0c8090620483001c1282b5bc0fad607d67056b181f1ac158c74845ba122982adbc0f6cf3b35f9b1abcb4d3c0b4d405a4202cafcac5780b2b60595a02cab81a5580b2a60595202ca7c905380b2860594202c9d8164e80b26efe13602c9680e1bc090d6038670243180e17c090b6038570242980e13c090860483b01c1b80e07c0703a0481b0240c80e05c0702a04813024088365f00f2e81394c02ca40365100b28006e790373881f5c80d8dc06c6a0363301b1880f8ba07b4d7e1a28169880f2fc0597d06cbe0165e80f2ec0597503cba0165c80f29c0594d03ca60165280b2920594803ca30165141b2880594202ca08165000b274e213602c9680e13409092038450242080e07409032038150240881b1a0178c00a97c03cba3e85300b290e014402ca000e1300908005b6a035a93e08f5c046a0383d0241c80e0d40906206e790373881f5e80d8dc06c6a0363301b1880f8ba15b4d7c9a28169880b49405a48054bf0165f4152f80597a03cbb0165d40f2e805972054a7016534152980594a02ca48165202b28c059457b8a20165080b2820594002c9d37c4d80b25a0384d0242480e114090820381d0240c80e054090220a97c03cba04e5300b2900d94402ca001b5b40dad206d65036b0bd51a42b8c207b7603db3016948152fc0597d054be0165e80f2ec0597503cba0165c8152dc0596d054b60165a80b2d20596809cb3016594272c80596202cb0816581ce29c0594202c9680e1b4090d2038650243080e0740903203815024088165a80f2cc0b95602caa83a5380b2840592d06cbe01e5d1cc2b8e514c02ca43c85100b28005d6903634bc0da5ca6c20594201c368121a4070ca04861036bf01b5f40daf806d79036ba81f5c80dae2f357003e3cbc51c40f6fc07b6e02d2901e5f80b2faef17c02cbd0165e40b2f00797602cba81e5d00b2e40597102cb801e5b80b2daea16c02cb501e5980b2ca0796402cb13905380b2840592d03c3f00e1f4070f80487901c3a81e1c8090e20487001c0e8120640702a04811769ae016d302d4680483801c1a0571f80f8f407c760ae3901b1b80d8d406c660363101adb80b4c40d97e02cbd01e5d80b2e4ec14e02ca6b485300b2940594902ca40525180b28a1494402ca10165040b280059356689a0164b40709a0484901c228121040703a0481901c0a8120440fadc0ad6d0363681b1940f6d20db6103d3701e1b8090d20786202430812180150b40985602eb481b1b40d8d206c6503630836da41b6c20aa6e0552f00e1b4090d203865024308175bc0badc05d6d0363781b1b40d8d606c670363281b16c0d8b207b6b06db482ad8c156c20ab5b06dac82ad4c156a206b4b035a182a9bc154da07a677513282a97c154ba0aa577492a81a93c0d48e0da3f01c378121ac090d20386702431812184070be0385d0242d82a168090b20485801c2b82a158070aa03854024298121440709e0484b01c2381210c0707e048330241580e09c156d813b6809db202ad800b68806d7c076b83991c02d6f807b7803dba394dc0070f804870036b781b5ac0dace06d630362d05adbc156dc16b6b03db505ad9c0f6cc16b63055b1016d35ce4dee42670352f81a95c2d47ed223d0b51b85a8d40b2a40386f0243580e19c090c60385f0242d80e15c090a60383f01c1e8120ec090720383701c1a8120cc090620482b01c1381ed301b6900db4403da000e0f0090600383c0241802ad31c2690e0344055a00165200707804830 15 32767 6 63 11 2047 21 2097151
def cc_40_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x8d0c2a2102fa77923c81b96dc06e0360994ebe65e0a7bd28a9214901f2cf0474223b918059a2c015089884822401200808400010 0x174811c36805db001ad523c4a80485801c2a0260f20c061162548e23601b1900d6c80ba4c02d1c0261301908006b588b9a80260f01906007e788d23002edb00d6b1153508c936016580070d80486004c1e0320c22e8a11625c05e36455192166c806a4c02d1a0261320a0810e35006d22012120070880883c8201800e0d00f6cc0bb5e035ad01ad58176a50e34d06d1b00e0f624074048390241c0220d80706a0383402418c39172126b805a380442640c1000d4890f4520553702e9780d4b406a5605d294389340705a0482901c12812084174a00594004c1e4080c00dadc06d69056b101b5840d6b30c3510352f0169640b4a405a5102d2801a9380d49206a428592082e9000b2d40595202c9900e174070aa0982e8081102adb8156c406b5a035ab02e978174a50924102d188165a80707a038350441740008a0e0890235402d1a0220d00b4a102240831af032d68196ad05352821a740cd08154dd01256801270168f80b2d40594201c1f00e0f40707804825 13 8191 5 31 11 2047 21 2097151
def cc_40_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xa11542027a2c4ea88850922120400969dad1099a23340638cc7018a13140600a9b951a7177029165104a2012872500431c354844908800d10141800a 0x3e3501716a506933f3410352b4c48f80709a0484901c22812104172b8059589e8aa016540070a80ad7e03ebd01f5d815ae5414599922881ad980d6ad3034e02d3d016908172dc0596a034b3016588172bc0595d05cae0165680b2b205958a00ab0165567c2a80595202ca88165424e29c0594202c9680e176780b4048590242c026158070aa038540242880e074090320381502408816d000b26005a5002d200165424c298059489d0a20165021826806d6602e2cce0d664c6a20593201c2e812164070aa048510373f01f9e80dcf207e780373b02b9c80dce20ae7003634ce51840d6dc06b5e02d3d0169880b4c005a42034b70165b66e2d80596a02cb48165a00d2cc05965034b20165880b2c205960034af0165680d2ac05952928a70165080b26b0a13402c9680e1b4090d2038650243080e07409032038150240880e130090800b95c02cac4d45500b2a00b94c02ca44cc5100b2800484801c2202e572622a92f35c02da60368d009070038340563f01f1e80f8ec0ac729a23701b1a80d8cd32462981b70169e81d2dc0596a034b301658a5c29c0594d888a60165280b292059480a4a3016514292880594202ca08165000b26b0813402c9680e13409092038450242080e07409032038150240882b5b80dad406d66056b10171641d6b20eb5105d2f02e9380b2640385d0242c80e154090a206d6f056b701b59c15ac60ad620363381b1980b8be05c5e02e2e81edac156c606b5b05da982ed2c1d6920bb4305da082a9bc0f4ce0ba5f0352b82e93c1749a0ba479612283a8fc0b2640386f0243580e19c090c60385f0242d80e15c090a60384f01c2681212c090920384701c2281210c090820383f024198120ac0704e06c5e06e2e81b1540d8a40ab6e035b101ad340b69405b4602da2816d100b6892945805dae4a0d601b6a80bb500242c00e1500fcf00ae7006db601ada00d6c92636002cb002b5bc0fad607d67056b182b18a548b40db5f05daf036d6c0d6b40db57035ab036d4c176a405b4d0553781e99e4e4bf2525706d1fc448f41b46e0da3501c378121ac070ce0486301c2f81216c070ae0485301c1f80e0f4090760483901c1b80e0d409066048310241580e09c0d6d00bb60035a603ad201d68806b400352600e0f00906006b4002c9800e0f0090600ba5002d180120800d6d00bb60879a802ed32446912134405da04809100707804830 15 32767 6 63 11 2047 21 2097151
def cc_40_10 : Nat → List (Nat × Nat) := unpackCursorV4 0xe78ba6a74035e28ba096d1eda05a83a3c73a36177c1468202fd1da7533c46702c9154341b743680671883310401c9037086e00b4a04c804140020000 0x5cae016562be2a80595001c2a01f5f80faf407d7603eb9585166b28a206b66035ab560d380b4e40b96e02cb501a5980b2c40b95e02cae82e5700b2b40595902cac5805580b2aa1595402ca90165440b2a15314e02ca10164b4070bb5e05a0242c812160130ac0385501c2a0121440703a0481901c0a8120440b4915215c0aca60165202b288059400373f01f9e80dcf207e780373b01f9c80dce215e7003634d711840d6dc06b5e02d3901a5b80b2da1596c02cb50165a40b2d00696602cb281a5900b2c40596102cb001a5780b2b40695602ca95445380b2840592d01c368121a4070ca0486101c0e8120640702a0481105cae0165602b2a80595002d2402e5300b2901594402ca00121200708813b5c02da605a8d00f8fc07c7a03e3b01f1cab48dc06c6a0363356518ab06dc05a72074b70165a80d2cc05962ab8a70165342b2980594a02ca48165202928c059450a4a20165080b2820594002c9680e13409092038450242080e07409032038150240881b5b80fad407d66036b10171641d6b20eb5105d2f02e938070ba0485901c2a8121440dade07d6b03eb501b59c0facc06c6f0363701717c0b8bc05c5d03db581ed8c0d6b60bb5305da583ad24176860bb4103d3781e99c174be06a5705d2782e9341748f552450751f80e1bc090d6038670243180e17c090b6038570242980e13c0709a0484b0242480e11c0708a048430242080e0fc090660482b01c1382ed702b6b016b5405da8012160070a805b4403f3c0379c2a48c016b6c035b401ad902b6c007d6f03eb581f59c0fac607c6a0adaf82ed782b6b606b5a0adab81ad582b6a60bb5202da681e9bc0f4cf5325fa892b8568fc2b47a15a370b51a8165880b2540386f0243580e19c090c60385f0242d80e15c090a60383f01c1e8120ec090720383701c1a8120cc090620482b01c1381ad301d6900eb44035a00168c01769813b480ada202ed029c48807d6f03eb581f59c0fac607c6b03e31d3d16e9a8a613b5f05daf04ed6c0d6b413b57035ab04ed4c176a413b4f0ada704ed0c2768407a6602d1f00e1bc090d6038670243180e17c090b6038570242980e13c090860383f01c1e8120ec090720383701c1a8120cc0906207d6f03eb581f59c0fac607c6b03e31d9516ec48a607b6f03db3d74d7eb66af5634f02d310168e80b2bf5415e02cad8165680b2ae0695602ca98165480b29f5014e02ca18165080b2760593a02c9bd304d80b25a0386f0243580e19c090c60385f0242d80e15c090a60384f024218120ec0706e0381f01c0e81206c090320381701c0a81204c090234a14c02ca403a5100b2800384c0242001b588158fc06c7a03e3b01b1c80d8ba06b4da49a28169e80d2dc0596a034b30165880b2bb2a15c034a70165340d2980594a02ca48165200d28c05945074a20165080b2820594002c9d48c4d80b25a0384d0242480e114090820381d0240c80e0540902207c78056380169028e29805948908a20165024026806b5c02da601b1680f6d405b5aa211ec848d40b2d40383d0241c80e0d40906206d6a0563f01f1e80f8ec0ac720362ecc8d368c68a05a7a05cb70165a80d2cc0596205ca7016534172980594a02ca48165228a28c05945a18a20165080b2820594002c9d47c4d80b25a0384d0242480e114090820381d0240c80e054090232915c940a60165201d2880594002e2e01a9127a09009844 15 32767 6 63 11 2047 21 2097151
def cc_40_11 : Nat → List (Nat × Nat) := unpackCursorV4 0xc885833af255d83b9876b22874452f8a010d1e102b5b26a82ce1d9423280620cbe19722ae015c00b11d23018af2e0c37945e40b8103ce03100018000 0x1ed900d6880bc6c036325f91701b6f807b74035a602ad201b68807b40bd11a012120070880483801c1a02f1b00d8c80ab7c03dba01ad300f69013b44055a00120e0070680bc5e0762e853154176b80aa380241c5e8da8296cc0bb5e075ae82ed70296aa04839024188531fafa8f414c76be23902f1b81d8da0bc6c0363501b198298ca14c6406dbf01ede80f6ec0db72075b703adb41d6bb7b35c035a701ad340d6980ea36bc91a052526da2820593902c9880e13409092038450242080e0f41d074048390241c0220d80706a038340241881b5bc17ad606d6705eb182edbc156dc0bb6b03db502ed9c0f6cc0bb63055b102ed7c176bc0bb5d05da682e8dab22d732163034ad82e54c172760593905c998164c4070de0486b01c3381218c070be0485b01c2b81214c0707e0383d0241d82e0e8090720483801c1b8220d80706a03834024198120c40703e0481305d3601a990174b806a54bb1260120a0070480ba6c0353202e9700d4a813a4c036b782f5ac0dace0bd630763782f1ac1d8ce0bc63075a50529beea4d614a67ba13182e97c1d4ba06a5b0352d01a95c0d4ac14a550352581a92ab02d730163034ad82e54c1d2960b9430a495db048c070de0486b01c3381218c070be0485b01c2b81214c0709e0484b0742500e11c1108c0484301c178120ac0704e0482301c0f81204c0f2c97245c02d240365f00f2e8059480242400e1100b4900a97c03cba016522de8b805a48074b601a5900b2916b13402d2402e5b00d2c8059480242400e110172d80696405cae01a5502f29805a38b59ad052d58174bc0ba5202c9d0220bad404414c7eb8a3d0531dae08e414c6eb723505319ada8c56c36e02d250169201b2fc0597a03cbb0165c81d2dc0596a034b30165880b2ba1795c02c9ada44d00b25a0384d0242480e114090820381d0240c80e054090239c56fccab5e4d59f1aac614b6fc61b7628dac0f6d414b6703db361cd8f0c6c414b5fc29af5fcd6c0d6b414b57035ab5e0d4eee6a57325eab0b5cb458dd62b6af1530a49d8164e6d02660593101c378121ac070ce0486301c2f81216c070ae0485301c1f80e0f4090760483901c1b80e0d4090660483101c0f81204c2b29805948074a20165000709804840036b101f1f80d8f407c760363901b1740d69b6634502d390168e80d2dc0596a034b30165880d29c0594d034a60165280b29205948034a30165141d2880594202ca08165000b2754f13602c9680e13409092038450242080e07409032038150240881f1e0158e005a480aca60165202b28805940a709a016d300dad407c7e03e3d01f1d80f8e406c5dac9a6d90d140b4e405a4a02d240168e8172dc0596a034b30165881729c0594d05ca60165280b29205948b18a30165142b2880594202ca08165000b2754d13602c9680e13409092038450242080e0740903203815024088565300b2900e94402ca0017172be09009844 15 32767 6 63 11 2047 21 2097151
def cc_40_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x8a8088887deb7d0378d16ea96e806dc36dc069d067c85c2f5a475a4059835980555149af3e6d3c0931e931c02f8926651bab11690eca0e810c0a0bc1094a0025 0x33e6a40aa6e0553101a9480d49406a460442f6781481bcfc06e7d03ebd01b5e40daec06d71036b301b594156fc07b7a03dbb02adc80d6dc06b6d035b601adab466d3a0368035b3052d94296c806b62035b081ad800d6bc06b5a035ab01ad480d4cd9d2640352f0165a40b2c20593902c9880e1b4090d2038650243080e0f409072038350241884ed700f6980ea3403db701ada80d6cc07b62055af01ad680d6ac0ab5209da682e9781d46c0593902c9880e0f409072038350241881f9f80dcfa06e7503f3901b5d80daea0dd6e03eb681edf80f6f407b7603db902edb80d6d406b6605db101ed780f6ba07b5c03dad66cd67346b007b560a5aa852d500f6a407b5103da802e9b80b2b20595102c9c8164c4070ba0485901c2a8121440707a0483901c1a8120c4276b806b4ccc11a01edb80f6d407b6603db101ad780d6b406b56035a904ed372c46c0593902c9880e0f409072038350241884eda80d4d407a5a03d2b01a9280d48c0592902c9081b9f80fcfa06d7e036be81b5b80dad207d62036b081adf8296fa14b7c035bd01ade40d6f006b76035ba81add00d6e597371ca9b801edb80f6d407b6603db101ad780d6b406b56035a901a9fb284f806a5e02cbc8165c40b272059310343f00e1f4070f80487901c3a81a1c8090e20487001c1e8120e40706a048310563702b188178bc0bc52055a682e9781b46d9135c055a60368d00d6dc07b6a03db301ad880f6bc06b5a035ab01ed4b1e69a0ba5e06d1b0164e40b2620383d0241c80e0d40906206e7d03f3d01f9d80dcea06d7e036be81f5b80fada0dc5ac922c02adf80f6f407b76055b902edb80d6d406b6605db102ad781b6ba0ab5c06dad640d671c6b00db560a5aa852d50156a40db51055a802e9b80b2b20595102c9c8164c4070ba0d85a0242c812160110ac0385501c2a0121440707a0483901c1a8120c415ade0ad6e056b682b1bc0f8d607c670563182b17c0d8ba0ac5b05e2c82b15c0d8aa0ac530562881e5ac152c60a95b02cac82a54c0b2a21594b0aca180e1bc090d6038670243180e17c070ba0485b0542d012164090b0038570442b00e154070a8048530242880e13c09096038470242180e07c0902614c6d03e3301f1940f8c814c5ebf2295d8978292937214103e3f0531f4298f807c7603e3a81f1d00f8e414c6ec223505319afa8c407b7603dba83adb80d6d406b6603db101ed77166b80db4e03da682ad32ea4dc07a3606d1a052526e22820593902c9880e13409092038450242080e0f40f074048390241c01e0d80706a038340241882adb81b6da14b65c19ad052d58174bc0ba5204417624088158fc0dc7d0563e01f1e80f8ec14c750a63a0531bb048d414c66be231036df81b6fa0eb6e035b501ad981b6c40db5d09dae01ed380f69a07b4cba1370368db1046814949b80a08164e40b2620384d0242480e114090820383d0241c80e0d4090620ad6f03eb581f59c15ac60ab6f055b702adb4156be0bb5e055ad81ad68156ae06b56055a982ad481569a0aa3603cb582a58c2b2b6159530549d8164e4152660593101c378121ac070ce0486301c2f81216c070ae0485301c1f80e0f4090760483901c1b80e0d4090660483101c0f81204c0dade0bd6b036b382f58c178de0ac6e05e3581f1a8178ce07c6605e3182b188178be0bc5e05e2ed685ae682c60695b05ca982e52c0b2920b94302ca080e1bc090d6038670243180e17c090b6038570242980e13c0709a0484b0242480e11c0708a048430242080e07c090260dc7c03e3a03adb00d6c806b4c03da4036d100d6800483801c1a02a8e0158f807c74c0a2e03adb00d6c806b4c055a403ad100d68183234035a20531bb028c414c5d0362b01b1540d4bc14949b78a08121240908214c7ec223d0531db048e406c6e0a6368531b00d8cc06c650363201b1881b6fc06b7a03dbb01adc80d6cc06b65035aee00d701d69c06b4d05da601a9b80d46c0ea340a4a4db85040b2720593101c268121240708a0484101c1e8120e40706a04831 16 65535 6 63 11 2047 21 2097151
def cc_40_13 : Nat → List (Nat × Nat) := unpackCursorV4 0xf907a50b6ced80b6027d79f026859906640951254095023c68f023818e02380852608382020418101e484db06b31a0054515005010050000 0x154a006d6e036b482b5880dac206b520352f01a9640d4a40aa510552801a9380d49206a42df9208220bb7c04406e7e03f3d01b9e40fcf006e760573901b9c415ce006d79036b881f1e80d8c5b9460035b7714db7886d806b6a035b481ada00d6cc06b65035b201ad88156c20ab60035af70cd77846b806b5a035ab01ad540d6a806b5203da681a9b80d4bdc0236de91a0165a40b2c26a14102c9c8164c4070da0486901c328121840707a0483901c1a8120c40dad206d61dda2e81b1680d8ac06c55dc1b681eda80f6cdb3365035a681ed280d68c06b45035a201a97b7448c0594902ca08164e40b2620484902420ee11c00d8c1b6378055b801ed93606c9b647c03e3a6d4d701569806c70d9a3002adf00f6d1af360d90b86c0db0158f9af474075b66b8d700f6980ea34d689c0120e00706805a5002d200165400b27005a48d50be6a45d01d2d9a815c0749a0120600702806d6f036b581b59c0dac7b94620362d6dcdbc156ddb436b03db56c4d9c0f6cdac363055b101ad340d4bd5c16b9c8b181a56c0d2a669141d589d8164e74e2660593101c378121ac070ce0486301c2f81216c070ae048530242080e0fc0707a0483b0241c80e0dc0706a048330241880e07c0902606d6f036b701b5ac0fad406d67036b301b58f8eac406c6f0363581b19c0d8c7c636bde1b181ad6c0d6b206b53d31a881ad2c0d68606a5e0352756c5ae6c2c60695b02cac81a54c0b2a20694b034a19984cc070de0486b01c3381218c070be0385d0242d812164070ae03855024298121440709e0484b01c2381210c0707e0483301c0f81204f486b806b4c06d1a0120e00706803834055b701eda80f6cc0ab62035af01ad680d6ac06b52d11a68368d80b2720593101c1ee840e809072048380441b00e0d40706804831 14 16383 6 63 11 2047 21 2097151
def cc_40_14 : Nat → List (Nat × Nat) := unpackCursorV4 0xbb80b694aab09cf7936687af7e26717366ea660365c1630b576f4d684c444b444b40498741df3d9139cf2ead20b8127907ea074205090386020601c100070000 0xf8dc07c6903e3102f184178c007b6203d3701e9a40f4c40ba610553001e9780f4b207a52ef12881e1b8090d207862024308121800fafc06d7d036be01f5e40daea07d7205eb882f5c00f8e5e34700362d01edfbc46fbe137c03dbd01ede40f6f007b7603dba81edd00f6e40bb7105db801edb80f6d407b6603db101ad340f4fc07a6eef91b7748d00b2f20597102c9c8164c40f0fc0387d01c3e0121e4070ea07872024388121c00707a0483901c1a8120c40f8de06c6d03e3581f1a40f8ce06c6503e31fd91840f8be07c5b03e2b81f14c0f6d607b6903db1f9cd840f6b607b53f31a5f70d0c0f4dc07a5e03cb58165a40f2c60596103cad81e54ddc296b21433789980e1bc0f0dc0386d01c360121ac090d20386701c3281218c0f0c4048610243000e17c090b6038570242980e13c09096038470242180e0fc090660381f0240982f9f817cfa0bd7905eb881b5940f8f40bc7905e3c01f1d8158e40bc710563801f1980f8ca07c64075b483ad841d6920bb410352b01a9181d47c0596902cb0f40524172820386d0243480e194090c20384d05c25012127960900984601c22826110090820ad6f056b702b5b40f8d60bc690363382b18c158c206c570362a81edac156c60ab5b06dac82ad4c156a206b4b05da181e5ac152c60a95b02cac82a54c0b2a20694b05ca18364cc070de0486b01c3381218c070be0385d0242d812164070ae03855024298121440709e0484b01c2381210c0707e0483301c0f81204c0fcfc07e7d036be81f5a417ac207c7e05e3e82b1f00f8dc07c6a03e3481f1a00f8c40bc6105e3001ede41d6e20eb4905da081a9580d48c0ea3e02cbc8165c79e2920b94101c3e8121e4070ea0487101c2682e12809093ca04804c2300e1141308804841036b781f5ac0dace0ac6f0563702b1b4158be0bc5e0562e81edac156c606b5b05da982ad2c1b6920ab43055a082a9180f2d60a963034ad82e54c1529605949054a18165041b2660386f0243580e19c090c60385f0242d80e15c090a60384f01c2681212c15094048490242400e11c1308c0384501c2201210c090820383f0241980e07c0902607e7905f3881f5f80faf407d7603eb901f1c8176dc06b6a035b301ed88176bc07b5d05dae01ed680f6b207b58075ab01ed541b6a807b5203da881ed400f69a06a660352b0165640b2a20593902c9880e1741d0b4048590242c022158070aa038540242880e0f409072038350241882edb0156b00ab5005db601f5a8178d20bc610362e81a9180b2b20595101c2e812164070aa0485105f3c82f9c415afc07d7a03ebb02b5c80f8f40bb6e075b682edb00d6d406b66ea9b281ad90176c40bb5e075ae82ed701d6b40ab59055ac03ad5ba86abd335405da902ad44156a007b4d0353301a9580b2b205951370a08164e40b2620385d0742d012164090b00885601c2a80e150090a20383d0241c80e0d40906206d6f05eb581b59c17ac60bc52075b782adb81d6d607b6a075b381ed981d6c60ab6205da6d845ae822c60695b05ca983a4ec0b2720e93302c9880e1bc090d6038670243180e17c090b6038570242980e0fc0707a0483b0241c80e0dc0706a048330241880e07c0902605a68054be01e5d00b2d005a7002cb87385b00f2c80ac7ce723a01f1a0090d00386409424026113a0afc0bd7ae7abb02f5c81d8b20bc51035b301ad581d69c05a6202d290169439a2fc0597a03cbb0165c81d29c0594202c9680e174170b4048590942c026158070aa098540242880e07409032038150240882f5b817ada0bc6905e3081b1541d6b20eb510352303a8f80b2b20595102436812194070ba048590242a8121440fadc07d6d0363681f164178a207b69075b08165a40b2c20486d0243480e194090c20485d0242a81b5bc17ad606d6705eb182f1bf968dc0bc6b05e3502f19f948cc0bc6305e3103adac1d6c606b5b05da982ed2c1d6920bb4305da081a9580d48c0ea3eaf0b5cf058c0d2b60b95305ca584a524172860b941074998121bc090d6048670243180e15c0708e0384601c2280e1100907e048330240f81204c0dade0bd6b036b382f58fb48dfd946e05e3581f1abb08ce07c6605e31f5d18bac6d7d2363035ad82ed4c1d697d134905da1ddcd040d4ac06a46b991f5745ae762c60695b05ca9f3052c0b2920b94302ca09b04cc070de0486b01c3381218c070be0485b01c2b81214c0709e0384d02425f24128090920484801c238261180708a03844024218121040707e0483301c0f81204c0dade06d6d036b581b59c0daca06c6f0363701b1b40d8be06c5e03db5836da4156c60ab61035ad81ad4c156960db49055a182ad040f2d615969054b182a5840d2b606953054a5816524152860594106c9980e1bc090d60486901c3381218c090c20385f0242d80e15c090a60384f01c2681212c15094048490242400e11c1308c0384501c2201210c090820383f0241980e07c0902606e7e03f3d01b9e40fcf006e7603f3901b9c41bce006d79036b881f1c80d6dc07b6d06db601ada80d6d206b68035b301ad940d6c806b6203db081ed800d6bc06b5a035ab01ad480f69a06a6e0352f0165a40b2c20593902c9880e1b4090d2038650243080e0f409072038350241881f1400d6a806c660362f0165240b2826b13101c268121240708a04841057386ed1800d6d00ab60035aa7048d00dadc0ad620362f02f1740d4bc0ba4e0552802b9c3748c00ab600353402a983824b806a54 16 65535 6 63 11 2047 21 2097151
def cc_40_15 : Nat → List (Nat × Nat) := unpackCursorV4 0xe6b79aced77d0e88fc91e05f5231f34a668f151c0a38045088a01140200a40007f04fe01e853b867700e8192aa0f581e003c0040e070406200c00006 0x1b5aa0447e02f1ea0347602f1c806c5d02ed36023450169e805a6201690805a400365f80597a01e5d8059720164e9ff1360164b40384d012124038450121040381d0120640381501204406d6f02f5ac06d6702f58c06c5a87cdbe1c36e02edac07b6a868d9c07b6602ed8e1736201ad35f826f77099c0ba5f01a95c0ba3f5dc8f6142378148d56216b50858c0695b02e54dfe13b0164e40b9330164c40c12b00e1bc0486b00e19c0486300e17c0485b00e15c0485300e0fc0383d0120ec0483900e0dc038350120cc048310120ac0382700e07c0481301b5bc0ad6e01b59c0ad6302b58806c6701b1980ac5f02b1780ac5d01edac0ab6301ad6c0bb5302ed2c0eb4902ed0c0bb4101e5ac0a96301a56c0b95302e52c0594902e50c0594103a4cc0386f0121ac0386701218c0385f01216c0385701214c0384f00e1340484b0121240384700e114048430121040383f0120cc0381f01204c0ad6f01f5ac07d6702b58c0ac62036d7c0bb5e036d6c06b5a036d5c06b56036d4c0bb5202ad340796b02a58cf515b2e054c0d93b0164e40d9330164c40386f0121ac0386701218c0385f01216c0385701214c0383f00e0f40483b0120e40383700e0d4048330120c40381f01204c06d6d01b5a406d6501b58406c5202adf806b7a01edd806b7202adb806b6d02adb006b6a01ada406b68036d9806b6503ad9006b6201ad8406b6001ad3407a7601e99805969016584059390164c40386d0121a4038650121840383d0120e4038350120c40ab7c01b5b40bd6901b5940bd6101b1680ab7e01ede807b7602adc80ab6e036db40ab6c036da80bb6902eda00db667e4d9413b6402ad880bb6102ad8006b4d01e9d807a660165a4059610164e40593100e1b40486900e1940486100e0f40483900e0d40483102b1bc07c6b01f19c0ac6302b17c06c5d04f16dfc45904f15c06c5502b14dd745101edac0ab63036d6dfb35902ad4d863517e8d2df834301e99807a5601e5ac0a96304e56c0595902a54c059513d052cb71431c84cc0386f0121ac0386701218c0385f00e1740485b0121640385700e154048530121440384f01212c0384701210c0383f0120cc0381f01204c06d6f01f5ac07d6a01b59c07d6601b1bc06c6e01f17c07c5e01f17407b6b01ed8c06b5b03ad640bb5302ed440bb4b03ad240bb4302ed040796b01e58c0695b3cc5640b95302e5440b94b0165240b9430165040e93300e1bc0486b00e19c0486300e17c0485b00e15c0485300e13c0384d01212c0484900e11c0384501210c0484100e0fc0483300e07c0481379518007c507d0da00bb6001ad51ee3547d11b006c647ccd700bb4c01f9e007c607911400bb6c01ad61ed3507c49b1f016000e1b0048607b8d700bc6c7b5191ec35c01ad300da3401694005a4001654005a480365f1e915c01f5bc07d6b01f59c07d6301f1a9e34527d4d7c0bb5e7c8d6c06b5a7bcd5c06b567acd4c0bb5201ed340796b01e58cf115b2d454c711417a84ec059397a04cc0593100e1bc0486b00e19c0486300e17c0485b00e15c0485300e0fc0383d0120ec0483900e0dc038350120cc0483100e07c0481301b5f806d7d01b5f006d7901b5d407d7201b5c40ed7001b14807b7e01adf40eb7c01ade806b7901ade007b7601add407b7401adc806b7101adc007b6e01ada807b6601ad8806b4d01e9f807a6e0165e4059710164e40593101e1f80387d00e1f00487900e1d4078720121c40487000e0f40483900e0d40483179517406c5a01b159e445501eda807b6601ad3407b4a01ed1806b4501ad11e02360164e40593101b18007b6401f5b806c550165640595100e1740485900e1540485102f5c1e047002edc007a7802e9c004870 15 32767 6 63 11 2047 22 4194303
def cc_40_16 : Nat → List (Nat × Nat) := unpackCursorV4 0xa6033b46197c28274c2d94178ea0f93f887b10bee17422c885804a6294c0288448249001200230446007c40f021d8211a81a20244038407000a10005 0x385c02b5b806c5d02f16406c5502f1440aa6e02a978059590165440885e00e1740385c01216403855878148048510121400ad6f02b5b80ad6d01f1ac0bc6901b19c0ac6302b18406c5701b1540aa6f01e99c0aa5f02a9740aa578749540ba4f01a91c0796b02a58c0a95b0165640a9530165440694b02e50c1592b00e1bc0486b00e19c0486300e17c0385d01216c0485900e15c0385501214c0485100e13c0484b00e11c048430120ac0382700e07c0481302adf20f23401f9f807e7d01b5f407d6902f58406c5a01edf80bb7d02adf007b6e01eda807b6901eda007b6202ed840bb6001ad361b27d01e9d40ba3d8548d4059790165c60313902e4c40387d0121e4038750121c40383d0120e4038350120c40ab6e02ed780aa6e01e9980ba5e01a9580aa3e0164e4059310564a40383d0120e4038350120c40482900e09406c5f01f16c06c5702a97c07a5702a94c0ba4f01a91c0ba4301e56c0a95301a52c0b9430564ac1592300e17c0485b00e15c0485300e13c0484b00e11c0484300e0bc0482b00e09c0482300e07c0481301b5bc07d6b01b59c0ab6f02adb80ab6d02ad7c0bb5e02ad740ab4d02a9bc07a6702e97c06a5702a8fc0aa3d02a8e80aa3702a8da192358608d00796b02a58c0695b02e54c0a93b02a4e8059390164e00a93602a4cc059310564ac0386f0121ac0386701218c0385f01216c0385701214c0383f00e0f40483b02a0e8048390120e0038370220d80383500e0d0048330120c40482b00e09c0381f01204c07b7802adc007b6484c9900ab7c01eda00db6083c9f006d6a0371f807c7a01f1d80dc72858df80bb7a854dd80bb7201ad75df27602e9b80ba4e02e8f80ba3c016524059418084e40b93100e1340484900e1140484100e0f40483900e0d4048310120a40bc500121421137802adc007b6484c9920c3648451f007c7402ad3007a7401e8f007b6882cd8006d7c01b1c00ab7c01eda20a36083c9f20e17000e1f004870830db20b16002b1f20a47401ed31de27402e8d2091380120e0038340169020013401692006d6f02f5ac06d6702f58e1236f02adba1036b01edaa0d36701ed9a0836302ad89dd26602e9780ba3e5905ad4616301a56c0b95381c4ec059398184cc0593100e1bc0486b00e19c0486300e17c0485b00e15c0485300e0fc0383d0120ec0483900e0dc038350120cc048310120a40381f01204c05a6802a5f0079740165a005a700165c00d96c01e59005a408004d00ba500120800bb60804d420024400e0f004830 15 32767 6 63 11 2047 22 4194303
def cc_40_17 : Nat → List (Nat × Nat) := unpackCursorV4 0xd0db9f0b303e3c9c6856b8ad6058c8b1035b1eb6055c4a6174c029805282a18f3d1a741ce809c8338065863fed64ecbb39119972c14e628044238021 0x1f9e806e7901f9e006d7e01b5e40ad7201b5c40ad7001b5b806d6d01f1e806b6e02adb40bb6c01ad7806b5a01ad6406b5801ad480ab5102ad4007b4d8fc9b406a6575497406a5502a8f63b2350165a4059610565041593902a4c40686e00e1b40386c0121a40386501a188048610121800383d0120e4038350120c40384c01210006b6802ed8006b547049923825400e0f00483002edb006b5803ad423426c01a9500386c0121800383c0120c00aa3c00e1323d67902b9c407d7a03b1b806c6a01b1980ec628f0db80ab6a8ecd980ab6201ed740aa7e7009980aa4e02a8f80aa3c056544059490165041593902a4c40884e00e1340384c012124038458e8108048410121000383d0120e4038350120c63636802ed8006b548e09500485800e1500883c8a80c2313548d91b006c6402ed3006a6401a8f00884c03210006b588c0d400883c0320c007e7801f1800bb6c01ad622f3508d09b23316000e1b0048600220f00c8308c4d723015002f1b22f46401ad31bf26402a8d00884c8a410005a400564d00884c04a1000481800e05005a48022130128408ac1100aa348a8d780cb5a032d5a2935202a9b9be25602a8f81293904a4c40383e00e0f40383c02b5bc07d6b01f59c0ad638dcd7c0bb5e8d4d6c06b5a8c8d5c06b568b8d4c0bb5202a9b9bd25602a8f80796b02a58cf915b2f054e2d13b0164e62c1330164c40386f0121ac0386701218c0385f01216c0385701214c0383f0220f80383d00e0f00483b0120e40383700e0d4048338a00c8048310120c00381f01204c0ad6f01f5ae4556901f59c0ad6391158407c6a908d7e4035e02ad6c06b5a8f8d5c06b5602ad4e1735201ed340aa6f01e99dd225f6f095c0aa3f6188f63923789c8d40796b02a58cf615b2e454c731410564ec0593902a4cc0593103c4ac0386f0121ac0386701218c0385f01216c0385701214c0383f00e0f40483b0120e40383700e0d4048330120c40482b00e09c0381f01204c06d6e01b17406c5901b15406c5102a9b80aa5e01a938059590165440385d0121640385501214406d6f01b5b806d6d01b1bc06c6d01b1ac06c6701b19406c5b01b1640aa6f01e99c0aa5f02a9740aa5789495406a4f01a91c0796b02a58c0a95b0165640a9530165440694b01a50c1592b00e1bc0486b00e19c0486300e17c0385d01216c0a85a0121640485800e15c0885600e1540385401214c0485100e13c0484b00e11c048430120ac0382700e07c0481301b5bc06d6b01b59c06d6303adbc0ab6e03adac07b6a03ad9c07b6603ad8c0ab6201a95806a3e5985ad4916301a56c0695303a4ec0593903a4cc0593100e1bc0486b00e19c0486300e17c0485b00e15c0485300e0fc0883e00e0f40383c0120ec0483900e0dc038350120cc0e8320120c40483000e07c0481301b5bc06d6b01b59c06d6301b14806b6f890db806b6b01ada806b6701ed9806b6301ad8806b4d7e89bde626701a97c06a5701a8fc06a3d01a8de232355945ad4816301a56c0695301a4ec0593901a4cc059310384ac0386f0121ac0386701218c0385f01216c0385701214c0383f00e0f40483b0120e40383700e0d4048330120c40482b00e09c0381f01204c06b4401b5b00bd6088518007b6484c8d00386c0121800be7e02f9f40bd7902f5c406d6501b16807b7a02ede40bb7801edd80ab7202edc40ab7001ed9807b6501ed9006b4d0369b62026502e8f6162350165a4059618104e40b93100e1b40486900e1940486100e0f40483900e0d404831 15 32767 6 63 11 2047 22 4194303
def cc_40_18 : Nat → List (Nat × Nat) := unpackCursorV4 0xe441f22038d09adb2ca98dd10ab86149a5a4415200685174182a080ca6be4817063c741e319116156aa0d49579faa0c86a640030c2932a86b5c330510130663402620002 0x1694005a4001654005a480365f00797497457006d6f01b5ac06d6901b58c06d6101f1a806c5a01edac07b6a01ad6c06b5a01ad3407a6f01e99c06a5f01a95e6223f6548f66123797c8d40796b01e58c0695b01a54c7f1419784ec059399704cc059310644ac0386f0121ac0386701218c0385f01216c0385701214c0383f00e0f40483b0120e40383700e0d4048330120c40482b00e09c0381f01204c07d6f01f5b406c6f01b1b406c5f01b16c06c5304edac13b6904ed8d9536101ed6c07b5301ad2c06b4301a99807a5601a9199423e04e5ac0596904e58c0596101e56c0795301a52c069431f84cc1812900e1bc0386d0121ac0486900e19c0386501218c0486100e17c0485b00e15c0485300e13c0484b00e11c0484300e0fc0483300e07c0481301b5bc06d6e01f5b406c6f01b1b806c6d01b17c06c5e01b16c06c5901b14c07c5201b14406b6b01ada406b6396cd8407b5b01ed4c06b4b01ad0c06a6f9689b406a6701a99407a5f01e95c06a4f01a91d9323f01a5ac0596901a58c0596101e56c0795301a52c069431ec4cc1712b00e1bc0686e00e1b40386c0121ac0486900e19c0386501218c068620121840486000e17c0485b00e15c0485300e13c0484b00e11c0484300e0fc048330120ac0382700e07c0481301b5bc07d6b01b59c0ac6202f14806b6301ad8807b5301ed480ab4d02a9bc07a6702e97c06a576489340da3f6388f40da370368d40796b02a58c0695b02e54c0d93b0164e40d9330164c41612b00e1bc0486b00e19c0486300e17c0485b00e15c0485300e0fc0383d0120ec0483900e0dc038350120cc048310120ac0382700e07c0481301b9f407e7a01f9d806e7501b5f807d6e01b1f806c7d01f1b807c6d036de40ab71036d640db51036d240ab4102a9f80ba6e02a9780aa4e02a930059590165441594902a5040385d012164038550121440384d02a128048499401200984600e114098440121058f4500368d18f45802adb80bb5e63cd340ba5e1e8504059390164c40383d0120e4038350120c405a500564d005a5801b5bc07d6b01b59c06c6f01b1b807c5f01f17807b6b02ad8c06b5b02ed4e5634b638d2655343950d040aa6e02e9780aa4e01e5ac0a96301a56c0b95394c52c0594994850c059411e04cc0386f0121ac0386701218c0385f01216c0385701214c0384f00e1340484b0121240384700e114048430121040383f0120cc0381f01204c06c6e01f1780db49036d040aa6e02e9780aa4e0165240594100e1140482501b5bc06d6d01f5ac07d6a01b59c07d6601b59406c6f01b1b806c6d01f17c07c5e01f17407b6b036da40ab6302ad8406b5b02ed4c0ab4b036d240ab4302ad040aa6f01e99c0ba5f01a95c0aa4f02a9340aa479409140da3f01e5ac0a96301a56c0b95302a52c1294902a50c0a9410364cc1592b0121bc0486b00e19c0486301217c0485b00e15c0485300e11c0384600e114038440120fc048330120ac0482701207c0481301b5bc06d6d01f5ac07d6a01b59c07d6601b59403c6f00f1ac03c6700f18c03c5f00f16c03c5700f14c06b6f01adb806b6d01ed7c07b5e01ed7403b4f00ed3804b4d012d3007a6b0229a408a6302298406a5b02294c03a4b00e90c08a3b0228e408a330228c40996f01e59c0995f01a55c0394f00e51c0993f0264f4099370264d40892f01e1ac0a86301a16c0b85300e12c0384302a0ec1183902a0cc0a83102208c0981b01b5bc06d6d01f5ac07d6a01b59c07d6601b59406c6f01b1b806c6d01f17c07c5e01f17407b6b930da40ab63910d8406b5b02ed4c0db4b960d240ab4385cd040aa6f01e99c0ba5f01a95c0aa4f75c936572479449158d23f01e5ac0a96301a56c0b95305652c0594902a50c059411d44cc1512b00e1bc0486b00e19c0486300e17c0485b00e15c0485300e13c0384d01212e4f04a0121240484800e11e4e04600e1140384401210c0484100e0fc048330120ac0382700e07c0481301f5bc07d6e01f5b406b6b01ada806b6701ad9807b6301ed5c0db5601ed5407b4d02e9bc06a6702a97c0da5701e8fc07a3701a5ac0b96303656c0a95301e4ec079330504ac0386f0121ac0386701218c0385f01216c0d85a00e15c0885601214c0383f0120ec038370120cc0482b00e09c0381f01204c06c6e01f1a807c6601b18807c5e02e9780ba4e0165240594100e1340484900e1140484101b5bc07d6b01f5a806d6701f59806c6f01b1b807c5f01f17807c5d01e9bc07a6702e97c06a5702e93c0ba4d02e91e4b24501e5ac0796301a56c0b95302e52c0594902e50c0594104c4ac0386f0121ac0386701218c0385f01216c0385701214c0384f00e1340484b0121240384700e114048430121040482b00e09c0381f01204c07d6f01f5ac07d6701f58c0db5f02ed780db5b01ad680db5701ad580db5302ed4807a6601e8f80796b01e58cfc15b2fc54c0d93b0164e40d9330164c40386f0121ac0386701218c0385f01216c0385701214c0383f00e0f40483b0120e40383700e0d4048330120c40381f01204c07d6f01f5ac07d6901f59c07d6393158407c6201ed7e4a35e01ed6c06b5a01ed5c06b5601ed4c07b5201ed3407a6f01e99dd625f71895c07a3f01e8f407a379248d40796b01e58cfb15b2f854c0793b0164e4079330164c41212b00e1bc0486b00e19c0486300e17c0485b00e15c0485300e0fc0383d0120ec0483900e0dc038350120cc048310120ac0382700e07c0481302ad8807b4d0565040885e91c14807d6f02b5b807d6d01adac06b6a01ad9c06b6602ad8c07b5701ed5a4635501ed340ba6f01a99c07a5f01e95c0aa3f8f48dc0696b02e58c0795b01e54c741410564ec0a9330444ac0386f0121ac0386701218c0385f01216c0385701214c0383f0120ec038370120cc0482b00e09c0381f01204c07d6f01f5b807d6d02b1680ab6f02adb406b6b01ada806b6701ad980ab6501ad6c06b5a01ed340ba6f01a99c0aa5f02a95c0aa3f02a8dc0696b02e58c0a95b02a54c1594102a4ec0a9330564ac0386f0121ac0386701218c0385f01216c0a85a00e15c0885601214c0383f0120ec038370120cc0482b00e09c0381f01204c06d7802b5c013c5001ad523823402b9f80ae7202b9c40ae7001b5d80ad6e02b5b407c7a01ada80ab6902ada006b6602ad880ab6102ad8006b5601ad5406b5401ed340ea6d70c9940ea5d90c9540aa3d8f08d405959016544159410564e40a93100e1740485900e1540485100e0f40483900e0d40483102b1b806c6a01b1980ac6202b1780ba5e02e938059490165040384d0121240384501210406d6f02b5b806d6702b58c0ad6201b19c06c6602b17c0ac5e02b1740aa6f01e99c0ba5f02e97406a577089540ba4f02e9340ba479049140796b02a58c0695b02e54c0b94b0165240b9430165041012b00e1bc0486b00e19c0486300e17c0485b00e15c0485300e13c0384d01212c0484900e11c0384501210c048410120ac0382700e07c0481302edb234234 17 131071 7 127 11 2047 22 4194303
def cc_40_19 : Nat → List (Nat × Nat) := unpackCursorV4 0xd0b1cd86cb05c60ac306c183c101c100ba8da0b481be7b8c59c441b029b009c0088207030681000d 0x1b5ac06d6901b59c06d6301b5840ac6201b1680ab6302ad8806b5b01ad6806b4d02a9bc07a6701a97c06a570368fda023d0368dc0da3501e5ac0a96301a56c069530364ec059390364cc059310744ac0386f0121ac0386701218c0385f01216c0385701214c0383f00e0f40483b0120e40383700e0d4048330120c40482b00e09c0381f01204da24600368d00886c9b01800483800e0d1a246867c93006a3c0221b26b06001b1480ab6e01ad59a234d0164e40593100e0f40483900e0d404831016980159340261b012860012060038140169a00986c04a1800883402b5b806c559b0d666b35102a9b806a5e01a9199e23e04a5641295100e1780385d00e1700ad6f02b5b806c6b01b19c06c6301b15c06c5501edac0ab639c4d6da03599c0d4e6f35101ad2c06b4302a9b806a5e01a9199d23e01e5ac0a9639b856c059599b454c0595101a52c069432244cc0386f0121ac0386701218c0385f0261780385d00e1700485b0121640385700e154048539a8148048510121400384f01212c0384701210c0383f0120cc0381f01204c06d6f9995b806d6d01b1ac07c6a01b1a406c6701b19806c6301b18406c5701b15806c5501edac0ab6301ad6e7235901ad4c06b5101ad2c06b4302a9bc07a6701a97c06a5d01a95e6925501a93c06a476708fc0796b02a58c0695b016564069530165440694b01a50c861330704ac0386f0121ac0386701218c0385f00e1740485b0121640385700e154048530121440384f01212c0384701210c0383f0120cc0482b00e09c0381f01204c06c6e036d240db4101e9b806a5e02a938059490165040384d0121240384501210406d6f01b5b406d6b01f5a806d6701b59806d6501b1bc06c6e01b1b406c5f01b17807c5d01edac07b6901ed8c0ab6101ad6c06b5302ad2c0db4902ad0c0ab4101e9bc07a6701a97c06a5702a93c0aa4d02a91e672450368fc0796b01e58c0695b01a54c0a94b0165240a9430165040d9330564ac0386f0121ac0386701218c0385f01216c0385701214c0384f00e1340484b02a128048490121200384702a1180384500e110048430121040383f0120cc0482b00e09c0381f01204c06d6f01b59c07d6301f1a80bc5201adac06b6a02ed4c0ab5201ed3407a6f01e99c0ba5f01a95c0ea3f6688f40ea3703a8d40796b01e58c0695b02e54c8514103a4ec0593903a4cc0593106c4ac0386f0121ac0386701218c0385f01216c0385701214c0383f00e0f40483b0120e40383700e0d4048330120c40482b00e09c0381f01204c06d6f01b59c07d6301b19c06c6602f17c0ac5e01edac07b6301ad6c0bb5304ed2d9a34904ed0c13b4101e9980ba5e01e9380796b01e58c0695b02e54c1394b016524139430165048413300e1bc0486b00e19c0486300e17c0485b00e15c0485300e13c0384d01212c0484900e11c0384501210c0484100e0fc048330120a40381f01204c06d6f01f5b806d6d01b59c06d6501f58c07d6201b19c06c6601b19407c5f99917807c5d01edac07b6901ed8e4536101ad6c0bb5301ed2e6534901ed0c07b4101e9bc07a6702e97c06a5701e93c07a4d01e91e642456648fc0796b01e58c0695b02e54c0794b01652407943016504801330684ac0386f0121ac0386701218c0385f01216c0385701214c0384f00e1340484b0121240384700e114048430121040383f0120cc0482b00e09c0381f01204c13b5c6589119623c00e1300484000e0f007b6a01ad699623e0164e4059310220f80383d00e0f00483900e0d6600320120c404830 16 65535 7 127 11 2047 22 4194303
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_40_19 (Nat.sub p 608)) (cc_40_18 (Nat.sub p 576)) (Nat.blt p 608)) (cc_40_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_40_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_40_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_40_14 (Nat.sub p 448)) (Nat.blt p 480)) (cc_40_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_40_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_40_11 (Nat.sub p 352)) (Nat.blt p 384)) (cc_40_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_40_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_40_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_40_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_40_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_40_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_40_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_40_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_40_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_40_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0x4d2d666a6b7353539a9a8cd456e6a2a735b599ada8cd414a694aa00c5f99d22cc917a64693322450062dcb88fe5c46f300329711acb84ee5d2b92e133969b0cb49b4018af2734993923ca4d2e5268729341948a5ca450e4e48b282459382549c118018a724d6192d22c92d7a4946a00b5b91c2948cd5627ad313d6190d2ac4ed7e4148b13b5e8fd36c4ed5e3acf31d36e8e9b347410a2746f1c2548a1afc6d1b2286b719a6c8ccb0450d5e306b9181508be32450d4e28277141338ac22452d7a296a51403289d1a802d4e254ab11b6e88d1a802d2e218c1102657f9b7c3c14a1d4aaff36e86d3ebfcd9e1846b0c2347f9b142adfa156ecff23784d3240cdbe118f90336b8393e41c5c2066cf05b6c82cb04131d209271033638189dc0c4cdfe46affc7e7fe3b3fed16006a1002447fc9b3fc4ec01686fc4597e1acbf0d2df96cafc3430052fbb9185e86bef9c6c7cdae3d0d6df04d8f81607a1abbdcd71ec8c8f635c7a1a9bd04ede92b8f4133771b0bb8d2de48baf2455776383badf5dd6f8f04707751b3bc945dd468ee3430052bb931bdc98dce4c6772631392dadd36cae9b5574daa392d8dc9692e6d7e736bb39d1d1cd2fce494b72a37395199c909400a4f69ab134cdadbd6dadeb6c6f5aeb7ad71c14b8dea366f920b7c089bd468d33636ea2eb74919a78c4dc47069db7b6b1f1b56b8d3b6b6ca303645c1a76ced836c6b63a35ad71ad270d3b6369c9db505f1a82e8d415c69c99b4cd440148ed235c675b4b42d35a1074ceb68679a933c1499d4c8b456f669acb34d6168ad6cc234651b8b2c8d9946e0ca27c5a2b3b1d161916b8c735963da6b1cd6168ac6b436e62dae2d0dad89044c42345a1b1ad0d89686bcc047a60d1a3011c9818c4c035c5a1adafd171798f4bcc725e5ae2f4da979468b43535a1a92ec931744d6ba2635a12f2e5171698f4b4c725be2e2d31a9698c4b4b6e5a9ad2d408969268b41330051faccd154c8b6b1b4558ca329914d5e8b2af15657caa2bc1694c6beae461531abaaf1b9578c4abb6e55ca7298d3d5548aa615e5452faa5181514aea614e5362da9c9114d8a6a6136004ada945314968a7f45b51ca6286d154328ca223d50ca21fd14d3c8b29e1564fda0a785513d2a89e05a3f9afa74511378c29c3594dcb61fcd5d352a89746e4cca225d189312a89736e4bdae25c538fe69e962453f8af24b169288b0943584952fa4cd81254ae7f14e3fe2da40d2120688902443fe29a3c950ff6be8e46c3fdada33181194d87fb5745a2822c971158c87fb533fda7a240e8ff69c7fb4343a2921c934ff68485b5142d209fe959094827fa4e41c22200d79006a48034e401a1204901004ac8024e3fc191fc4d8012a67e345306359f4530f768a7c23d3dca218318cf58d260b6f3beb81e4510ef8e2783693bcbe182d9ced6b87614e305a79d2994e94aa6096e391379cb1c0e56e072267304a71851ace06907034430a319bc990c26de6e47c309b59b35c0d94f86136735d361ad1d0c26c66134f34c1d184d38c26866824d309a119c904c249c6605430db7186da8c84d86406c30db3186d88c369c61b4230d271840c8c126c0094b2fda29191acbd2985d3452ed1e9745108c8c65c469231b796c510b38e25a3692ccbe118d9cb16b85814e231a795c188ad4aa4616e29e351551a0a74de5437029d33918538a548846c6b285a4142d10a148846c6327d3211adbc9d8f846b6b26a381349f08d6ce4bc6025d3612d1d08d6c646b4f235a711ad0c908c44824d235a111c9448d4cc46136004a19145b0876ca4425d21cb203f5bc818b040b5520926904108812a80fd6b1f2380f8df47d4ca3e17c07eb38f3140792b83b3551dd268ec5501fac63a56907e3103edbc708e03817c07db38db1c86d2a80fb5f1ae360cf1c8678c03436219cb603ed5c654da2ec65175328ba954618c82ea4f17ab40bcd405d48e0f96e159378b31f0596e02b2671592a8ac9141f2bc29b6814db20415bc4f6b027b5413d2a0415ac4c6f826370082b3890d60486a824254082b188c990206de2247c081b58815f040ae02027c081b387b5803d4d81e474081b1874950206be1c46c081ad8699e034ce01a26c081ab863580314b818464081a985c904204ac16054085b7042da8278c013a6c09c36042d98216c412044085af042d48214ac1003207c9b0024cc1d8d20156f06e2c8055ac188e20c37c00ab382d16402ac609e7104e370051ac10cf20846e00a3180516c0d28c01453008b700457803ade01d6b01a3800c9f003ace0245800eb1804538012560003f 10 11
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 fullMask g_40 ep_40 627 bds_40 (dagTraceF fullMask rootStock 10 f_40) (cur_40 0) rootStock 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_9 : treeBlockF 288 320 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_10 : treeBlockF 320 352 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_11 : treeBlockF 352 384 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_12 : treeBlockF 384 416 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_13 : treeBlockF 416 448 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_14 : treeBlockF 448 480 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_15 : treeBlockF 480 512 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_16 : treeBlockF 512 544 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_17 : treeBlockF 544 576 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_18 : treeBlockF 576 608 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_19 : treeBlockF 608 627 (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nj_40_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_1 (fun _ h1 h2 => treeBlockF_at nb_40_2 h1 h2)
theorem nj_40_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_2 (fun _ h1 h2 => treeBlockF_at nb_40_3 h1 h2)
theorem nj_40_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_3 (fun _ h1 h2 => treeBlockF_at nb_40_4 h1 h2)
theorem nj_40_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_4 (fun _ h1 h2 => treeBlockF_at nb_40_5 h1 h2)
theorem nj_40_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_5 (fun _ h1 h2 => treeBlockF_at nb_40_6 h1 h2)
theorem nj_40_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_6 (fun _ h1 h2 => treeBlockF_at nb_40_7 h1 h2)
theorem nj_40_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_7 (fun _ h1 h2 => treeBlockF_at nb_40_8 h1 h2)
theorem nj_40_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_8 (fun _ h1 h2 => treeBlockF_at nb_40_9 h1 h2)
theorem nj_40_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_9 (fun _ h1 h2 => treeBlockF_at nb_40_10 h1 h2)
theorem nj_40_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_10 (fun _ h1 h2 => treeBlockF_at nb_40_11 h1 h2)
theorem nj_40_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_11 (fun _ h1 h2 => treeBlockF_at nb_40_12 h1 h2)
theorem nj_40_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_12 (fun _ h1 h2 => treeBlockF_at nb_40_13 h1 h2)
theorem nj_40_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_13 (fun _ h1 h2 => treeBlockF_at nb_40_14 h1 h2)
theorem nj_40_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_14 (fun _ h1 h2 => treeBlockF_at nb_40_15 h1 h2)
theorem nj_40_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_15 (fun _ h1 h2 => treeBlockF_at nb_40_16 h1 h2)
theorem nj_40_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_16 (fun _ h1 h2 => treeBlockF_at nb_40_17 h1 h2)
theorem nj_40_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_17 (fun _ h1 h2 => treeBlockF_at nb_40_18 h1 h2)
theorem nj_40_19 : ∀ i, 0 ≤ i → i < 627 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := block_join nj_40_18 (fun _ h1 h2 => treeBlockF_at nb_40_19 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 627 → (dagCheckNodeV4 fullMask g_40 ep_40 bds_40 627 (dagTraceF fullMask rootStock 10 f_40) cur_40) i = true := nj_40_19
theorem lb_40 : LowerBin fullMask rootStock g_40 11 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def wg : List Gate := [⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [4, 0]⟩, ⟨GateOp.and, [4, 0]⟩, ⟨GateOp.or, [7, 5]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [7, 3]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [9, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.and, [16, 15]⟩]
theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4274579648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276808928 * 2 ^ 32 + 4274579648)) (12 - 1) := by
  rw [show canon fullMask (4276808928 * 2 ^ 32 + 4274579648) = g_40 by decide]
  exact lb_40

end PEqualNP.Outside.L_meta_43549

theorem PEqualNP.Outside.L_meta_43549 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4274579648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4274579648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_43549.table2_from_lowerBin (4276808928 * 2 ^ 32 + 4274579648) 12 PEqualNP.Outside.L_meta_43549.root_lb PEqualNP.Outside.L_meta_43549.wg 17 rfl PEqualNP.Outside.L_meta_43549.wfits PEqualNP.Outside.L_meta_43549.weval
