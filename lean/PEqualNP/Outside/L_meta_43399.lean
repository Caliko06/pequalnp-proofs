import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43399

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

def m_0 : Nat := 0x202020202020202
def s_0 : List Nat := [0x2000200020002, 0x20200000202, 0x2020202]
def g_0 : Nat := 0x200020202
def ep_0 : Nat := 0x2020000000002000002000000000200020000000000000000000000000000000000000000000000000000
theorem epk_0 : ep_0 = edgePack 0x202020202020202 g_0 := by decide +kernel
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, 0x202020202020202 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
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

def m_1 : Nat := 0xa000a000a000a
def s_1 : List Nat := [0x2000200020002, 0xa0000000a, 0xa000a]
def g_1 : Nat := 0x20002000a
def ep_1 : Nat := 0x2000800000002000000080000000000000000000000000000000000000002000200000000000000000000
theorem epk_1 : ep_1 = edgePack 0xa000a000a000a g_1 := by decide +kernel
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, 0xa000a000a000a &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
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

def m_2 : Nat := 0x222200002222
def s_2 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_2 : Nat := 0x200000222
def ep_2 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
theorem epk_2 : ep_2 = edgePack 0x222200002222 g_2 := by decide +kernel
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, 0x222200002222 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
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

def m_3 : Nat := 0xaa000000aa
def s_3 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_3 : Nat := 0x20000002a
def ep_3 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
theorem epk_3 : ep_3 = edgePack 0xaa000000aa g_3 := by decide +kernel
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, 0xaa000000aa &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
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

def m_6 : Nat := 0x33003300
def s_6 : List Nat := [0x11001100, 0x3000300, 0x3300]
def g_6 : Nat := 0x1001300
def ep_6 : Nat := 0x12000000000000000000000000000100020000000000000000000000000001001000
theorem epk_6 : ep_6 = edgePack 0x33003300 g_6 := by decide +kernel
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, 0x33003300 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
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

def m_11 : Nat := 0x2222222222222222
def s_11 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_11 : Nat := 0x200220222
def ep_11 : Nat := 0x22022000000002000002000000000200220020000000020000020000000000000000000000000000000000
theorem epk_11 : ep_11 = edgePack 0x2222222222222222 g_11 := by decide +kernel
def bds_11 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2)]
theorem kn_11 : KnownBin bds_11 := by
  intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_0
  · exact lb_2
theorem sub_11 : ∀ b ∈ bds_11, 0x2222222222222222 &&& b.1 = b.1 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_11 : Nat → List (Nat × Nat) := fun _ => []
def f_11 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV4 m_11 g_11 ep_11 0 bds_11 (dagTraceF m_11 s_11 4 f_11) (cur_11 0) s_11 4 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_11 g_11 ep_11 bds_11 0 (dagTraceF m_11 s_11 4 f_11) cur_11 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_11 : LowerBin m_11 s_11 g_11 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_11 kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xa0a0a0a0a0a0a0a
def s_12 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_12 : Nat := 0x200020a0a
def ep_12 : Nat := 0x20a080000000200000a080000000200020000000000000000000000000002000200000000000000000000
theorem epk_12 : ep_12 = edgePack 0xa0a0a0a0a0a0a0a g_12 := by decide +kernel
def bds_12 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1)]
theorem kn_12 : KnownBin bds_12 := by
  intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_0
  · exact lb_1
theorem sub_12 : ∀ b ∈ bds_12, 0xa0a0a0a0a0a0a0a &&& b.1 = b.1 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_12 : Nat → List (Nat × Nat) := fun _ => []
def f_12 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV4 m_12 g_12 ep_12 0 bds_12 (dagTraceF m_12 s_12 4 f_12) (cur_12 0) s_12 4 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_12 g_12 ep_12 bds_12 0 (dagTraceF m_12 s_12 4 f_12) cur_12 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_12 : LowerBin m_12 s_12 g_12 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_12 kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0x303030303030303
def s_13 : List Nat := [0x101010101010101, 0x3000300030003, 0x30300000303, 0x3030303]
def g_13 : Nat := 0x101010301030303
def ep_13 : Nat := 0x2020000000002000002000000000200020000000000000000000000000000000000000101010001000000
theorem epk_13 : ep_13 = edgePack 0x303030303030303 g_13 := by decide +kernel
def bds_13 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_13 : ∀ b ∈ bds_13, 0x303030303030303 &&& b.1 = b.1 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_13 : Nat → List (Nat × Nat) := fun _ => []
def f_13 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV4 m_13 g_13 ep_13 0 bds_13 (dagTraceF m_13 s_13 4 f_13) (cur_13 0) s_13 4 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_13 g_13 ep_13 bds_13 0 (dagTraceF m_13 s_13 4 f_13) cur_13 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_13 kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xaa00aa00aa00aa
def s_14 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_14 : Nat := 0x20022002a
def ep_14 : Nat := 0x22002800000002000000080000000000000000000000020000000800000002002200200000000000000000
theorem epk_14 : ep_14 = edgePack 0xaa00aa00aa00aa g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_1
  · exact lb_3
theorem sub_14 : ∀ b ∈ bds_14, 0xaa00aa00aa00aa &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_14 : Nat → List (Nat × Nat) := fun _ => []
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 0 bds_14 (dagTraceF m_14 s_14 4 f_14) (cur_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_14 g_14 ep_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) cur_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x3300330033003300
def s_15 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_15 : Nat := 0x100110001001300
def ep_15 : Nat := 0x20000001000000012000000000000000000010000000100020000000000000000000100110001001000
theorem epk_15 : ep_15 = edgePack 0x3300330033003300 g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_15 : ∀ b ∈ bds_15, 0x3300330033003300 &&& b.1 = b.1 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_15 : Nat → List (Nat × Nat) := fun _ => []
def f_15 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 0 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) s_15 4 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_15 g_15 ep_15 bds_15 0 (dagTraceF m_15 s_15 4 f_15) cur_15 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xf000f000f000f
def s_16 : List Nat := [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f]
def g_16 : Nat := 0x500070007000f
def ep_16 : Nat := 0x2000800000002000000080000000000000000000000000000000000000002000200000005000400040000
theorem epk_16 : ep_16 = edgePack 0xf000f000f000f g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_16 : ∀ b ∈ bds_16, 0xf000f000f000f &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_16 : Nat → List (Nat × Nat) := fun _ => []
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 0 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_16 g_16 ep_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) cur_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xaaaa0000aaaa
def s_17 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_17 : Nat := 0x200000a2a
def ep_17 : Nat := 0xa28000000000000000000000002000000200000000200000a0800000002000000200000000000000000
theorem epk_17 : ep_17 = edgePack 0xaaaa0000aaaa g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_2
  · exact lb_3
theorem sub_17 : ∀ b ∈ bds_17, 0xaaaa0000aaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_17 : Nat → List (Nat × Nat) := fun _ => []
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 0 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_17 g_17 ep_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) cur_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0x333300003333
def s_18 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_18 : Nat := 0x111300001333
def ep_18 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
theorem epk_18 : ep_18 = edgePack 0x333300003333 g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_18 : ∀ b ∈ bds_18, 0x333300003333 &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_18 g_18 ep_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xf0f00000f0f0000
def s_19 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_19 : Nat := 0x105000001070000
def ep_19 : Nat := 0x2000000000000000000000004000000060000000000000000000001000000010200000105000001040000
theorem epk_19 : ep_19 = edgePack 0xf0f00000f0f0000 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_19 : ∀ b ∈ bds_19, 0xf0f00000f0f0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_19 : Nat → List (Nat × Nat) := fun _ => []
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 0 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_19 g_19 ep_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) cur_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xff000000ff
def s_20 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_20 : Nat := 0x170000003f
def ep_20 : Nat := 0x2800000000000000000000000000000000000000060000000c00000012000000300000001400000000
theorem epk_20 : ep_20 = edgePack 0xff000000ff g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_10, s_10, 4, g_10)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_3
  · exact lb_10
theorem sub_20 : ∀ b ∈ bds_20, 0xff000000ff &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_20 g_20 ep_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0x55555555
def s_21 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_21 : Nat := 0x1151515
def ep_21 : Nat := 0x14000000000000140000000000000104040400000000011010100000000000000000
theorem epk_21 : ep_21 = edgePack 0x55555555 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_7, s_7, 4, g_7)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_4
  · exact lb_7
theorem sub_21 : ∀ b ∈ bds_21, 0x55555555 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_21 g_21 ep_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0x5555555500000000
def s_22 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_22 : Nat := 0x115151500000000
def ep_22 : Nat := 0x1400000000000014000000000000010404040000000001101010000000000000000000000000
theorem epk_22 : ep_22 = edgePack 0x5555555500000000 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_8, s_8, 4, g_8)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_5
  · exact lb_8
theorem sub_22 : ∀ b ∈ bds_22, 0x5555555500000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_22 g_22 ep_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0x33333333
def s_23 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_23 : Nat := 0x1331333
def ep_23 : Nat := 0x12000000000000320020000000000100020000000000000000000000000001001000
theorem epk_23 : ep_23 = edgePack 0x33333333 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_23 : ∀ b ∈ bds_23, 0x33333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0x3333333300000000
def s_24 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_24 : Nat := 0x111111300000000
def ep_24 : Nat := 0x1002000000000010000200000000010000020000000000000000000000000111111000000000
theorem epk_24 : ep_24 = edgePack 0x3333333300000000 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_24 : KnownBin bds_24 := by intro b hb; simp [bds_24] at hb
theorem sub_24 : ∀ b ∈ bds_24, 0x3333333300000000 &&& b.1 = b.1 := by intro b hb; simp [bds_24] at hb
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_24] at hb
def cc_24_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_24_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cc_24_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x0 0x0 1 1 1 1 1 1 2 3
def cur_24 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_24_2 (Nat.sub p 64)) (cc_24_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_24_0 p) (Nat.blt p 32)
def f_24 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 64 bds_24 (dagTraceF m_24 s_24 5 f_24) (cur_24 0) s_24 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_0 : treeBlockF 0 32 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 64 (dagTraceF m_24 s_24 5 f_24) cur_24) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_1 : treeBlockF 32 64 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 64 (dagTraceF m_24 s_24 5 f_24) cur_24) = true := by decide +kernel
theorem nj_24_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 64 (dagTraceF m_24 s_24 5 f_24) cur_24) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_24_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_24_1 h1 h2)
theorem nc_24 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 64 (dagTraceF m_24 s_24 5 f_24) cur_24) i = true := nj_24_1
theorem lb_24 : LowerBin m_24 s_24 g_24 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xf0f0f0f
def s_25 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_25 : Nat := 0x1070f0f
def ep_25 : Nat := 0xe080000000000060000000000000000000000000000010200000000000001040000
theorem epk_25 : ep_25 = edgePack 0xf0f0f0f g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_25 : ∀ b ∈ bds_25, 0xf0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_25 g_25 ep_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xf0f0f0f00000000
def s_26 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_26 : Nat := 0x105050700000000
def ep_26 : Nat := 0x402000000000004000200000000000000000000000001000002000000000105050400000000
theorem epk_26 : ep_26 = edgePack 0xf0f0f0f00000000 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_26 : KnownBin bds_26 := by intro b hb; simp [bds_26] at hb
theorem sub_26 : ∀ b ∈ bds_26, 0xf0f0f0f00000000 &&& b.1 = b.1 := by intro b hb; simp [bds_26] at hb
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_26] at hb
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cc_26_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x0 0x0 1 1 1 1 1 1 2 3
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_26_2 (Nat.sub p 64)) (cc_26_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 64 bds_26 (dagTraceF m_26 s_26 5 f_26) (cur_26 0) s_26 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) cur_26) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 64 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) cur_26) = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) cur_26) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) cur_26) i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xff00ff00
def s_27 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_27 : Nat := 0x1001f00
def ep_27 : Nat := 0x1e0000000000000000000000000001000e0000000000010010000000000001001000
theorem epk_27 : ep_27 = edgePack 0xff00ff00 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_4
  · exact lb_6
theorem sub_27 : ∀ b ∈ bds_27, 0xff00ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xff00ff00000000
def s_28 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_28 : Nat := 0x15001700000000
def ep_28 : Nat := 0x2000000000000000000000000000400060000000000100012000000000015001400000000
theorem epk_28 : ep_28 = edgePack 0xff00ff00000000 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_28 : ∀ b ∈ bds_28, 0xff00ff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
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
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_29 : ∀ b ∈ bds_29, 0xff00ff0000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_29 g_29 ep_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xffff0000
def s_30 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_30 : Nat := 0x1370000
def ep_30 : Nat := 0x360000000000000104000000000000013200000000000001040000
theorem epk_30 : ep_30 = edgePack 0xffff0000 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_7
  · exact lb_9
theorem sub_30 : ∀ b ∈ bds_30, 0xffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_30 g_30 ep_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xffff00000000
def s_31 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_31 : Nat := 0x151700000000
def ep_31 : Nat := 0x200000000000004060000000000001012000000000000151400000000
theorem epk_31 : ep_31 = edgePack 0xffff00000000 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_31 : ∀ b ∈ bds_31, 0xffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xffff000000000000
def s_32 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_32 : Nat := 0x115000000000000
def ep_32 : Nat := 0x14000000000000010400000000000001100000000000000115000000000000
theorem epk_32 : ep_32 = edgePack 0xffff000000000000 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_32 : ∀ b ∈ bds_32, 0xffff000000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_32 g_32 ep_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xaaaaaaaaaaaaaaaa
def s_33 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_33 : Nat := 0x200220a2a
def ep_33 : Nat := 0x220a280000000200000a0800000002002200200000000200000a0800000002002200200000000000000000
theorem epk_33 : ep_33 = edgePack 0xaaaaaaaaaaaaaaaa g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 5, g_11), (m_12, s_12, 5, g_12), (m_14, s_14, 5, g_14), (m_17, s_17, 5, g_17), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_12
  · exact lb_14
  · exact lb_17
  · exact lb_0
  · exact lb_1
  · exact lb_2
  · exact lb_3
theorem sub_33 : ∀ b ∈ bds_33, 0xaaaaaaaaaaaaaaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 5 f_33) (cur_33 0) s_33 5 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 5 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0x3333333333333333
def s_34 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_34 : Nat := 0x111111301331333
def ep_34 : Nat := 0x22022000001002000012000010000200320020010000020100020000000000000000000111111001001000
theorem epk_34 : ep_34 = edgePack 0x3333333333333333 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 6, g_24), (m_13, s_13, 5, g_13), (m_15, s_15, 5, g_15), (m_18, s_18, 5, g_18), (m_23, s_23, 5, g_23), (m_11, s_11, 5, g_11), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_13
  · exact lb_15
  · exact lb_18
  · exact lb_23
  · exact lb_11
  · exact lb_0
  · exact lb_2
  · exact lb_6
theorem sub_34 : ∀ b ∈ bds_34, 0x3333333333333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x87030e021c0430285830a0614042418306f73d9d4b2456402c801862b0035e86bc055882ac15580aa055402a805500a9052e919722a2223c40310001 0x19130070d40049500124e0181440604d0192440165701715408c9782025207c9281e2460228e808a360165781d15a06c55805952068538161420124b80492d0121585545f15116c5045712d14c04b5f012d7804b5b118d6804b57012d5804b53016d4804b4f012d3804b4b012d1c04b430f4d0808a5f02295c08a4f02291c3b15f0e856c361570c454c2e14f0b052c2914709050c0493f00e4f40493b0124e40493700e4d4049330544c40892b02249c0485602c5700814c012520069440125000a24c00e9b0122600445b0049600245300625c0124b00481400ed500525c0120500393401317804c5d020d640d35102297408a5500e5740794901e5040892a01e49803856012118048440120b803816012d100a1500120500b45a02515805b5e020d6807356016d4804b4e012d3408a4902290408a3d0228d4061490145040892a022498048560120b807c5f04d16c1045701f14c07b5f022d6c08b5701ed4c08b4f022d2c08b47022d0c03a5f01e96c03a5701e94c03a4f03c92c03a4703890c03a3f0228ec08a3a00e8dc08a360228cc0495f0165780495b01256804957030558049530125480494f0105380494b01251c049430125080493f0124ec0493a0124dc089360124cc048560120f80382600e05807c5e01f14808b4d022d1403a4d00e91408a3a00e8d80595e01e568079560165480394e00e5340893a0224d80485601f17c07c5b01f15c07c5301ed7c07b5b01ed5c07b53022d3c08b4b022d1c08b4300e97c03a5e00e96c07a5a00e95c03a5600e94c05a5200e93c03a4e00e92c03a4700e90c0224200e8fc03a3b0228e803a3700e8d803a3300e57c0395b00e55c0395300e53c0394b00e51c0394300e4fc0393b0224e80393700e4d8039330121580382e00e07a4f34f938d2e3b3478c4d0e2f24f8a492e2024786890dfd23f7e48edf62377c08cded14f79852dc61476f050db413f6bc4edad13756c4cd5712f4484ad041273a848ce904f35c128cb0472901189303f2440dc5702f05009c0301f00405c0001f 15 32767 6 63 11 2047 22 4194303
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xa017f17e07076846806806805c65c058258054240a3e13e03453402c42c02a11e61a21a01811800a7081080080023001 0x494c8a8bd0914845a688b450b4bd04969f92b05a520949c1293580a6aa1450725af84a41c9296121090ac0ed71e1ac04b54076a00e4f11898048540f2981252024a21d140728d8e118025b603b68076c8dcd801c9e2213007258844801d26202406a2b8d055198a6049480928816501909a0481409488c0d401da62f348096880ed001d261f2405a29812510c89004b5c566a0a8d0140a00393c3c2609c4f0c89827144504a89853024a4049442c280944d0240a0484444488848d0249204924 12 4095 5 31 11 2047 19 524287
def cc_34_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x98098098098098098082b5b45a05244a44a04a04a04244204014003e12c92c02822802610ec0c10c00c0063060060003 0x6125a5f2565e24e5d2420595e5c15a5b156059525a14e59142048568f45f8e45b8a4578545305a5e822567b24e7915f7815b741576f1536d14f6a14b68147621435812903925048560484e0481e5635804b54453400485404b4c06b4804b444134004b6c533605216c5116044240432404235004b4c4f34804b4405b404e2444d1484c144048444a138039344814c08b5d08b5504a5604a554924e412420392d47129039251d1210485604854048444434404a444314404b500395c40150 12 4095 5 31 11 2047 20 1048575
def cc_34_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xf03c0f02fdbc2c39d67094a5079de0781e078186601354c13040cf130cb12c0a1280910601004001 0x8145a7f45605b5e7e35a7d35605b526c149671410393d7c13903935591310485603a5c7a254048546123803a345c138079340481c60128039247746c764607526c03a645f128039240486c7315c721547114405938701340481403a4c6e2445e12803924048446c35c6b13404814661406925c651400485c03a446624c0483c6735c652545d23803a346414459138631340481c60350 10 1023 4 15 11 2047 20 1048575
def cc_34_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x881e1048011fc17f01f817e01f417d01f406b48fec333081320007821a106801a006411414500140050014003860d04301012c0400100001 0xa04609f36c03b6803b6404b60991380393404b4c9814803944048349724803a440394c04814049249a3500481408b4d08b459b25a992569824e9724208a3e08a320595e9615a95156059520893a089360492e0492d048560483e06c5b06c5304b5f05b5e04b5b04b5a04b57a235604b5304b5206a5f08a5b08a5706a5308a4f08a4d08a4508a4304a3f04a3d04a3b04a3708a3504a330695fa115b9e157069539d14f9c1430493f0393d0493b94139049370393504933049310892f0892b0892708923048560482e08b4d06a5e06a5208a3a08a360595e0695a06956059520893a089360485606c5a05c5206a5f06a5b06a5706a5308a4d08a3d0695f0695b06957069530394d921410892f0892b08927089230485690254048548125c7e24c06a440484c8024c8d26c7f24c8c16c8b1600486c8934405a4c8824487148861440484405a34059347e359843510395d5c15903955831510485604846048440483e0481e80150 14 16383 6 63 11 2047 20 1048575
def cc_34_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xa562844a1026c6990a5c29606580940a44390064008f063c07e45f807e01f80791562158015c157015c05508f5817985c0083c0860008000 0x4a5908a5107a4d08a450395d0495a04956039550794a079460793eb91320792e089220385e0385d0384e05842bf03eb60320882a088260481e0481d0393404854b40440383406a340693407924bc05cae054ad02403934b204404854b104405b400584cb7024069340585c0383c038240382405a4e07a4206a3eb4232b314dae145b212d069250584e068420783eb10320382d0382506824aa01a0781604a58af25005a4cae244ad14406b5ebd35205b4e05b4206a4dbb245ba23d06a350795eb91520594e059420393d0393506934a912a07926b805e0485a04856b60520584e0684d0584c0684a06846b5045b0044058420383e0383da602aac026aa0440584ca704408a5e08a5207a4d08a450495a049560794a079460793ea91320392d039250885e0485a04856088520584e0784a0784605842a803ea6032038260382506a4f04a4b04a47c924305a3f06a3b06a3705a330894f0494b04947089430593fc813d0893bc7137c213505933c012f0692b06927089230784f0484b04847be0430583f0783b07837058330782f0682b06827ab0230781fa501b078170881304c5e04c5d06b4906b4108a5d08a5508a3d06a350395d9615903955a315104846048440482e9b24803a440494c9614807944049409a14803944 14 16383 6 63 11 2047 20 1048575
def cc_34_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xaa815502aa0518fa301401a35340598080ef49de037526d06d905b00b6006b04d50592624f649807e54bd010db21023f0c7c08ec30b4a160000b0000 0x7a5a07a5607a4ede24203a3d03a350595e0795a0795605952dd14edc14203936039350785603a350595e07956da14e0792e0785604a4f04a4b04a4704a4305a3f05a3b05a3705a330494f0494b04947049430593f0593d0593b0593708935059330692f0692b06927069230484f0484b04847048430583f0583b05837058330682f0682b06827068230781f0781b078170781305b4f06b4b06b4705b4305a4fe824be724705a43e523f06a3b06a37e32330594f0794b07947059430793f0693b06937df1330792fdb12b07927d9123d804606c5a06c5604b4e04b4d06a4908a4108a3d08a3506949d21410393dd613903935ce1310485604836048340482e07a5a07a5607a4ed124207a3e08a320395ed414ece1420893a089360492e0492d048560483e03826048160481403a4403944048140481404844cf1340481406934d246003a6cd126006a44d016c0496804964ce1600595ccd1540481c0481404b5f04b5b04b5904b5704b53d535105b4f06b4b06b4705b4304a5f08a5d04a5b04a5704a5504a5305a4f08a4d08a4b08a4708a4505a4308a3f06a3b06a3708a330495f0395d0495b04959049570395504953d31510594f0794b07947059430793f0693b06937cc1330792f0892b07927089230485e0484e0483e048360482e048260481e0481604b5a04b5606b4a06b4605a4204a3e04a3d04959089510694d0894506939089310892d0892506839bd0310382dca02903825b602105b4f08b4e05b4d06a4f04a4b04a4706a4305a3f05a3b05a3705a330894f049470593705936089350692f069270784f0484b04847078430583f0583b05837058330682f0682b06827068230781b0781704c5506a5906a5105a3d06a3906a3505a310595e0595d0894e089420593e0593d0593c059320692a069260385d0785903855078510583d0783907835058310781d078150692406b5406934059240782407954079240582404b4708b4306a4fc624b06a47c524306a3f04a3b04a3708a330594f0594e0594d0893f0893e04937089320892f0692a06927069260784fc404b07847c30430783f0483b04837088330782f0682b06827bb0230781d0881b078170781504b5a04b5606b4a06b4608a5e04a5a04a5608a5205a4e06a4a06a4605a420895e089520694d0894506839ba0310382dc102903825a6021 15 32767 6 63 11 2047 20 1048575
def cc_34_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xcd03244c903105c10f040af4abc0af02b81ae02b80ae02b80ae027909e027809e0231272690713920a50290070d1c0058615045401404014 0x3b447f1223c8571e024803b547e1223c4571dc278ec12c02d1a00e4d009068f43597d1a881ed35f268a0395d03cac80e5540f2a20794903ca080e494090ba0485503c2681e1280f08c08845044223d8541ee8b4f545602daf3d0d69e66ac05b52790a4bc4505e0272ec1316d02d0221581109a088450241e8120d40f4b403a5601d273b89080746a0595e03cad01e5580b2a4ed14e760a100e4d40f0b4078560441680e0940903a0481503e2fc0d16dfe8ae07c5301d2f81e96c074ae07a5301d27bf492c0748efb24301d1a816579f02acef14e7589701e17db20b4088570442b02213c1108e0882f01c138120540b6be05b5b02dab816d4c0969e04b4b035a4812d1c0968604b4102d2f8169740b4b605a570452a81694c0949e04a4d0252581291c1148a04a430351f81a8ec0d46e06a3302caf81656c0b2ae05953024a780e5340929607949024a380e51409286049410349f81a4ec0d26e0693303c9781e4ac0f24e079230242b012119b008805b5e035a30169580d49c0793503c9480e4940b0ac06b59035a88169780b4ba05a4e02d2101a8e80d46c0395d03cac80e5540f2a20792d03c928161181108806c5a0362b016d780d6b406b5602da901a525c42820393d7309c80e4d5b82620685602d2f01a9580d49ce412901c9281a15807488e103c02e2f017149c469a06b4502d2f0169480749a03a45035223788e80f46c0595e034ad01a5580b2a40394e01ca6b704e9c026c06856 14 16383 6 63 11 2047 21 2097151
def cc_34_8 : Nat → List (Nat × Nat) := unpackCursorV4 0xf207c41f103b44ed03b01eb07ac0e90ba40e80768ea3de4529006400891e20188022008022000800200068612200cf024309001830600006 0x47c5322e2991825c8f12a47451238278a70448b89a45c5322a2591513402caf46856a322ac05952768a74605361a26d16135780974504b5b80b4a60560240e8120540f8bf5645ba922b81f14c0f6bf51357a81a7d3cd1c074be07a5ba712d00e95e904ac07a5301d27d1893a8a49603a47a2121cf49080747a03a3701d1a81e57c0b2bd3b15b9c0ad4d855e642ac0795302ca94c053e4c29d2214b900a3c6c50e262840393701c9b00e4d40f0bedb05a0442ba941581109e088470441b8220bc1105a038270441282207c0903a088170240a81f1780f8a51034d861a28169780f4b407a5602d2900e9380749aec23a8691b00e5340728a0785a03c2b0120b40904a03944881a800ed31d868109150878a400e510110780483c01dae434d42186800395c858a8420500110b80883c03e2f01f148076bc05b5201da680ed140f4b407a5684926c209140747cee23d03cad01e5580729c0394d01c9f41c4f40f0b40785601c1f00e0c80903a0481503da781ed2c0f68e07b430252781292c0949404a4703d2301290c0947e04a3b0251b8128cc0f29e079470449f8224dc0925e0492701c2780e12c0708e0384301c1f80e0ec0706e0383301c1380e08c070360381703e2f81f16c0f8ae07c5301daf80ed78076b607b5a01dab80ed58076a605b5201da780ed380769603b4701da1c44d080f4be07a5a03d2b81e95a1c49f0a24701d1f80e8f9d647a0395f01cad81e568072ae0395601ca980e53c0729c0394b01ca380e50e0c2840392b01c9480e4840f0be0785a03c2b81e1581109e0884701c1f80e0f80907b0503c01c1b80e0d4070640882701c0f8220740702e038157b8ae3d05300d2890223402cae3d8530074d901260800b6016571f22a8f514c 14 16383 6 63 11 2047 21 2097151
def cc_34_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xca0a34a209669609607ae7816c66c06a16a04724603e43c13c03a13a03a03a03a03a0381152121120120085080004000 0x7c5e03e2950cd368468a05a5e02d294c49364248a03a3601d1ad0456a802ac0394e01ca6cfc4f67c26ade05a5482b0120740902a07a6c9a93200e9100f2893c13c02c9600e8f40746a079569a8aace853a342840793603c9a81e4ba7225a0785a03c2b0120740902a03a3401d324dc9600b2d93515803ca800e4d0072693545e03e2ecb0d66686a203a5d01d2a81e9366648a0395d01caa81e5240f2820392d01c92812174090aa0784a03c234c494007499251588c0a8016d125c2a11713497a2d4b51580b6bd2c35a959ab016d49d869d1834d95126ca49140747a03a35940a4c9c505ba0b4a80560241e8120d63e2892525c920a248c4f1d82580881401d2e484901da2b91e140 12 4095 5 31 11 2047 21 2097151
def cc_34_10 : Nat → List (Nat × Nat) := unpackCursorV4 0xfc13f00fa0b03aac526148d2dc1d68219c167019c061195ca51192873848dc13700dc02e24b801d447010c40204021808002000800008000 0xaf9aa0145712e27804824ae9aa0120700f8bc06c5b0362981f1480d6bfa835bd19ab81ad4f4469f9f34dce9a2e6cd0c074be06a5e03d2d80e95c0d4a606a5201d2780e9340748b9724401d1fd108ee7a47403a378311b3ec8cc0d2be0595ecb0ade4c56b242af8d156034a98165480729e0394e01ca6e204ff062771313abe09bdc04dac22660685f6f82d33015d560ac9c04f3101f8900dc1c05e03827af00f812076b802e0481503e2f01f1680f8ac07c5202daf01ed680f6ac05b5201ca680e5240728a0394101c9e80e4d40f0b407856044268221140907a0483503da781ed2c0f68e07b4301ca780e52c0728e0394301c9f80e4ec0726e0393303c2781e1280f08e078460441f8220dc0703e038170352300e53c072960394701ca181a13c0d094068470342300e07c0702e07c5f03e2d81f15c0f8a607b5602d2f01e95ab449d5924cac12200e57c072b60395701ca980e53c072960394701ca180e4e40724a0785f03c2d01e15c0f0ac0884f044238120940703e0381703d2e00e932824812f15c960a601a5200d2891a1409712600e9b2aa4c007a4caa0b654c5825a29803a6c9e13000e5b00f2d00396402cb0016572662a8039340442a50c9423849003a44950ae00e531d828003a5c91928508900072b8ec150948a60221700b4bc07a5d9b92a8169480746c03a3501cab00e5540f29d4114203c9e81e4d40b25a0592503c2d01e1580903a048150349a5308ea9646c0594e02ca101a4d80724c0392503c2501e118078bc07c5d01daf00ed64076a54d351a51a800e57a922ba0594e02ca100e4980724a0485d01c2a81e1280f08c0392403e2d01f158076b407b56771a700ed340b2bc0595201c9b51c4d40724c0392503c2d01e1580707a048359412e490511dc278ec12c01dae00ed50076892725c8e8a23b0480076a0aa044 14 16383 6 63 11 2047 21 2097151
def cc_34_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x8e08c17c87a17437407407406c46a16a06a06a06623973802e52a22a02242012001e11a21a0181180161122028020001 0x5f8510078b98235cbf92a00e9127c47116138b58985f41300905803b500242e2b8112f06a005a50bb8a82b41122a271720540241e016d7af66b57a35602da900ed38076857925abb12b5d493ae84851623e7611ec744a5f8242e005a5602b5cc0f80907a0483c0241adc40c8c805a25025b691a01a572d42a96f14cb280a5a4512c80296d244b40aa5b04f2c602969124b489a5a8912d026964124b209a594912c62696e354b592201a5b2ce2c8f115cb309e3b04b2c40296014c 12 4095 5 31 11 2047 21 2097151
def cc_34_12 : Nat → List (Nat × Nat) := unpackCursorV4 0xab026d09a065068a2a2808419ad9641d8c162052d741290013f04f033a08565150054015004c20c1c3000b04281090410504001000400004 0x171480d6b406b56ce1a681a9780d4a403a4da111d4208d80d2b406956cf0a681a1680d0ac0481d0240a80e913386b96623801d1a5d0511d82700393402da7016d080d29406946c089ee284d71625b801250342501a1180b69c05b42c091ee648d40d0940684602da101a93c0d49606a4703521e688f40d29e0694b034a501a51c0d28c06943cc09ee244bf0c2577f127b709181a13c0d09406847034231940bc5004f5f01fae80b81ad500d4d99126401d2e01e5700d2780592c01d220120f00b8bc05c52ca9a681ad140b4bc05a5201d2680e9140d4894123a03d1b01a55b222aa0694e03ca6c684eb2826c0692e0349681a1680d0ac0481d0240a80f1800f8a003a6c0352801a9100b2d991158034a800e5316a0a806a445982a01a8d00d2680792401c9a2c8113228bc06c5d02daf00ed640f6a403b5101da8016d380d69205b42035a0e40976f44aa06a4dc7922e388f40d46a0595e01cae80e5540d2a40594e03ca48165080d2820393d01c9a81a4d280254079260242e8121540d09a0684a03423334115600898b34cc5126631170076b9892549f92400e8d30a2910d134c38a65b04d22a26986354c29264589124e2b98413cc09a6600932da2417e03c 14 16383 6 63 11 2047 21 2097151
def cc_34_13 : Nat → List (Nat × Nat) := unpackCursorV4 0xbf26ac26884888008506850082858280828077965c375c00560c4e104512361e2d911e9e1e011e001e001d81190917041602158114820d8e0b050a810a800015 0x2da7816d2c0b68e05b4301d2781692c0b48e05a430351f81a8ec0d46e06a3301ca781652c0b2940394702ca301650c0727e0693e0349d80e4dc0d2660693201c9781e4ac0724e0792302c278161280b08e058460341f81a0df8205fbf02703c0f80e05c0b69e05b4b02da3816d0c0b49e05a4b02d2381690c0d47e06a3b0351b81a8cc0729e0594b01ca381650c0727e0693b01c9b81a4cc0725e0792b01c9381e48c0709e04847024218120fc0907604837024198120bc09056048270241181207c0702e0481302e2f81716c0b8ae05c5302daf816d6c0b6ae05b53035a781ad2c0d68e06b4301d2f80e9740b4b605a5a01d2b816958074aa03a4f0352701a92c0748e06a430352100e8fc0f47603a3703d1980e57c072bc0395d02ca781a5380b29bc514c02ca581651c0b28bc414402ca18165080b27e0593de189e0164ec0b27405937e109b0164d77c2680593302c9781e4b80b25a0585f02c2d01615c0b0ac0684f034239bc0fc6206e0782f01c1381607c0903a0581a02c0b8160580902bbd014ce22e3b0d2007681b7244dd89c00e4d36c68803a4c769226e44a00724805c5e03e2d01f1580b8a407b5a03dab3b0d25da68207a5a03d2b00e9380749bb723edb11900e4e4072620392d01c9281e1680f0ac0484d0242281b16c0f8b407c560362980ed7c0b6bc03b5b01dad00ed5c0f6ac03b5301da900ed3f6069c03b4d0352f81e96c0f4ae06a53dd127ee090c0747e03a3d01d1d80e8df6a46a03a3301caf80e578072b60395701ca981a548072920394301ca080e4bc072574612a01c9380e498072460685f03c2d01e15c0f0ac9d04f01c1f80e0f40706e04835368178b809c0703e0381702e2f0171480d4b406a5601d2680e9140d2adb3146ce09701a1680d0ac0481502daf01ad680d6ac05b520352d01a9580d2b4069567609cbc04c648252fe1210342d01a1580907a0483503629670d34074bc06a5201d26bb88e80746c0595e034ad01a5580b2a40394d7609d4344d80d0b4068560240e8120540d8a406b5f035ad81ad5c0d6a7b234d01d2f81a96c0d4b403a570352b01a94c0749a03a3fa291d80e8ddfa4660595e034ab6c44db6025c0685f0342d01a15c0d0ac6a03f1601b83c0bc0704e048150362d016d780d6b406b5602da901a568072ac03941cd0a000e4f40726a0392d01c9281a1680d0ac0483d0241a81b1680b8a406b5a0352f81a96c0d4ae06a53d712680e57c072b60695a01cab80e558072a60394d01c98e5c4c00725e0392b01c9380e48c0d0be0685a0342b81a1580909a6802f1481380e07c0702e03a440241601b153586b806a5403d226ac8e00746979144d509c6a44d00b68803a4401ca25e04d00b469771345e0220164d009029a7460035a200e9b34c4c006a4403d1a6945b2342d17a164d20b00165731e2a9761345d82a610920074880394c760a05d44d00748805c5e02e2901a9780d4a403a4dd09256809180748a03a44a191d4248db2a2b58e15601ca680e5171827b821357102d2e81580903a04815 16 65535 7 127 11 2047 21 2097151
def cc_34_14 : Nat → List (Nat × Nat) := unpackCursorV4 0x850285008481848084018106800280006c286c006410630263006281628062015e085e005b855b805b805b805b015787364325221a161014011e010001000002 0xee92276c093ba469db234ef1a2016973b84a9c912801c92768091342700393402da781ed2c0f68e05b4302d2781e92c0f48e05a43f111ff848efbe46fd923301ca780e538072960394701ca18165080727e0393b0349d00e4dc0726c0393301c9780e4ae942540392701c9300e48c0b09e0784a03c2381e11bb007fd70373b0178e009c0703e0381703e2d01f15baa693d134103d2d01e9580748c03a4501ca680e5140725a0392503c2d01e1580909a04845e80a400e51007269d0350e9a30748db0076d003b64e89b001a5239e27003934e69a201697007489c912801c92724d43988c1cb26c01d32016973944a9c812801c9200f17c078bc07c5d01daf80ed7bca6b803b5b01dac80ed5c076a603b52f19a8f58d400b69e06b4b035a3816d0c074bfd425d01d2d80e95c074aa03a5302d2781e92c0f48e05a43e711f81a8ec0d46fc723301caf80e578072ba0394f01ca700e52c072920394302ca100e5040727e0393b0349d00e4dc0726c0393301c9780e4ae902540392701c9300e48c070be0485d01c2b80e1540b09e0784a03c2381e1193c07e068373a0178d809c0703e0381702da7816d2c0b68e03b4302d2781692c0b48e05a430351f81a8ec0d46e06a3301ca781652c0728e0594301c9f81a4ec0726e0693301c9781e4ac0724e0792302c278161280b08e058460341f81a0dce605e3502703c0f80e05c0b49e05a4b02d2381690c0729e0594b02ca500e51c0b28c0594301c9781e4ac0724e0792302c278161280b08e05846390178d009c0f03e0381702da7816d2c0b68e05b4301ca781652c0728e0594301c9f81a4ec0726e0693302c278161280b08e058460341f81a0dc0f03e0381701daf00ed480d69c06b4202d2f0169680b4ac05a520352701a9280d48c06a4202d1f0168f40b2b405956034a701a5080f2720793101c9681e4a40724a0792102c2d0161580907a04835388168c809407279c0130 16 65535 7 127 11 2047 21 2097151
def cc_34_15 : Nat → List (Nat × Nat) := unpackCursorV4 0xf885e1aeda8ed58ad00bc712c00eb614a89ba7829f11978f97808f9085157a1667264740468146804288428042804084213f1714158304a20382020302000004 0x450921ff2444a85700394c5d44d006c5b86516a1345601b14c06b5f016d7a1235b83cd6a0d357828d5806b53016d4806a5f81c95c0695f7a856dce15701a54dba14f6c8525a214367c5060613f00e4f60413b8084e60113700e4d5fe13344c4c55012b43849c0685f394168088573001580884f022134088450220fc0483d0220dc0483502209c0881f02205c06a5e01a96806a5601a9480595e01a568069560165480685a01a1580882d0220940481d0120540694f01a52c0694701a50c0684f01a1280684701a1180881f02205c06a4600e53c0394b00e51c0394301a13c0684a01a11c0684600e07c0381701ad5805a5e01a9580695f01a56c0695701a54dfc1297ec4a0039257e84900685f01a1680685701a1580482502207c0881701a97806a5248c8e90b2360165780695a01a558059523b04e90d13601a1680685601207404815012d3c04b4b012d2804b4701ad1804b4301a53c069470124fc0493701a13c0684b01a11c068430120fc0483b0120dc0483302206c0881701b16805c5201ad6806a5f01a96806a5701a959f324d01a57c0695b01a55c0695300e535f81416744c54f12b42849c0685f01a1680685701a1580484d7dc1300883d02209c0881f02205c0593401205006b5901ad4406b4901ad040395d7a0564039557d45440694d7285140485d0121540684d01a128068460221140884401b16805b5e01ad6806b56016d499c14100e4f4f013900e4d4ec13101a168068560221340483d0120d5e925a720959b924e5989080595e7a0569f2156016548ed14e3b0508e405a0221580882d0220940481d01205406c5b01b14c05a5e7d0959f324e01a57de715b71c55c069536e053d9b1437c44a40392501a17ce305a02215c0885602213c0482502207c0881701716405c5101ad6406b5100e97803a5d01693805a4201a8e806a3600e574039550165280394600e4f80693200e4b4039250121740485501612805846012d3c04b47012d0c05a4f01692c05a4701690c04a3f0128ec04a370128cc0594f01652c0594701650c0493f0124ec049370124cc0692f01a4ac0692701a48c0384f00e12c0384700e10c0383f00e0ec0383700e0bc0382b00e09c0382300e07c0381b00e05c0381300f17c05c5e00f17405b5f016d6c05b57016d4c03b4f00ed2c06b4900ed1c03b4300ed0405a5f01696c05a5701694c03a4f00e93403a4b00e91def24500e90c06a3f01a8ec06a3701a8cc0395b0165680395900e55c0395600e54c0395100e51c0394600e5140393f00e4f80393b00e4dc0393301a4c80392f00e4ac0392700e48c0585f016168058570161580384f00e1340384a00e11c03846012115ee04401a0fc068371e40bc3b02700e07c0381701649006a587b092003a446545400794c7ac52007944468501e923800e8d1e813801e4d005c5f01b16c06c5701714c05b5f01ed6c07b57016d4dea34f01ad2c06b4779cd0c03a5f01697803a5d00e95c03a5501694c05a5200e93c06a4b01a92803a4701a91807a4300e8fc07a3b5388e803a3701e8d807a3300e55c0395600e5540794f01e5380694b01a51c0794364c5080793f01e4ed3813a01e4dc0793601e4cc0592f0164b80592d01617c0785a01e15c0785628413c068471e00fc3a03701e0bc0382701e07c0481d01e05c0481501693c06a4b01a91c05a4300e53c0394b00e51c0394300e4bc0392b00e49c0392301613c0684a01a11c068461dc0bc3902700e07c0381700ed01cd2400120f005c5e01b16806c5601714806b5a01ad5803b4e00ed35d324d01a92406a45730905d123d7908d40395e0165480394d00e5240694800e5140394400e5040393d00e4d80393500e4d14d12a00e4980685a01a158a004d01a1140483d0120d5d013800e4d14c13801a4a0039247788c00394452c4a1e004c 16 65535 7 127 11 2047 22 4194303
def cc_34_16 : Nat → List (Nat × Nat) := unpackCursorV4 0xd05de529eb21771fb0c1840bc35e02f0159096b462a30118070e3801a10d0068026713009804061a30c845482a00580090040001 0x5a4601653c0594b01651c0594301613c0584a01611c0584601e07c07817016d3c05b4b016d1c05b4301653c0594b01651c0594301a4fc0693b01a4dc0693301613c0584a01611c0584601a0fc0683701e07c07817016d3c05b4b016d1c05b430169180394f00e52c0394700e50c0393f00e4ec0393700e4cc0584f016128058470161180683f01a0dc0381f00e05c05b4f016d2c05b47016d0c0494f01251c049430124fc0493b0124dc0493301613c0584b01611c0584301a0fc0683b01a0dc0683301207c0481b01205c0481301717c05c5b01715c05c53016d5805a5e01a93a1f24c8789100595f01656c0595701654c0694f01a52c0694701a50c079298744a0039258704900585f016168058570161580684f01a11c0482586c0900781f01e05c05c5e01b1760e45501714805b4d016d1406a3a01a8d80394d00e514069396544c40685a01a1580483d0120d403a4c00e91007944016d3805b4200e4f4079358584b61512501a1280684601b1761835d016d3805b4285c5461415000e4f4039350121740684a01a11806c6c8311920935c016d3006a3401ad5a0c35501ad3a1134d01a8d806a3500e4f61013900e4d51a13101a168068560120f40483583916005b6c830d6006b5083117806c5d01ad2406b4101a9360824500e575eb15900e5560b1510121740485501a1280684682518006b68016d8005b5c820d5008854440d70ec34c6dc8d20514800e510088348004d1a12508149311424000e511ec25a73c959bb24e6109091c23a43c8d80595e7ac56a03156016548ec12e4504b4e605a3041580481d012054f034c6805400393c7fc4c20013c 13 8191 5 31 11 2047 22 4194303
def cc_34_17 : Nat → List (Nat × Nat) := unpackCursorV4 0x910191008b5783de800f791c7900790078c1715e6ada635e5bde4c7e44de373732d132c02ed02ec02a52235c220520c520c01bd41a4618c618c0131705380014 0xa14c016d0805a4f01a92c06a4701690e1423d01653c0694b01a51c0594301e4f64812f91c4ae451278fc48c0584f01a1280684701a1188b02f14409e3e01f8f405c06c5d016d0a4c25d01693c06a4b01a91c05a4384c8f40395d92c572491518f05400594f01a52c0694701650c0793d01e4bd5212b01e49cff1230121740584f01a1280684701a1188a02f14009c1001f01e05c05b4b016d0c0594f01652c0594701650c0693f01a4cc0584f016128058470161180683f01e07c0781701716805c5601ad3806b4201697805a5a01695805a5201a93806a420168f805a3d01a5240794100e4f40793900e4d40793101e4b40792901e49407921016168058560120f4048352240b44e0258dcd0005b4b016d2805b46016d0c05a4b01691c05a4301a8fc06a3301653c0594b01651c0594301a4fc0693901a4cc0793101e4bc0792b01e49c0792301613c0584a01611c0584601a0fe3802f8d809c0781f01e05c05b4b016d0c05a4f01692c05a4701690c06a3f01a8cc0594f01652c0594701a4fc0693301e4bc0792b01e49c0792301613c0584a01611c0584601a0fc8702f13409c0781f01e05c05b4b016d2805b46016d0c03a4b00e91c03a4300e8fc03a3900e8cc03a3101653c0594b01651c0594301a4fc0693300e4bc0392b00e49c0392301613c0584a01611c0584601a0fc0382f00e09c8601f13005c05b4b016d0c04a4701290c04a3f0128cc0594f01652c0594701650c0693f01a4cc0492f0124ac0492701248c0584f01612c0584701610c0683f01a0cc0482f0120ac0482701208c0781f01e06c0781701e04c05c5b01716805c56016d3c06b4e016d3405a5f01696c05a5701694c06a4f01a90c05a3f0168f405a3b0168ea3a2380168dc05a368e48d6352340168cc0595f01656c0595701654c0694f01a5240694301e5040593f00e4f40593b0164e8079398d04e0059370164d8039358cc4d0059330164c40792f01e4ac0792701e48c0585f016168058570161580684f0160fc0483d0160e8058370160d8048358c80d08502f12c09c0781f01e05c04b47012d0c05a4f01692c05a4701690c04a3f0128ec04a370128cc0594f01651c0493f0124dc0692f01a49c0584f01612c0584701610c0483f0120ec048370120cc0682f01a0ac0682701a08c0781b01e05c05b5f016d6c05b57016d4c05b4f016d2c06b49016d1c05b43016d0405a5a01695c05a5601691c05a468b891406a3f01a8dc0595f01656c0595701654c0594f00e5340594b01e5240594700e514059430165040693f01a4ec0693701a4cc0792b01e49c0585f0161740585a01615c05856022154c805401613c0484d01612805847016118048458c01100683f01a0dc0882701e07c0781701ad6406b5101697805a4e01a8d80395d01e5640395501e54407925012174048550161340584a0161180884502211006c5a01b15806b5a01ad58069496b05040393d8b44e4039356a84c40685a01a1580884d01a1140483d0120d407a5a01e95807a4e6ac90803a3500e5780795a01e558039528ac539aa14200e4d40785a01e1580882d01e0940481d01205405c5f01b16c06c5701714c05b5e01ad1a2e2568b09380595f01e56c0795701654c0794f01a52c069476a050c079358a84a40392501617ce805a02215c0885602213c068470120940881f01e05c06c6c8451820835401a8d0c60548451a006c6401a91005a3431415006c5a01b15806b4e844d360924d01a91405a3d01a8d805a350168d00694969c5040393d8984e4039356904c40685a01a1580483d0120d407a6c4e4980039644cc550079343101513926801e99007a3400e5b00593430c15007a5a01e95807a4e69890803a3d4f08e807a3600e8d40395e00e54a2214e6905080393d0164e80593601e4d40593401e4b93912d01e168078560120740481501ad7e2835b83cd6406b5789cd4e25351016d3c06b4b01ad1c05b4301697c05a5e01697405a4f01693805a4281c8fc06a3a01a8dc06a3601e57c0395d89056d3815901e55c0395588c54e2115101653c0794b01e51c0594301e4fc0693b01a4dda313301e4b55112b01e49c0792502217c0485d02215c0485501613c0884d39c1280884731c118088453081100883f01a0dc0882702207c07817016d3c05b4b016d1c05b4301653c0594b01651c0594301a4fc0693b01a4dc0693301613c0584a01611c0584601a0fc0683701e07c07817 16 65535 6 63 11 2047 22 4194303
def cc_34_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x2cd09c5e01c4bd52c03f30ad429084190e083410d0024407081c006041800504005 0x5c5e01714805b5a01697805a5200e5340794900e5140794101e4c40792d01e4940585a0161580484d01211404b4f012d1c04b4301653c0594b01651c059430124fc0493b0124dc0493301613c0584b01611c058430120fc0483b0120dc0483301e07c0781b01e05c0781301717805b5a01697c05a5b01695c05a539449140595f01656c0595701654c0794900e5140793101e4bc0792b01e49c0792301617c0585a01615c058560121165004423c0bc5502701e07c0781701717805c5301714805b4f016d3805b4d01697c06a5b01a95c05a5301a93e1924d01a91406a4301a8fe0f23d01a8ec06a3701a8d406a3301657c0695b01a55c0595301a53c0794d01a5140694301a4fc0393d01a4ec0693901a4dc0393501a4cd9313101e4bd5612b01e49d0312301617c0685a01a15c0685601a13c0683f0120f4068370120d48e02f15009c1301f01e05c06c5d01b15406a4a01a9180395d9345640395554c5440485d0121540684a01a11803b4f00ed2c03b4700ed0c0394f00e52c0394700e50c0593f01a4ec069370164cc0384f00e11c0583f01a0e80683701a0d88c01f14805d021200120f005c5285cd3405a5e01a96806a5601694803a4d01e93007a3e5548e807a364048c80395e01a5680695600e5480394d54c4ea4a13601a168068560480b40782501207404815858d3007a4c4b853003b4c854932441209180f2431449040524312490449244234016572421543d853240014 14 16383 6 63 11 2047 22 4194303
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_34_18 (Nat.sub p 576)) (cc_34_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_34_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_34_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_34_14 (Nat.sub p 448)) (Nat.blt p 480)) (cc_34_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_34_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_34_11 (Nat.sub p 352)) (Nat.blt p 384)) (cc_34_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_34_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_34_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_34_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_34_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_34_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_34_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_34_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_34_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_34_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0x25048b28044005a7802d2e4d2b31e25d8f0ae4944da3c2a31e92f8f495c8c0f23d24f2023490c9248055241249200148f491c7a07e3d02f1e150005a3c648e23246b1b02f8dda046c09e32469191388c89a4640d0016871804400527c5495a2d2731524e8aca74544a40149710b5b885a9c4c4e6216a31095b884a9c4453a212a200a4786d264369121b2510d92486c1200290dfe8b50a35d850a8c2a4b61524b0a1507fa2b3fcd6e1069b081397f9ad41d161fe6af05c5e82ca8bfcd5a088c1043547f92bbfc4fe05498ff13b80cab3fc4e5fe26f0013c7fd223fc4cc0147efd1297e8943f449001476fb9417dc260028ddf52a2f8a567c5273e4559f125200a337b922bdc1100129ef5a487aca43ced3de8470f413879da180252dc76b8f223571da8bae8fdd7476f004c75d1bbb4d11dd468ed25476d1a3b4091d7466eb83f75c1bb8ed41d5692e3a5d73e3039edb1cf6c0e835073c9c38e8fdcd688e446072136390951c96a0e412871d1980251dbd298de9446f49e37a4d9bf05ee01306fc13b7a4d1bd028009436ec9c36a93db9250daa436d91f36c8c9b546a0093f6cca3360d35b026cd812e0049db5c9340126ed4b5c6a51c3524e1a9268ae35b69230348981a42d8d2160571abab8d3da0494d0246571a6b3c5355c68ace35c571a1b308f59946acc13d571222b856d9469aca136570ad2b855d8e8bcc725d63922b1c8f55c2acc4c5c629a6314931894a8ae13f61ca6308d5184498c213c5709dafad7180698c024c5f52a2fc5117d098ae1375c5ad2e2d59714b4bbb505dca82e29597149cb8a425c41f2e415171064ae1365bca62c4d516c488b613c589222d091169268b4134588b22c44f163488b213458c9a2c40515c266b014c57daa2b807d5d6a8ae01700499ab093958498ac24400497a2716d534c0a996c54cb022715d136ae89b4f44da3a26969496a2a5a3a52d1b292d41492ba89a5651c9aa269391349689a434f9a6a7cd153e2b49f1564f89ea7c4d5134849e13c44cada725393925a8995a4dd2c22655d338bc99b514cd22a26559314a08994f49e2d25c541278ac93b5a49dab24e9352748a9394949ca0a26539234b89194448c9e22652d214808994747ca62389511c2888e13c44ca1a28569142ac8a14d45ca62284d5152688a12d44ca10024ad0568487b5043ca420a93d0b6a085b4042ca820a91d0749a83a4541c9ea0a50905078009273ae2da048d1004c08016c3ae2b9fc910eb4967e2443ad219f2d44f968a759563c22d1ec540f08ac7835a3c1ab1e0524f0282781393aca71d8908ec29c761423ac9700248c0109e6c24b361239cc4e4d847e72129361199c0d34e107870136360999b8908dc29c6e142360959b4538d82466c046004251ac4e4cc6a26a14e330a899b180cd4c06696c33c9a19a580cd2a866133004239940a4a54865293d2949b98692cc34866184b30c2194a4d4c10525292f2fc1f14a10cac6a45e05c2b1229588f4ac2a45605e2dc12158148ac08a58a322c4a69624b4b1064560442b52815a910ad2885602629411954110a62645303e29c2214c0c8a50360084628ca8928d58942b64fc6027db612855c9429e4a1432552d134d40954ac4aa4e2552112a568952ac4a1390041f9245040106e482541622f8b116c8b4d84596c22cb00b115c8668843244218a410c510588a641b5120ca88b09587c8b4401501f22b0f8d687c6ac3e139161270f4950582be2c15b1d6360eb180754d82c1571c0ae0e05507028838134160a98dc9105829e35b5c1ac9a0b052c694b82c14718dae0cc930634a83194418c9a0b050c594b4303501652b0b2938594842c95a164ab0b2538592842c129004178acd60158be0ac5b145b00a25b0512c00ac57131a40989104c29026144056298944e04749c2414c11c9482ad683e8bc21b4410ca207d1483e4b4201500f92b07c4a4156841e358054af82a56c378d81bc600ddb002a55c322b8191540c8a60644d0152a617b500bda402a53c2d2980a94b0a9a8054d001528e12a5409ca204a530252680a9430592f042910214680b2520592502c918162b40e350058ab02c538174880c13405caa02c50815262008270122d822980112d8024570112580890c0d6a2021560162d014540058ac02b5a015ab00a524052820214e0040f8049080102e0001f 10 11
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 594 bds_34 (dagTraceF m_34 s_34 8 f_34) (cur_34 0) s_34 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 64 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_2 : treeBlockF 64 96 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_3 : treeBlockF 96 128 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_4 : treeBlockF 128 160 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_5 : treeBlockF 160 192 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_6 : treeBlockF 192 224 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_7 : treeBlockF 224 256 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_8 : treeBlockF 256 288 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_9 : treeBlockF 288 320 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_10 : treeBlockF 320 352 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_11 : treeBlockF 352 384 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_12 : treeBlockF 384 416 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_13 : treeBlockF 416 448 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_14 : treeBlockF 448 480 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_15 : treeBlockF 480 512 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_16 : treeBlockF 512 544 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_17 : treeBlockF 544 576 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_18 : treeBlockF 576 594 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nj_34_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_1 (fun _ h1 h2 => treeBlockF_at nb_34_2 h1 h2)
theorem nj_34_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_2 (fun _ h1 h2 => treeBlockF_at nb_34_3 h1 h2)
theorem nj_34_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_3 (fun _ h1 h2 => treeBlockF_at nb_34_4 h1 h2)
theorem nj_34_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_4 (fun _ h1 h2 => treeBlockF_at nb_34_5 h1 h2)
theorem nj_34_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_5 (fun _ h1 h2 => treeBlockF_at nb_34_6 h1 h2)
theorem nj_34_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_6 (fun _ h1 h2 => treeBlockF_at nb_34_7 h1 h2)
theorem nj_34_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_7 (fun _ h1 h2 => treeBlockF_at nb_34_8 h1 h2)
theorem nj_34_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_8 (fun _ h1 h2 => treeBlockF_at nb_34_9 h1 h2)
theorem nj_34_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_9 (fun _ h1 h2 => treeBlockF_at nb_34_10 h1 h2)
theorem nj_34_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_10 (fun _ h1 h2 => treeBlockF_at nb_34_11 h1 h2)
theorem nj_34_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_11 (fun _ h1 h2 => treeBlockF_at nb_34_12 h1 h2)
theorem nj_34_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_12 (fun _ h1 h2 => treeBlockF_at nb_34_13 h1 h2)
theorem nj_34_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_13 (fun _ h1 h2 => treeBlockF_at nb_34_14 h1 h2)
theorem nj_34_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_14 (fun _ h1 h2 => treeBlockF_at nb_34_15 h1 h2)
theorem nj_34_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_15 (fun _ h1 h2 => treeBlockF_at nb_34_16 h1 h2)
theorem nj_34_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_16 (fun _ h1 h2 => treeBlockF_at nb_34_17 h1 h2)
theorem nj_34_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := block_join nj_34_17 (fun _ h1 h2 => treeBlockF_at nb_34_18 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 594 (dagTraceF m_34 s_34 8 f_34) cur_34) i = true := nj_34_18
theorem lb_34 : LowerBin m_34 s_34 g_34 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xf0f0f0f0f0f0f0f
def s_35 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_35 : Nat := 0x105050701070f0f
def ep_35 : Nat := 0x20a080000040200000e080004000200060000000000000000000001000002010200000105050401040000
theorem epk_35 : ep_35 = edgePack 0xf0f0f0f0f0f0f0f g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 6, g_26), (m_13, s_13, 5, g_13), (m_16, s_16, 5, g_16), (m_19, s_19, 5, g_19), (m_25, s_25, 5, g_25), (m_12, s_12, 5, g_12), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_9, s_9, 4, g_9)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_13
  · exact lb_16
  · exact lb_19
  · exact lb_25
  · exact lb_12
  · exact lb_0
  · exact lb_1
  · exact lb_9
theorem sub_35 : ∀ b ∈ bds_35, 0xf0f0f0f0f0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x99025c28a362418902240860e141840610084020828105c507005c007001b436c05ac16b01ac06909a0167059c0660588452408ef0188001 0x1e24c00e4a008a5d022954049560125541f14e0545081d13e0284c80392e0121580485400e0b80381e0121101a3440649100494401251006130012d40142500129301b45e0611481734d058d1408a4d0229140595e054568131560165480494e0125341213e00c4c80485600e0b80484403cd100e2340124d0049340184c00935001294004a3801451005234018d100595c01055003814040d780d352030d280b3460228f408a350165780a15a0205580595201c538031420124f80493d0121580382e10917c4145b0f515c384530d8d7c3535b0c4d5c2c3530a8d3c2834b098d1c2134301297c04a5e01296c1c25a01295c04a5601294c05a5201293c04a4e01292c04a4701290c112420128fc04a3e0128ec04a370128cc0223202257c0395b02255c0395302253c0394b02251c039430224fc0393b0224dc039330121580382e00e07a4f34f938d2e3b3478c4d0e2e24f8b492e1a24784090e0e23f82c8ee0923775c8cdd514f72452db61476c050d7b13f5dc4ed7213756c4cd1612f4484ad041273a848ce904f35c128cb0472901189303f2440dc8002f1f809c4401f00405c0001f 14 16383 6 63 11 2047 22 4194303
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x800f11e03b1760e8585300588a114028050091120231460884c51802a6540919201aa2c8580a11400a010002 0x806d8fcd8025363e2603448064501e1a43b344304a012931d12404a440b4800e521c8a2048446e4b012950811804854094781e8e0251a0a230688d8cd1802536322601e460384c181ae2f3541a480128f1711c04a340b4600e4e1689a048342e4a0ac92025220c24052470128d129a004a5c4e4a0589005918242380c46090d112a2a04a3c46470128d019180393844268120d1011c03938 11 2047 4 15 11 2047 19 524287
def cc_35_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xee0f703b03b0ad60ea06d9f681b405906c81640b205902c8128f920c9024032009004802401200900393c4622000820010000000 0xbe298120b2f22a03a38ba4694457250a64613c07271704d01c980483c0b268164901e2f03c5da86b368d46492cd9251072ba0e5241ca0848560908c12110241f0482e0702c0ed12b1285745aaa8ac16d7aa1ad533560b6a40ed381da6d2249a2483408e631188394907282121581d1a4d3509c6b530d5a59a74a3420b4bd2496a412b05a528e49d189081d1f03a3d072720e4c4242b7c45ff68b7dd15f9229f035fde6b7acd5f31a9e434fc469780d1ed9a183a5f074b60e95c1d2983a4f074960e91c1d2183a3f074760e8dc1d198395f0b2bc0e56c1cad03957b02ac0e54c1ca90394f9e29c0e52c1ca383943072840e4fe289f0393b0726e0e4cc1c99048560909c120f81c1303816864b012950d92004854094981a920252215240 13 8191 6 63 11 2047 19 524287
def cc_35_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xfe7f83c1ec6d81a87505e6bc1782f05e099330231ba6740e05c02c6580b01602c03526809212014820402000 0x3e2f87c5b0f8ae1f14c3dad05b52fe6841e57c3cad879570f2a62253c44a58894711286224f41c988892d090ac0e563e8aa04854ae2b9505301ca4069440728012132b0a67a36cf26c1e05b01cb05514c090d9d8d23a9a203a48e8488165301ca47314407280121101cac71154090a938532489e039380f2680e4c0241e4d13cdc8d9b518360b60396098278121b351ae6935407471a08d02c9e03938ce2680e4c0241a03948ca2892c4f024225215c072718c4d0241a5f230bc681845701ca80485c 11 2047 5 31 11 2047 19 524287
def cc_35_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xd813543d30b481d203441d103401d003400bc5242c8239bd36a15a416901944620d802600144f50054004f053c04f013c04e04e940eb000e 0xa04609f36c04b609923804b4c9824804834973480482404a349a350048249b35a993569834e9734205a5e9625a9525605a5204a3e04a3d0894d0894508939089310892d039290892503921048560481e06c5b06c5304b5f05b5e04b5b04b5a04b57a235604b5304b5206a5fa125b9e25706a539d24f9c24304a3f04a3b9423904a3704a3304a310695f0895b08957069530894f0894d08945089430493f0493d0493b03939049370893504933039310892f0892b0892708923048560481e06b5e06b5205a5e06a5a06a5605a520894d0893d089350892d0392908925039210485606c5a05c5206a5f06a5b06a5706a53922410695f0695b06957069530894d039410893d0892f0892b0892708923048568825c8524c04a4806a4404a408734c8f3608e26c04a608624c8335c04a3c048248235c0482404c5e04c5d853598a35107a4907a410895d0395908955039510892d0792504846048440481e04b4487250048248845a8645605b5e8535a8435605b5204b4e04b4d832498224108949089410893d0393908935039310892d08925048560481e07c5f9045b8d45707c5307b5b07b538c34b8b34304a5f05a5e04a5b04a5a04a578925604a5304a5204a4f8124e04a4b04a4704a4304a420795f0895b08957079530894f0894b08947089430893f0893d08935089330492f0492d0492b0392904927089250492303921048560481e07c5e07c5205a5e07a5a07a5605a520894d089450893d0892d03929089250392104856 14 16383 6 63 11 2047 20 1048575
def cc_35_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x9081123e2404345773ec89954f2a415306a505441a8805100a2013639bec37806e04dc015982b005504aa0154029843b602b30540031e01140008000 0x5a4e07a4206a3ec02320594e069420793ebf13206924be04db2045ae02d06825aa01d0781504958bc1500594cb2144b104406b5ec635205b4e05b4207a5ec525205a4e05a4206a34c415e0495a04956c21520594e0694d0594c0694a06946c1145bd144059420684db0045ad03d06835a902d07825a601d03819bb0150381105b4f08b4e05b4d06a4f04a4b04a4706a4305a3f05a3b05a3705a330794f0494b04947079430593f0593b05937059330692f0692b06927069230884f0384b04847038430583705836088350682f0382b06827038230781f0381b078170381303c5d04c5503b5e03b5d06a5906a5105a3d06a3906a3505a3107959079510593d0793907935059310585e0585d0884e088420583e0583d0583c0383905832038310682a068260781a078160682406b5406834058240781407a54078240581406a34b315cb2154068340782403818b101403b4f04b4708b4306a4fb724b06a47b624306a3f04a3b04a3708a330794fb514b07947b41430793f0493b04937089330792f0692b06927b01230584f0584e0584d0883f0883e0383b0483703833088320882f0382b0682a0682706826038230881f0381b0781a078170781603813ae14404b5a04b5606b4a06b4608a5e04a5a04a5608a5205a4e06a4a06a4605a4203a3e03a3d06939ad131ac129a61210885e088520684d088450383903831aa1440594ca714404a5a04a5607a4a07a4607a3ea92320895e0495a04956089520594e0794a0794605942a813ea61320392e0392d0885e088520784d08845038290382106a4f04a4b04a47c924305a3f06a3b06a3705a330794f0494b04947c71430593f0793b07937059330792f0692b06927ba1230884f0484b04847088430583fb903d0883bb8037af03505833ab02f0682b0682708823a501f0781b078170881304c5e04c5d06b4906b4196259a32510895d0395908955039510893d0693504846048440481e9b34804a4c9624807a4404a409a248 15 32767 6 63 11 2047 20 1048575
def cc_35_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xf903e40f903a8fea037cbb99a819a0023928e01f127b05e817905e40760dd416a2cd3634007d51f0029508081820504140020c0020000000 0x7b5a07b5607b4ede34205a5e07a5a07a5605a52dd24edc24203a3e03a3d03939039310785603a3d03a350595e0395a0795603952da14e039420793e0393d0785604a4f04a4b04a4704a4305a3f05a3b05a3705a330494f0494b04947049430593f0593b05937059330692f0692b06927069230484f0484b04847048430583f0583d0583b0583708835058330682f0682b06827068230781f0781b078170781305b4f06b4b06b4705b4305a4f07a4b07a4705a4307a3f06a3b06a37e62330594fe514be414705943e113f0693b06937df133db12f0792b07927d9123d804606c5a06c5604b4e04b4d06a49d2241d6239ce23106949089410893d0393908935039310485604836048340481e07b5a07b5607b4ed1342d424ece24204a3e04a3d07939089310892d0392908925039210485604826048240481e04824048240484403928cf1240482406a34d2460d136006b44d026c04a6804a64ce26005a5ccd2540482c0482404b5f04b5b04b5904b5704b53d535105b4f06b4b06b4705b4304a5f04a5b04a5904a5704a53d325105a4f07a4b07a4705a4307a3f06a3b06a37cc2330495f0895d0495b03959049570495504953039510594f0894d0894b0894708945059430893f0693b06937089330892f0792b07927089230485e0484e0483e048360482e048260481e0481604b5a04b5606b4a06b4605a4204a3e04a3d06939c6131ca129c212104859088510684d0884506839088310882d03829088250382104a5a04a5607a4a07a4607a3ec523205942c813ec21320492e0492d04859088510784d0884507829088210881d03819088150381104954c014404954bf14405b400594c03818c301406a340595c 14 16383 6 63 11 2047 20 1048575
def cc_35_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xff03e85fa03d06f10fc01d95f601d8035c1d7035c0d7035c0d703056c103040c102c8f81c543150013c13d48b111a486801a002cf0b0000b 0xe8e1fc468f215c01c9c3c04d007470fc234788ae3b8531d82780393001daa0164d00906803c5001e2f00f175e86b2fa35103da6be4d140f4b207a5103d2481e904072ba0395501ca480e5040725a039250242e8121540f09a0784a03c230221141108803b447b1283dd169ea8ac05b5e7a1ad3ccd580b6a403b4e01da6bc8925e2482f02397611880e524072820392d01c92b68168110ac0884d044228120f40906a07b5a771a10169780f4b407a5602d293b4939d848403a3d01c9881e1680f0ac0883d024168120940f8bf0345b7fa2b81f14c0f6b607b537e9a5becd0c074be03a5b01d2b80e94c0749e03a4b01d2380e90c0747e03a3d01d1a80e57c0b2bc0395b01cad00e55df02ac0395301ca900e53dde29c0394b01ca380e50c072840393f7589f00e4f40f0bed905a0442b8221581109e088470441f80e0bc0704e0381f01c0e80e05c0902a05b5f02dad816d5c0b6a604b4f025a581ad240968e04b43025a081697c0b4b605a5702d2981293c0949607a490252381290c0948206a3f0351d81a8dc0d4660595f02cae81656c0b2ae0895502ca981253c0929a0494b01ca481251c1128a0494301ca081a4fc0d276069370349981e4bc0f2560792703c918121580908cd8044740160171780b8a405b5e02da901ad100b4bc06a5a0352b016949c629a069456f09e81e4d5b825a039297389280e4840d0ac05a5e01d2e80e954074a403a4a0352300e8e80f46c0595601caa81a538072840793e01c9900e4b80725a0585601e2f00f1740d6b206b5103d2c81e9440b2bc0595d02ca700e5240b284039410349d01a4d80f2540792602c230221100d8b406c5602daf01ad680d6ac05b5201da700ed340d492e32417111cb708c407292039410342b00e9340748a0595e01cad01a558072a40694e01ca6b804f80726406856 14 16383 6 63 11 2047 21 2097151
def cc_35_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x848109021204144828105020a0400564eeb4553eaa4cc3abc6738ce015912b005600ac0144528025000a0013c123902e641d002450480060c0c00006 0x11e3508e9a4470971d84811a3508c9a03b0942304980885c03e2fd6916eac8ae07c5303dadd54d6a9e6ac07b53a69a7530d2e966874634203d2f81697a8a4b74225aa012bcf49580f4a605a529d927ccc93a604972e24795121c889080747e03a3e01d1e81e57c072b71f15701ca9c6c53c072971714701ca180e4e4072660393103c2fb6c168110aea50560442782211c1107e0883d0441a8220bc0905a088270241280e07c1102e07c5e03e2d01f1580f8a405b5e03dad01ed580b6a40394d01ca480e514072820393901c9880e4b40f0b407856044268221140907a0483503da781ed2c0f68e07b4301ca780e52c0728e0394301c9f80e4ec0726e0393301c9681e13c0f0940784703c230220fc1106e0381f01c0b80e53c072960394a01ca381a518072860684f0342501a11c0d08c0381f01c0b81f17c0f8b607c5703e2980e97c074b603a5a01d2b81e958074a603a4f01d2580e91c0748603a3d02caf01e55a2a29d1414c898a200e4b80f0be0785a03c2b81e1581109e0884701c1780e09c0902a07c5e03e290169780f4b407a5602d294385361228aec12d8509281e1680f0ac0482d0241281f1780f8a405b5203d2d01e95a2047a0795a03cab4345360e28aee13d01c9480e4840f0b407856024168120961c6a0ec34086928430920110780482c01c90428d4212681082508392000e500072400885c0441e01ed3c0f69607b4703da181293c0949604a4a0252381e9180948604a3f0251d8128dc094660784f01c2581e11c070860883f01c1d8220dc070660482f0241380e08c0f8be07c5b03e2b81f14c0f6b405b52889a101e96a1e4840795f01cad81e5680f2ae0795601ca9c2c53c072970614701ca1bac4f4072420785f03c2d01e15c0f0ac0884f044238120f60a0780882d01c0f82205dee2b8f414c01ca401a510072810223402cae3d8532026c10016c01cb0016571f22a8f514c 15 32767 6 63 11 2047 21 2097151
def cc_35_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xa418508407c47a17a07817807807807615325015004654603e43e03c13a13243203012e12c12c02c02820ce0c00c0006 0xe4e27e8bc07c5d9b9accf8d44074b203a5103d2481e904072b20395103ca6c80514090ba0485503c2501e11a786a003b409912c49c9400b68939250928924e916a708ac05b5e9b9ad4d8d580b6a4ec34e939a6cd49266848203a3901d18c705363028add05a5402b0120f40906b2d244991ae468931d8479311240441200ed425e680ed25c961204b49324a4992735c961aa47493256248a7044928924904924a2992413c02d2f4a496a504ac05a527692749c935e047d2623d91893428495b80b4a605602416812096426c007a6802d30016972404a808854 12 4095 5 31 11 2047 21 2097151
def cc_35_10 : Nat → List (Nat × Nat) := unpackCursorV4 0xbb02ec0a559d316d1db016c01b00671551353054c053013074c0108a4200dcb3118b052b04a812a00a801650445110044005301400014000 0x58cd6ac26ad6034eaf9a101697abc4b55d25602d293b4939d848403a3e01d1e80e5340728a0393901c98b80168110ac0883d0441a8120b40904a06c5b0362981ad7ee26b76d357035a9dacd3ed268603a5f01d2d80e95c074a603a4f01d2680e9140747e03a3b01d1b80e8cc072be0595e01cad80e568072af6615601ca980e5480729f6414e01ca680e4feb827c0393b01c9b80e4cc072640685f6f82d02215c110ac0884f0441f8220dc0705e0382701c0f80e0740702e0481503dae528d02744b93724c0352401a912524813934cac9b001ed32b04d9572609c126016d780f6bb4135502da901e93a9448405a3d01d1d00e8d80b46a03a3403c9500e4a40f24c0392103c2d01e1580905a048250351a0169380b48406a36a989d5484d80f0940784603e2ed50d46a26a15025d02d27016908072a20485d03c2501e1180f8b407c5603dab3b8d380b4bc05a52a711a80e4e40f0b4078560241acd4d71dc498ec23c01d1a00e4a2622493435c01d1c3b08c0072512b12401d1a2a81100f8bc07c5202daf016d4a7869b2f345a512d5249580747403a368f0a6c645169025403929a389300e485bc0b4a9056024168120940f6d93f364909260168f00f24807a569f92ad1093a5248407a3ea191e81e4980f24a0785a03c2b0120b40904a03b68a09ac0169b27e4b007a50 14 16383 6 63 11 2047 21 2097151
def cc_35_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x97012e025033c776e2ac755766275e479c8f00fc8995922c040148000f431e8037186e00c8519002c185218a0108ae11000478041008000040000000 0x2fc8c006b6802db0016d72fa6a8088540362debd16b528ac06c53035af816d7b506b7a535ad19abe80d580d6a605b5201da780ed380769a06a5fcf92de6c95c0d4a79a24fcc124e5c90f244839023fc691de148e70646f7f2339111881a57c072b77c15701ca980e52407286039418d89780e4ae1624e039230342fb84168110aeab056044278221341108a0883f0241e8220dc0906a0882f0441380e07c1102e06b5e035ad01ad580d6a405a5e0352d01a9580b4a40394d01c9e80e4e40726a0393101c9480e4840d0b4068560441e8220d40905a048250352781a92c0d48e06a4301ca780e52c0728e0394301c9e80e4bc072560392701c9181a13c0d09406847034230220bc1104e0381f01c0b80e53c072960394a01ca381a518072860684f0342501a11c0d08c0381f01c0b81ad7c0d6b606b57035a980e97c074b603a5a01d2b81a958074a603a4d01d1f80e8ec0746e03a3302caf01a55af427d7913cbc09a00e4b80d0be0685a0342b81a1581107e0883701c1780e09c0902a06b5e035a90169780d4b406a5602d294684f61026aec12d8509281a1680d0ac0482d024128171480d6bc06b520352d01a95aea49a0695a034ab5945363227b0713501c9480e4840d0b406856024168120940969e04b4b025a5012d1c0d68c04b43034a781a52c0d28e069430249f8124ec0926e049330342780e12c0d08e038430241f8120dc070660881f01c0d82205c0702606c5a02e2901ad680d4be06a5b0352b81a94eec48374231034af80e56c0d2b406957034ab00e54ec829a039318b89780e4ae0c24e039230342f81a1680d0ae0685602426dcc1301107a0882f0441380e07c1102f6314caf09e00e4e00f26803930b8122016572c42796f460b70b600e5800b2b967154b089e00e922d848803948768a25804f0074716a234b28ae57c531d82780393001d2a0164900904803c5001e2f00f1740d6b206b51035a481ad06bc4b36825103526d9c914072ba0395501ca480e5040727a039350242e8121540d09a0684a034230221141108806c5a02daf01ad680d6ac05b5201da6d94905e0472ec23101ca081a1680d0ac0884d0241e8120d40746962350 15 32767 6 63 11 2047 21 2097151
def cc_35_12 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41b40b40aa59e69e088b7e57c17a17a07a05345204854804613e43c13c03a13a03813803801521400c40c00a1081004 0x62c9233c8c19d36cce1b001a923144716535c761a600ed131249003938c889a0171780b8a406b5a035ab01a95b3248d6523e01c9481a1680d0ac04825c41a400e921d848003928c009200e9115c08805c5e02e2901ad780d6a58f34ac21a365896b2a4ac03a4a01d234784f61a26b9412a01c94e4c49807242e305a5682b0120b40904b0e35c761a66389232226808834c111a63cd431c6992634001d280168d3166a124124c61ad628d5b1269d8834202d2f61c96b0c4ac05a5201d2700e909d847d2623d8e89ec304d5c40b4ac05602416812094078a0f035cc21206048c30449924238931a4604d12384b980124 12 4095 5 31 11 2047 21 2097151
def cc_35_13 : Nat → List (Nat × Nat) := unpackCursorV4 0xc701c602c483c284c280c280c084b98e98c287a27c966ba260964ca829c6201320001f811f801f801c07170a1485148014800e8c0e800c050c000b8103900007 0x2cc150090b8b204401d2a0164900904803c500351a01a4d00f249ba350dc92801654162089c0460df9b001ad137c4d929268de9326f09800b4b9bb254034a201e4d007251b81245802a00f17c078bc03c5d035aff20d6f4a6b206b57e39a9f14d440b69e06b4b035a3816d0c0f4bfc425ba112c81e95f864a7c125102d2781e92c0f48e05a4303d1f81a8ec0d46fb723302caf8165780b2ba0594f02ca700e52c072920394302ca100e506f827e0393b0349d01a4dc0d26c039338f89780e4ac0f2540792703c9300e48c110be0485d0442b8121540b09e0884d7202502211d7008c08845578220220fc0d06e0882f03c1380e07c1102e05b4f02da5816d1c0b68605a4f02d2581691c0b48606a3f0351d81a8dc0d4660394f01ca580e51c072860393f01c9d80e4dc072660392f01c9580e49c072460584f02c2501611c0b08c0683f0341b81e0bc0f04e0381f01c0b81693c0b49605a4702d2180e53c072960394a01ca3816518072860392f01c9580e49c072460584f02c2501611c0b08c0782f03c1380e07c0702e05b4f02da5816d1c0b68605a4f02d2581691c0b48606a3f0351d81a8dc0d4660394f01ca580e51c072860393f01c9d80e4dc072660392f01c9580e49c072460584f02c2501611c0b08c0683f0341b81e0bc0f04e0381f01c0b816d3c0b69605b4702da180e53c072960394a01ca3816518072860393f01c9d80e4dc072660584f02c2501611c0b08c0683f0341b80e07c0702e05b4f02da5816d1c0b68605a4f02d2581691c0b48606a3f0351d81a8dc0d4660394f01ca680e52c0728e0394501ca180e4fc072760393701c9980e4bc072560392701c9181213c0908e048430241f8120ec0906e04833024178120ac0904e0482301c0f80e05c0702605c5f02e2d81715c0b8a605b5f02dad816d5c0b6a606b4f035a581ad1c0d68603a5f01d2e80e96c074b403a5702d2b00e9540749e03a4b01d2380e90c0747e03a3b01d1b80e8cc072be0595e01cae80e53c0d29c0394dda8a600e52c0728e03945da0a200e50c072840393f03c9f00e4f7662780393b01c9b80e4d7642680393301c9900e4bc0725c0392d02c2f8161680b0ae058560342781a11c0f07e0783701c1780e09c0703e0381d01c0d00e05c0702c04815d880a0171780d8bba445502e29016d340769403b4602da280ed100d473962310349d00e4e40d26c039310342d01a1580907a0483503d22016d380b68407a35d60956ac4980d094068460362eeb8d740b69c05b42d6928ea8940072a20485d0342501a1180d8d9a2464bf1ae016d300d26806b56d11aa81ad3b4e69ba62399491881a4d80d26a0685a0342b0120f40906a03c68d222c016db3446b006b5001c946891780d8ba03b5901da881ad240d68387259d092880e564072a20694dbe8a2812174090aa0684a0342301ad63186919625003d2661c9200f48929240 16 65535 7 127 11 2047 21 2097151
def cc_35_14 : Nat → List (Nat × Nat) := unpackCursorV4 0xbb83b709b700b681b484b480b3829b31882667c167806701618b5617560056004b164b004b004a813f96203f1d851b051b0011140e850c050c00021401020002 0x784d100392877c491e945400e8e1e623401a5b1e21643c45715f14c3b04f1de014770931db4542089709724c0120d1d94540120b007c5e01b16c06c5301f14806b5e01ed6c06b5301ad4a0534401a97c05a5e81096e0225a80495dfe25601a94c05a5201a57dd215b6dc55c0695365c53d9214d5d05156914352c4fd4613d43c4d4fb1337ec4bd2212d7d84ac039297c049deb12577448c0392101a17ce605a33015cba05627013c8b03f7680bc0482d76009c0482516c07c2101700ed3c04b47012d0c05a4f01692c05a4701690c04a3f0128ec04a370128cc0594f01652c0594701650c0493f0124ec049370124cc0692f01a4ac0692701a48c0584f00e12c0584700e10c0483f00e0ec0483701a0bc0382b01a09c0382301e07c0381b01e05c0381300f17c03c5e00f17405b5f016d6c05b57016d4c05b4f016d2c06b49016d1c05b43016d0405a5f01696c05a5701694c05a4f01692c07a4901691c05a4301690406a3f01a8ec06a3701a8cc0395b0165680395901655c0595600e54c0395101651c059467445140693f00e4ec0693700e4cc0792f00e4ac0792700e48c0585f0161740585a01615c05856022154b905401613c0484d01612805847016118048457581100683f01a0dc0782f01e09c0381f02205c0482c01b15006a5401e91003a387508d1d015c734531cb13c00e4e1d313400e4c003c5e00f17406b5901ad4407a5901e9440595e00e5740594e00e5240394200e5040393a01a4d80392a01e4980485d0121540584d016128058460221140884401b16806c5601ad6806b5600ed3803b4d01a925d024173c8e5cb23100e5240394100e4e80393900e4e00393101a16806856022134068450120f40483500e4a007b5a01ed5807b4e734d0807a5a01e959cc24e72c90803a3e00e8f40393900e4c40392a00e4a40392800e4840785a01e1580883d01e0d40482d01209405c5f01b16c06c5701714c05b5f01ed6c07b57016d4c07b4f01ad2c06b47748d0c03a5f01697803a5d00e95c03a5500e94c03a5200e93c03a4b00e92803a4701a91803a4300e8fc03a3b00e8e803a3701e8d803a3300e55dd115600e5540394f7385380394b00e51c0394300e5080393f7284f80393b00e4dc0393300e4c80392f00e4b80392d01617ce505a02215c0885602213c068470220fc0783700e0bc0382700e07c0381d00e05c0481501b1b1a74605f4d50069342dc151a746801b190069440164d0b605401b16806c5600ed6803b5601ad39a734d01a925c02417188e5bc2315f8534069450164f4069360164d40593401a168068560120f40483501edb143360480950079242d41514336801ed9007934016490b405401ed6807b5601ed39bf34200e96803a56708939bc24201e8f94323d4844f4079350164b4079260164940592401e168078560120b404825016511ba1240164d1b9124 16 65535 7 127 11 2047 22 4194303
def cc_35_15 : Nat → List (Nat × Nat) := unpackCursorV4 0x8d04602282fc67e03f01e84f016c33601b00c84640310550ea4152029013844952400d145842c00e206043001410418104080001 0x80117806c5d016d7807b52016d3806b49016d0806b4101697806a5201693807a4901690806a4101a8d1ff15d00e565bd15500e5440694d6ec5159513d01a4d54912d01e4940485d0121540684d01a12806846334114bd0447f4931fc4544d09718824c00e8f1f713848c4d1fa24c7e4531e71247e11519425c520931f723c00e8c10a1347d4d31f414c7a0481f203c7c8d11f345400e8f19315c51c5312312c798481f103c0120b1ed0540120b005a5e7bc969bd256016949d415a6e05598014e5a85092b13e3f04c92312e3b04b4e705a2ec159ee02e0120b40482c012095ec022174074220157a08d00695c794551ea14c784051e4144780051e834478c551e712c77c051e41247908d1e534400e4a1e3124780491e0234 13 8191 6 63 11 2047 22 4194303
def cc_35_16 : Nat → List (Nat × Nat) := unpackCursorV4 0xf601d55faa0724cd5bd916b008d99aa5394a02940524195bd0d799ff2fd0533296410c81b5931165048a00128620142764423080104ae021c0208001 0x16d3c07b4b01ed1c05b4301690806a3a01653c0794b01e51c059438a44fe2813b8984de201335444b40584f01e1280784701e11a1f03f8780dc6d01f0cc05c07c5d00f16407c5500f1461c359670d440794a01e5180485d0121540784a01e11807c5d8b0d722a351874d4005b4f01ad2c06b47016d0c05a4201a8ea1b15d00e5440594f01e52c0794701650d9b13f01a4ec069375b44cd4f12d0121740584f01e1280784701e1189e03f01a0dc6b01f0c405c05b4f016d2c05b4701692c05a4301a8ec06a3301653c0594b01651c0594301a4fc0693b01a4dc0693301e4bc0792301613c0584a01611c0584601a0fc0683701e0bc6a01f0c005c05a4b01692805a4601690c0594f01652c0594701650c0792f01e48c0584f016128058470161180782f1a407c2f017016d3c05b4b016d1c05b4301692c05a4301a8ec06a3300e53c0394b00e51c0393f00e4ec0393700e4cc0392f00e48c0584f016128058470161180683f01a0dc0782f00e07c03817016d6805b5601ad3806b4200e96803a5601a93806a4201e8f807a320165780595a0165580595201a5380694a01a5180694201e4f8079320164b80592d016168058560120b4048251a00742d0158508c005b4f016d2c05b47016d0c05a4b01692805a4601690c06a3e01a8ec06a3301a8c80594b01651c0594301a4fc0693b01a4dc0693301e4bc0792301613c0584a01611c0584601a0fc0683701e0be1501f84c05c05b4f016d2c05b47016d0c05a4b01690c06a3b01a8cc0494701250c0493f0124ec049370124cc0492f01248c0584f01612c0584701610c0683f01a0ec0683701a0cc0782f01e08c0481f01206c0481701204c05c5f01716c05c5701714c05b5b016d6805b5601ad3806b4b01ad0c06b4201693c06a4e0169361924c01692c05a470169161824401690c05a420168fc07a3e0168f40595f01656c0595701654c0694f01a52c0694701a50c0793f01e4cc0592f0164b40592b0164a80392985c4a00592701649a161258484900592300e4840585f016168058570161580684f01a11c0783f0160bc0482d0160a805827016098048258440906601f0b005c07c5a01f15805b5e01ed6807b56016d48ec34e3b4d080795a01e5599114e5b05080785a01e1580483d0120d406c5b01f16807c5601b14c05b5e01ed5a0d34e01a9480695f01e56c0795701a54d9a14f5ac50c0393983c4d54d12d01a17c0785a01e15c0785627413c0483519007c2a01701b14806b5201697806a5a01a95805a52594534ee13d3b04b4039294284940392101a168068560120b40482501ad6806b5601697806a5a01a95805a523b08f8f023201a568069564c44f8fe13201a168068560120b40482501b14806b5b01ad6806b5601ad4c05a5e01a95a0d23e01a57c0695b01a55c069536605354c13f3f44cc039298304940685f01a1680685701a1588c03f0120946201f0a005c05c5e01b16806c5601714806b5a01a96a0623001a168068560121340484501b16805c5201ad6806a5a8148c00695f01a56c0695701a54e0a14d00e5040685f01a1680685701a1580484d18007c26017016d3805b427d44f60813501a12806846016d3805b4201a92806a467d48f5f92357e84a9f412601a12806846016d0806a4f01a92c06a4a01a91c06a4601a90e0723d01a53c0694b01a51c069438184f5fc12f7e04adf31277a448c0684f01a1280684701a119db02f76409c5e01f09405c06c5401adb20036401e97006a4c0168f00482c01717805c52016d7805b5201ad1006a5680095406a4e01e93406a3e01a8f59614d01a5154a13d01e4d52912d00e4a60312500e4840685a01a1580482d01209407c5001ad4006b440169b20025801a940c105401ad10be044 15 32767 6 63 11 2047 22 4194303
def cc_35_17 : Nat → List (Nat × Nat) := unpackCursorV4 0xd8afb1034a661deb6b55c4684d499c930126024a0c1de74bcabf93682117343833d452509c2082e0f041a103400506080810001c1038006040228001 0x16d0805a4f01a92c06a4701690c07a3d01653c0694b01a51c059436a84f64a12f9244ae4712790448c0584f01a1280684701a11a4002f8fc09c7901f0fc05c06c5d00f16406c5500f1463d25955c9440694a01a5180485d0121540684a01a11806c5d016d0a4d25c92c9463e25001693c06a4b01a91c05a4301e8f63c15d00e5440594f01a52c0694701650da913d5584bc0792b01e49cff1230121740584f01a1280684701a1188d02f01e09c7701f0f405c05b4b016d0c05a4f01692c05a4701a8fc06a3301653c0594b01651c0594301a4fc0693301e4bc0792b01e49c0792301613c0584a01611c0584601a0fc0782f01e09c7601f0f005c05b4b016d2805b46016d0c0594f01652c0594701650c0693f01a4cc0584f016128058470161180683f1d407c3b017016d2c05b4301693c05a4b01691c05a4301a8fc06a3300e53c0394b00e51c0393f00e4cc0392f00e4ac0392700e48c0584f016128058470161180683f01e0bc0782700e07c0381701716805c5600ed6803b5601ad3806b4201a92407a4101e8e407a310165780595a0165580595201a538069420164f80593d01e4b80792a01e49807922016168058560120f4048351d0074390158d4d0005b4b016d2805b46016d0c05a4b01691c05a4301a8fc06a3301653c0594b01651c0594301a4fc0693901a4cc0793101e4bc0792b01e49c0792301613c0584a01611c0584601a0fe3602f8d009c0781f01e05c05b4b016d0c04a4701290c04a3f0128cc0594f01652c0594701650c0693f01a4cc0492f0124ac0492701248c0584f01612c0584701610c0683f01a0cc0482f0120ac0482701208c0781f01e06c0781701e04c05c5b01716805c56016d3c06b4e016d3405a5f01696c05a5701694c06a4f01a92406a4301e90405a3f0168ec05a3a01e8e63a2380168dc05a368e48d005a330168c40595f01656c0595701654c0694f01a50c0593f0164f40593b0164e8039398e04e0059370164da371358cc4d00593300e4c40792f01e4ac0792701e48c0585f016168058570161580684f0160fc0483d0160e8058370160d8048358c80d00782f01e09c7201f0e005c05c5e00f16803c5601714806b4901ad0405a5a01a8c80595e0165480693a01a4d80585a0161580484d01211404b4f012d1c04b4301693c05a4b01691c05a430128fc04a3b0128dc04a3301613c0584b01611c058430120fc0483b0120dc0483301a0bc0682b01a09c0682301717805b5f016d6c05b57016d4c06b4901696806a3201657c0595b01655c0595300e5263014501a4fc0693b01a4dc0693301617c0585a01615c058560121162f04401a0fc068371c007c3601701717c06c5b01b15c05c53016d7805b53016d4806b4b01ad2806b4601ed0c07a4f01e93806a4b01a91c07a4380890805a3f0168f805a3d01657c0795b01e55c0595367c53c0694b01a51d7114301e4fd5513d01e4d40793301e4bd4212d01e4ac0392901e49c0792501e48c0392101617c0785a01e15c0785628413c0684701e0fc0782f0120b4078270120946f01f0d405c0594f01a52c0694701650c0584f01a1280684701a1186e01f0d005d701400120f005c5e01b16806c5601714806b5a01ad5805a5201a9219e14d01a524069455bc5059c13d00e4e62b13500e4c55412d01a16806856280134068450120f40483562c8e15323c01a4f2251305484b22704c890512220148904d2221348949100595c88c5516213c8840509a238 15 32767 6 63 11 2047 22 4194303
def cc_35_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x26d0845da1c33d4a4a27084170f043420d00283080820007041c006040450004000 0x5c5e00f16803c5601714805b5a01e92407a4101e8c40595e0165480792a01e4980585a0161580484d01211404b4f012d1c04b4301653c0594b01651c059430124fc0493b0124dc0493301613c0584b01611c058430120fc0483b0120dc0483301e07c0781b01e05c0781301717805b5a01697c05a5b01695c05a5301e92407a3101657c0595b01655c0595300e5265114501e4bc0792b01e49c0792301617c0585a01615c058560121165004401e0bc078271f007c4201701717805c5301714805b4f016d3805b4d01697c06a5b01a95c05a5301a93c07a4d01a91406a4301a8fc06a3b01a8e406a3701a8ce0223101657c0695b01a55c0595301a53daf14d01a5140694301a4fda513d01a4ec0393901a4dc0693501a4cc039315684bc0792b01e49d0312301617c0685a01a15c0685601a13c0683f0120f4068370120d49002f01e09c7b01f10405c0593f01a4ec069370164cc0583f01a0e80683701a0d87a01f10005d021300120b005c52016d7806b5a01ad5805b5201ed3006a5a01a959ad14d5644f40793901e4d50113155c4b4039299304940392101a1680685623c0f4078350120b4048254e4931ac24c01e531ab14c9184824803c91451243014914492431249188d00595c910550f614c9080508724c 14 16383 6 63 11 2047 22 4194303
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_35_18 (Nat.sub p 576)) (cc_35_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_35_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_35_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_35_14 (Nat.sub p 448)) (Nat.blt p 480)) (cc_35_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_35_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_35_11 (Nat.sub p 352)) (Nat.blt p 384)) (cc_35_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_35_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_35_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_35_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_35_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_35_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_35_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_35_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_35_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_35_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0x25028b28044005a7802d2e3c4b9261258f128c7e4be3f2572403c8fc93c848d2452492115490c924840523f2471f82f8fc13c789423d4b31e15d005a3c648e232469191388c89ac680be356811a0278c89a4640d001687179458bc2200293c014970db5c8ac9ac36d461e27f0f13b89c2643c4de2148912134884aa4444d2210290f1338781fc3c0de1b6a10e35986cae80291e1149908a44844944224961303f0a23084c0bc224921104800a4383c9a8028fe0c47d061250051dc145340146f041358191ec0c4f5d8688ec25b80c92bb0969d84aeffc5e7fcaebb0959fd498fe45476097bf2931f9298fbc547dd1e3b04adf4698fa14c7c62a3e4d11f1078ec1277b12d3d80b9ed0a8f602276092bd4531de8a8f3b4479c963bc8d1e3688f223478c923bc591df688f023477c923bc051d8246ee24c76e2a3b00bdd98a8ec02700519bac1100129ee9a3474c9a394d0dca2ace7a4173d1cb94539cb684e5a4e72d213944f801296dbb5b6dda9b8c8e5b76a2dba5b6dd29b84939b74a2dc4606e1b03709b1b84c8dc2606e12a372d41b94a0dc1246dd1980251db1298d89446c49e3624d1b1028009435f22d354d75aa4a2d592a6ac933549417c8acbe35b699a6b4c8e57c6b4d24585f1abb43179a14a2be3565f12db391819c6d8ce3605f12baf893d9948cbe2495f121b26969934acc992a64c932f890591268be23f639a831cd317c476c335a62da830cd598669cc33426192d30c9597c472c22405f11bb0493180688c01245f119afb1817d6a8be1570049faf04f978278bc1340049dae69057549ab9a315cc260024dd5c6b6b82445ba302dc5b15c6aeb6244571a7ad48d15c686b3a5159d22ab855965482ae14e575ad2c4d415d6acaeb4e575a12ba9695d4acae13e00499a2f16d576c0aba6c55d3022f15d176b4a83515489d2a44d9506a0a825d45dab29c8d51769c8bb4b45da1a8e969474aca392a51c9322ed09174b6a1a4e50d1ea2e969416b08ba574fa2f27cd45174ac9e35045d27a69169394a09a4564d1ad268d59344929a24145d27262d71312488ba4b4bda022e91d2d49895b544ac9222e90d234b491a5648d26a468f5242989213c48c9322e909206c09025445caba38d411c6908e25c45ca7a30d41186808c24c45ca38024bd1329c8994c44ca20024ad056848823d41521218d410c4a086248414a7a0ed410768083a5041d2020a51d05078009273ae2da048d1006c08016c3ae2b9fc8d0eb6967e2343ada19f2d44f968a759563c22d1ec940f08ac7835a3c1ab1e0924f0482782393aca71d8d08ec49c762423ac9f00248c0109e7402c39c929b08ccd82966c147389209c48e4d827e7013e360999b8d08dc49c6e242360979b4538d82466c046004251ac8e4cc6a26a24e3312899b180cd6c066a6c33c9219a980cd4a866233004239944a4a54866413e294a1976d48bb4a45d95e30c0a176548bb28a5f2322f89917c134bb2885e1502ec0a94a48ca507a528372c12596090cb0296581432c4ae162550b1028581232941a95c510ac2625612929417954510a64645313e29ca214c4c8a503e0084628d28928d58944b64fc6027db612895c9449e4a243255ad134d40956ac4ab4e255a112a968954ac4a2390041f9249040106e40c5b239b011c9b0818ae40b4b205a1914d44814ac4145a21d28105158826b441356209249049048149c0082f1fda100209c7d2a822c5f1162d8f0db0786c03c16c1162b8e6d207368839a441cca208b14c712a822b5f115ad8d91b06c8c03616c115ab8ced70676a833a3419c9a08ad4c6528822b4f18c9a08ad2c612b822b4717ca60b91505c4682e134115a18b2d44594a2229561422d0ac940508ac2835a141ab0a09245048228239114a708cd684d6a023356119a708cd08464b4232561192708c9084527c0081f10d2c00517c028b61f36c0f9b007c980028ae1cb480e5a207292039288014530dd2c004d7c026b61946c0ca30064980026ae16b5c0b5aa05a8e02d268013530ad24004d3c294700134b09d28004d1c228a8123440891c0444d00268610238074a703c9301d27c0125a04a2f032d101948809452049a6824d14122b40a250048ab0244f80248401b5e039a201c8d0036a401b4a00da3006568096a00195600ca7008d10054680215400ca10048c80102e0001f 10 11
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

def m_36 : Nat := 0xff00ff00ff00ff
def s_36 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_36 : Nat := 0x1500170037003f
def ep_36 : Nat := 0x22002800000002000000080000000000000000000400060004000c00100012003200300015001400040000
theorem epk_36 : ep_36 = edgePack 0xff00ff00ff00ff g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 5, g_14), (m_16, s_16, 5, g_16), (m_20, s_20, 5, g_20), (m_28, s_28, 5, g_28), (m_3, s_3, 4, g_3), (m_10, s_10, 4, g_10), (m_1, s_1, 4, g_1)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_16
  · exact lb_20
  · exact lb_28
  · exact lb_3
  · exact lb_10
  · exact lb_1
theorem sub_36 : ∀ b ∈ bds_36, 0xff00ff00ff00ff &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_36 : Nat → List (Nat × Nat) := unpackCursorV4 0xc1 0x1fffdfdfe61f 4 15 3 7 6 63 9 511
def f_36 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 1 bds_36 (dagTraceF m_36 s_36 6 f_36) (cur_36 0) s_36 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36 : treeBlockF 0 1 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 1 (dagTraceF m_36 s_36 6 f_36) cur_36) = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 1 (dagTraceF m_36 s_36 6 f_36) cur_36) i = true := fun _ h1 h2 => treeBlockF_at nb_36 h1 h2
theorem lb_36 : LowerBin m_36 s_36 g_36 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xff00ff00ff00ff00
def s_37 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_37 : Nat := 0x100150001001f00
def ep_37 : Nat := 0xa000000140000001e0000000000000000000100040001000e0001001000010010000100150001001000
theorem epk_37 : ep_37 = edgePack 0xff00ff00ff00ff00 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 5, g_15), (m_27, s_27, 5, g_27), (m_29, s_29, 5, g_29), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_27
  · exact lb_29
  · exact lb_4
  · exact lb_5
  · exact lb_6
theorem sub_37 : ∀ b ∈ bds_37, 0xff00ff00ff00ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_37 : Nat → List (Nat × Nat) := unpackCursorV4 0xc0602e361924824102803883a01 0x526084c0fac435076806481520223034684530fa11e4f3c96791cf219d4f3a96751cea1d12f9256c49c491801f 9 511 4 15 10 1023 15 32767
def f_37 : Nat → Nat × Nat := unpackForestF 0x14bca57f50fa0149e48123051a2530a4601f 3 10
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 11 bds_37 (dagTraceF m_37 s_37 6 f_37) (cur_37 0) s_37 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37 : treeBlockF 0 11 (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 11 (dagTraceF m_37 s_37 6 f_37) cur_37) = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 11 (dagTraceF m_37 s_37 6 f_37) cur_37) i = true := fun _ h1 h2 => treeBlockF_at nb_37 h1 h2
theorem lb_37 : LowerBin m_37 s_37 g_37 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xffff0000ffff
def s_38 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_38 : Nat := 0x151700001f3f
def ep_38 : Nat := 0xa28000000000000000000000002000000200000040600000e0c00001012000010300000151400001000
theorem epk_38 : ep_38 = edgePack 0xffff0000ffff g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 5, g_17), (m_18, s_18, 5, g_18), (m_20, s_20, 5, g_20), (m_31, s_31, 5, g_31), (m_3, s_3, 4, g_3), (m_10, s_10, 4, g_10), (m_2, s_2, 4, g_2)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_18
  · exact lb_20
  · exact lb_31
  · exact lb_3
  · exact lb_10
  · exact lb_2
theorem sub_38 : ∀ b ∈ bds_38, 0xffff0000ffff &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_38 : Nat → List (Nat × Nat) := unpackCursorV4 0xc1 0x1eff5f9fc61f 4 15 3 7 6 63 9 511
def f_38 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 1 bds_38 (dagTraceF m_38 s_38 6 f_38) (cur_38 0) s_38 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38 : treeBlockF 0 1 (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 1 (dagTraceF m_38 s_38 6 f_38) cur_38) = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 1 (dagTraceF m_38 s_38 6 f_38) cur_38) i = true := fun _ h1 h2 => treeBlockF_at nb_38 h1 h2
theorem lb_38 : LowerBin m_38 s_38 g_38 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xffff0000ffff0000
def s_39 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_39 : Nat := 0x115000001370000
def ep_39 : Nat := 0x22000000000000000000000014000000360000010400000104000001100000013200000115000001040000
theorem epk_39 : ep_39 = edgePack 0xffff0000ffff0000 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 5, g_19), (m_30, s_30, 5, g_30), (m_32, s_32, 5, g_32), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_30
  · exact lb_32
  · exact lb_7
  · exact lb_8
  · exact lb_9
theorem sub_39 : ∀ b ∈ bds_39, 0xffff0000ffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_39 : Nat → List (Nat × Nat) := unpackCursorV4 0xc0602e361924824102803883a01 0x514041303c58845072403130534042303244213c3b4f3b4b3b473b433a42394f394b39473943a13f913b61371133001f 9 511 4 15 11 2047 16 65535
def f_39 : Nat → Nat × Nat := unpackForestF 0x93f24efc50e9009378d02230491113c24cc01f 3 11
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 11 bds_39 (dagTraceF m_39 s_39 6 f_39) (cur_39 0) s_39 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39 : treeBlockF 0 11 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 11 (dagTraceF m_39 s_39 6 f_39) cur_39) = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 11 (dagTraceF m_39 s_39 6 f_39) cur_39) i = true := fun _ h1 h2 => treeBlockF_at nb_39 h1 h2
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xffffffff
def s_40 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_40 : Nat := 0x1371f3f
def ep_40 : Nat := 0x1e0800000000003600200000000001040e0c00000000013210300000000001041000
theorem epk_40 : ep_40 = edgePack 0xffffffff g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 5, g_21), (m_23, s_23, 5, g_23), (m_25, s_25, 5, g_25), (m_27, s_27, 5, g_27), (m_30, s_30, 5, g_30), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9), (m_4, s_4, 4, g_4)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_23
  · exact lb_25
  · exact lb_27
  · exact lb_30
  · exact lb_6
  · exact lb_7
  · exact lb_9
  · exact lb_4
theorem sub_40 : ∀ b ∈ bds_40, 0xffffffff &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_40 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00b4eb40b4098e9809809809047ca64c4cc292033001 0xb251d239523139513941593d393959353931685d683d483968354831b451a24e5242895d892d39298925392148514831682d4829682548213928712448286024825e5252592d392959253921782d4829782548218a5e8a525a4e5a423a3d594e39423931782d4829782548216b5e6b524b4d7a397a31593d3939593539314841782e48226a5e6a525a4e5a427a3e7a32594e3942492e392d783e4832382e382d381e481938123811c34392434233894f3943593f3933312f3923684f4843203f4833782f4823381f481b10173813001f 12 4095 5 31 11 2047 16 65535
def f_40 : Nat → Nat × Nat := unpackForestF 0x351c8b43a8a34938521aa5e6248c0915290a33125e20fc40b801f 4 11
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 14 bds_40 (dagTraceF m_40 s_40 7 f_40) (cur_40 0) s_40 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40 : treeBlockF 0 14 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 14 (dagTraceF m_40 s_40 7 f_40) cur_40) = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 14 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 14 (dagTraceF m_40 s_40 7 f_40) cur_40) i = true := fun _ h1 h2 => treeBlockF_at nb_40 h1 h2
theorem lb_40 : LowerBin m_40 s_40 g_40 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xffffffff00000000
def s_41 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_41 : Nat := 0x115151700000000
def ep_41 : Nat := 0x1402000000000014000200000000010404060000000001101012000000000115151400000000
theorem epk_41 : ep_41 = edgePack 0xffffffff00000000 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 6, g_24), (m_26, s_26, 6, g_26), (m_22, s_22, 5, g_22), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_31, s_31, 5, g_31), (m_32, s_32, 5, g_32), (m_8, s_8, 4, g_8), (m_10, s_10, 4, g_10), (m_5, s_5, 4, g_5)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_26
  · exact lb_22
  · exact lb_28
  · exact lb_29
  · exact lb_31
  · exact lb_32
  · exact lb_8
  · exact lb_10
  · exact lb_5
theorem sub_41 : ∀ b ∈ bds_41, 0xffffffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_41_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x96012c02521ca4094811a3e340460281ab03020213b157600ec01d21ba407384d255a4034806786cf019a12e153dfa7224e209b4427bc1ad402c8001 0xe8a600e49009028203520f9a100e9383048403a3d0f0af0705483629c1a14201c9e80e4a80b09c1204202c1e812074160600682804e2900e978134a403a3e0c11900e5342e27c0493201c970124b4130b40585602c1f0280c80705c0482d0240f0160640902404811024080441000d07009b5201d2f0269480749c152420a0a70125080727a0392e024968261680b0ac0584e0802100e0b80905a0481e02c0c8120480902204810088a603c0f0090200f0300241401f148074bc07a5201d1f0488c80f2b40395601c9f0404c80725c0392d02c268380f80d0640382e0341680e078070320381203408812040162780904c024080241000907007b5201d2f01e9480749c0c24203cad00e5580729c0a14201c9700e4b41009c0684202c1e80e0b80d05a0381e01c0c80e0480d0220481003e2d8c514c0f6b62f353169a180e97c074bc03a5b01d2b80e94c504a403a4f01d2700e90c4248403a3f01d1f00e8cc324640395f01cad81e568072ae0395601ca980e53c0729c039430b0a100e4fc0727c039330989900e4bc0725c0392d02c2f81616c130b40585702c2b01614c0b09e0584e02c218341080b07e0583e02c1981c0c80705e0382e0241680e07c0703c0381b01c0c80e04c0702405811010080128e0074680693802c9a00c49011078048380441a0120c0110280412801c920220b00904007b4b03da181e92c0f4860323301ca780e538072960394701ca181e5080727e0393301c9780e48c0909e0484b0242381210c0907e0883e024198120c80905e0882e024118120880703e0381e0240e81f16c0f8a607b5b03da9814d0c074be07a5e0252d80e95c094a604a5201d2781290c0747e04a3302caf81e5780d2b605957034a981a5480b29e0694302c9f81a4cc0925e0492d01c9580e4a80724e0392602c92808490090be0785e0242d81215c090a6048520242782213809086048420241f8220f80906604832024178120b80905a0381f01c0f00e076b26974c343a4125ccc90dc6466e114f6b8a5b0c51d6e286aa13f54099a684bd2e2469504f458259dc11cd60865e03f2c0199280bc860463b01f1980d81805c020260001f 15 32767 6 63 11 2047 21 2097151
def cc_41_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8901110602832786402c0218002c105800af053e819f833805a34b40134d25063f2c7818e431c8039002d185020a00140028004430880023c0010000 0x1c1209b52134bc26949f1273d2420947a2253824a10493109242161784c290583d0705a0e0681c0b07c5b138a61ed6c4da9c1343074be1296c252d03a570f4ac1294c1d2788a4e09486129081d1f88a3e09466128c824af8995e092b61255c24a9849520929efc53824a1849420927ef04f82499849320925e124b824968585f0b0bc1616c2c2b85853130a41613c2c218583f0b0660e0ac1c15058290704e0e0982411848210702e0e0581c0a84820094700e8d02c9e069306a0780e0e1d01a038300f8a41ed783da903b4d70472d48c41caf079520729a0e4f43420848311105c1a0882c0e83815072481ed483d2f07a526c49cd49081d1e8395e0f2a40e4f41c968884e0d0841a0c424108581d0702a1f16c3e2987b5b0f6a6e4d0c1d2f83a5e074b60e95c1d2987a520749e0e90c1d1f83a330b2be1a56c34ad059570f2ac1a54c2ca78894e0d2861a5082c9f8893e0d2661a4c81c978392e0b25a0e49c1c9283923072440e17c3c2f0385b070ae0e14c1c290384f6e09c0e10c1c210383f6807c0e0cc1c19038270704c0e0941c0f8481e0703ab0981392803a4c644900e911192009950092900e5103c28068480b0881e04159302024007478c08e01d1a1c23013280124e01c9a078400d070160d03c0803924080401205131281f24007478b88e01d1a1a23007278124c02c1e0683006020269403c2807820134801e1003c1007c59588a21ed6559a883a5d074aa0e9384d2103a3e134640e5781caeaa14e46284a44f8e0990392a0724c0e4941c920585d0b0aa161383c210583e0f0640e0b81c14838220b0421e080240e858160902a120501d2205844482780e490240a274524c6820e9341d1f152324a2bc8c5481ca6a213e342640e4a82c268583e18064120741d1a05834 15 32767 6 63 11 2047 19 524287
def cc_41_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x96592a0a54047cb8e850e3dc36b8017000d725ae0328d6500ca01920aece5d02ba01548274d38d86f08de0190b2b9a55088c7866d0c0210202000010 0xb6bfa4d782dad85b570b6a616d482da687a5bcc4a6168ef111c85a330b4622257c3cad87957112a6164fc1c9e8593b09272164dc1c9a8593309262224bc44918585f0b0bc1616c2c2b85853be0a4161042c178582e0b047180882c0f8581b110341605c2c0b058132224812112e92e101340d25016492d0260483c07068120b034145c024090400e4d0781207c520f6b41e9783d2906a3db42620e4b4249483925092421e1783429068310d034380583e2907b5b0f6a61e97c3d2d87a570f4a6228fed9198595f0f2bc1a56c2cab869530d2a4165342c9fcb13e0d2661a4c82c978692b0d2541649c6893069230d0be1e178342d868570d0a61a1482c268683fb207c1a0cc34190682f0905c1a0ac1c15068270704c1a08c241106a34ae69148972812605a48ac488169003c280584c0d080171782e2ed4349a06820e53424a48394509282161742c2a8583e0f06416084351c52452a26bd40d482da68894d0727a124e41c9a849310b0bd381482c268881a0b02c22052712705a420b47a124a424908585e0b0bb341383421058260d04a1a0741c0d038160d02a220503e2907a5e0b4a4168f41c96839250f0bc1a1482c26858260d04a0e0681c0b07c5baa8a61697e992f05a5b0b4ae1694c2d2905a4f9e49c1690c2d2105a3d112be1e56c3cab889531129e2250c2c978392d0b256124a42c93839250b246124842c2f8585e0b0b61615c2c29cc0520b09e161382c21cb0420b0621607c2c0d8881a0b02e160582c098b1240906924930509a069280b24914170241e03834090581a0a24012048200f6bc16d482da687a520727a0e4d43c2f068520b06c1a0d42c168381a0702c0e510481207c5a0f6bc1ed4835a687a528a2820e4f4249c83935092621e1783429068410d034200583e2d87c530f6a41e97c3d2d87a570f4a62293e39218595f0f2bc1a56c2cab869530d2a41653e30a7069430d284164f42c978692b0d2541649c3893069230d0be1e178342d868570d0a61a1483427c404e0d0861a1082c1e8682f0905c1a0ac1c15068270704c1a08c24110492007478128c1e89e0493884268124c0341c05834138a426d784da904b4d80472f48c424a0849311125c124882c2f098520b09a0e0f41c0d03816 15 32767 6 63 11 2047 19 524287
def cc_41_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xf403cc1eb23ac0de37702cd3ed19b402b08ac0280ca0028009432500824a0026860df13700a8d2904a40202480020007c111384011000010 0x5824804607f3607e26c7d2607b16c79160068280582403a3b03a330393b039337b1230383f0383b03837038330582f058230581f058130682805824792330493f049330492f049230583f058330582f058230481f0481b0481a048170481604813893518635084251812507c2330395d7a15c04951781500893f089330892f089230585d058410583f058330582f058230581f0581b0781a0581705816058130593c069307103c0683876034068306f02c6d02407c5205b5206b4d74239712310393d049390393504931068414d02e0682207b5205a527224e7124206a3d0392d0492903925049216004e068420683107b4307a436f2330494f049430493f049330492f049230584f068430583f068330582f068230481f0481b048170582c0682007b4307a436d2330394f039430393f039330392f039230584f068430583f0883e06833068320582f0882e06823068220381f0381e03817038130381207c5307b537534307a5f07a5308a4f09a4308a3f09a330595f0595d059550594f5f14e06943069420593f4c13e06933069320592f0992e0692b0592706923069220585f0585e0585d0684f7304e06843068420683f7003e06833068320682f0482e0682d6e02c0682b0382a0682703826068256c024068230482205c5e05c5d6a249632410394d0494903945049410585d05855058310582e0782206b44653486825c05a4c632486724405a40078300582c0682006a4c653526425e6325205a3d0893d0392d0492903925049210585e610520583d0881a058160881405b4d6123905a3104939049310585e0585d05836068356002e068220681d0381a038160681508814 14 16383 6 63 11 2047 20 1048575
def cc_41_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xa28345026a84a0d7e58ef35c07aced568c80b50001e863d007a00dc61b8037006b0cbe6129525003c387800e8213a6270032706400b84044c0410002 0x88149e24e03a4203a3d0395e0395d9d14e04942039260492506829038210481d0481a04816058150881409c5209a5e03a5203a3d0995e049520394d03926049250382d058250481d0581509c5ba545303a5fa325e03a5b03a5703a5303a5203a4f9f24e03a4303a4203a3d0395f0395e0395b03957039539c1520394f0394e039439b142039310885f0885b08857088530884f088430382f0382d0382b06829038270582503823038210381f0881d0381b03817038150381309b5e03b5203b4d09a520995e0495203936049350392d0383d058350481d0581509c5a09b5e09b5204b4d09a520995e04952049415d0410583d0683905835068310481d1401509c5b09c5309b5203a5f09a5e04a5b03a5704a5304a5203a4f9924e04a4304a4203a3d0495f0995e0495b0495704953049520494f9814e04943049420393d0885f0985b08857098530884f5b0430482f0482d0382b0382713025048230481f0481d0481b068190481705815048130481105a5c07a5807a5405a500582c0682005c5f06c5e05c5d07b5305b4b07b4905b4305b4107a5305a4b07a4905a4305a41962330795f079530594f0394d0594b04949059470394505943049410893f089330892f089230585905853058510583f0583e05833078320582f0582e05823078220581f0581e0581b05817058130781206938059349205c8f04c8d03c9403492241912398d231099410393d04939039350493106841068310681a098160492803924068288f3428e24e8d242099310392d04929039250492106831068210681a098169334308a4f09a4308a3f09a330595d0594f069430593f069330592f0692b0692a0592709926069239004e8c03e0482e038260681e802418a2397d2310894d089410393d0493903935049310584d058410583d0781a0581606828058248823b872330893f0893b08937089330892f089230583f05837058330582f058230581f0581b0781a0581705816058137f3428524e7d2420893d089310392d0492903925049210583d058310582d0781a0581606828058248323f822330893f089330892f0892b08927089230583f058330582f05827058230581f0581b0781a05817058160581306828058240682805824 15 32767 6 63 11 2047 20 1048575
def cc_41_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x97012e02446488088250e09ecc31716280b8356e0adc05712ae015c02b414f9c9e053c023903158533c4d6894112801c2438003cd07800f001c0800e 0x9b5203a52be24ebd24204a3dac14e04942049310582d06829058250682107b4307a43bb2330394f049430393f049330392f049230684f038430683f068330682f068230481f0381b038170392c0492009b4309a43b92330394f049430393f0893e04933049320392f0892e04923049220384f058430583f058330582f058230381b0581903817048130481109c5309b53c134303a5f03a5d03a5503a4fab24e04a4304a4203a3f9c23e04a3304a320395f0395e0395d0494fbf14e04943049420493fbc13e04933049320785f078530884f078430883f078330482f0382b078290382704823048210481f0481d0481b0481a06819ba018048170481605815b8014048130481103c5e03c5db6249af2410395d03955039310392e099220584d06849058450684104b44b1348b425c03a4caf248b324403a40099300392c0492004a4cb1352b025eaf25203a3d0395ead1520393d0883d0582d0682905825068210881d038150881403b4dad23903a310395e0395d0393604935ac12e0492206839038310481d0481a04816058150881403b5fb535e03b5b03b5703b5303b5203b4d09a5bb225303a3bae23903a3303a310395f0395e0395b0395703953ab152039410392f0392e03923991220885f0885b08857088530383f0383d0383b06839038370583503833038310882f088230381f0881d0381b03817038150381309c5209b5a09a5e09a5204a3d0995e0495204931490310582d0682905825068210481d1701509c5209b5b09b5303a5f09a5e04a5b03a5704a5304a5203a4d03a3f9b23e04a3304a320495f0995e0495b0495704953049520394d0493fa913e04933049320885f0985b08857098530883f470330482f0482d0382b0382716025048230481f0481d0481b068190481705815048130481104a34a7348a225ca024c03a48a624403a40099500394c0494003c5e03c5da4349a03410395d039550393e09932039210584d06849058450684104a38a2452a135ea035203b4d0395e9e1520394d0884d0583d0683905835068310881d03815 15 32767 6 63 11 2047 20 1048575
def cc_41_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xce06703099840c205f8ecd93d59e0483a4011c27b9bd81b5cda06b12c4d584a8254029852d09603e69e08b5e299140062030000c 0xde241dd239d92310494104931078410583d0683905835068310481d07815049280682805824db342da24ed92420493104921078310582d0682905825068210481d07815df34303a5d03a4f04a4303a3f04a33dc14ed813e0492e0784f078430783f078330482f0482d0382b0382707825048230681905815cc241d6239c92310394d039410393d0784d078410583d0683905835068310781d038150492803924d423bd32330393f03937039330392f039230783f0783b07837078330782f078230381f0781d0381b038170381503813cb342d124ec92420393d039310392d0783d078310582d0682905825068210781d038150492803924cf23fce2330393f039330392f03927039230783f078330782f0782b07827078230381f0781d0381b0381703815038130492803924049280392403924cc460cb360ca26cc92600492803924c706cc506005a4b05a430594b05943c71230384f0384b03847038430382f038230381f038130492803924c52330393f039330392f039230683f068330682f068230381f0681d0381b038170381503813d5351d2350d0251cd250c82330395d039410393f039330392f039230585dc605c06851c40500783f078330782f078230381f0781d0381b03817038150381303a3c04a30bd13c04938c213404930bb018b901409c5203b5204b4dc0239bd231049419d12e049220583d068390583506831 13 8191 5 31 11 2047 20 1048575
def cc_41_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x8f063038c022828516083820204181020407c15ec17a05e027801c477005b436d01ac266158c3630188162018805d14e6433181ad0600006 0x440a3e0491fc0500881404496012481fa47804a3001c9a3f0061f602804a3c01c963dc481f025804a387b91a3d8571ea2980393c02c12016091dc050058247992e3c89300d478f1128780923b40e00b06808814770943a0090110280882c034103b44f00d26005834760163ac0900d4780582c738103a00b00d270e71347302e3941300b07931452969a94a897e524bd2425b8e92bc5094e084a4e215f6f8adb2055d822a6ff12f01c96be84ac09252f912701c92bd048c092429605f4982d9f015cea0a6ef02f02c16ba80ac0d052e902702c12b9008c0d0424101f1c80d8b405c0a02603a5c04d2c026950074a00392c0249000f17c098bc03c5d04da980ed2c1369203b4301da082694c0749609a4901d2180e905c44660395901ca980e5440727e0393e01c998264c80725e0392e01c918264880f0be0785301c2780e134070960684901c2381611407086038410441f81e0cc1105e0782301c0f80e06c070320381701c0981e0440947003a346f0ae36c531b2278e0134 14 16383 6 63 11 2047 21 2097151
def cc_41_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x8807887807617607607607607607606686606606225e25835805804e54e04e04834804804803e51741411210e20e0007 0x91a28488d42264d91b250908b64805823e0d91e0608e12e448db2366c91a25c8c9264604a22e249160288a812438492100490d1248381200e4921605106024870a64344f0092590a0180440a42c4a21424805824840a641c4f00d259060180440a44c97a244bb1124d8811e80e4b61e25404929024944304980724a03924024908160b61205406829034144140980b04a058240341080e49007248fe12801c9240c9720449804a3c7e89c00e4d20205100024 12 4095 5 31 11 2047 21 2097151
def cc_41_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xdc06e03683b01ca3e50300b704b805716988b665a024252008044001724b805c0262092840220010004100080000000000000000 0x21c4990824c889ae4f89b27a498099289e09201e0a2760493926c04d260128f013270039340251e02650007258099209b13601e9300d4780783802c1a01a8f00f0800582c03c105191668a8a743451969a150493e7e49d3a2438212102657c132a6b214f04ca18264c67025e0392d04c958124a66e24e0392504c918124840f0be078533302781e10c0f0633502f02c1681e0ac0d0533402702c1281e08c0d0420981f03c0d8bc05c0f02730352979a84c8d2a584bb23255024948124840d05206821024948124840d05206821982294bd1425c69b2b25d9112a8124a4092420682903410cb1182566c1282688913049517a248ba0394d024a480e514092820584d034248161140d0831c2540249400e4900d05005824941b649c9724c4992523c 13 8191 6 63 11 2047 21 2097151
def cc_41_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x952a1ce840de0c7801dc17605bc76f01a85661198061157443798dc0340ca8a1c38700190c58316003c70f003030c0000c 0x264c40725a0492901c928124840f0620582d034148160940d04346251ad11c8124e40726a0992f04c9181a0e40b06a0782f03c1181e07c0f0360781703c09d10d82646a1103409e9a94408f54e27a0392d0249480e494092425703d02c1681a0a40b04a068218691c41c8e2206915626ca012e0264a2aa24807828aa012548db0136b804b4c04ca400e510096980995001c9e0264c29e6d807b5c035a601e1200b08806b4c03c280160f00f0614a259a2929d0c946624835823bab91cd4c8ce084620995f04ca9826506a227e0393d04c9d8124e6a026e0393504c998124c54a25e0992303c2f81e14c0f0834e03f02c1e81e0ec0d0734d03702c1a81e0cc0d0625502f03c1182607c0f0363101703c09d2c918132a20785104ca080e4f409272039350249881e1040b07a0683902c1a81a0c6948a34924e04ca782650c092520392503c2781e10c0d0520582503c0f81e06c0f02e07813a39228264c40f063303509e9a45009725e6a14434aa112e826544132620785103c18d095825c6a111250a0229444d356829a0393d0249c80e4d4092626804d02c1e81a0e40b06a06831 14 16383 6 63 11 2047 21 2097151
def cur_41 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_41_10 (Nat.sub p 320)) (cc_41_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_41_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_41_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_41_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_41_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_41_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_41_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_41_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_41_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_41_0 p) (Nat.blt p 32)
def f_41 : Nat → Nat × Nat := unpackForestF 0xad23900b4ba6a3ba6a39aa26caa124aa024a6a33a936ca693fa6937a7b6ca683fa683700b43a5a46a4c51a4a4e00a4ba3a459a4599a453a234a9a451a15609a24fa04529a24e9da6c9da4c9d9249d8249a2439ca6c9a12f9a1279b26c9a02f9a02700a439934a7245297452974509734d7235295c6095b607225f7225e92b6c92a5c92a4c92a3c7225b8f4508f3508f16c8f1608f06c8f060722578e25c8ab648aa5c8aa4c8a9288a9248a8288a8247225382a5e82a5d82a4d82a3d8292a8694c8693c8292685128851248282a8314c8313c8301882826722528025c8024c80028800247212f7f0287da3c7d8187d8147212b721277c12c7aa347a95c7a94c721237825c7824c78128781247202f771287593c7582c758247202b720277402c729347285c7284c7202300a33712330094f701346c3436ea416ea396c14e6cb426ca4e6ca426c13e0094b6b2396235169a3b69a336235068a4e622516723f672336225064c6064b6064a6c64a6062233639236205c62a336205000947611345c343602395c14e5ea4e5ea425c13e5da335c0185ca335c014009435b24955b5e59a5c59a4455a5357b5257a5e57a5255a39562395612e559520093f5493e0093353348532444dc53523494da5e504525035e503524da4e4ea4e4e94e4d9524d9420092f4c24e4c14e009234b2330084f4a0344634348a4148a394604e46b4246a4e46a424603e0084b452393c35143a3b43a333c35042a4e3c2514123f412333c2503ec603eb603ea6c3ea603c2333d9233c15c3ca333c150008473b034363433a2393604e38a4e38a423603e37a333602c36a333602400843352492fb5e33a5c33a442fa5331b5231a5e31a522fa39302393002e2f8520083f2e25c2e0242ca332d1312c83e008332b3482b24425c532a34925a5e284522835e2835225a4e26a4e2684e25852258420082f2424c24024222432214e229412204e00823211341e343202391e14e1ea4e1ea421e13e0081f1d0341a3431c2391a04e1aa4e1aa421a03e0081b1924803c531823803b531723803b4314c5114b511494e1493e03a5211452113411115e1213c111521113e03a420d3520d3420d15e0e94c0d1520d14e0d14203a320ba320b93e039420a2420a14e03932072320894c07132078300703e03842042420593c04142048400404e0383200817013430212801a3301124008130001f 9 11
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 347 bds_41 (dagTraceF m_41 s_41 8 f_41) (cur_41 0) s_41 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_0 : treeBlockF 0 32 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_1 : treeBlockF 32 64 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_2 : treeBlockF 64 96 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_3 : treeBlockF 96 128 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_4 : treeBlockF 128 160 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_5 : treeBlockF 160 192 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_6 : treeBlockF 192 224 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_7 : treeBlockF 224 256 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_8 : treeBlockF 256 288 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_9 : treeBlockF 288 320 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_10 : treeBlockF 320 347 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) = true := by decide +kernel
theorem nj_41_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_41_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_41_1 h1 h2)
theorem nj_41_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join nj_41_1 (fun _ h1 h2 => treeBlockF_at nb_41_2 h1 h2)
theorem nj_41_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join nj_41_2 (fun _ h1 h2 => treeBlockF_at nb_41_3 h1 h2)
theorem nj_41_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join nj_41_3 (fun _ h1 h2 => treeBlockF_at nb_41_4 h1 h2)
theorem nj_41_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join nj_41_4 (fun _ h1 h2 => treeBlockF_at nb_41_5 h1 h2)
theorem nj_41_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join nj_41_5 (fun _ h1 h2 => treeBlockF_at nb_41_6 h1 h2)
theorem nj_41_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join nj_41_6 (fun _ h1 h2 => treeBlockF_at nb_41_7 h1 h2)
theorem nj_41_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join nj_41_7 (fun _ h1 h2 => treeBlockF_at nb_41_8 h1 h2)
theorem nj_41_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join nj_41_8 (fun _ h1 h2 => treeBlockF_at nb_41_9 h1 h2)
theorem nj_41_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := block_join nj_41_9 (fun _ h1 h2 => treeBlockF_at nb_41_10 h1 h2)
theorem nc_41 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) cur_41) i = true := nj_41_10
theorem lb_41 : LowerBin m_41 s_41 g_41 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def g_42 : Nat := 0x115151701371f3f
def ep_42 : Nat := 0x220a280000140200001e0800140002003600200104040601040e0c01101012013210300115151401041000
theorem epk_42 : ep_42 = edgePack fullMask g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 9, g_34), (m_35, s_35, 9, g_35), (m_41, s_41, 9, g_41), (m_40, s_40, 8, g_40), (m_38, s_38, 7, g_38), (m_39, s_39, 7, g_39), (m_36, s_36, 7, g_36), (m_37, s_37, 7, g_37), (m_33, s_33, 6, g_33), (m_26, s_26, 6, g_26), (m_24, s_24, 6, g_24), (m_22, s_22, 5, g_22), (m_23, s_23, 5, g_23), (m_11, s_11, 5, g_11), (m_25, s_25, 5, g_25), (m_12, s_12, 5, g_12), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_31, s_31, 5, g_31), (m_32, s_32, 5, g_32), (m_13, s_13, 5, g_13), (m_14, s_14, 5, g_14)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_34
  · exact lb_35
  · exact lb_41
  · exact lb_40
  · exact lb_38
  · exact lb_39
  · exact lb_36
  · exact lb_37
  · exact lb_33
  · exact lb_26
  · exact lb_24
  · exact lb_22
  · exact lb_23
  · exact lb_11
  · exact lb_25
  · exact lb_12
  · exact lb_27
  · exact lb_28
  · exact lb_29
  · exact lb_30
  · exact lb_31
  · exact lb_32
  · exact lb_13
  · exact lb_14
theorem sub_42 : ∀ b ∈ bds_42, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_42_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xd644cce6c16ebd11b892b316a82ca3d1996a8eea8e428d4483e680cc7bd4706e6c1167926216572c540c4f1442f136b12f9c22751cd615dc08b50394004d0001 0x885c0f0a81e0b0341203b5f076b60ed5c1da987b4b072be0e5781cad83953072a41a53c34a70694b0d2921a50c44a1069410d27e0e17c1c2d83857070a62213cbc268b84b1708e2e1144421a203f420767c0dcf0198681f1403a1a06c340b868150d0260f5bc1eb686c6f0d8dc1f1b435b11d3600d2de1a5b834b68395f072bc0e56c1ca9839520d29e1a53834a5869490d2862250834a08686f090da1a1ac2c3486867090ca1a18c2c308385f070b60e15c1c298884f2f09a2e12c5c238b845110861a07c480e8681b0d02e1a05434098795b0f2b41a55c44ab03947110be2216c442b888532109e4212c8423908430f03e1a06c340b87813072be0e56c1cab8694f0f2961a51c1c2f8385b070ae0e14c2c278584b0b08e1610c2c0f8581b0b02e1604c1caf8395b072ae1a53c34a68794b0f2941a51c44a306945070be0e16c1c2b838530909e1212c2423848430903e1206c240b84813074de0e9ac1d3386a5f0d4ba1e96c3d2d06a57114ac1a9541cb78396e0f2da6c5b034af8695e0d2ba1e4bc3c970792d070de0e1ac1c3383863110be2216c442b888530f05e1a0ac3413878230f03e120743c0d8781a0b032680603c0b878160902a640503c0985811114be2296c452b88a53092b62256824ab849560925e124ac2493849232b05e560acac13958230703e0f1bc1e3704c6d2e8d81317c2e2f04c5d072de0e5ac1cb383963112be2257444ad889572f2aa2254c24a78494d092961e52424a38694509286125041c3583867070c61216c442d04859090ae121582429848510908e1211824228481f090361205c240983a6f074d60e99c1d3188a5f174b62e95c45298396f072dc0e59c1cb183962092be2257824ae84957092aa1654c2ca90492f0b256164a82493979260b2460e19c1c3304857090ac121542c178782e0b056160a82c13868260b046160882c0f8581e0b03a2e550240a0895c0b2a816060240a03a5f074b60e95c1d2985a4b072be0e56c1cab839531129e445345ca58b9471728a2250cbc979412b2f24e4c48c1c2f8385e070b60e14c1c290484f0909c1212c242484843110841210424178481f090365e068240b84816090260f178362e869460d28a0e1781c290484e090921a10824208681a0902c131b8363683c5e0d8ba129888930049690d2c21a51834a28486e090da0e1781c290484e090921a10824208681a0902c0f5bc1eb684c6f098dc171b4253112260092de1a5b424b584969092ce1259424b187961072be0e56c1cab839531129e405345ca58b9471728a2250c24378486e090da0e17c1c2f0385b070a60e14824278484e0909612124242188842090821207c240d9781a0902e1205824098895f112b62255c44a99394f272964e51c9ca18585b0b0b41215c442b038470903e1606c240b85813072be0e56c1cab839530f29e1e52c3ca384943070be0e16c1c2b8484f0b0961211c240f8581b0902e1604c1caf8395b072ae0e54c24a78694b0d28e1a50c1c2f8385b070ae1213c24268584b0b0941211c4423048450903e1606c240b85813074de0e9ac1d3383a63114be2296c452b88a53072de0e5ac1cb38495f092ba1656c2cad04957112ac1255424978592b0924e1648c1c378386e0b0da381b0242f8485e090ba160bc3c170582d1a058160ac2c15058270d04c160946012058230b0441607c2c0f0581d072bc0e54844a70494909284125041c2f038520909a12114240b048150d8dc1f1b435b10a3600d2dc125b41caf039521129c1252424a104941090d2121841c2f038520909a12114240b04815074de0e9ac1d3383a630d4be1e96c3d2d06a57124ac1e94c1cb78396e072d60e5a81cb383966072c60e58824af8895e092b61256824ab8b956092a61254824978592e0925a0e1bc1c370386b070ce0e18c1c310485f090b61215c24298482b0d054120a42413848260904612084240b848160902a0e9bc1d3703a6b074ce0e98c1d3106a5f0d4b61a95c35298396f072d60e59c1cb18495f0b2b61656824ab979560b2a6124bc34970492d0924e124942c9185922070de0e1b81c358386a070ce0e1981c31838620b0be221782c2d8585a0b0ae2e1582c29858520904e1209824128581f0b03c16074352f86a5b2f4b41a95c352b06a53092be0e4bc2c9583927072461217c242d9785a090ae1215824298482f0905c120ac2414848230d04412084240f8381b0702e0e04c1d3783a6e074d60e9a81d3483a68074ce0e9981d3183a62094c218980252f84a5e094b62e968252b84a56094a6229481cb78396b072ce0e58c34af8695b2f2b41a55c34ab069530925e124b82c968386f070d60e19c1c318485f090b65e168242b84856090a6120bc24170482d0903e12078240d84819090261a048240883c5f078bc231741caf8395b072ae0e54c34a78794b0d28e1250c1c2f8385b070ae0e14c24278584b0908e1610c240f8581b0902e0f17c34af8495b0d2ae1e54c1ca78394e072960e51c1ca183942090be1616c242b858530709e0e1381c2583847070860e108240f8481d0b03616068240b868160902a0e9bc1d3703a6b074ce0e98c1d3106a5f0f4b61a95c3d298396f072dc0e5ac1cb383963072c41257c2cad849570b2a6124bc24968592b0b2541249c349304925070de0e1b81c358386a070ce0e1981c31838620b0be221782c2e8405c0b0b6161682c2b8b8560b0aa0c1502c29858520905e120b824168581f0b03c160741caf8395b072ae0e54d20a7a314b3828e6050c1c2f8385b070ae0e14cb0279504b1e08e2c10c400f8701b0a02e0804f792fed25bc84af5894ea8afd115b802aee054d9897ae12b5224e9848c082b0003f 16 65535 6 63 11 2047 19 524287
def cc_42_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00bc85fc54cc2cabf4ebbceb2e4add4a6dc9c6a93258b2086147f1c74aa6b6563605a254e6f469f3edf35e42c6622681ade16910c2a01aa0102008200800002 0x4c5f1314d795f5e56d79575e54c894f2252c89472250c8846135bc4d6e175b44b62fcd804a6f129ac4a671298c8a5f2296c8a572294c496f125b8596df85b0495f12578495d164bc592d164ac592a1649c692616497a1241648c8856160587a5f1e96c7a571294c495f1656c4957124bc592b1249c5923341585a4b1253c694b1251c49431a4bc692b1a49c6923221184c5f131785c5d1294bb2501257c495b1255c49531253c694b1251c4943221184a5f1a96c6a571a94c495f1656c595a1255fa156124bc592b1249c5923301588b6f5edad7b6722d8c4a6f129b45a6b169a84a67f49984a65128fc5a3b128dc5a33125bc496e125b4593f1e4f8593df04f0593b164e859371a4d85935e44d05933164c8592f164b8592d2c19858160e0507c5b1297c8a5e1296c4a571294c4a521293c495f1256c49571254c494f1252c49471250c4927124984925281586d6f1b5b87d6d1b18b7460129bc6a6e129b44a5f229784a5b1295c4a5312948496f125ac49691259c496312584495f1256c49571254c4927124984925241584d6f135b84d6d1a9bc7a6b1e9a87a691a99c8a661e98c7a611a97c6a5d1e96c7a5a169645a581a95c8a561a9545a5316944496f125b4496b1259c49651258c495f12574495b12564495712554495312544492b1249c49232219888560e1504d6f135b84d6d1a9bc6a6d169ac5a691a99c6a651e98c5a611a97c7a5b1e9646a571e94c7a51125bc496d125ac49691259c49651258c49611257c495d1256c4957125544953124ac692a1249c49261248cb8561adbc7b6b1eda86b67d8d987b63129bf526e129ac4a6a1299f42661298c4a62128fc5a3e128f4496f125ac49671258c493b1a4e84939124dc4936124cc49311249c492612494806616d6c6a5f1a96c6a571a94c6a3f1a8ec6a371a8cc595f22578595b1655c595316548593f1249c4926124957856135bc4d6e175b44b62c8d804a6f129ac4a691299c4a631a9846a5f1a96c6a571a94c496f125b8596d1657c895e1656c59571654c59521249c4926124957856175bc5d6e175b46a6f1a9b46a6b1a99c6a651a98c4a5f129746a5b1a9646a57129546a531a944496f165ac596a165a4496722598596316584495f12574595b1656859591656049572255849551654c5951124bc49271648c8866221583854175bc5d6e175b46a6f129b46a6b1a9a44a67129946a631a9846a5f1a9746a5b1a95c6a551a94c496f125b4596b165a4496712594596316584495f1656c59591255c595316544492f124b449271249459232e1586b6f1adac6b671ad8c4a6f169ac5a6a1299f12661698c4a3f1a8f84a3d128dc4a35168cc5a32165bf016e165ac596a1659ef1661658c5962124dc4936124d4592f164b8592d1c1986b6f1adb46b6b1ad9c6b651ad8c4a67129984a651a8fc6a3e168ec5a3a1a8dc5a361a8cc6a32125bc496d125ac4967125944963124fc493b124cc492f124b4492b124a4492712494492312484b8662e0b8382c1adbc6b6d1adac8b6a1ad9c6b661ad946b63129bc4a6e129b46a3f1a8f88a3d168ec5a3a1a8dc5a361a8d45a341a8cc6a32125bc496d125ac896a1259c4966125944963124fc493b124cc492f124b4492b224a849291249c49261249449241248c49212219888260e0904b6f12db84b6b12d9c4b6322d886a671a9986a65128fc4a3e1e8f4496f125acb96a1259c49661258c493f124f8493d124bc492e124ac49291249c49231e48849215e198483e12dbc4b6e12dac4b6712d8c8b621a9bc6a6b2e9a86a671a9986a63128fc4a3e168f44967125984965124fc493e164f4592f1a4b8592b164a459271648c5922164857866120f84b6f12db84b6bb4da84b6712d984b63b0d886a6f1a9aeb26a1a99c6a661a98c4a3f128f85a3d125bc496ba85a84967125984963124fc493e124f4492f124b8492b124a449231a488492114198483e0e0f05d6f175b85d6d1a9bc7a6b1e9a46a671e98c7a611a97c6a5d1e96c4a591a95c6a551294c4a51125bc596b165a449671658c59611257c495d1656c59591255c49551654c5951124bc592b1249c88661019088560e1505d6f175b85d6d1a9bc6a6d129ac4a691a99c6a651e98c4a611a97c7a5b1e9646a571e94c7a51125bc496d165ac59691259c49651658c59611257c595b1656449571654c5951124bc492d164ac592a1249c692612494b8560c1506b6f1edac6b671ed8c4a6f169ac4a671698c4a3f128f45a3b168e84a371a8d84a35165be816e165ac596a1659e71661658c5962124fc493e124f4592f164b8592d081986a5b229686a571a958392f2217c885b2215c88531a0bc682b1a09c68234a07d281b4a05d28130f1bc3c6e1b1b6546c1b17c7c5e1b174396b0e59c39631a56c895a1a56469571a55869531a54469471a51869450e1bc386b0e19c38632217c885d2216c88574015488531a13c484d1a12c58491a11c48451a10c58411a07c681b1a05c68130e9bc3a6e0e99c3a630e9886a5f229786a5d1a95c6a551e94c7a520e59c39661a55c69561a554792f1e4b8792d0e1bc386b0e19c38632217cb85b2e15c88531e0bc782d1a0ac68275e09478231e07c481d1e06c58191e05c48151e04c581122d707b542e15068240f1a20460 16 65535 6 63 11 2047 18 262143
def cc_42_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xa1839b9898cb911f8e0c8b8a880e848e7ba473a06aa461a45b1a53204dd54d8149514511450044c13e993916341433822d5923a723801d1a18140ea606220018 0x4a340f2797c4d03e2d86a5f0d4bc1a9743d278895f112b62255c44a9e314fc22978051ef0a18792f0925a1e4ac3c95079270f24c12496c89207923110ac1e098362f86c532f2be5e56cbcab979531129e2252c44a3889431108c1b5bc36b707d6d0d8c575180353786a6e0f4db709b0352f86a5e0d4ba1a5bc34b5869670d2c62257c44ad88957112a61e4bc24968792b0f2541e49c3c9304925b02481e48c442b078260d4be1e96c352b8595f0b2b61655c2ca98592f0b2561649c2c919a0560f6961253c24a58494709286124fc249d849370926622118362f86c5e0f8ba1ad4ac9a80495f092b61255c24a98494f092961251c24a1888460d4be1e96c3d2d06a57b04ac1257c24ad84957092a6124bc249584927092466415835b786b6d0f6d61eda835b3db3660d6ca1a9bc353706a6d0f47e1e8f83d1e8896fa62d70459c44b18793f0d2761a4dc3c998792f0925a1e4ac3c9505929b42501e49c3c9304925ae2481e48c2c90980660f04c0e09026b785d6e09ada229bcbd3597a67114c61297c252e84a5b0f4b21295c352a84a53094a2125ae90b504969092ce1259824b184961092ae1255824aa8492f092561249c249196066090ac0e1503f3f06e7d116f41ade435bb06b710d6cc1ad94453f04a7d094ea169c8353704a6d094d8169a4253285a620b4c2169802d1d06a36092ec125d434b305965842c81a4f82c9d069360b264164b82c96888760d0cc0e190363e87c7a118ec1b1d435bf06b7d0f69c1ed34453f04a7d094ea169c82d2506a460947a168e82d1c85a380f46c128d4251a05a31092ec125d43ca70594a0d28c165083c9b0593590268164b82c96888760f06c0e0d026b785d6e09ada229bc453588a67114c61297c252e84a5b094ae1a954252984967092cc1259424ab849560b2aaf85502c978592b0b24e1648c443304856a86de2edac5db3d3363094df489b8253684a67094ca1698c2d3104a3f0b476168e8251baa2360b4661259c24b3049650b27e1e4f82c9d8593a0b26e1a4d82c99859320b25e164b82c9695066116dc16da82db306b620f69c1ad36792506a490d48c1a904351b06a35092dc5e588249e849390926a124c43495049262f0cd308d279a706b4d0d68a1ed085d3306a460d48a1e8f83d1e8496e2f2c41a4e8249b049260924a12490a0330bc6a0d69c1ed34352706a4d0d47c1a8e6591906a31092dc5e58824a68692a0924c5e19834270384c984981ad343da54b3460d68a229b82d3505a660f4c41a938352687a3e0f47a125b8bcb10693a0926c124b43c95049290b25012498249284924092424c1982dadc625f174b62e95e1929d023f9c477348de51198495f092bc1256c24a9bf1520927e124bc2495b212a0924e12498249192056116d41ad98253506a620947c168e8251b04a32092dc22588349d049360925a1a4a82494849260924a124902490888660b250124903eb706d6d8e6b2229a8353486a660d4c21a958352a8496e112c41257824ae8495c092b21255434a9049510b2a01a4a8249308866220c81a1581c2a04e7e0bcfa135f836bec857c0fadc1b5b425b9463700d4fa129e4253a86a71114d41a9a4353306a610d4ac1a95424bf0497d092dc125a444b104961092bc1257424ae04959092aa1a54824a8859500d254124984433100640d0ac0e15035b687b6a116cc1ad94353706a6d8849c1e8f83d1e8496e092d22258824b08693a0926c124b43c95049290b2501249824928492409242221983c130382409ad41b5883d3508a66094ba12964252a85a51092dc2258824af0495d092b2125543ca9049510b2a01a4a824930886609cfc179f42639434700d6fa12de425ba87b710d6da1eda845b306b65094fc1e9f6113e06a6e0d4da1e8f83d1e8497e092fa125b824b488962092c21a4e8249b0492d0f254124a42c94049260924a124902490888660f04c0e09026b784d6e0bada12d8a49b004a6f0d4da129ac253484a67094ca1298c3d30c525f174b62e95e09298496f092dc125b424af8495e092b61256424a9bd152092a2124bc2495b112a0924e1249824918f0560b6b62297c452d88a57114a65e8fcbd1d97a372f4661257c24af0495d0b27e164bc2c968592b0b2541649c349305925762481648c442b05816 16 65535 6 63 11 2047 19 524287
def cc_42_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x3320b26a4a07d55f016b456915a016414064a9608881c10604102010c001 0xdade1f5b836b686a6bdc4d41a9a4353386a660d4c61a984352b86a560d4aa225bea0b5c5167112c61a57c24ae8695b0b2b21a55c24aa869530b2a21a4bc3495869270d24690198342b038540dade1f5b836b686a670d4cc1a994352b86a560f4ab7095044b78896b112ce2258c34af8495d0d2b61a55c24aa869530f25e1e4ac3c9387923110cc1a15835b7ee36e0d6da1ad9c35b287b630f6c41a99c353306a650f47e1e8f83d1e9796f172d62e59cbcb18793f0f27a1a4ec349bab1350f2661e4bc24968792b0b2521e49c2492879230b2428c198463704c6a0f8cc131882e2f04c5d0d4dd8c988252686a490d48a1290758ad04959092ac1254424a3049450925a124951033681440d6dd84d8b592f04a5d094aa16948251e84a35172cc1255824aa869360b26a1a4d02c970592d420cc2f5a8262f05c5d0d4dd80988352e8495e092ba1253824a4e714209282124b424929f066090bc0e17340ae06b6ebc6c4129742d2d67256094aa128f4251a8896e0b2d41e5982cb10495e092ba1a4f82c9e8793c0b2741a4d82c9a869340b264164b82c969e0660f8b61a97c352f06a5b0d4a77494835279795f172b62e55cbca9ec14fd4297a451f30a18692f6e25a1a4ac3493869250d2467415836b786d6e0fada1b18b2a3006a6f0d4dc1a9b4352f86a5e0d4b61a9643529db2520d4a21a5bc24b68696b0b2d21a59c24b2869630b2c25e57c5cad8b9572f2a61a4bdb0968692b0d24e1a49434919c0560924812490251a6213417ad0124901c2e04924 14 16383 6 63 11 2047 19 524287
def cur_42 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_42_3 (Nat.sub p 96)) (cc_42_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_42_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_42_0 p) (Nat.blt p 32)
def f_42 : Nat → Nat × Nat := unpackForestF 0x297f736e0296f314fd697b314bcc51f415cce95b3143cb1800a57bc53f1134bc52ef147be4d2f143b9182e26caed9ab928b2d42c256ae4900a530257e936fa4d8e926e0256e523f9ed3a523b948de624c96d1a523382d82357c8ed6633708297e224e851c2127c8294c09577cd81f16c72999c93c76941d156724d009536f181a366689b9a266024bd93605e999796e5e598092b54da95362549a9516a0249d396e4e59809234b1b0114f0452cf03f3c0ed04603c0dcf0333ad801147325b0c8183205011432f1b0104f0412c992b2648c826022980814d0411c606c180b060240410c536012958101f0406c32600405c185c06150101302158003f 7 11
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 fullMask g_42 ep_42 112 bds_42 (dagTraceF fullMask rootStock 10 f_42) (cur_42 0) rootStock 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_42 ep_42 bds_42 112 (dagTraceF fullMask rootStock 10 f_42) cur_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_42 ep_42 bds_42 112 (dagTraceF fullMask rootStock 10 f_42) cur_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_42 ep_42 bds_42 112 (dagTraceF fullMask rootStock 10 f_42) cur_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_3 : treeBlockF 96 112 (dagCheckNodeV4 fullMask g_42 ep_42 bds_42 112 (dagTraceF fullMask rootStock 10 f_42) cur_42) = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_42 ep_42 bds_42 112 (dagTraceF fullMask rootStock 10 f_42) cur_42) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nj_42_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_42 ep_42 bds_42 112 (dagTraceF fullMask rootStock 10 f_42) cur_42) i = true := block_join nj_42_1 (fun _ h1 h2 => treeBlockF_at nb_42_2 h1 h2)
theorem nj_42_3 : ∀ i, 0 ≤ i → i < 112 → (dagCheckNodeV4 fullMask g_42 ep_42 bds_42 112 (dagTraceF fullMask rootStock 10 f_42) cur_42) i = true := block_join nj_42_2 (fun _ h1 h2 => treeBlockF_at nb_42_3 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 112 → (dagCheckNodeV4 fullMask g_42 ep_42 bds_42 112 (dagTraceF fullMask rootStock 10 f_42) cur_42) i = true := nj_42_3
theorem lb_42 : LowerBin fullMask rootStock g_42 11 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def wg : List Gate := [⟨GateOp.and, [4, 0]⟩, ⟨GateOp.and, [3, 0]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [7, 1]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [5, 0]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.and, [9, 8]⟩, ⟨GateOp.or, [9, 9]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.and, [10, 16]⟩]
theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4274577600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276808424 * 2 ^ 32 + 4274577600)) (12 - 1) := by
  rw [show canon fullMask (4276808424 * 2 ^ 32 + 4274577600) = g_42 by decide]
  exact lb_42

end PEqualNP.Outside.L_meta_43399

theorem PEqualNP.Outside.L_meta_43399 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4274577600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4274577600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_43399.table2_from_lowerBin (4276808424 * 2 ^ 32 + 4274577600) 12 PEqualNP.Outside.L_meta_43399.root_lb PEqualNP.Outside.L_meta_43399.wg 17 rfl PEqualNP.Outside.L_meta_43399.wfits PEqualNP.Outside.L_meta_43399.weval
