import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45423

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

def m_2 : Nat := 0xcc000000cc00
def s_2 : List Nat := [0x440000004400, 0xc0000000c00, 0xcc00]
def g_2 : Nat := 0x40000004c00
def ep_2 : Nat := 0x480000000000000000000000000000000000000004000000080000000000000000000000040000004000
theorem epk_2 : ep_2 = edgePack 0xcc000000cc00 g_2 := by decide +kernel
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, 0xcc000000cc00 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
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

def m_3 : Nat := 0xf0000000f0
def s_3 : List Nat := [0x5000000050, 0x3000000030, 0xf0]
def g_3 : Nat := 0x1000000070
def ep_3 : Nat := 0x6000000000000000000000000000000000000000000000000000000010000000200000001000000040
theorem epk_3 : ep_3 = edgePack 0xf0000000f0 g_3 := by decide +kernel
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, 0xf0000000f0 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
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

def m_4 : Nat := 0xf0000000f000
def s_4 : List Nat := [0x500000005000, 0x300000003000, 0xf000]
def g_4 : Nat := 0x100000007000
def ep_4 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000
theorem epk_4 : ep_4 = edgePack 0xf0000000f000 g_4 := by decide +kernel
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, 0xf0000000f000 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
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

def m_5 : Nat := 0xaa00aa
def s_5 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_5 : Nat := 0x2002a
def ep_5 : Nat := 0x280000000000000000000000000002000800000000000200200000000000000000
theorem epk_5 : ep_5 = edgePack 0xaa00aa g_5 := by decide +kernel
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, 0xaa00aa &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
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

def m_8 : Nat := 0x33330000
def s_8 : List Nat := [0x11110000, 0x3030000, 0x330000]
def g_8 : Nat := 0x1130000
def ep_8 : Nat := 0x120000000000000102000000000000000000000000000001100000
theorem epk_8 : ep_8 = edgePack 0x33330000 g_8 := by decide +kernel
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, 0x33330000 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
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

def m_10 : Nat := 0xf0f0000
def s_10 : List Nat := [0x5050000, 0x3030000, 0xf0000]
def g_10 : Nat := 0x1070000
def ep_10 : Nat := 0x60000000000000000000000000000010200000000000001040000
theorem epk_10 : ep_10 = edgePack 0xf0f0000 g_10 := by decide +kernel
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, 0xf0f0000 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
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

def m_11 : Nat := 0xf0f000000000000
def s_11 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_11 : Nat := 0x107000000000000
def ep_11 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
theorem epk_11 : ep_11 = edgePack 0xf0f000000000000 g_11 := by decide +kernel
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, 0xf0f000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
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

def m_12 : Nat := 0xff00000000
def s_12 : List Nat := [0x5500000000, 0x3300000000, 0xf00000000]
def g_12 : Nat := 0x1700000000
def ep_12 : Nat := 0x60000000000000012000000000000001400000000
theorem epk_12 : ep_12 = edgePack 0xff00000000 g_12 := by decide +kernel
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, 0xff00000000 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
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

def m_13 : Nat := 0xff000000000000
def s_13 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_13 : Nat := 0x17000000000000
def ep_13 : Nat := 0x600000000000000120000000000000014000000000000
theorem epk_13 : ep_13 = edgePack 0xff000000000000 g_13 := by decide +kernel
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_13 : KnownBin bds_13 := by intro b hb; simp [bds_13] at hb
theorem sub_13 : ∀ b ∈ bds_13, 0xff000000000000 &&& b.1 = b.1 := by intro b hb; simp [bds_13] at hb
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

def m_14 : Nat := 0xaa00aa00aa00aa
def s_14 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_14 : Nat := 0x200020002002a
def ep_14 : Nat := 0x2800000000000000280000000000000000000200020002000800020002000200200000000000000000
theorem epk_14 : ep_14 = edgePack 0xaa00aa00aa00aa g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_5, s_5, 4, g_5)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_0
  · exact lb_5
theorem sub_14 : ∀ b ∈ bds_14, 0xaa00aa00aa00aa &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_14 : Nat → List (Nat × Nat) := fun _ => []
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 0 bds_14 (dagTraceF m_14 s_14 4 f_14) (cur_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_14 g_14 ep_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) cur_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x5500550055005500
def s_15 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_15 : Nat := 0x100150001005500
def ep_15 : Nat := 0x400000001400000054000000000000000000010004000100000001001000010000000000000000000000
theorem epk_15 : ep_15 = edgePack 0x5500550055005500 g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_15 : ∀ b ∈ bds_15, 0x5500550055005500 &&& b.1 = b.1 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_15 : Nat → List (Nat × Nat) := fun _ => []
def f_15 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 0 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) s_15 4 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_15 g_15 ep_15 bds_15 0 (dagTraceF m_15 s_15 4 f_15) cur_15 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xcc00cc00cc00cc
def s_16 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_16 : Nat := 0x400040044004c
def ep_16 : Nat := 0x40004800000000000000080000000000000000000400040000000800000000000000000004000400440040
theorem epk_16 : ep_16 = edgePack 0xcc00cc00cc00cc g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_16 : ∀ b ∈ bds_16, 0xcc00cc00cc00cc &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_16 : Nat → List (Nat × Nat) := fun _ => []
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 0 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_16 g_16 ep_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) cur_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xcc00cc00cc00cc00
def s_17 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_17 : Nat := 0x40000004c00
def ep_17 : Nat := 0x48000000040000004c000000000000000000000004000000080000000000000000000000040000004000
theorem epk_17 : ep_17 = edgePack 0xcc00cc00cc00cc00 g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_17 : ∀ b ∈ bds_17, 0xcc00cc00cc00cc00 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_17 : Nat → List (Nat × Nat) := fun _ => []
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 0 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_17 g_17 ep_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) cur_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xf000f000f000f0
def s_18 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_18 : Nat := 0x10001000500070
def ep_18 : Nat := 0x40006000000000000000200000000000000000000000000000000000100010000000200010001000500040
theorem epk_18 : ep_18 = edgePack 0xf000f000f000f0 g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_18 : ∀ b ∈ bds_18, 0xf000f000f000f0 &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_18 g_18 ep_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xf000f000f000f000
def s_19 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_19 : Nat := 0x100000007000
def ep_19 : Nat := 0x600000001000000070000000000000000000000000000000000000001000000020000000100000004000
theorem epk_19 : ep_19 = edgePack 0xf000f000f000f000 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_19 : ∀ b ∈ bds_19, 0xf000f000f000f000 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_19 : Nat → List (Nat × Nat) := fun _ => []
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 0 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_19 g_19 ep_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) cur_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xaaaa0000aaaa
def s_20 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_20 : Nat := 0x200002a2a
def ep_20 : Nat := 0x2a2800000000000000000000000200000000000000020000080800000002000020200000000000000000
theorem epk_20 : ep_20 = edgePack 0xaaaa0000aaaa g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_20 : ∀ b ∈ bds_20, 0xaaaa0000aaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_20 g_20 ep_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0x5555000055550000
def s_21 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_21 : Nat := 0x115000001550000
def ep_21 : Nat := 0x40000000000000000000000014000000540000010400000100000001100000010000000000000000000000
theorem epk_21 : ep_21 = edgePack 0x5555000055550000 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_21 : ∀ b ∈ bds_21, 0x5555000055550000 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
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
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_12, s_12, 4, g_12)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_1
  · exact lb_3
  · exact lb_12
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

def m_23 : Nat := 0xff000000ff00
def s_23 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_23 : Nat := 0x150000007f00
def ep_23 : Nat := 0x6a0000000000000000000000000000000000000004000000080000001000000020000000150000004000
theorem epk_23 : ep_23 = edgePack 0xff000000ff00 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_2
  · exact lb_4
theorem sub_23 : ∀ b ∈ bds_23, 0xff000000ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xff000000ff0000
def s_24 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_24 : Nat := 0x17000000570000
def ep_24 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
theorem epk_24 : ep_24 = edgePack 0xff000000ff0000 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_24 : ∀ b ∈ bds_24, 0xff000000ff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_24 g_24 ep_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xaaaaaaaa
def s_25 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_25 : Nat := 0x22a2a
def ep_25 : Nat := 0x2a280000000000020000000000000002080800000000000220200000000000000000
theorem epk_25 : ep_25 = edgePack 0xaaaaaaaa g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_25 : ∀ b ∈ bds_25, 0xaaaaaaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_25 g_25 ep_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x5555555500000000
def s_26 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_26 : Nat := 0x115151500000000
def ep_26 : Nat := 0x1400000000000014000000000000010404040000000001101010000000000000000000000000
theorem epk_26 : ep_26 = edgePack 0x5555555500000000 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_6
  · exact lb_7
theorem sub_26 : ∀ b ∈ bds_26, 0x5555555500000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x33333333
def s_27 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_27 : Nat := 0x1133333
def ep_27 : Nat := 0x32200000000000120000000000000102000000000000000000000000000001100000
theorem epk_27 : ep_27 = edgePack 0x33333333 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_27 : ∀ b ∈ bds_27, 0x33333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0x3333333300000000
def s_28 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_28 : Nat := 0x113111300000000
def ep_28 : Nat := 0x1000000000000012000200000000010200020000000000000000000000000110111000000000
theorem epk_28 : ep_28 = edgePack 0x3333333300000000 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_28 : ∀ b ∈ bds_28, 0x3333333300000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xf0f0f0f
def s_29 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_29 : Nat := 0x1070f0f
def ep_29 : Nat := 0xe080000000000060000000000000000000000000000010200000000000001040000
theorem epk_29 : ep_29 = edgePack 0xf0f0f0f g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_29 : ∀ b ∈ bds_29, 0xf0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_29 g_29 ep_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xf0f0f0f00000000
def s_30 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_30 : Nat := 0x107050700000000
def ep_30 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
theorem epk_30 : ep_30 = edgePack 0xf0f0f0f00000000 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_30 : ∀ b ∈ bds_30, 0xf0f0f0f00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_30 g_30 ep_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xff00ff
def s_31 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_31 : Nat := 0x57007f
def ep_31 : Nat := 0x280000000000000000000000000002000800000000000200200000000000540040
theorem epk_31 : ep_31 = edgePack 0xff00ff g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_31 : ∀ b ∈ bds_31, 0xff00ff &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xff00ff00
def s_32 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_32 : Nat := 0x1007f00
def ep_32 : Nat := 0x7e000000000000000000000000000100080000000000010020000000000001004000
theorem epk_32 : ep_32 = edgePack 0xff00ff00 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_32 : KnownBin bds_32 := by intro b hb; simp [bds_32] at hb
theorem sub_32 : ∀ b ∈ bds_32, 0xff00ff00 &&& b.1 = b.1 := by intro b hb; simp [bds_32] at hb
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_32] at hb
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb49682d05a0b4149290520a4148290520949282504a09410921042084108210420748e81d03a0740c901c001 0x1124c852040531f280e83c701a360b1a048b34855a0284f13260884c40221e0b0e04852482520108e07460284c1022060f02069ea3fe91df28df7467a13fc49de04dee267592fa095ce49e5247203f8c1dbc0dd9066c02f5c15a409cd046601f2c0d8c05c1026000f 11 2047 5 31 10 1023 17 131071
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x910a04074d5a3160c15285088e9c3260c12204050508040000000000 0x3f271f134f094764938461c344d91c6a8d332799134bc985e912d4996244a8a65251262413234 7 127 2 3 10 1023 17 131071
def cc_32_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x0 0x0 1 1 1 1 1 1 2 3
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_32_2 (Nat.sub p 64)) (cc_32_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xf938f934063fed28ed24063b0637e3440633d638d634053fc93cc934053b0537be440533b24cb244052fa54ca544052b05279a340523043f043b7e4c7e407d4c7d400437683c6834682c68240433042f042b4f484f404d3c4d300427384c3844382c38240423041f041b1e481e401e381e300417084c0844083c08340413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 64 bds_32 (dagTraceF m_32 s_32 5 f_32) (cur_32 0) s_32 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) cur_32) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 64 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) cur_32) = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) cur_32) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) cur_32) i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xff00ff0000000000
def s_33 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_33 : Nat := 0x100150000000000
def ep_33 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
theorem epk_33 : ep_33 = edgePack 0xff00ff0000000000 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_33 : ∀ b ∈ bds_33, 0xff00ff0000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xffff0000
def s_34 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_34 : Nat := 0x1570000
def ep_34 : Nat := 0x560000000000000102000000000000010200000000000001540000
theorem epk_34 : ep_34 = edgePack 0xffff0000 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_10, s_10, 4, g_10)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_8
  · exact lb_10
theorem sub_34 : ∀ b ∈ bds_34, 0xffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xffff00000000
def s_35 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_35 : Nat := 0x151700000000
def ep_35 : Nat := 0x200000000000004060000000000001012000000000000151400000000
theorem epk_35 : ep_35 = edgePack 0xffff00000000 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_35 : ∀ b ∈ bds_35, 0xffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl <;> decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xffff000000000000
def s_36 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_36 : Nat := 0x117000000000000
def ep_36 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_36 : ep_36 = edgePack 0xffff000000000000 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9), (m_11, s_11, 4, g_11), (m_13, s_13, 4, g_13)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_9
  · exact lb_11
  · exact lb_13
theorem sub_36 : ∀ b ∈ bds_36, 0xffff000000000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x945282053e2784f01e030c5c4b09602b1560ac150aa03d8708d11a0322640c09803005c4b81702c22b00c801 0x7c0c0705236850a4280a73c509506260210e0eba064382a101150a0074d0b2601d246da0b49043a9a1d3e4c99074b8a2441c4d641f200c9805c282250a0074d092601d2451a0220b16684aa310ea7265083a7a1d2e20912413900841c3d3c1704088b2801d24249807490b4804a30181e06130d48462320ea7145083a7c41320e968e1385084203e0819070b6846721337091870fd70661c2f38118707c1026000f 11 2047 4 15 10 1023 17 131071
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb85c1b4c1603005411080040000 0x4e506326351297890b610560621c2da41487095004312409da0c28ca627cf13268209a084383b28190e0a8a04624811340 9 511 4 15 10 1023 17 131071
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_36_1 (Nat.sub p 32)) (cc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 43 bds_36 (dagTraceF m_36 s_36 6 f_36) (cur_36 0) s_36 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 43 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0x5555555555555555
def s_37 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_37 : Nat := 0x115151501555555
def ep_37 : Nat := 0x40404000001400000054000014000000540000010404040100000001101010010000000000000000000000
theorem epk_37 : ep_37 = edgePack 0x5555555555555555 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 5, g_15), (m_21, s_21, 5, g_21), (m_26, s_26, 5, g_26), (m_7, s_7, 4, g_7), (m_6, s_6, 4, g_6)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_21
  · exact lb_26
  · exact lb_7
  · exact lb_6
theorem sub_37 : ∀ b ∈ bds_37, 0x5555555555555555 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 5 f_37) (cur_37 0) s_37 5 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 5 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xaaaaaaaaaaaaaaaa
def s_38 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_38 : Nat := 0x2000200022a2a
def ep_38 : Nat := 0x2a280000000000002a280002000200020000000200020002080800020002000220200000000000000000
theorem epk_38 : ep_38 = edgePack 0xaaaaaaaaaaaaaaaa g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 5, g_14), (m_20, s_20, 5, g_20), (m_25, s_25, 5, g_25), (m_5, s_5, 4, g_5), (m_0, s_0, 4, g_0)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_20
  · exact lb_25
  · exact lb_5
  · exact lb_0
theorem sub_38 : ∀ b ∈ bds_38, 0xaaaaaaaaaaaaaaaa &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 5 f_38) (cur_38 0) s_38 5 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 5 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0x3333333333333333
def s_39 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_39 : Nat := 0x113111301133333
def ep_39 : Nat := 0x222000001000000032200012000200120000010200020102000000000000000000000110111001100000
theorem epk_39 : ep_39 = edgePack 0x3333333333333333 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_27
  · exact lb_28
  · exact lb_8
  · exact lb_9
theorem sub_39 : ∀ b ∈ bds_39, 0x3333333333333333 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_39 : Nat → List (Nat × Nat) := unpackCursorV4 0x1e0f0783c1c2e07038193c86432190b95c2e170a1d02813190c824111883503801 0xca5cc250b238aa34a134835c7b506a4c6244592432302244223433442a5c1a541124db4fd34bbb479b43924f8a4b724752434a3f423b3a370a33001f 9 511 4 15 10 1023 16 65535
def f_39 : Nat → Nat × Nat := unpackForestF 0xe9e1d2f12e62500e8f48e291a51340e86193c325bf5c7ea0191d7262e445a48190c31f863b0c6e2d1052e123414a82490319801f 5 10
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 28 bds_39 (dagTraceF m_39 s_39 6 f_39) (cur_39 0) s_39 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39 : treeBlockF 0 28 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 28 (dagTraceF m_39 s_39 6 f_39) cur_39) = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 28 (dagTraceF m_39 s_39 6 f_39) cur_39) i = true := fun _ h1 h2 => treeBlockF_at nb_39 h1 h2
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xcccccccccccccccc
def s_40 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_40 : Nat := 0x4040400444c4c
def ep_40 : Nat := 0x4048480000040000004c080004000000440000000404040000080800000000000000000004040400444040
theorem epk_40 : ep_40 = edgePack 0xcccccccccccccccc g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 5, g_16), (m_17, s_17, 5, g_17), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_17
  · exact lb_1
  · exact lb_2
theorem sub_40 : ∀ b ∈ bds_40, 0xcccccccccccccccc &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_40 : Nat → List (Nat × Nat) := unpackCursorV4 0x1e0f0783c1e0d9ec36192c86432190c858ec160a1502814098cc1e8f070b443801 0x322a1805cb828540e28069035c79a8385418098b04418201d160c8a0514010180cd004289b34fd1a5d8d1e6687204f8825b411d4086903f401d900dc2066001f 9 511 4 15 11 2047 17 131071
def f_40 : Nat → Nat × Nat := unpackForestF 0xb4f0b4bb950b85cb8500b47a038a0340b43084f084b735c735071500847584c58440843083f083b2c582c50294008371b4011440833001f 5 11
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 28 bds_40 (dagTraceF m_40 s_40 6 f_40) (cur_40 0) s_40 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40 : treeBlockF 0 28 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 28 (dagTraceF m_40 s_40 6 f_40) cur_40) = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 28 (dagTraceF m_40 s_40 6 f_40) cur_40) i = true := fun _ h1 h2 => treeBlockF_at nb_40 h1 h2
theorem lb_40 : LowerBin m_40 s_40 g_40 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xf0f0f0f0f0f0f0f
def s_41 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_41 : Nat := 0x107050701070f0f
def ep_41 : Nat := 0xa080000040000000e080006000200060000000000000000000001020002010200000104050401040000
theorem epk_41 : ep_41 = edgePack 0xf0f0f0f0f0f0f0f g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_29
  · exact lb_30
  · exact lb_10
  · exact lb_11
theorem sub_41 : ∀ b ∈ bds_41, 0xf0f0f0f0f0f0f0f &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_41 : Nat → List (Nat × Nat) := unpackCursorV4 0x1e0f0783c1c2e07038193c86432190b95c2e170a1d02813190c824111883503801 0xca5cc250b238aa34a134835c7b506a4c6244592432302244223433442a5c1a541124db4fd34bbb479b43924f8a4b724752434a3f423b3a370a33001f 9 511 4 15 10 1023 16 65535
def f_41 : Nat → Nat × Nat := unpackForestF 0xe9e1d2f12e62500e8f48e291a51340e86193c325bf5c7ea0191d7262e445a48190c31f863b0c6e2d1052e123414a82490319801f 5 10
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 28 bds_41 (dagTraceF m_41 s_41 6 f_41) (cur_41 0) s_41 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41 : treeBlockF 0 28 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 28 (dagTraceF m_41 s_41 6 f_41) cur_41) = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 28 (dagTraceF m_41 s_41 6 f_41) cur_41) i = true := fun _ h1 h2 => treeBlockF_at nb_41 h1 h2
theorem lb_41 : LowerBin m_41 s_41 g_41 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xf0f0f0f0f0f0f0f0
def s_42 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_42 : Nat := 0x10101000507070
def ep_42 : Nat := 0x40606000001000000070200010000000500000000000000000000000101010000020200010101000504040
theorem epk_42 : ep_42 = edgePack 0xf0f0f0f0f0f0f0f0 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_19
  · exact lb_3
  · exact lb_4
theorem sub_42 : ∀ b ∈ bds_42, 0xf0f0f0f0f0f0f0f0 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV4 0x1e0f0783c1e0d9ec36192c86432190c858ec160a1502814098cc1e8f070b443801 0x322a1805cb828540e28069035c79a8385418098b04418201d160c8a0514010180cd004289b34fd1a5d8d1e6687204f8825b411d4086903f401d900dc2066001f 9 511 4 15 11 2047 17 131071
def f_42 : Nat → Nat × Nat := unpackForestF 0xb4f0b4bb950b85cb8500b47a038a0340b43084f084b735c735071500847584c58440843083f083b2c582c50294008371b4011440833001f 5 11
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 28 bds_42 (dagTraceF m_42 s_42 6 f_42) (cur_42 0) s_42 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 28 (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 28 (dagTraceF m_42 s_42 6 f_42) cur_42) = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 28 → (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 28 (dagTraceF m_42 s_42 6 f_42) cur_42) i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xff00ff00ff00ff
def s_43 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_43 : Nat := 0x1700170057007f
def ep_43 : Nat := 0x40006800000000000000280000000000000000000600060002000800120012000200200014001400540040
theorem epk_43 : ep_43 = edgePack 0xff00ff00ff00ff g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_16, s_16, 5, g_16), (m_18, s_18, 5, g_18), (m_14, s_14, 5, g_14), (m_24, s_24, 5, g_24), (m_31, s_31, 5, g_31), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5), (m_12, s_12, 4, g_12), (m_13, s_13, 4, g_13)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_22
  · exact lb_16
  · exact lb_18
  · exact lb_14
  · exact lb_24
  · exact lb_31
  · exact lb_0
  · exact lb_1
  · exact lb_3
  · exact lb_5
  · exact lb_12
  · exact lb_13
theorem sub_43 : ∀ b ∈ bds_43, 0xff00ff00ff00ff &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 7 f_43) (cur_43 0) s_43 7 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 7 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xff00ff00ff00ff00
def s_44 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_44 : Nat := 0x100150001007f00
def ep_44 : Nat := 0x6a000000140000007e000000000000000000010004000100080001001000010020000100150001004000
theorem epk_44 : ep_44 = edgePack 0xff00ff00ff00ff00 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 6, g_32), (m_17, s_17, 5, g_17), (m_19, s_19, 5, g_19), (m_23, s_23, 5, g_23), (m_15, s_15, 5, g_15), (m_33, s_33, 5, g_33), (m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_17
  · exact lb_19
  · exact lb_23
  · exact lb_15
  · exact lb_33
  · exact lb_2
  · exact lb_4
  · exact lb_6
theorem sub_44 : ∀ b ∈ bds_44, 0xff00ff00ff00ff00 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_44_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x9503280a5004a009401193e300be5f69ccb5796a02d405a80ae1d5a0aa835482a60cf561e803d007808c6a98c03180600cc00178224aa23980310001 0x1b13001a8c00394c070d3806b4206c93807a4201a8c01a14e0485080393d01e4d40392d01a4940683d0280d40782d0100940394c08917804c5a0131582045207cd7806b5207897807a5201a8c00695e0445480694e00e5340394c01a52403945074508069410645000393d00e4d40392d00e4941804d016124050450161040683d0240d40782d00c09403b4f022d3803b4d01a93c04a4b01291c06a4300e8fc03a3b00e8dc03a3301e53c0494b01251c0794300e4fc0393b00e4dc0393301a4bc0692b01a49c0692302213c0484b01211c0584300e0dc038360220d40682f0160ac0682701608c0781f01606c0781701604c06c5901b14407b5901ed4403a5e00e97403a5c01296803a5600e95403a4e01a92803a4601a90803a3e01e8e803a3601e8c80395e00e5740694a01a5180793a01e4d80392e0124b40885d0221540481901604404c5805114006b5001e94006a3004c5301214001a57003c5001ad400693001e57003b5001e94007920022d3c04b4b01ad2404b4701ad0c06b4102293c04a4b01e92404a4701e90c07a4101a8fc07a3b0448dc06a3300e53c0394e00e5340693f0404ec0f13701a4cc0792f0384ac0d12701e48c0884f0221340484b01211c0884501610c0683f0160ec088370160cc0782f0160ac0882701608c0481b02205c058130285000584002317804c5a01315808c5201ad6808b56016d3805b4d02c9340524501a8f40923501a5780895200e5140693901a4c40585a022158058390160c404c580191400394c01050005840022d7804b5a012d5808b5201cd280534601e96808a5601e928032460168f805a3d01e5780895200e4d40792901e4840585a022158058290160842634f01ad2c08b4701ad0c2424f01e92c08a4701e90c06a3f01e8ec1723701a8cc0394f0585380894b00e51c151430305080393f01a4ec0393701a4cc0392f01e4ac0392701e48c0884f01612c0884701610c0683f0160ec080370160cc0782f0160ac0202701608e4434f900d2e3b3478dcd0e2324f87c92e1a24784090e0623f7ec8edb62376748cd9b14f63c52d891475c050d6d13f5804ed561374c04cd2d12f4684ad101273a848cb004b1b410c5c03b1680cc4902b11c08c3601e0d006c280130040480001f 15 32767 6 63 11 2047 22 4194303
def cc_44_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xa5014a02920d240a481374a4c8c5127db2d599498a8c15102972d2e0258142248401080204340026e4871b0e001030200010c0200030406000228001 0x1e81a3e45e098b413159e2293b35e0d6a4e89783d2906a300729a1a5241ca2869410727a0e4d41c96839250d03c13164362884b590f6a20e9781d2e83a55094a40e4b81c2b03855090941a118241d078360705c120b4362c86c510f6b21ed441d2e84a5a074ac0e9541c970892c070bc0e1743425068460f0741e0d81c170482d8a69e1ad2e19a386b438249e1e92df92387a430d47e1e8edc91b86a330729ee052c1ca3b71430727e1a4ec1c9b869330725e1e4ac1c93879236a03c1ad3c35a586b470d6861e93c3d2587a470f4861a8fc351d86a370d4660e53c1ca70394b0728e0e50c44a10393f072760e4dc1c998392f072560e49c1c918584f0b0961611c2c218583f0b076160dc2c198582f0b0561609c2c1186c5f0d8b61b15c362987b5f0f6b61ed5c3da986b4f0d6961ad1c35a183a5f074bc0e96c1d2b83a53114a40e93c1d2583a47074860e8fc1d1d83a37074660e4881c2f8885e070b60e1681c2b84856070a60e1481c278384b070940e11c3423038430707e0e0ec1c1d038370f06c0e0cc1c0eb501c0d6800e12035a003a5c664a0165602ca83205c0b0b0ac1502c282f0445406816100462f04c5a098ac2314835ad08b560b69c16d358126ab2450d47abc8d4349c869310b0b4161081c2005812098b0b11401c2005840116bc12d6825ab08b525a694acd183d2d08a560f494a89182d1f05a3d0f2521e4842c2d058320706016048462f86c5b118ae1b14c45af87b5b116ae1ed4c35a787b4b6268e1ad0c1d2f88a5e114b60e95c452988a520749e1a92c1d2386a430747e1e8ec1d1b87a330b2b4165482ca5059420b274164c81c950585f110bc1616c242d05857090ac1614c2c290584f0b096161282c23ae0460b086160fc2c1d8583a0b06ea40d82c198381d096b412d5825a304b454449a9c914351e9f2350d2bc225481ca6869490728a1a504349c86931110ba221544426858491108a161042c1c858314469a94d14252d04a560948c129143d1d1e2360f2bc225481ca6879490728a1e5043c9487921110ba221544426858491108a161042c1485821462900e510a0a80393c24260160e1081a1c130 15 32767 6 63 11 2047 19 524287
def cc_44_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x8901033daf6324e5b26b30d6212b055582ab014e229c05302a6014a0a940520290512002400409e55b08e70d131a00253c4a0068b0d000b3c160000b 0x462f06c520d4941a91844af0495a092ac2254af89d5e1360b25c164b42c2d058220b0402317c462f08c57118a422d7c45ad88b57116a7b0d2f59a386a5f114b61a95c452986a4b0d48e1a8ff511d86a37ce466165682c910585f110bc1616c242d05857090ac1614c2c290583f0b076160e82c1be00360b066160bee8170582b070541609c1c13058230b0442317845af04b5a096ac22d48452f08a520727a1a4e41c9a869310d25a1a4942c0908c5e116be22d6c45ab88b530d4be1a96c352b86a530d47e1a8ec351b86a330b24422178242b5b0360d05c0e0982ca4530540b0901654290225005498058160a03412058209e08958912702a05828aa048161001ca64f134118bc13168262b08c52116b422d582da705b4d114bc2294a991ed22350729b305241ca2d1141a0273384c42c2d05812116bc1ed483d1d07a36112bc1256824ab08952982952c5182c970592d0b0b4160882c1008c5f118b62315c462988b5f116bc22d5c45a95934fb068e1e97c452d87a57114a61e93eb92587a47a84861e8ec3d1b8595a0b2441617c442f0585b090b41615c242b058530b0a41613c2c258584a0b08f341182c218582f9405c160ac1c15058270704c1608c2c1108c5e098b413158462908b5e116a4229781ca6879490728a1e5043c9e879350b0242317c462d88c57118a622d783d2f87a5b0f4ae1e94c3d2787a4b0f48e1e90c2c910885e090ad201183c1703826096b412d5825a304b457c49b18914351ebb2350729a1a5241ca2869410d2721a4c4340f04b5e0d6ba12d3825a14425d094aa0e57424ac839550d2a21a079f1a6c2345094b412958252304a450f474e88d81ca6879490728a1e5043c94879210f03d00d7425aa84a5e0f4ba1293825210395d092b20e5543ca88781e 15 32767 6 63 11 2047 19 524287
def cc_44_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xfc07d07e03f00f417907c81e40ec1e643301980c816403201882aa6a6bd1868423829b04d805c42e01604b005412a01404028000 0x7e1307d3447b1440593405828783507734005a308234a8034608a5e08a527f24e7c24205a3e05a3d0393d71139039357a1317912d761250485a0581203c587324c03b587034808a5e08a52039567414a721467113a6f1360592e0592d0485a05822058200481208c5f04c5b04c5708c5308b5f04b5b04b5708b53ae34fac34ba9347a534308a5f04a5b04a5708a53a324fa224b9d247992439723f9623b912378d2330495a059220584f0584b0584a0584783046058430583f0583b0583a0583775036058330582f6e02e0582b0382a058270382605823058220481d0593866044058380595065034630445f02c0582807824058206203469254610440582868024058400393c6214408c5e08c5208b5e04b5a04b5608b5208a5a08a566624a6524605a3e05a3d0393d5f139039356413163129611210585a05812 13 8191 6 63 11 2047 20 1048575
def cc_44_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x8c078a7807807807047006846045e15e05c15c048a4804804804043e13c13a13a03623413403402e30f00c10a1024001 0x4d68a1560a035c9f350059509e05c038580385405850840449c24c9b244058289a024059387904405838980347102c058280782405820780447704404c68954609445893450059409204c038480384405840760349025c8f254058288e02405b4405a4c7d3440594489134058388645005b408524008b5e08b5205b4e05b4d8c24d802458b2398a2310394d7414903945881418713d841350485a0581205a347e2307d2300394c811400484005a38 12 4095 5 31 11 2047 20 1048575
def cc_44_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xe607303981cc0e607207901c41c47e203083840c00d13d0628003a19d00d0668032091208803c21e00a145001840420104080001 0x393cb8144be34abd34604a5a04a56bc24abb24604a3e04a3d0393db313903935ba131b9129b71210581203c5003b5004a5a04a560395eb514ab4146b313ab21360492e0492d048520584a0583a05822058200581204c5f04c5b04c5704c5304b5f04b5b04b5704b53e834fe634be3347df34304a5f04a5b04a5704a53dd24fdc24bd7247d3243d123fd023bcb237c7233049520594a0593a059220484f0484b0484a04847bf046048430483f0483b0483a04837b6036048330482fb102e0482b0382a048270382604823048220481d05848af0447f0348b05405838ad034a823004d68ab560a734005950aa05c058588005405850a804c7d044a74548a0547c04405838a6034059488705405848a40447402c0582806824058208605485044 13 8191 6 63 11 2047 20 1048575
def cc_44_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x86100dd33a0740e81d0319620c05802a65409cd0b210420841081893005c4b8116220440881102024007880f 0x594804848de04405920c2054b502c04828068240482004d68db560da35cd935005950d805c038580385404850c1044d624cd524405928c005404828d40240593804838d203405920b9044b302c04828078240482004c68cf460ce458cd45005940cc04c038480384404840b8034ca25cc925405928b704404828c80240394cc113404b5a04b5604b4e04b4dc624dbd245c523dc42350394db514903945c3141c2139c013105812 11 2047 4 15 11 2047 20 1048575
def cc_44_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xf81cb7ca0c81c42c40c21c01b65b60b60b22b20ac3ac0ac09e79c19c06f733e3202a42a02242202010ca0a10a0081004 0x6b4881a2f013168098ad02452809af01ad69fe6ac06b527f12f01a8f00d2920694101c9e81a4e40726a0693101c928161240b082690390341881a0780d024fc2447812e01a8d1ea680f4340799a03e4970072b8f81507b8283d4501e8080f34547792e3c80e1e0492ef2410351c80e4f40726a0781e03c091880d1f669efa34b7b1a3bc4d0ddc49c06a3e01ca781e52c0728e0794301c9f81e4ec0726e0793301c92b2412d1e086ed03b7601981e078070360781303c0943517c0d8b70945703629c1cd780d69c03a5f03d2d80e95c0f4a603a4f0352580e91c0d48603a35828af01255a08298fd146758a201e4b98e0b68d0533382581a10c0f05c0382b03c1181e0880b032059486282a012121d2088059385e0220120e1ce06805848026b4395581c4680059587202e0121617a0a804850620222ec0d1c2068e13447122a0164e009070e0034 12 4095 5 31 11 2047 21 2097151
def cc_44_8 : Nat → List (Nat × Nat) := unpackCursorV4 0xae835d02b80d157886af669b4e36806d00d90576f285a4822727869f0cc119802e145a08b01160026184c0070a0e0010300c50180020403040600003 0xb09006b409022f01b14a3e6bc07b52035a000e9340748a03a3d01d1ac78578092b4049568e8a901a5180f28a069360349a81a4ba3825a0682e034110160640b0232a45f0362dc9d15c0d8a607b5f929af01ed5c0f6a406b4f035a701ed1c0d68403a5f03d2d80e95c0f4a603a4f0352580e91c0d48603a3d01d1b80e8d40f2be0795e03cad8125680f2ae0495603ca9c845480d29e0794b8d8a501e51c0f28c0694301c9b80e4d80726ad005b4b0299a812c0d0860783b03c1700e0ac0f0460782203c0d8160640f02605811035a781ad1c0949e04a4b0252381290c0947604a3701ca780e52c0728e0394301c9d80e4dc072560392701c9181a12c0d0860783b0241581208c0703c0381b01c0980e0480d8ba06c590362a81b1440f6ba07b55035a501ad18074bc03a5d0352501a9180f47407a3601cae80e564072aa0395101c9c80e4c407252039216782ca541440b0520582101c0f00e04a2c08806b4f035a501ad1c0d68c06a4f0352581a91c0d48607a3b03d1b80e53c072960394701ca180e4ec072720393701c9880e4ac0724e039230342581a10c0f0771702b8a81180e078070360381301c0901ed3c0f68e06a4f0352581a91c0d48606a3b0351b80e53c072960394701ca180e4ec0726e0392b01c9380e48d9c0969404303c1d81a0ac0d0460381e01c0d80e04c0702407b4f03da380e53c072960394701ca180e4ec072720393701c98b3412d260860783b01c0f00e06c0702603812035a781ad2c0d68e06b4303d2781e91c0d47e06a3701ca780e52c0728e0394301c9f80e4ec0726e0393301c9580e49c0b09e0584b02c2381610c0b07e0583b02c1b8160cc0b0560582701c0b80e04c0d8be06c5b0362b81b14c076be03b5e01dad812d68076b31935801dab80ed58076a71835201da8c50d400769e03b4b035a500ed262669003b4701da300ed0c076831234003d2f81e95c0d49e06a4a0352381a9180747e03a3e03d1e80e57c072b60395701ca980e53c072960394701ca180e4ac07252039216582da4414c0d0960684301c1f00e0ec070720383301c190160c6220600782b01c0f00e06c07026038127e09a43cd500d6990315c870aa404511f226804924861b600e9b2164c10a16c024b23fc5100749a03a45024ab420519fc26cee13403c9701e0b80f04405819819a6c18d140f2b20795101ca681e5240728a0794102c248161040f03c0781201ca781a52c0728e0694365025a4010c0d03c0381b0340981a04a008a8058387e122400d01f24b80395c 15 32767 6 63 11 2047 21 2097151
def cc_44_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xb415a02cc3641ad2d682b415a0ab15582a074e1a70485dcbcc504bb97f0b825c02739304980425210074c3801c00e00130042001 0x27e8b807a449c1204dc9027a6b93624001cae4f0542760a1381409b8204e51726c6a93502827822508d3a8049f3e24b9d123cd090c0f4720394f034a580e51c0d2860393501c9781a4ac0724e069236a825a6c10e66057320230340f00e06c0d02606812aa22f544d7c0f6b74d35703da981ed24074be06a5b01d2b81a94c0748a03a3f0351d80e8dc0d4674b15e024ab5284f28626d311340349734c16d320a65403b03c1981a0b80705606823034110160640d6b206b51035a681ad140d46c0395d01caa80e534072920394501ca080e4a40b0920584101c0f00e0480d69e06b4b035a381ad0c0729e0394b01ca380e50c0727e0393b01c9b80e4cc0b09e0584b02c2381610c0b07e0583b02c1b8160cc070360381701c0981b17c0d8b606c570362981ad1a5e4bc04a560352300e57c072b60395701ca980e53c072960394701ca180e4e40724ad105b4b82981a12c0d086058299701400e078070360381301c0900e532586a806b4c03cae4ac5600f2a91d150900a400e552526d80796c024b4012592502c003a4d9312501e9180748a0795d024ad0125580f2aa0394d024a50125180728a039448f89d01e4d80f05c0782202c0c8160440f2bc0795d8e8a54905180f26d2313503c974884b40f05c0782202c0c8160440928804944 13 8191 5 31 11 2047 21 2097151
def cc_44_10 : Nat → List (Nat × Nat) := unpackCursorV4 0xfa73e80fa03e41db7b05ab04649e54f95004a29241490110543050814200f063c00c0c262894125008c222048801f0c217011c0400004000 0xd8ba06c5501daf00ed740d69406b4603d2e81e9640f4aa07a510352681e9140f47a07a3501cae80e564072aa0395101ca480e50407272039316d82ca841440b0720583101c0f00e04ab80a806b4b035a381a9340d49606a4703d2281e8fc0f47607a3703d1980e52c072920394701ca080e4ec0726e0393301c9780e4ac0724e0392303425d740eeb60660782b03c1180e078070360381301c0901ad3c0d68e07a4f03d2581e91c0f48606a3b0351b80e53c072960394701ca180e4ec0726e0392b01c9380e48db4096a00430341d81e0ac0f0460381e01c0d80e04c0702406b4f035a380e53c072960394701ca180e4ec072720393701c98b6412d3e0860683b01c0f00e06c0702603812035a781ad1c0f49e07a4b03d2381e90c0d47606a3701ca780e52c0728e0394301c9d80e4dc0725e0392b01c9380e48c0b09e0584b02c2381610c0b0760583702c178160ac0b04e0582301c0b80e04c078be03c5e01e2d813168078b35f45801e2b80f158078a75e45201e28d691400d6be06b5701da780ed380d69a07a5f03d2d81e95c0f4a603a4f01d2701e936b249803a4b01d2380e9140748603a42ac12001a8f40d47606a3703d1a80e57c072b60395701ca980e4ec072720393101c9780e4ac0724e039236b82da7414c0709c0384b01c2480e10c0708405841ab82001a0ec0f0560782301c0f00e06c070260381201d2680e914092ad55146a489b5084d00d25c0682e03411016066822695345403da4520572a42a9461349e89a012492a08d803a6ca79305385b0092c944134a4126d309140d2b20695101ca681a5240728a0694102c248161040d03c0681201ca781a52c0728e069436b025a7010c0d03c0381b0340981a0480f6914535402c14504d127a6b94524001cae52517a906bc04b5a025ab51cd4a8c4bc07a5aa212b01e9480f490039450349c81a4c40725a0692901c9281a4840b072058312b01481e0840d03c068129f924ce49040f4720393d01c9a81a0780d02541344 14 16383 6 63 11 2047 21 2097151
def cc_44_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x9d009d009d009c02921492008f858d058d008b838b808b808a8280945fc257904c173e1c3e003493340134003087300130002d852d802d802d80278c0d35001a 0x2f88a003b5001e2f00f1480d8a203c50bf1af01ad4ac869c06b4dbe926dd49140d47b7b235024a48125040d2720693102c248161040d03c0681203d2648c9100f2d97913c0701800f1800f6c12313803c98034080078a00494002c205cd140074a003b5e01da901ed44076a17634aba9a35d09780f4a407a4ab912348c8f80f47a049390249881e4a40f2420583902c1881e0780f0258845f0262d81b164098ae06c5303628e1cd7c096b607b59025ab81ed4c0f6a206b4f03da5e08d1c0d68603a5f01d2e81296c094b403a570252b00e9540749e06a4b01d2381a90c0747e07a3b01d1b81e8cc072be0395e01cae81a53f002976114abf8a3de85180d2860793fbc09dc844eaee26f7113603c998124bc0925c0492d0242d82214c11096068430441d81e0cc6e05c0382b0441482208c2a044088210601002206c0b0320881302c0881e9640f4a207a4d03d2281e8d4072ba0395501ca680e5240728a0394101c9c8161240b0820381e01c0901e93c0f49607a4703d2180e53c072960394701ca180e4bc072560392701c9181613c0b0960584702c218160bc0b0560582702c1180e06c0702e03813b79af012d580f4be07a5b03d2b81e94c0f48a07a3501caf80e56c072ae0395301ca480e4d40725e0392b01c9380e48dba0b6a305302c1cdb80e00f0560782301c0f00e06c070260381201d26db09280d48c03a45034ae812568092ac0695501ca68125280928c0394501ca24804e80d26c0682e034110160640b0220395cb522a01ed200d2b969158034aa4745423e27003944b3a3601a5b0092d004964b30b001a5780d2ba06946b20a2c744eac626c0692eb109681a0b80d0440581902c0881b17ed68bc06c57036295a0d7c0f6b76535703da981ad2c0f69206b47035a080e97c0d4b603a570352980e9340748e03a4501d1f81a8ec0746e06a33034af81a5780d2b60495a034ab8125580d2a76115201ca380e5180728a0693f0349dc6c4e80d26e0693603499b7016d440a60684b2b81d81e0cc0d05c0382b0341181a0880d03605819034098160440969604b470352581a91c0947e04a3b0251b8128cc072960394701c9d80e4dc072660392f01c9580e49c072460684b0241d8120cc0f0560782301c0f00e06c0702603812 16 65535 7 127 11 2047 21 2097151
def cc_44_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x8545c0649dd4cce416700336059016c80064002f4597a00bc815e402c6594c2e86bf3ad11aa58b3444e961d5405f18290c118607c2036101a020c02028701400050a0005 0xcf91a00e5340d29203945034a081a4e40d2520584902c2081a0780d025a4344cf12f0129580d2be0695b034ab81a54c0d292069390349480e495be0b6a505302c1481a0780d036068130340901ad3c0969604b47035a181e93c0949604a4703d2181a8fc0d47606a370351980e53c072960394701ca180e4fc072760393701c9980e4bc072560392701c9181613c090960584302c1f8160ec0b06e0583302c178160ac0b04e0582301c0d80e05c0702603c5fc822f00f1740d6be04b5b025ab81ad4c0769e03b4d01da580ed1c0d68a03b4303d2f81296c094ae07a5301d2780e9340749603a4703d2280e90c0d47e06a3b0351b81a8cc072b60495a01cac80e55c072ac0395301ca880e51c0728c0394501c9f80e4ec0726e0393301c9780e4ac0724e039230242d82214c070960384a02c24e701200708c0384301c2081a0ec0d0660782b03c1180e078070360381901c0980e048110221601002c240135a334ac006c6003db001ad03322b804958c98aa0125432c2899213401e2d013164078b003c56025ad012d580969c04b4dcb926e4c9140d47b96235034a481a5040d2720693102c2481610411072068310340f01a048078b003b5a025ac80ed60076ad9434ac99a3012968094ac07a4ac91230128f80947a0793903c9881e4a40f2420583902c188220a40f0420781e03c090131640d8a204b5903da880e974094b403a5601d2a80e578072ba0694a034a301e4e80f26c0392e0249680e0b80705203822044108220800b032058110262f81316c098b204c570262981b144096be04b5b025ac812d5c096a607b51035a781ed2f3068e06b4301d2f812978074ba03a5701d2a81294c094a403a4f0352580e91c0d48603a3f03d1d80e8dc0f4660395701cab00e5540929e0494b024a501251f2a28c049430249f8124ec0927404937c889b0124cc0925f9012e0249681216c090a60884b034218220ec0f0663802e01c1582208c110440481b02c0c81204c0902204b4f025a5812d1c0968604a4f0252581291c0948606a3f0351d81a8dc0d4660394f01ca580e51c072860393f01c9d80e4dc072660392f01c9580e49c072460484b0242181a0ec0d0660782b03c1180e078070360381301c0901293c0949604a470252180e53c072960394901ca380e50c072820392f01c9580e49c072460484b0242181e0ac0f0460381e01c0d80e04c0702404b4f025a5812d1c0968604a4f0252581291c0948606a3f0351d81a8dc0d4660394f01ca580e51c072860393f01c9d80e4dc072660392f01c9580e49c072460484b0242181e0ec0f0660682b0341180e078070360381301c09012d3c0969604b47025a180e53c072960394901ca380e50c072820393f01c9d80e4dc072660484b0242181a0ec0d0660381e01c0d80e04c0702404b4f025a5812d1c0968604a4f0252581291c0948606a3f0351d81a8dc0d4660394f01ca700e52c0728e03943024a100e4fc072760393701c9980e4bc072560392701c9181212c0908e0484302c1f8160ec0b06e0583302c178160ac0b04e0582301c0d80e05c0702603c5f01e2f013174076be03b5e035aee38d70076b603b5701daa80ed4c076a58d350025a7812d2c0968e04b4301d2f80e9780f4bb8c25c01d2d80e95c074aa03a5301d2962c9400949e04a4b0252381290c0d47e06a3b0351b81a8cc072be0395e01cae80e53c0729c0394b01ca480e50c092840394101c9f80e4ec0726e0393301c9780e4ac0724e0392301c2f00e16c070b20385301c29016147140a00484b0242181a0ec0d0660782b03c1180e078070360381301c09604960074a80395c034a85f8510110417925801d2a00e5700f2a174134044105f055007289731340a01001b1400f6a006b400249204c0402404005818026b46195800d8c007b60035a000e9730a4a18415c8e8ac5d4553062a17b144b909a0440800d4b964254034b66044f02006003d60036305905200d2800f020 17 131071 7 127 11 2047 21 2097151
def cc_44_13 : Nat → List (Nat × Nat) := unpackCursorV4 0x9b1a50793064819105c606d11ac23ac4e803904dc23700d813504c053000c002e08b802a10a80241890023048c00a642800a002800a0000a 0x6b400352e470940072a8079440349a01ad02384b006a5403d2201a8d0072b81d0200e01006c08034021bc45e036296ecd780f6a406b400352f6149480749a06a4a0352300e9140747a07a3a0351b00e8d7742bc0495a024ab60c5480729a0794501c9e81a4d40d25d1c12d0341701a0a40d044330210c8100160640b023a634002ca8148110ca069a534002cac7e917fe88bdf145b0262d7b915c098ade8453f1229778d7fb26bdd6357e99a973c97f904bdc4257df9296908c00d2bf9815b034abe0854c0d29e0394ddf0a5c6c5240d28e03945de8a1ee45040f27a0693b0349b81e4d40d25a0792b0349381a495c60b6a9053dc0258161276e086058413581d9600ac7203c0681b1880985c04b6a489a325cd091a6b8d035a681ac340d912e01a573622a1b0050d70a06b4103588a9a225cd011e6ac0e35249da024201c9680e4940d03c06812d381a6d0d3f66697af347d51a1e7c93b5047c0694f034a581a51c0d2860693f0349d81a4e40d26e069330349880e495c4096a7043d301de940cc0d03c0681b0340981a04b46493a2241d091ce808c40727a039350349481a4840d03c06812 14 16383 6 63 11 2047 21 2097151
def cc_44_14 : Nat → List (Nat × Nat) := unpackCursorV4 0xbc5bc0bc0bc0bc0954940940886880880671641640621585580580580580580580314300300300246240221220220011 0x131a3c28c1c745c0262a77c950096b5dd359025ab770d440969404b46e612f70c94bb6495da24601ca680e51640273bc1310349681a4940b072058311d80f07c04b8e8d804c640262c761143aa6d9d726c0262d01315baa6bdd434ee592f7089480d2b206951034a481a5040726a0692d034928161240b0820681e03409745153a268004c68e923071d170098a9d0354025ad738d64096adcd351025a5012d1b984bdcb252e51257249180729a039458f89ceec4c40f25a0792502c1c8160c47403c1e012e3a36013190098b1c6450e29b67049b0098a804c5a0262b70cd7b846a5c125ee012701e5640f2a20794903ca081e4f40f26a0392502c248161040f03c07812 12 4095 5 31 11 2047 21 2097151
def cc_44_15 : Nat → List (Nat × Nat) := unpackCursorV4 0x91040c1c60b195232885440a01500278505c8013f09c98d866632a49500a42501242118470e3421908c806402e202a8084040001 0x1ff35d7f8d55c734d7e0d140795901e5440394d01e5240394501e5040793901e4c4058490161040781e01e049c745e01316804c567c9149d535e7049780394d01a5240394501a5040693501a494058490161040681e01a04a0445f80915e0035e7f497804a567f09180695f01e56c0695701e54c0694b01e5240694701e5040693501e4a40392539816cac0531b012c0582901e0780681b01e04c078127cd1a1e7460013151d035477c951b4230744d31e035c08c081f245e79d175f93467e0d15f72467d89140394d7d452403945474504058490161043e01e088049ed3540160e1f356c013591dd46c7c8d71ce26c6cc90004c587b1141b1230013161eb4506c08c1c746c013161ea450714db1d726c6bc8c00696c7c0581ef0606b8901ad2407b4d71ac2407b0541eb0506ac8c1e756c7a9591dc46c012d71cd26c6a8901e9038745151e025401604005a3c7900c1e145d761155c735e79cd75d225d7189559a1596185440393d7984e40393560c4c4e50592ac145e503a0160e40583878c0d8058310f007820012780951e0350 13 8191 5 31 11 2047 22 4194303
def cc_44_16 : Nat → List (Nat × Nat) := unpackCursorV4 0x8c81035a001ba575c62b801662acc055909c3d3802700471c7564ab0154025163a407400e801a0c34006800bc50b3216002030400058a0b000058000 0x4b5a012d5804b46012d1404a5e012949c724d7d89160923d7148d40394d87852403945598505671395404c405849016104088390220c44001e02204803c5001250005840012d7804b5201296804a5601e9394f24201e8e807a3600e5780395259852a1c14601e4e8079360124b80492d01e0b80782901e088088210220800581901604404b5f874d7404b5b012d5c04b55012d4c04b4f012d2c04b47012d0c04a5f01297a1525d01293c04a4e01290a0723f7108dc0495f00e5740495b0125640495700e5540495386c5440494f01252c0494701250c0793f5944ec079375344cc0792b01e49c0485b012164048530161440484b01210c0883b0220cc0882b0fc0780781b02204c08812864d51c334471c972142440220a004d64012d91c235485cd12132547c8910088480220a1c734d7e0d1404a56012919c123600e5340794900e5140794101e4a4058490161040882901e0780781271d179f2452850d7a1335200e5340794900e5140794101e4f4079350161240584101e07807812022d3c04b4b012d1c08b4301e53c0494b01251c0794301e4fc0793b01e4dc0793301613c0484b01610c0583f0160ec058370160cc0581f01e0780581b01605c0581301604a1845f01316c04c5785914c04b566fcd1a1525e8489180795f01256c0795901255c0795301e5440794f01e52c0794701e50c0793901e4a40392501216c0885302212c088430220e4058298440a00781e01e06c0781301e04804b5683cd19d523500e5340394501a4e40692901a4840583901a0780681282c9760825571c935f624501a5640695100e5340694900e5140694101a4a4069210161240584101a078068128311520b36c012d91c735c012d51c12348251b1f636c012d920835c012d520e45e834d7804b5682897e072577f08d40695f01a56c0695701a54c0694501a4e40393501a4ac0692901a49c069213a016cae0530160e45902b01a0780681b01a04c06812814d51ff26c012991c725c012951d524480cdb1f826c012991fe25c01295004a56804919c123600e5340394501e4e40793101e4a40582901e07807812 15 32767 6 63 11 2047 22 4194303
def cc_44_17 : Nat → List (Nat × Nat) := unpackCursorV4 0xbaad720eb6bcab18d9f0d39e8cb5206808cb1596031c46302c2117c22f805f00be015892b005582ab014c2a845500290411629537241833543ca801e 0x1c735d7e0d5404b4e012d0804a5601295404a4a01291a0323a75c8d80395d8fc564039554a05452912943048405859016144088290220844401e02204803b500124c00583001317804c5201296804a5601a92806a4601a8f90b23200e5780395201a528069464a04ea3d1360124b80492d01a0b80682901a088088210220800581901604404b5f012d7a3a35d012d3c04b4e012d0804a5f8f897404a5b01295c04a5501294c04a4f01292c04a4701290e0223b7588dc0495f00e5740495b0125640495700e554049538f05440494f01252c0494701250c0693b01a4dc0692f49c4ac0692742448c0485b012164048530161440484b01210c0883b0220ac0882310c0780681b02204c08812012d5804b4671c935f62457548d40394d01a5240394501a50406939016124058410220e40681e01a049c735e7c8d4a2925e85c9480393d01a4e40393501a4c40692d01a494058390160c40681e01a04808a4f01292c04a4702290c0694f01252c0494701a50c0692f01a4ac0692701a48c0584f01212c058430160bc0582b01609c0582301607c0681e01606c0581701604c0581201315a3a35e8d497c04a5b01295e1625374c9163923501a57c0495b01a5640495701a54c0695101a5240693900e4d40692f01a4ac0692701a48c0485b02214c088490160e6380380220ac0882301a0780681b01a04c0681271d1422f3548d0911cc2348b9151c735c72c912292340220e1d246c8c8d61f93548d09122b3448c9171f835472891004a347e4d322a340012991c92347e4d79c735d8bcd3a2e34201297404a558308f5d023500e5756915900e5562d1515a84e55313101616405851108078250128acd722a45482cdb1c735c8a48d00883801e971222504988e0039540124e003c5801e9797925201e8e807a3600e568039565a452a261460124e80493601e4b92212d01e0b8078220160640581148896007a5401e5b00395c5d04d23635f012d6c04b578d4d4e3334f7d0d363134b8c0d1e2c3458a0d0c04a5a01295c04a5601291c04a460129160a23f8008e9cf2377208d80795f01256c0495761c54c0794f00e5362714b8945240794700e516241434845040793f5a04ec079375444cc0792b4944a40792741c4840485b02214c0884b016124088430161040883b0220cc0882b0220a4088211040780781b02204c2401201253c0494b0125240494701250c0694101212c0484301a0780681b01a04c0681201316804c56012d7804b5a012d5804b520129780394d01e5240394501e5040793d01e4e40793501e4c405849016104088390220c40781e01e04804b4f012d2c04b47012d0c04a4e01253c0494b01251c0494301e4fc0793b01e4dc0793301212c048430220ec0883301e0780781b01e04c0781201317c04c5b01315c04c53012d7804a56888932212468809100495f01256c0495901255c0495301e5440794f01e52c0794701e50c0792900e4940485b01214c0884b02210c0582901e0780781b01e04c07812 15 32767 6 63 11 2047 22 4194303
def cc_44_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x31c4c607084be12f80ac4ab00ab06985a11680190422c554dd20c33547950078000 0x1e146c8bcd12502587dc9524b244940d71db3447d895004a44012d51f724c928901da234012d3404b458d097a192527dc939c724d8148e9df23600e5352b14900e5164d1414b04a50f121016124058411180782701292c9324a3547fc9b1c725c8509100882801a971622505b09200395401252003b5801a9798125201a92806a4600e56803956012528049464ac4ea4713601a4b96212d01a0b8068220160640581158896006a5401a5b00395c5f851004b5a012d5c04b56012d1c04b46012d163625f01296c04a5786094e5124f7d09364f24b93891e4c24592490e0e23d8108edde2377648d40695f01256c0495762054c0694f00e5364814b9185240694700e516451435845040693b5ac4e4069375504c40692f4a84ac0692743448c0485b02214c0884b016124088430161040883b0220e4088310220ac088231140780681b02204c2601201253c0494b0125240494701250c0694101212c0484301a0780681b01a04c0681201317804b5a012d5804a5e01296804a560129480393d01a4e40393501a4c40692d01a4a40692501a484058390160c4088290220840681e01a04804b4e01293c04a4b01291c04a4301253c0494b01251c0494301a4bc0692b01a49c0692301212c048430220ac0882301a0780681b01a04c0681201317804b5601297c04a5b01295c04a5390c8e2422359048d00495f01256c0495901255c0495301a5440693900e4d40692f01a4ac0692701a48c0485b01214c058390220ac0882301a0780681b01a04c06812 14 16383 6 63 11 2047 22 4194303
def cur_44 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_44_18 (Nat.sub p 576)) (cc_44_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_44_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_44_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_44_14 (Nat.sub p 448)) (Nat.blt p 480)) (cc_44_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_44_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_44_11 (Nat.sub p 352)) (Nat.blt p 384)) (cc_44_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_44_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_44_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_44_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_44_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_44_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_44_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_44_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_44_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_44_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_44_0 p) (Nat.blt p 32)
def f_44 : Nat → Nat × Nat := unpackForestF 0x24549f2835c91525c8a91e4d28322a4592d26494d52454872294b91c9b48a5264528600b4f9051c4828d64146800b4b8fcacc789763d26d1e151005a3c70d7a3846b1c038005a1c48d7e246a71a244891a7c6517224697123478b5a745ad0a2d2a3123458adae4531522946912343890a5c4c51a242931214300527c409322048d1024400525c3c5261b6bb0e14686ca880291e196a908c5f85da242314e114bd09b5e84da942291a1105000a4383da340f17a076bd05c5482db640e97e088d90435c81d2b8028fe056a8fe45f80db63f915e0148cfe35e7f9aebfcd55fc4bcfe2460051db6f17df568cfab457d5233ea915f5292dbc5e7cab63e4d71b78b6f79607bc3036f15deb6b8f59507ac283d3591e9070dbc5378daebc64e5e3074f203078c1b36f149df8c0f035077d2a36ed7dda6b2ed351769253b4919b76bcebc5075d3636ed5dd46bcea34e6dda93a1181d1680e83546dd2fb92d65c96a2e4a5e72529392929c948cdba5e7163638b141c56d8dba57701af380d49c04bce024e6dd2936e52db7286dd45e6e9af374579b7282db84b6dc218028ddb5488d2b4f695a5b60971b02a0d8050695a3b5a501ad080d5c546ac1c34ad0da949cd2a3e69c1a34a0eda5066cf34468124b40905a0472d023167d1a33c97801466ce048004a7b33581992b8c834765926b2c8d59028cc934a649a33249199026cc812e004a5b14d718a6a0c525c629283141400128eb8c5f5c5afb07581834a0c195c60ca82e2d1d81278b894b5c4a3af6d797b49abe4505ed1aae251979278b893b5c49bae4d297268cb925e5ce282e49197126c009435b9af2dc0e00127eb624a5862f2d3151692b0b0b5f59a362cc581616aeb11455889b2c44b5612a40093b55e2c2af1495b076ae05456c19aaf14157498aba4055c200024dd5528c98c5e54a2a2a4551316bea746c5393029c5b1316aea62454c4af2624f1448bca235e511a928897945480a22564c49b264d39416889924f4fe2e26492d3b6b89d9504ec2826491d358b89b9404dc2026ad5135050992434c815a6408d31268009334b92f25c0a00125e95b544acac23717d286d89416046e2ba4c9291b6bc911464889aa444b51b2a48e45e471af2385791c2a48e12d46ca50024ad116b088b5245415a2c1111504688b50445a4222d011106000927439aa21c550eb8be8536c429302145b0eb8ae841463adaf20cd14eb2bc7594c3fa2f1fd148fe6bc803403f9ab1fc978eb28c7e2443b1a79d8d2cf74b87b9503dc281d8d1cf42807a0403ca2a1e40e0ec68677a493bd209d8938ec076760333aca200248ce908858b4f39c1a162d2ce4ac07205c2c5a39c1150e1688700342c5a19bc110b149e58a4b362b01b0d70d86a06c05c2c5239a8930d44886a0242c5219a40d0b147e58a3b33230199160cc8a06604c2c51b990970c84a8640242c519980934c047a60235300a09804e4c1268601312c42316ed28b768c5ba4a2dd2316e4c4b72525c1442dc909620d8b2294591462c89d1644d8b105c0084b2bc220dcd3cad0683734b2aab01541706e68e5404c29a2a14c0d06e686520441b9278dc92c9eac04f35c279a813c1706e48e4d24c269221340906e4864c0341b91f8dc8ec928c04945824a281241306e46e4725c2392a11c0906e4664224d2111c9088c489268421412109e90b14085480421351b8230ecd28812803b3461d9270fc4c07d6883b2421eca20ec4c47625a3bb501dda00ec4946e06c3794a1cd260de5186f274383481bc9b0dc0b8010862eb4b175a38ba8ec684a834024175198c29286148c30931184948c4510612422e8361789d0bc4d85d05c0083b16c1b0020cc4a69e25347129258aa91055048252431391e89c8d44e2822713913c9a09c4c44a08c2594a12ca30940b801056240460041188c9143769e2225d0dda3884d143749e2035d0dd238751783d0681d4520e9af0749783746e1b94b0dca1802078350380081b0c9280641702968e17a4d0bd1a8521182a694164500a9a30549182906c0081309d22804d3c2568a0124f08ca4031178210680c452061af030978182840d34e06927034538182800c04d0091b8045380228609450048a60245000d46e0693b0349b81a4ac0d24e01142025268145000946a0103700da500d1400368c0214000d2300409c010240001f 10 11
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 594 bds_44 (dagTraceF m_44 s_44 8 f_44) (cur_44 0) s_44 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 64 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_2 : treeBlockF 64 96 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_3 : treeBlockF 96 128 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_4 : treeBlockF 128 160 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_5 : treeBlockF 160 192 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_6 : treeBlockF 192 224 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_7 : treeBlockF 224 256 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_8 : treeBlockF 256 288 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_9 : treeBlockF 288 320 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_10 : treeBlockF 320 352 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_11 : treeBlockF 352 384 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_12 : treeBlockF 384 416 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_13 : treeBlockF 416 448 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_14 : treeBlockF 448 480 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_15 : treeBlockF 480 512 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_16 : treeBlockF 512 544 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_17 : treeBlockF 544 576 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_18 : treeBlockF 576 594 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nj_44_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_1 (fun _ h1 h2 => treeBlockF_at nb_44_2 h1 h2)
theorem nj_44_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_2 (fun _ h1 h2 => treeBlockF_at nb_44_3 h1 h2)
theorem nj_44_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_3 (fun _ h1 h2 => treeBlockF_at nb_44_4 h1 h2)
theorem nj_44_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_4 (fun _ h1 h2 => treeBlockF_at nb_44_5 h1 h2)
theorem nj_44_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_5 (fun _ h1 h2 => treeBlockF_at nb_44_6 h1 h2)
theorem nj_44_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_6 (fun _ h1 h2 => treeBlockF_at nb_44_7 h1 h2)
theorem nj_44_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_7 (fun _ h1 h2 => treeBlockF_at nb_44_8 h1 h2)
theorem nj_44_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_8 (fun _ h1 h2 => treeBlockF_at nb_44_9 h1 h2)
theorem nj_44_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_9 (fun _ h1 h2 => treeBlockF_at nb_44_10 h1 h2)
theorem nj_44_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_10 (fun _ h1 h2 => treeBlockF_at nb_44_11 h1 h2)
theorem nj_44_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_11 (fun _ h1 h2 => treeBlockF_at nb_44_12 h1 h2)
theorem nj_44_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_12 (fun _ h1 h2 => treeBlockF_at nb_44_13 h1 h2)
theorem nj_44_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_13 (fun _ h1 h2 => treeBlockF_at nb_44_14 h1 h2)
theorem nj_44_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_14 (fun _ h1 h2 => treeBlockF_at nb_44_15 h1 h2)
theorem nj_44_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_15 (fun _ h1 h2 => treeBlockF_at nb_44_16 h1 h2)
theorem nj_44_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_16 (fun _ h1 h2 => treeBlockF_at nb_44_17 h1 h2)
theorem nj_44_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := block_join nj_44_17 (fun _ h1 h2 => treeBlockF_at nb_44_18 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) cur_44) i = true := nj_44_18
theorem lb_44 : LowerBin m_44 s_44 g_44 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xffff0000ffff
def s_45 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_45 : Nat := 0x151700007f7f
def ep_45 : Nat := 0x6a6800000000000000000000000200000000000004060000080800001012000020200000151400004040
theorem epk_45 : ep_45 = edgePack 0xffff0000ffff g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_20, s_20, 5, g_20), (m_23, s_23, 5, g_23), (m_35, s_35, 5, g_35), (m_4, s_4, 4, g_4), (m_12, s_12, 4, g_12), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_22
  · exact lb_20
  · exact lb_23
  · exact lb_35
  · exact lb_4
  · exact lb_12
  · exact lb_0
  · exact lb_1
  · exact lb_2
  · exact lb_3
theorem sub_45 : ∀ b ∈ bds_45, 0xffff0000ffff &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 7 f_45) (cur_45 0) s_45 7 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 7 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xffff0000ffff0000
def s_46 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_46 : Nat := 0x117000001570000
def ep_46 : Nat := 0x40000000000000000000000016000000560000010600000102000001120000010200000114000001540000
theorem epk_46 : ep_46 = edgePack 0xffff0000ffff0000 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_36, s_36, 7, g_36), (m_24, s_24, 5, g_24), (m_34, s_34, 5, g_34), (m_21, s_21, 5, g_21), (m_11, s_11, 4, g_11), (m_13, s_13, 4, g_13), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_36
  · exact lb_24
  · exact lb_34
  · exact lb_21
  · exact lb_11
  · exact lb_13
  · exact lb_7
  · exact lb_8
  · exact lb_9
  · exact lb_10
theorem sub_46 : ∀ b ∈ bds_46, 0xffff0000ffff0000 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 7 f_46) (cur_46 0) s_46 7 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 7 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xffffffff
def s_47 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_47 : Nat := 0x1577f7f
def ep_47 : Nat := 0x7e280000000000560000000000000102080800000000010220200000000001544040
theorem epk_47 : ep_47 = edgePack 0xffffffff g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 6, g_32), (m_27, s_27, 5, g_27), (m_29, s_29, 5, g_29), (m_31, s_31, 5, g_31), (m_25, s_25, 5, g_25), (m_34, s_34, 5, g_34), (m_5, s_5, 4, g_5), (m_8, s_8, 4, g_8), (m_10, s_10, 4, g_10)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_27
  · exact lb_29
  · exact lb_31
  · exact lb_25
  · exact lb_34
  · exact lb_5
  · exact lb_8
  · exact lb_10
theorem sub_47 : ∀ b ∈ bds_47, 0xffffffff &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x950b29064e149c093812702307be5f7c80f709ee038957100e009c0038006e86c855453211e4182800cfe09f033e007c00f801d4724d823980310001 0x395c07c540058580141500404401604007b440164b01b34a01ed181a24a02291807a34064528051460164e4089310164a40792101e0e4160310220a41202108d16807c56088d6808b5601ed1004a5e0809681e25601294807949054504089390444c40392d0744a4039250384840785a00c15805849016104058390160c40782d01e0a8058290160a01c02601e0941802401608403a340580d006c5e01b14807b49054d0403a5e01a94803a4d00e9140495e01a568069560125480394e00e5341413e0384c80685a01a1580784d01e1140581100e8d0120340125700f15401606006b5e01ad4808b4e044d0803a5e01a94803a3d00e8d40495e01a568069560125481014e0385080393e00e4f40685a01a1580883d0220d405811012d3c06b4b01ad1c04b4301293c06a4b01a91c04a4301e8fc07a3b01e8dc07a3300e53c0694b00e51c0494300e4fc0693b00e4dc0693300e4bc0692b00e49c0692301611c068460161140583f0160ec058370160cc0582f0160ac0582701608c0581f01a0780581d01717805c5d01ed6407b5101ad3407b4502296408a5101a93408a4500e5740395501a524069410121780485d0121380584a016124058480121080584101e0f80583a01e0d8058320220b80582a0220980582201e91007b5401ed1005a4402251008a540229100594401ed1008a4401e8d00615c0145500494c01051005b4f016d3805b4d01e93c0a24b01e91c092430128fc06a3d01a8ec06a3701e8d404a3302253c0814b02251c071430124fc0693d01a4ec069370224d4049330224bc0792b01e49c0312300e13c0384701a10c0383f01a0ec0683900e0dc0483301a0c40382f01a0ac0382701a08c0381f01a06c0381701a04c06b4f098d2c07b4701ad0c06a4f09092c08a4701a90c08a3f01e8ec07a3705c8cc0394f01a52c0394701a50c0393f01e4ec0393704c4cc0392f0224ac0392703448c0684f01612c0c04a02c11c0204601610c0783f0160ec078370160cc0882f0160ac0882701608e4e34f900d2e3d3478dcd0e3324f87c92e1624784090e0623f7ec8edf92376748cd8314f58851d5913f55c4dd4e12f53049d4104f4f812d2504747c10d0a03f4080eccd0372d80cc9b02f24c0ac5e02711c08c3601d0d006c280170040540001f 15 32767 6 63 11 2047 22 4194303
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xa30146028c05180a283334a448c4127bb2d199418a7c14f02932d240a48040247f04fe01fc03e066a4869b0d000e301c0008c00c1010202000010000 0x1d8ae3e45a0f8acf4d6845ab07b44094bcf0969d12b04a520b092161042c1c858310f05a160a43c12858210f02a13178262e84b5d0f6aa1ed2425a084a5d114aa2292425208485a0b0b2121582428848460b08a160542e2f05c5d0f6b21ed443da687b45114b222944452688a45090bc1217424270584909084161042c0a868140f69f14d2c3da3c33431149f0492c4523bf2431147e1e8ec3d1bb92337009e1612db823858430f07e160ec3c1b858331105e160ac4413858236a02a1ad3c35a586b470d6861a93c352586a470d4861e8fc3d1d87a370f4660e53c1ca583947072860e4fc1c9d83937072660e4bc1c9583927072461613c2c258584a0b08e1a1182c218583f0b076160dc2c198582f0b0561609c2c1186c5f0d8b61b15c362986b5f0d6b61ad5c35a987b4f0f6961ed1c3da18595f0b2b6165682cab869560b2a61653c2ca5859470b286164fc2c9d859370b2660e4941c2f8485e070b60e1681c2b86856070a60e1481c278784e070960e11c1c21838420707e220f81c1d83837070660e0c81c12b5024072481ed103e2a302505a4800e8f1991c03a34544600e4f01c9a05838640680e8d0362f06c520f692c0d041d2f0495e0d2b41a55824a90394e0729abc4f9509903925072481e1343c2283825074681257158aa039240d6bc1ad4845a72d342074bc1257834ad06956092a4b053950a10393e0727a0e4941c920883d1106a0e094362f86c5b0d8ae1b14c35af86b5b0d6ae1ad4c45a787b4b0f68ec4d0c1d2f83a5e074b61a9681d2b83a56074a6129481d2783a4e074960e91c1d21ae2420747e0e8f81d1d83a3707466a48c81caf039560729c0e5181c9f039360725c1a17c2c2d8685a0d0ae1a1582c298784f0b0961e11c2c218883f0b076220dc2c1983819098bc1314825a704b4d0f4928c905391ca02310d2b21a5441ca6839450727a1a4e41c9a869310d0b41a1583c26878450f07a160e43c1a85831096bc12d4845a7223424a49c80908251f04a3d0d2b21a5441c9e839350725a1a4a41c92869210d0b41a158441e888351105a160a444128582136048680902c1421024 15 32767 6 63 11 2047 19 524287
def cc_47_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x943d28023e4c7038e011229f0d3e007c00f705b6e36c06d80da0578f2f005e00a269440288050829044e4f0d3e1a00253c4a0068b0d000b3c160000b 0x7c5f9045b07c578c4538a35a04b528934883342743406e25a07a4a6815f641575f14f079470393d0885f0585b08857058530784f0584b07847058430883d058210881d0581b08817088150486c570640385c058585d054038504f04c4c04403824560544b044038345b3605a06c0386803864058600485c550544e04c4a0440382404b4f04b4b04b4704b4304a4b04a4307a3b07a330494f049470693f069370692f0484f0484b048470583f0583b05837058330582f058230581d0581b05817058155625005c5e05c5d07b5907b5107b4d07b4907b4507b4108a5908a5108a4908a4107a3e07a320395d039555714d551450485d048550584d0584905845058410582d058250581d058155225007b4f07b4b07b4707b4308a4b08a4307a3e07a3b07a3307a325314f511470793f079370892f0584f05847058430583f0583b05837058330582f0582d05825058230581d0581b058170581507b4f07b4b07b4707b4308a4b08a4307a3b07a334f14f4e1470793f079370892f0584f0584b05847058430583f0583b058370582f058230581d0581b05817058154b25008a4b08a434c14f4a1470892f0584f0584b05847058430582f0582d05825058230581d0581b058170581506b4f06b4b06b4706b4306a4b06a4307a3b07a330394f0394b03947039430393f0393b03937039330392f039230584f0584b05847058430583f0583b05837058330582f05823038170381307c5f07c5b07c5707c5308b5b08b5307b4e07b4b07b4307b425c25f5925707a4f07a4708a3f0595f0595b05957059530594f0594b05947059430593f0593d059350592d0592b05927059250585f0485e0585d5805c0585b0585a0585754056058555005405853048520584f0784e0584d4d04c0584b05847058454904405843058420583f0883e0583d0582d0582b0382a0582703826058254802404c5e04c5204b4e04b4d07a493e241462393c2310784d078450783d0583907835058310681504c5a04c5607b4e04b4d4423904a310483d0583907835048310681504b5e04b5208b4e3d3424224e3c24204a3e04a3d0883d088350882d0582908825058210681504b5a04b564024e04a4208a3e04a3d0482d05829088250482106815 15 32767 6 63 11 2047 20 1048575
def cc_47_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x8a386286086084184082178576176049746146046038738024a2402402212202011461401401400c40a10a00a0081004 0x71690fa901fcae3d92479048f6911e5223eb547c498f449016143c02461498e0d2a0927c024b7e48eee90c1f1eb594f6528eec4bdd4938444f058961111c162182c310885e0b0ac221382c230883a0b06c220b8441507c68e4935c52283e35058720b0c4220e8441504ea4e6d09c1a037a3d03a7a110f4161482c210883a11055a9a4353406d6b007d41b1a435b40694b0074f00fb433b6066690cad0185a430b40636a0c4d200fa030248 12 4095 5 31 10 1023 19 524287
def cc_47_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xc907240c4163f58f023038b062c08711dd0605d11c44010c13e14f803d04f013618d802a3080a1f047031c007001a080d701080400004000 0x3a349e34803a4c9d24808a4403a4007c5fb345b07c57b045308b5bae35a08b5608b5307b4b07b4a07b4608b4308a5f04a5e08a5baa25a08a5708a5608a5304a5208a4f08a4e07a4b07a4708a43a424205a3f05a3e05a3da115f9f1579c14f079470893f0892f0392d08927039250885f0585b08857058530784f0584b07847058430583905833058310881d0581b08817088150385c9a0540382403824983609706c038640382407b5907b5107b4d07b4507a320395d039550485d05859048550585105849058410582d0581d0581506b4f06b4b06b4706b430394f0394b03947039430393f0393b03937039330584f0584b05847058430583f0583b05837058330381b038170381307c5f07c5b07c5707c5307b429925f9625707a4f07a470595f0595b05957059530594f0594b05947059430593d0592d0592b05927059250485e950560784e03826940240581e8134088350923488634007a58912487c34004a30873508f34804b408e248058488d0448b24e862420392d039250885d088550882d0482908825048210881d088156c14f661470784f0584b07847058430781d0581b0781707815813487c3488525405848853400395c07c5e8845a07c56874527335a07b4804a5e8625a8425604a526314d079450392d039250784d058490784505841058310782d078250781d078157235807b488124c 14 16383 6 63 11 2047 20 1048575
def cc_47_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xdb036c0c16b040c103001af4645e53f948152012c74a052804515140324cc803200c802630941240490023048810b5c2810a001060400004 0x7b4b07b4308a4f08a4b08a4708a4307a3f07a33be14fbd1470793f0892f089270584f0584b05847058430583f058330582f0582b058270581d0581b0581705815ba35007b4b07b43bb14fb91470793f0584f0584b05847058430583f0583d05835058330581d0581b058170581506b4b06b4306a4f06a4b06a4706a4307a3f07a330394f0394b03947039430393f039330392f0392b03927039230584f0584b05847058430583f058330582f0582b0582705823038170381307c5b07c5308b5f08b5b08b5708b5307b4f07b4907b4308b41cb25fc825707a4f08a3f08a370595f0595b05957059530594f0594d059450593f0593b05937059330592d0592b05927059250585f0485e0585dc705c0585b0585a05857c305605855bf05405853048520584f0784e0584d0583f0883e0583dbc03c0583b0583705835b803405833058320582d0582b0382a058270382605825b702405a3407b58b5348a925008a4cb424808a44a724004a34b234804a4cb124808a4404a4004b5e08b5d08b5504b5208b4ea834204a3d05a3a05a3604a3504a340393d039350882a05829af026058210881d0881508a5608a55ad24ea724208a3eac23d0392d03925ab026088250881d0881504a4404a340395c07b44a945a07c56a835a08b5607b4404a5ea725aa625604a5207a4e08a4d07a3e07a3d0392d0392505849058410583905831a5026078250781d0781503a34a335803a5ca225808a5403a500392c08a6c03a6803a64a0260 14 16383 6 63 11 2047 20 1048575
def cc_47_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xb304e5e7013619b04d826832869404a025012048f0c7823c11c18a23679b00c69601b00159479a3c01e00ec23fc1f00f8078201e 0x3b8d29d849eea24b73923b8090c1147ad814f6a0a3b7c4bdbc24e0784f02c2581e11c0b0860583103c178160ac0f04e0582303c0e81606c0f02e078156c920364d21b88b003c506d9ac368931b04800394c01e34359181aa498d4240681a6340901a46a0d125c01d2833c932008b404c527f1ad02297df64b608a577b929bd8931de482dd2400451eb5c57da62ae0394d6709782249c0f0be0585b03c2b81614c0f09a0583103c178160ac0f04e0582303c0e81606c0f02e0781502436318190070b8058586602a00e1417c078bb03401c1231415007088ba034652303241b0070d00386402c30012171880a8bd03c5c81a00e0900969604b430252781292c0948e04a4303d1f81e8cc0929e049470349f81a4bc0d24e0484f0242581211c0b07e0583302c178160ac0b04e0582302c0e81606c0b02e05815629a80171780b8ba07b5903da881ed240f68208a59045288229341149208a450452081e8e4114620395d01caab185358828a0485d0242a8161340b0920584502c208160f40b06a0581d02c0ab04d400f69607b430452782292c1148e08a4303d1f81e8e40f46608a31610a7b0051c0f27e0892f0449381613c0b08e0584302c1f8160f40b06a0583302c178160ac0b04e0582302c0e81606c0b02e05815 13 8191 5 31 11 2047 21 2097151
def cc_47_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x9aa9a09818e58e08c18a17e66aa6816616036006005c22f72072001c21c01a11a01a01431021001000e10e00c1025001 0x4c52ff34df5241ee2400394d0784d05839058310781d07815eb240f435008b4cfd25cf2250fc24ce524004940f3350fa25c04a50f924c05828f8024da14fd51470784f0584b07847058430781d0581b078170781508a44eb34ce534cf125405838f12400395cf545a08b5ef435a08b56f335208b4c04a5ef225af025604a52d213d089350392d03925058410783d0583907835058310782d078250781d07815ed24de924508a3505839058310781d07815ed35808b48eb24ce9348e6240e815ce4124e2024e4244e2244e6354e524ce312405828e1024d024c 12 4095 5 31 11 2047 20 1048575
def cc_47_8 : Nat → List (Nat × Nat) := unpackCursorV4 0xca02dd3b702dc0b702accaa06a80a31e881a2027459c06700961a5809212441910230557d55c0540d4c153013c43f40a170c703000030000 0x98bc07c5d03e2a8131480969a05b4a02da3012d140968807a495492080e5340728a0783a02c1cc780d80b0620781d03c0a81ed580f6aa07b4e8e1a6c6c8e54e4620393d01c9ac680d80f06a0781d03c0a816d10116b8a83408c12e45c9300f49007a4453920012d122a4b91424c0252401e9100948003b448922c00ed72226b007b5401da800e4f00f6d803b6801db243cd80076890d25c8612600e9200f48803a4003e2dc751680f8ac07c5303daf812d780f6b71935a03dab81ed580f6a604b5202da7816d380b69a08a5f8b12d82295e264a607a4f0452681e9140f48607a3f03d1d81e8e40f46e07a3352118c4057e1c2ae0794f03c9f80e4f40f26e039358589782249c0f0be0585b03c2b81614c0b0920584302c2081e0bc0b0560782702c1181e0740b0360781703c0a80e172120a80382401c1241d1820c0d80386401c12022964114a208a4d045228228c4072ba039550242e816164090aa0585102c248161040b07a0581d02c0a81a93c0d49606a470352180e53c072960394701ca180e4bc072560392701c9181613c0b0960584702c218160bc0b0560582702c1180e06c0702e03813045af822d6c116ae08b53045a0c2097e0a4ae08a3f0451b81657c0b2b60595702ca98165340b27e0593b02c9b8164cc0b25a0592b02c93816494090bd040560441f00e09a060480581e8091cbc88c40727a0393503c2e81e1540f07a0483903c1a8120c40f03a07815 14 16383 6 63 11 2047 21 2097151
def cc_47_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xc441c185bf05bf00b514b500b500b206af85ad05ad00a314a300a300a0069f029e029d819c829b039b009b0099049704900e6f425e2253164222371623280046 0x4c5f03e2d81f15c098a604b5f045ad822d5c096a607b4f03da581ed1c0f68604a5f0352b81a93c0d48e06a3f0351b81257c092bc0595d02cab816554092a60495202ca781652c0b28e0594302c9f8164ec0b26e0593302c968164ac0b25405927034930164941824805857a002b0161540b09e0784e02c2581611c0b0860584202c1f8220f80b0760583702c198160c80b05a0582b01c1501609c0704c058259f81201207c0903c0481d03e364711800f6a9380340500a4711a00f8c807c5402daa024052728b407c5602dad016d580f6aa05b5403da7470d340f4932f2419d91ccac8c40727a0393503c2681e1140907a0483503c0e81e056728c007b6802db00160e27006806814045b62b0d80114a9310240400a2b0da0116c808b5402d2a01c052646b408b56045a74b8d080b4b405a560452a8169526849d2b2420451f2b08f40725a039250441e8220d40905a048250440e822056646c008a6802d300160a2620480681402e2a4a89500b6a9292540300a00e5700a02805a5401c920120900b8a12a340949200100500f68808a4403d1a0125425e8c007c54971b0022d500f6892d26c539344b0992564c004a5c9412a0160a24e0480301402e2f8171780b8ba07b5f9e9adc64d640f6af3c3539d1a8812d3c0f69b3734b03da381ed140968608a5f9b12daa8964114af352539992881293c1149b3024b045238229140948608a3f03d1d81e8de4c4660695f01cae81a55c072aa0494f034a381a4fc0d26e0692f0349381217c090bc0485d024278121380b09605849024218121080b0820783f02c1d81e0dc0b0660882f02c1582209c0b0463701d02c0d81a0680d02e068160580a8080500969e04b4b025a3812d0c0949e04a4b0252381290c0f47e07a3b03d1b81e8cc0929e049470349f81a4dc0d25e069270242781212c0908e0484302c1f8160ec0b06e0583302c178160ac0b04e0582302c0e81606c0b02e058150252781292c0948e04a43024a781251c0d25e0692702427812134090960484702c2281210c0b05e0582b02c1381608c0b03a0581b02c0b8160540969e04b4b025a3812d0c0949e04a4b0252381290c0f47e07a3b03d1b81e8cc0929e049470349f81a4dc0d25e069270242781212c0908e0484302c1f8160ec0b06e0583302c178160ac0b04e0582302c0e81606c0b02e05815025a7812d2c0968e04b43024a781251c0d27e0693702427812134090960484702c2281210c0b07e0583b02c1b8160cc0b03a0581b02c0b8160540969e04b4b025a3812d0c0949e04a4b0252381290c0f47e07a3b03d1b81e8cc0729e0394701ca180e4fc072760393701c9980e4bc072560392701c9181213c090960484a02423812118090860583f02c1d8160dc0b0660582f02c1581609c0b0460381b01c0b80e04c098be04c5b0262b81314c096be04b5b025ab812d4c0f69e07b4b03da381ed0c094be04a570352781a91c0d47e06a37024af812574092b60495a024ab8125580b2aa0594f02ca581651c0b2860593f02c9d8164dc0b2660592d02c9581649c0b24a0485f0242f0121740909e0784e02426c90130090960484702422c8c11009086048420241f8220f80907b2203c0241d8120dc0906b21034024198120c80905a0482b01c1501209c0704c048259001201207c0b03c0481d 16 65535 7 127 11 2047 21 2097151
def cc_47_10 : Nat → List (Nat × Nat) := unpackCursorV4 0xcd839b030ea61c0bc1f4cb27c74ad39407260a4c0494192811152220408f6b58c8396a9ad404fac9f0112b224044808901100a1c13e163dfc4cb8026 0x1c9201b1680d8ac06b5e035a957cd3abc68404a5e0352d01a958094a403a3e01d1e80e5793c07a600354e8168160a6ba04a0582101c0a81b1680d8ac04b5e035ad01ad58096a49d239ad91880e5780f09c0784201c1f00e0f40702a038140362d81b1680d8ac06c5301daf812d78076b603b5a01dab81ad58076a603b520352f81a96c0d4ae06a53b0927d8090c0747e03a3bae11c80e8dc0746603a3101caf01a17c0d0b6068570342981e13c0f0860383f01c1e80e0ec0b07203837ad01a80e0cc070629c02f03c1597c09c0f046038150362d01ad680d6ac04a5e0352d01a958094a40783903c1881e0b40b0520782502c1080e0540d8b404c52035ad01a97c0d4b606a5703529d609040d0be0685b0342b81a14c0f09a0584103c1781e0ac0f04e0782301c0ad50d700747803924a99ae00e4900724806c5e03629012d780d6b406b56025a900ed380769a06a5a0352b550926a64820395e86826b3c1161807a05839a901a8160c40702a06b5a035ab0129780d4b406a560252943093aa04840395e0441f0220c80705c0382d01c0a80e0500d8be06c5b0362b81b14c0d6b606b5a035ab01ad4eac6975534301d2f812978074b603a5a01d2b81a958074a603a5201d27d449380749603a4701d2180e908072bc0685f0342d81a15c0d0a70b04f04425b3811c110860883f0441980e0bc0705a0382b02c1480e09e9e04a0382301c1080e0540d8b406c56035ad0129780d4b406a5602529022124110820882d02c148220940b042038150362f81b16c0d8ae06c53035ad012d4a9a68406a5a0342f81a16c0d0ae068530442782212c1108e088430441e8160c40702a04c5e02629012d78096ba04b5c025a9012d380969a07a49a3920d2c8e6884620694d034a280e4f40726a0784d03c2281e0f40f06a0781d0340a812d78096a408b4ea31a1012978094ba04a5c0252952493a8848404a3e0251e81a4f40d26a0392d01c928220f41106a0882d044128220740d02a04a5c01cae01f1928e8b008b64a31ac01ed10094d9452640252e510962864a804a500262f813178098ba04b5f025ae812d6c096ae07b55025a9812d3c096974a349025a3812d0c0968204a5f0252e81296c094ae08a550252981293c09497482490252381290c0948208a3f03d1d81e8de844660495f024ab81253c0729a0494701ca281a4fc0d26e0692f0349381216c090b4058590242b812158090a6048510242381211a8008a0783f02c1d81e0dc0b0660882f02c1582209c0b0463801d02c0d81a05c0d02a05c5e0262e81ed640f6a204b4d03da2822964114a204a4d0452280e574072aa0485e0242e8121380b09204842024208160740b0340681602c0a81a0500969e06b4b035a3812d0c0949e06a4b0352381290c0f47e07a3b03d1b81e8cc0729e0394b01ca380e4fc072760393701c9980e4bc072560392701c9181213c0b09605847024218160fc0b0760583702c198160bc0b0560582702c1180e06c0702e03813 15 32767 6 63 11 2047 21 2097151
def cc_47_11 : Nat → List (Nat × Nat) := unpackCursorV4 0xee0f703a85950c80e403087801c005d0ee81701b60d616a05500a60d2069014419a24d022911408614302084d0d0b7820c004000 0x1d1c5f49000746006b5a035ab5dcd2ae468d7e24eb512100e8f80747a0395e4c01c96c0c54005a05829be0128160840702a03b44bd2305e4db0076c803a34bb9b05d89b0074c96d230b691800f1a2e88c173360b91305c08c2de4b96d250b791a5b0092d84696d34401c920160a2d604970344b713600e9a0074c96a2600252e5a49500724804b5cb391c012972ca49804c59b31acc3cd46c84b2a025101caf00e538070ac038550342501a1180702a0381401daf80ed6c076b203b5701da9dfcd440969e06b4b035a3812d0c074be03a5b01d2c80e95c074a77b2510252781a92c0d48e04a43bc11fdd48eee246f6823301caf00e538070bf6305d01c2d80e164070ae0385501c298161440909e0684b0342381210e1c07f0503b6981bb200cd3e05e9602b3201396408c0702a03b4caf92400e4d2bc69003924 13 8191 6 63 11 2047 21 2097151
def cc_47_12 : Nat → List (Nat × Nat) := unpackCursorV4 0xbd823318c023007d3df407d01b8f6e01b806a11a806a0198465058446101840610180160018005f0554a54054c1443c4f112044801008010 0x1a145a03e2b680d68116ac07b440252f67c96a584ac04a5202d248229040b47207a3101c9680e4940f0b52705603c270161240f084058410441f0160e40f064058315281701e0b40f03a0781a1900b01e05430029f845bfaa2d7cd15be28a7f035bf59ad79cd5bca6a7e1344ed92f81297baa4b7ce25ae312bee895b524a604a52c38afda055ec029f5513fd309780e4b74824e03925a102f81e16e4c0ae0785303c278221240f086088410441f81e0e40f06607831d1817a900b40f05605829d1013e780940f046058211c80e81e06c6202e170150262f0131480769c03b4dc9924e38907384738923189026b6c1162207a05839cd81a8160c40702a04b5e025a9654d3b1a6859924ec492100e8f80747aa303d3481aa880b40b0539802502c1080e054076b996354ca92c00e4d3268b003a5cc912a00e493184819045801e2862c8c0072998c34801cae6391631a6b18b34402536628990074b989258c412a00e9400725805b5402d2a01316a226938634151124e14904072ac0394601c9f00e4b8090bc0485201c2700e1340702a03814025af812d6c096ae04b5301da780ed2f3469203b4701da180ed04094be04a5b0252b81294c0749e03a4bcb92480e91c0748603a41ca11fe448ef1e46f8723301cab00e5180727c0392e0242f81216c090ae0485301c2780e134070960584901c23e1011407086038418801fc200edae06ecb03350817a640acd004e5c02301c0a80e93007681812300362d01b1580769c03b4dbd126dcc917044736a23101caf41c125940830f03d02c1ce000d40b06203815 14 16383 6 63 11 2047 21 2097151
def cc_47_13 : Nat → List (Nat × Nat) := unpackCursorV4 0x9a09a09629416b56a06055c25c05445405405405215205014a34814804614032e92e02c1244240202146067041021001 0x395cde80a00e5738a8bdb245de19a4f08d0780493bf241df0af00e574072b803955de0a9628536d228bbb05d02c2ccb01540b0a34504d940228e80743c02bb7354dc9266c44900f051ad024d80926b00936e689b625cd78926ac09360489b0234d89a20129735e4a9ac244d611a6b4d10094b9ab254dc22a012db36a6c9b425cd99266c88f35c24807828d50126a09334e8a95325caf12600e4d34a8a80392c03e2a0229700f49805a3c03c1c2940d00f8a805a3c0442801e1014a058078200e00a06c0503402819014 12 4095 5 31 11 2047 21 2097151
def cc_47_14 : Nat → List (Nat × Nat) := unpackCursorV4 0xd0340c8ac6b02b1a8691a062684610806007c5e14390040100400c4300b111c22080110401000400 0xef1ac774d23c08d1df368ee1a27609a0094c1d4254ed1266d8953824a9c4254eca2a760db38a6c9d725ceb1260128f0072b9c1254e212a084053a84adc5255e9927748937a247dd023d01c9680e4954e05a05829e78128160847803a20015e59ac728d236e481c815ce411a735163986b1c9344025367149636a4a1c716ce09267108f388471c124c 10 1023 4 15 11 2047 21 2097151
def cc_47_15 : Nat → List (Nat × Nat) := unpackCursorV4 0xe0068430214f99c5c54a14b0a085038d1c40c116002d1954aaa05502a8154083441020050005f12f014987d43e01930064000000 0x6c8965d12517fc925fe24100e5740395501e1740585901e1540585101e1340784501e0b40782501e074078157c9169e635a012979b225a75095804a5200e4b40392501e1040783101e0b40582901e0940582101e0740781581116a0235b800d4c04a5e7f4959fc23e64457d751575584fc0392501e17c0785b01e15c0785301e1040783f01e0f40783501e0cc0582901e0940781d01e06c0781701e055e424000e4f40393501e1340783d0160e4078350160c40782d01e074078157e916804c527848c18f15f5c455c0394d01e17c0785b01e15c0785301e1340584101e0f40782d01e0740781b01e05c07815758d2004a6c70c99004a486c8901ef35a7a8d59f734a7d8d1804a5e780975cd25501294804a4a0129180392d00e494058490161040783901e0c4a902d6840943e01d08c055f245d7b8d29e93467d097404a4e0129080392d00e4940585101e1340784501e0e40783101e0b40782501e074078157c9171b33480129b1c22646c892004a4075cd7004a6c70099004a386c88c1ef45a7b9159ed34d7b0d1404a5e77c975cc25501294804a3a0128d80392d00e49408849022104058390160c4a802d6800943d01d08805404a30799175ea34a7a4d19e825d01293804a4200e4b4039250161440884d022114088390220c40882d0220940881d022055b435c798d3004a6c6fc991b22380128c1de24d728915cb23d7748d4058390160c40782d01e0940781d01e055cb34a78cd18058390160c40781d01e055e434a77093dd924b72491db82437888f58b14f5c051da712f69449c0784f01e12c0784701e10c0583101e0bc0782d01e0ac0782701e0940782301e0740781b01e05c07815 13 8191 5 31 11 2047 22 4194303
def cc_47_16 : Nat → List (Nat × Nat) := unpackCursorV4 0x859d0b02160418583010601fc4395962c0c5015eb280f4e86865cab89540278c4f00942928025003a407400bcb0b32160016582c0028c05000028000 0x21d45a869159b235a750d580393d00e4d4088490221040883d0160e4088350160c40881d0220561d4606c8d81ea2408708e00696c7515821a350012d0219260012901e923001a5b00695c00ed3c03b4700ed0c03a4f00e92c03a4700e90c04a3f01a8ec06a370128cc0384f00e1340384b00e11c0884500e10c0483f01a0ec068370120cc0882f0220ac0882702208e1345d878d4404b4f86cd2e18347012d0c04a4279c8c80395d85c5700494f01a51c0693f01a4dc0692d0221740585101213c0884d02212c08847022114048430220fc0883b0220dc088330220b40881d01a06c0681702205404c5e01314804b4e012d3404a5a01295a012496d0905d12396c88c40694d01a5140393d00e4d51504d3e41151403d0160e6150350160c44001d01a05404b52798d09d324e6c890804a3d01a4f40392d00e4940883d0220b40582902209405821022074068150169500392401209004b5a012d5804a5a0129591424e84890808a3e0228c80392d00e4940485e0121480884a3e01180883e0220c80482e0120b40881d01a0680681601a0540681401317c04c5b01315c04c53012d6c04b5a012d5a0034b794d0c04a4f85093804a4b01291c04a4301290804a3f84c8f804a3d01257c0495701a53c0694701a4fc0492f00e4b40492700e4940485f01216c0485701214d1304f02212cf704702210c0883f0220cc0482f0120b40482b0160a404827844094048230120843f01d01a06c0681701a05404c6c82d191f245c6c8d2004b4483c8e004c6c82919004b4874cd120d2386c8d65d335182cd260a34100e574039550221740585902215405851022134088450220f40883502207408815012d79e634e8208d403935022134088450220d4058290160840881d0220560e45b83114c04b5e824d59fc34e81c9699415f5e055d6114f00e4d40885f01e16c0885701e14c0784f0221340884501e10c058390220d4078210220740781b02205c0881501297a052467c88f8039250161240584101e0f40783501e0940781d01e05404b6c7fcd91e634c80c971b22380128d004b6c7f8d920125c0128e1d1234 15 32767 6 63 11 2047 22 4194303
def cc_47_17 : Nat → List (Nat × Nat) := unpackCursorV4 0xb23344826a7cd408fad1c0e0abb5315faaaa553c6201e3e087714e621cc039807300c29180130005b14ae215c02b025600a421345240a47046e80037 0x3b4f00ed1c03b4300e53c0394b00e51c039430124fc0693b01a4dc0493300e13c0384d00e12c0384701e114038430120fc0683b01a0dc0483301e07c0781b01e05c078138f117404b428fc94404a4f8c492e1824701290df323100e5763e15c01253c0694701a4f40692f01a49c0785d0161440484f01e1340784b01e11c0784501210c0783d01e0bc0782b01e09c0782301e0740681b01a05c0781501314804b4d7c8905d12396c88c40694d00e4f40393501e1340783d0160e4078350160c40781d01a05404c5a01315804b5e012d4a0d34e6ccd09d324e6c890804a3e0128f40693d01a4d40392d00e494b203d2380d4b102d0160a63b0250160844401d01a05405a5400e4900482401316804c56012d6804b5601ed3807b422c48e63923100e4f4039350121780485201e138078420120f80483d01e0a88d02601e0740681a01a0580681501a05004c5b01316804c56012d3e3c34e012d3404a5f01296c04a5701294e0c24f7c490c04a3f0128ee3a2390128dc04a330128c40495f01255c0694f0124fc0393d0124dc0393501a4bc0692701217c0485b01215c0485301e13c078430120fc0483d0120ec058390120de380350120cc048312c00bc0782b23009c0782310c0740681b01a05c0681501317804c5a01315804c52012d7804b520129680694d01a5140393d00e4d40884d022124088450221040883d0160e4088350160c40881d01a05404b4f012d2c04b47012d0c04a4a01253c0494701a4fc0693701213c0484b01211c048430220fc0883b0220dc088330220740681b01a05c068150124fc049370120fc0483d0120ec0483701e0d40483301e0740681b01a05c0681501317804b5f012d6c04b57012d4e363498d4d22343440129680495f01255c0394501a4fc0693701217c0485d01216c0485702215404853016124088450220fc0883b0220dc088330220740681b01a05c068157bcd42253488bc971b22408a8d81ee3406c89822e24c01a5b1ed350012d022b2587489422f45a8b9159b234e748d360324975c90404a390128c40393d00e4d51804d3f01151703d0160e62d0350160c44201d094056272448acd71ff2648a8931b223c01a49004b507b0d01d325c8989022724c748d72263547009922524c0229913224c0168f0088382ac0d004b4c0168f0af04c2ac0b00882001297004a5e0129491724e88490804a3e0128c80392d00e4940885a4c41580883e0220c8ab02e0220b40881d02205404c5f8c916e3145701314c04b5e012d4c04b5281cd3a0234b7c0d0deb3428c093e2c24e8a492e2824789090dce2420128fc04a3e0128f40495f01a55c0694f01a51c0693f01a4f40693501a4bc0392d01a49c0392501217c0885b4c015c0485345813c0884b3ec11c088430220fcae03d1b80d40883388c0bcaa02d0220ac0582988809e2002502208c058211040740681b01a05c24015 15 32767 6 63 11 2047 22 4194303
def cc_47_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x3115af568cc857a0057f05ec47b01a52651194064058045b1558555051500edc00e 0x4c5a012d7804b5a012d5804b5201297804a5201a4f40693500e4b40392501e0f40783901e0d40783101e0b40582901e0940582101e07406815012d2804a4f01292c04a4701290c0494f01251c0692f01a49c0484f01212c0484701210c0782f01e0ac0782701e08c0781d01a06c0681701a0540494f01251c0484f0121340484b01211c0784501210c0781d01a06c0681701a05404c5e012d6804a5f01296c04a5701294e512499409224f24401257c0495700e5140692f01a49c0485f0121740485b01215c0785501214c0584901e1140782f01e0ac0782701e08c0781d01a06c0681701a0560b364874d71b234c9309200693491c8d1f7350930d31d03400129422535a870d5a0f34e758d0804a4e012909b223e7408f40392d00e494b503d2440d4b402d0160a64a0250160844601d09c05404c50744d31f62509188c24723c740d224634470c9922f25c01ed913935c016d300784846811004c5c016d311e05c4680f00783001297004b5e012d4804b4e012d08b42399088c40393d00e4d40785a4e01580784e01e1091a03e01e0f40781d01e05404c5e01314c04c52012d3c04b4e012d3404a5f8c896e1b25701294e0e24f810925f82437d49064d23f92c8ee492399208de452337388c40495f01a55c0694f01a5340694501a4fc0393d01a4dc0393501a4bc0692701217c0785b4dc15c0485301e13d1d04d3f8114078439100fd1903d01e0ec0583990c0de4103501e0cc058312cc0bc0782b24009c078231140740681b01a05c260158a8d6a193566c8969d425600e4b40392501e0e40783101e0b40582901e0940582101e07407815 14 16383 6 63 11 2047 22 4194303
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_47_18 (Nat.sub p 576)) (cc_47_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_47_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_47_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_47_14 (Nat.sub p 448)) (Nat.blt p 480)) (cc_47_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_47_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_47_11 (Nat.sub p 352)) (Nat.blt p 384)) (cc_47_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_47_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_47_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_47_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_47_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_47_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_47_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_47_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_47_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_47_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0x24f49327a4893d22002d3e4147f2634c9051dc940964147320a3791d1e48cd12414672083f9041bc848c64106a00b4b8f928c7c5700168f1c34e8ec12c708e6394631c035005a1c68d26346911a34400527c4116e208af1024f8b62d45b15a2d06b1024e8a9ae454932204971024789d2644ad52254991024388017c4009e214851002500525c2ed461c8c10e23885da5c32d42194c10bb4785cae00291e1506b08a4e8451f42490a1104a00a4383d1c40f16e0d47103c53829a4c14d06076ad0423581d2d0028fe0548cfe45a80d2e3f8d6e014b8fe3537f924bfc905fc4acfe23e0051dbf51680146ecf45b7d9a53ecd199e8b4fa25d67a2b3e51719e8a6cf35b7b22d3d9159ec69af6345679ad3d0d29e868cf425d679ab3ccd319e6a6f134a78da33c48f59e688ee468771b43bad61dd690ee3446792fbb4931d68a8eb36c7592e3ac9319e4b6e7a5673d2739e935cf47ce7a3d73c12b3c969c78b0e3b58729ac394d21c7688e423471cb633c95dbb8bce22386eda4b76d05c1498dda496ed20b76579bd028dd9526ec2eb3c959b9498d54546d9a236c971aa6c8d525c6a9263548f1af688d82346bd2a354491ab688d62346ad2a3540919e4a6d424c69e2a33c4bda58a8cf12767817b3c09d9f8b4cfb5a67d2d33c09401466cda3966c1ab08d259849ccc02561124b2ad51954b0c223f64a2c32495184476c84586111bb11161886b0c6348621a2310991884b0c425461119b0ad0585482c2045004a7b008e581460c003558da8af89397d480be02558d28af3181796d8b1a3f5d9b02ec9b163476b94605c9b02e49816346eb4b445bd1a2d29b16b688b62345ac122d2981694a8b1a3359d1c2c8d6565498b225958c2e80251d5a49ead243575a72bad095d04aad23956d18ab40d40127eac2410049ba9ed2d4f686a924954920aa40d54f49ca824253c128024bd4d6840092752d1ca84d254949ca124950e2c286d61434c8a1a5850d2a2848cc0109e9f8564fc1200212d266b6933534ed1ca4cd45388c09c034499a5a4c96d264a69a24e49928a62d81310489324b49e3024ed81274d893a6449d30252d012948093a5449c1224c8cc0108e9004c480222400f1200689002400421a3c0d90b8b48d34d4691ca340d90b6b48ba5c45d2621696d144b88a24c42d29a23161116b08595f43db021655d0c4b88624c42c978020fd090a881a5f41a3020c1b1034ae8185640c120020ed014726745a3fda699cd68fc4b87e24c3392d9f0970f84987c0243392999c930f08b47835a3c1a91e0968f148078256339209bcd28ed6b06f24f3ad261bc92ce86907415c379239c2d50e149872244384921c4910e10486f243378979bc49cce4806c458361ac1b0930d96906c240338af9a9180d44986a240338ab99ed40cf4b86824033d2619c4bc0106e660542dd2f993180c90d85ba572dc2e188534c56a0621452dc2b18053cc16a0601472dc2a17a53cbd28e5b83c2e4a7974d40b928e5b8342dc120020ccb46905a2482722d962d20b14904e4532bc13138d68ab49c55a3d2ac13138968a58b452b5a2952d14a958a504c4e242289ac1449609c2be50260270ab93ad209d4904e14f00417934150944be4bb6025c3612895c940ac4a02400415922d20914902fc5b235a411a9208d0882fc5322d270bed685f6904245a21229108968856804225617da10ea93c814983aa4b1fcae0ea91c786a83c24c1ed220f0490794883c0241d5218ea4bc7524e2fb401bda10e29347148a37b401bd1e8be968696b034b481a5a00d4d00694b02f95f195b00cad20656802f957181a80c0d20616803024817ca780209c5d0a82425f169b00b41b0484ae2405c154a68ac9405528a24056144a78a49405128e24054138a789c51c480982514f12d2809451c48088240240041188c8e437696222390dda1884938374962024e0dd218751683a6b41d25a0ecae074958374661b84f0dc23802074350480081b0c91c0640d02968617b410bc9f0529082a6841514e0acaa054508294640081709d1c804d2c2549c0124b0622d030d68210480c25a07ca8030958182520c026065a5032928192940c0240091982c0d0146820a13e008998240d00e6840714e03caa01c508022460104a0082380692c034860194b00ca1808570042a80214400c918041180102a0001f 10 11
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 594 bds_47 (dagTraceF m_47 s_47 8 f_47) (cur_47 0) s_47 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 64 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_2 : treeBlockF 64 96 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_3 : treeBlockF 96 128 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_4 : treeBlockF 128 160 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_5 : treeBlockF 160 192 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_6 : treeBlockF 192 224 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_7 : treeBlockF 224 256 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_8 : treeBlockF 256 288 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_9 : treeBlockF 288 320 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_10 : treeBlockF 320 352 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_11 : treeBlockF 352 384 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_12 : treeBlockF 384 416 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_13 : treeBlockF 416 448 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_14 : treeBlockF 448 480 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_15 : treeBlockF 480 512 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_16 : treeBlockF 512 544 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_17 : treeBlockF 544 576 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_18 : treeBlockF 576 594 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nj_47_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_1 (fun _ h1 h2 => treeBlockF_at nb_47_2 h1 h2)
theorem nj_47_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_2 (fun _ h1 h2 => treeBlockF_at nb_47_3 h1 h2)
theorem nj_47_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_3 (fun _ h1 h2 => treeBlockF_at nb_47_4 h1 h2)
theorem nj_47_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_4 (fun _ h1 h2 => treeBlockF_at nb_47_5 h1 h2)
theorem nj_47_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_5 (fun _ h1 h2 => treeBlockF_at nb_47_6 h1 h2)
theorem nj_47_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_6 (fun _ h1 h2 => treeBlockF_at nb_47_7 h1 h2)
theorem nj_47_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_7 (fun _ h1 h2 => treeBlockF_at nb_47_8 h1 h2)
theorem nj_47_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_8 (fun _ h1 h2 => treeBlockF_at nb_47_9 h1 h2)
theorem nj_47_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_9 (fun _ h1 h2 => treeBlockF_at nb_47_10 h1 h2)
theorem nj_47_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_10 (fun _ h1 h2 => treeBlockF_at nb_47_11 h1 h2)
theorem nj_47_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_11 (fun _ h1 h2 => treeBlockF_at nb_47_12 h1 h2)
theorem nj_47_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_12 (fun _ h1 h2 => treeBlockF_at nb_47_13 h1 h2)
theorem nj_47_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_13 (fun _ h1 h2 => treeBlockF_at nb_47_14 h1 h2)
theorem nj_47_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_14 (fun _ h1 h2 => treeBlockF_at nb_47_15 h1 h2)
theorem nj_47_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_15 (fun _ h1 h2 => treeBlockF_at nb_47_16 h1 h2)
theorem nj_47_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_16 (fun _ h1 h2 => treeBlockF_at nb_47_17 h1 h2)
theorem nj_47_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := block_join nj_47_17 (fun _ h1 h2 => treeBlockF_at nb_47_18 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) cur_47) i = true := nj_47_18
theorem lb_47 : LowerBin m_47 s_47 g_47 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xffffffff00000000
def s_48 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_48 : Nat := 0x117151700000000
def ep_48 : Nat := 0x1400000000000016000200000000010604060000000001121012000000000114151400000000
theorem epk_48 : ep_48 = edgePack 0xffffffff00000000 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_36, s_36, 7, g_36), (m_28, s_28, 5, g_28), (m_30, s_30, 5, g_30), (m_33, s_33, 5, g_33), (m_35, s_35, 5, g_35), (m_26, s_26, 5, g_26), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9), (m_11, s_11, 4, g_11), (m_12, s_12, 4, g_12), (m_13, s_13, 4, g_13)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_36
  · exact lb_28
  · exact lb_30
  · exact lb_33
  · exact lb_35
  · exact lb_26
  · exact lb_6
  · exact lb_7
  · exact lb_9
  · exact lb_11
  · exact lb_12
  · exact lb_13
theorem sub_48 : ∀ b ∈ bds_48, 0xffffffff00000000 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 7 f_48) (cur_48 0) s_48 7 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 7 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def g_49 : Nat := 0x117151701577f7f
def ep_49 : Nat := 0x406a680000140000007e280016000200560000010604060102080801121012010220200114151401544040
theorem epk_49 : ep_49 = edgePack fullMask g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_44, s_44, 9, g_44), (m_47, s_47, 9, g_47), (m_45, s_45, 8, g_45), (m_46, s_46, 8, g_46), (m_43, s_43, 8, g_43), (m_48, s_48, 8, g_48), (m_41, s_41, 7, g_41), (m_42, s_42, 7, g_42), (m_39, s_39, 7, g_39), (m_40, s_40, 7, g_40), (m_22, s_22, 7, g_22), (m_36, s_36, 7, g_36), (m_37, s_37, 6, g_37), (m_38, s_38, 6, g_38), (m_32, s_32, 6, g_32), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_31, s_31, 5, g_31), (m_15, s_15, 5, g_15), (m_33, s_33, 5, g_33), (m_34, s_34, 5, g_34), (m_35, s_35, 5, g_35), (m_16, s_16, 5, g_16), (m_17, s_17, 5, g_17)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_44
  · exact lb_47
  · exact lb_45
  · exact lb_46
  · exact lb_43
  · exact lb_48
  · exact lb_41
  · exact lb_42
  · exact lb_39
  · exact lb_40
  · exact lb_22
  · exact lb_36
  · exact lb_37
  · exact lb_38
  · exact lb_32
  · exact lb_29
  · exact lb_30
  · exact lb_31
  · exact lb_15
  · exact lb_33
  · exact lb_34
  · exact lb_35
  · exact lb_16
  · exact lb_17
theorem sub_49 : ∀ b ∈ bds_49, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xdca7d890d061cc50c3a3b969b550ad21a910a063a040a0019fc19fc09bd093e089a97eac73ac69e75eec53ec4a273f2c33ae29a825511a6c0eee04e800520001 0x2156f335accd678158c6c6f7d1b86c6d1b19c6c651f18c7c621b17c7c5b1b15c7c531ad9c6b661ad947b5f26d787b5b1ed687b5722d587b531ed487b4f1ed387b4d0e5ac39630e56c39530e52c39430e4ec39390e4cc3931335a88d661b1a88c621b1787c5a1b1586c521adb8cb621ad346b491ad146b410e52439411b9f87e7d1b5f88d7d755f09d6e235b48c7d1b1e46c75231c4cc6a231a48c66231848c56231546b7e1adf46b6e1ada4cb621ad846b5d1ad646b551ad446a7e129f039790e5c439590e5446d6a235889c6a331986c5d1b1646c551f1446b6e32d886b5d1ad646b551ad4439590e5446e7e1f9f48d7d1b5e46d75275c48d6d275a8cd66235946c7e271f5b47c231b88c6d271789c5d1adf86b7d1adb86b6932d886b611ad346b491ad146b411a9f84a7c0e5e439710e52439412612858481b5bc6d6e1f5b46c6f231b46c6b1b1a46c671b1946c6327185c45f3316ccc576914c6b6f1adb86b6d1ad7c6b5e1ad6c6b591ad4cf3521ad446b4f1ad2c6b471ad0c6a6e129b0396b0e5a439630e584395b0e54c394b0e50c393b0e4cccd6e275886c6e231986c5e1f1687c561b1487b6a32d986b4d1ed246b451ed0439490e504ce7e239f48e75279c88d76235d49d6e275b46c7d1f1e8cc761b1d46c5d1f1646c551f1446b7e1adf49b6e1eda88b661ed889b561ed5583541ed387b4d0e56439510e4e439311e0e85838235b46d611b1b47c691b1947c6123178cc521adb47b691ad947b611ed68cb560e5a43961239f89e7d235f88d7d235b88d69335888d611b1f47c791b1d47c711b1b47c6a331986c6522df87b7d58df06b6e1adb48b5e1ed688b561ed487b4e1ed348a7e129f039790e5c439390e4c4783a160e04a34161806c5f1b14d435f4cd6d235744d4ccb4f32d2ccb4732d0c395b0e54c394b0e50c393b0e4cc6d6f1b5b87d6d1b1bc6c6b1b19c6c633317ccc5b3315ccc531adbc6b6e1edb5036c1ad7c6b5e1ad747b4f1ed2c7b471ed0c6a6e0e5ac39630e56c39530e52c39430e4ec39331e0e8dd6f5d5ad55673758c6c6f1b1b47c6b1f1a86c673d1986c651b17c7c5b1b15c7c531adbc6b6e1adb47b5f26d787b5b1ed687b5722d587b531ed487b4f1ed387b4d0e5ac39630e56c39530e52c39430e4ec39390e4cc39311e0e858381b5bc6d6e1b5b48c6f271ac9c692319c9c63271848c5f231749c5b1f1648c57231547c531f1446b6f1adb46b6b1ad9c6b651ad8c6b5f1ad746b5b1ad646b571ad546b531ad446b4b1ad1c6b430e5ac39630e56c39590e54c39510e52c39430e4ec39331b5bc6d6e1b5b48c6f231b47c6b1f1a48c67231949c631f1848c5f2716c9c592315c9c53271446b6f1adb46b6b1ada46b671ad946b631ad846b5f1ad746b5b1ad5c6b551ad4c6b4b1ad1c6b430e5ac39690e58c39610e56c39530e52c39430e4ec3933235bc9d6b2359c9d631b1bcd46e1b1ac6c6a1b19cc4661b18c6c621b17c7c5e1b1746b6f1adac6b671ad8c6b5b22d686b591ad5c6b561ad4c6b511ad1c6b461ad14396b0e58c395b0e54c394b0e52439430e504393b0e4cc7d6f1f5b87d6d231bc8c6d231ac8c67231948c631b17c6c5d2316c8c592315c6c552314c8c511adbc7b6b1eda46b671ed8c7b611ad7c6b5d1ed6c7b591ad5c6b551ed4c7b511ad3c6b471ed0c396b0e58c395b0e56439530e544394b0e50c393b0e4cc7d6f1f5b87d6d231bc6c6d231ac8c691b19c6c652318c8c612317c8c5d2316c8c57231548c531adbc6b6d1edac7b691ad9c6b651ed8c7b611ad7c7b5b1ed646b571ed4c7b511ad3c6b471ed0c396b0e5a439630e584395b0e54c394b0e50c393b0e4cc8d6f235ac8d672358c6c6f1f1ac6c671f18c6c5f231786c5d1b15c6c551f14c7c521edbca36e1edac7b6a1ed9c93661ed8c7b621ad5c6b561ad547b4f1ed387b4d0e5ac39630e56c39530e52c39430e4ec39390e4cc3931235bc8d6d235ac8d67235948d631b19c6c661b1948c5f231787c5b1f1688c571f1588c53231486b6f1adb46b6b1ad9c6b651ad8c6b5f1ad6c6b531ad3c6b4d1ad2c6b491ad1c6b451ad0c6b410e5ac39630e56c39530e52c39490e50c39410e4ec3933235bc8d6d235ac8d67235948d631b1bc6c6e1b1b48c5f231787c5b1f1688c571f1588c53231486b6f1adb46b6b1ad9c6b651ad8c6b5f1ad6c6b531ad3c6b4d1ad2c6b491ad1c6b451ad0c6b410e5ac39630e56c39530e52c39490e50c39410e4ec39333612858481b5bc6d6e1b5ac756a1b59c6d661b58c6562231bc8c6b2319c8c631b17c6c5e1f1746b6f1adac6b671ad8c6b5f1ad786b5d1ad3c6b4e1ad2c6b491ad0c8b421ad0443400e5ac39630e56c39590e54c39510e52c39430e4ec39331b17c6c5b1b15c6c531ed7c7b5b1ed5c7b531ad3c6b4e1ed34395b0e54c394b0e50c393b0e4cc7d6f1f5b87d6d231bc9c6b271a48c672718c9c612317c8c5d2716c6c592315c8c551b14c6c511adbc7b6b1eda46b671ed8c7b611ad7c6b5d1ed6c7b591ad5c6b551ed4c7b511ad3c7b4b1ad1c396b0e58c395b0e56439530e544394b0e50c393b0e4cc7d6f1f5b87d6d231bc8c6d1b1ac6c692319c8c652718c6c612317c9c5b271648c572714c9c511adbc6b6d1edac7b691ad9c6b651ed8c7b611ad7c7b5b1ed646b571ed4c7b511ad3c7b4b1ad1cca6e129b0396b0e5a439630e584395b0e54c394b0e50c393b0e4cc8d6f275ac8d672758c6c6f1f1ac6c671f18c6c5f1b1747c5b1f1686c57231586c55111507b6f0cdb87b6b1eda87b6708d987b631ed886b5f1ad786b5d1ed3c7b4e1ed34396b0e58c395b0e54c394b0e50c393b0e4e439330e4c6f45fb516ec4579514e235f78d6d935738d4cb34f20d2c534704d0c395b0e54c394b0e50c393b0e4cc003f 16 65535 6 63 11 2047 18 262143
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x63a7b83d499e414c8008f831e063c043907740c5a54cfa1612f4e3f7c3d0801e 0x8d6f275b88d6d231aee46a231a48c67231988c63231848c57231588c5536dbe136b70d9cdb6322d7c6b5d22d6c7b5922d5c6b5522d4c7b5122d3c8b4b22d1c8b430e5ac39630e56c39590e54c39510e52c39430e4ec3933235bc9d6e235b48c67231988c652315c8c5627156745432dbccb6b32d9ccb6322d7c8b5b22d5c8b5326d3c9b4b26d1c9b430e5ac39630e56c39530e52c39430e4ec3933235bee56e235b48d67235949d63275888c67231988c652717c9c5e27176436f32daccb675cd8c9b5f22d6c8b5726d4c9b4f1ad349b4b1ed249b471ad149b431ed04396b0e58c395b0e54c394b0e52439430e504393b0e4cc8d6f235b89d6d231bc8c6e231b48c5f231788c5b231648c53991488c5122dbc6b6d22dac7b6922d9c6b6522d8c7b618cd7ccb5b32d5d535322d3c8b4b22d1c8b43229b84a6c0e5ac39690e58c39610e56c39530e52c39430e4ec3933128d058602317c8c53acd7ea35ba4d5e835332d3ccb4b32d1ccb430e56c39530e52c39430e4ec3933235bc8d6e275b48c6f231b89c6d9d1b08c5f231788c5d22dbc8b6b22d9c8b6332d7ccb5b32d5ccb5326d3c9b4b26d1c9b43229b8396b0e58c395b0e54c394b0e50c393b0e4cc984a235bc8d6d275ac9d6a2359e6566235948c6f231b88c6d2717c9c5e27174db6f80dada36736d8c9b5f22d6c8b5726d4c9b4f1ad349b4b1ed249b471ad149b431ed04396b0e58c395b0e54c394b0e52439430e504393b0e4cc984a161207e7e1b9f4cd7e235f48d75275c86d6d275a48d651b5848c76231d46c66271956464271789c5d32de86b791add86b711ad986b651ad346b491ad146b410e5a439610e5243941239f89e7d235f86d7d615f07d6e1b5b48c7e231f48c6e231a4cc62231846c5d231648c551b1446b7d1ade46b751adc4cb6a1ada46b661ad846b561ad548a7e129f039790e5c439590e5446d6f1f5b86d6d371be446b8d19cdc631b17c6c5d1b16c9c591b15c8c551b14c6c511adadf36a1ada46b671ad986b631ad846b571ad586b551ad3c6b4b1ad1c6b430e5ac39630e56c39590e54c39510e52c39430e4ec3933279f88e7d335e88d79235d88d71235988d65331f86c7d1b1d47c721b1b47c691b1947c611add86b7522d987b656cd908b5e1ed688b561ed487b4e1ed3439690e58439390e4c48e7d279e8ce76239d48d7e235f49d6e275b4cc7e1b1f46c751f1c86c5d1f1646c551f1446b761add49b6e1eda88b661ed889b561ed55d3541ed387b4d0e56439510e4e439312616858581b5bc7d6e1b5b4cc6f331accc673318c6c5f1b16c6c571b14c6b671ad986b651ad5c6b561ed5503541ed3c7b4b1ed1c7b430e5ac39630e56c39530e52c39430e4ec3933 15 32767 6 63 11 2047 18 262143
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_49_1 (Nat.sub p 32)) (cc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0x62fdd5b818b60c57a1afd0d6e86af43539e364d59818a71c6b8e3382d7dfadefd637e3702d6ddaf8d45f6e3e3514c16aec3543eb5acdf0face8b5f45ada2d5d16a6836c3e3302d4cc8dc646605a792db896cc0b4b1ab50d588168e145409b704d981686003f 6 11
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 fullMask g_49 ep_49 48 bds_49 (dagTraceF fullMask rootStock 10 f_49) (cur_49 0) rootStock 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_49 ep_49 bds_49 48 (dagTraceF fullMask rootStock 10 f_49) cur_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 48 (dagCheckNodeV4 fullMask g_49 ep_49 bds_49 48 (dagTraceF fullMask rootStock 10 f_49) cur_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 48 → (dagCheckNodeV4 fullMask g_49 ep_49 bds_49 48 (dagTraceF fullMask rootStock 10 f_49) cur_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 48 → (dagCheckNodeV4 fullMask g_49 ep_49 bds_49 48 (dagTraceF fullMask rootStock 10 f_49) cur_49) i = true := nj_49_1
theorem lb_49 : LowerBin fullMask rootStock g_49 11 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def wg : List Gate := [⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [5, 0]⟩, ⟨GateOp.and, [5, 0]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.and, [9, 7]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [14, 3]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [12, 16]⟩]
theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4272455808) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677352 * 2 ^ 32 + 4272455808)) (12 - 1) := by
  rw [show canon fullMask (4276677352 * 2 ^ 32 + 4272455808) = g_49 by decide]
  exact lb_49

end PEqualNP.Outside.L_meta_45423

theorem PEqualNP.Outside.L_meta_45423 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4272455808) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4272455808) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_45423.table2_from_lowerBin (4276677352 * 2 ^ 32 + 4272455808) 12 PEqualNP.Outside.L_meta_45423.root_lb PEqualNP.Outside.L_meta_45423.wg 17 rfl PEqualNP.Outside.L_meta_45423.wfits PEqualNP.Outside.L_meta_45423.weval
