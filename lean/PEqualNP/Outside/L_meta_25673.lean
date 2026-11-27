import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25673 : (let G := fun (i j : Fin 5) => (25298977 : ℕ).testBit (5 * i.val + j.val)
let u : ℕ := 0
let t : ℕ := 0
(∃ (π : Equiv.Perm (Fin 5)) (K L : Finset (Fin 5)),
    L ⊆ K ∧ L.card ≤ u ∧ 5 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L)))) := by
  refine ⟨((Equiv.swap 0 4).trans (Equiv.swap 4 1)).trans (Equiv.swap 1 3), Finset.univ, ∅, Finset.empty_subset _, by decide, by decide, ?_⟩
  intro i _ j _
  fin_cases i <;> fin_cases j <;> decide
