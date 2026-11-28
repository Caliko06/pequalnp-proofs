import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_32045
import PEqualNP.Outside.L_meta_32046
import PEqualNP.Outside.L_meta_32047
import PEqualNP.Outside.L_meta_32048

theorem PEqualNP.Outside.L_meta_32049 : (∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length) (h : ℕ),
  PEqualNP.MetaComplexity.FanInTwo C → C.size = 10 →
  (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) →
  0 ∈ (C.gates.get i).inputs → (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) →
  (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
  (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → i.val < k.val →
  7 + i.val ∈ (C.gates.get k).inputs → h ∈ (C.gates.get i).inputs → h ≠ 0 → h < 7 + i.val →
  (∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
    (C.wires (List.ofFn x)).getD h false = true) →
  7 ≤ h) := by
  intro C i k h hf hs he h0 hu hor hand hik hk hh hh0 _ hx
  by_contra hlt7
  have hcases : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨x, _, hx1, _, hw⟩ := hx
    have hpre : (C.wires (List.ofFn x)).getD 1 false = (List.ofFn x).getD 1 false :=
      PEqualNP.Outside.L_meta_32045.fold_prefix C.gates (List.ofFn x) 1 (by simp)
    rw [hpre] at hw
    simp [hx1] at hw
  · exact PEqualNP.Outside.L_meta_32045 C i k hf hs he h0 hu hor hand hik hk hh hx
  · exact PEqualNP.Outside.L_meta_32046 C i k hf hs he h0 hu hor hand hik hk hh hx
  · exact PEqualNP.Outside.L_meta_32047 C i k hf hs he h0 hu hor hand hik hk hh hx
  · exact PEqualNP.Outside.L_meta_32048 C i k hf hs he h0 hu hor hand hik hk hh hx
  · obtain ⟨x, _, _, hx6, hw⟩ := hx
    have hpre : (C.wires (List.ofFn x)).getD 6 false = (List.ofFn x).getD 6 false :=
      PEqualNP.Outside.L_meta_32045.fold_prefix C.gates (List.ofFn x) 6 (by simp)
    rw [hpre] at hw
    simp [hx6] at hw
