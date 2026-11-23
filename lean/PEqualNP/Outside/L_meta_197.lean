import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_197_aux

open PEqualNP.CircuitLowerBounds

/-- One evaluation step of a circuit: append the value of gate `g`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

/-- Evaluation only appends wires. -/
theorem foldl_prefix : ∀ (gs : List Gate) (w : List Bool), ∃ r, gs.foldl step w = w ++ r
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨r, hr⟩ := foldl_prefix gs (step w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ r, by
      rw [List.foldl_cons, hr]; simp [step]⟩

/-- If wire `j` (counted from the end of `w`) already reads `true`, replacing gate `j` by the
constant-true gate (AND of nothing) leaves every wire unchanged. -/
theorem foldl_set_true : ∀ (gs : List Gate) (w : List Bool) (j : ℕ),
    (gs.foldl step w).getD (w.length + j) false = true →
    (gs.set j ⟨GateOp.and, []⟩).foldl step w = gs.foldl step w
  | [], _, _, _ => by simp
  | g :: gs, w, 0, h => by
    simp only [List.set_cons_zero, List.foldl_cons]
    obtain ⟨r, hr⟩ := foldl_prefix gs (step w g)
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
      rw [List.foldl_cons, hr, Nat.add_zero] at h
      simpa [step, List.getD_eq_getElem?_getD, List.getElem?_append_left,
        List.getElem?_append_right] using h
    have : step w ⟨GateOp.and, []⟩ = step w g := by
      simp only [step, hv]; rfl
    rw [this]
  | g :: gs, w, k + 1, h => by
    simp only [List.set_cons_succ, List.foldl_cons]
    apply foldl_set_true gs (step w g) k
    have hl : (step w g).length = w.length + 1 := by simp [step]
    rw [hl, Nat.add_assoc, Nat.add_comm 1 k]
    simpa only [List.foldl_cons] using h

end PEqualNP.Outside.L_meta_197_aux

theorem PEqualNP.Outside.L_meta_197 : ∀ (n j : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool), (PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩, output := C.output } x || !((C.wires (List.ofFn x)).getD (n + j) false)) ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD (n + j) false = false ∧ f x = false) := by
  intro n j C f x h
  cases hw : (C.wires (List.ofFn x)).getD (n + j) false with
  | false =>
    right
    refine ⟨rfl, ?_⟩
    rw [hw] at h
    simp only [Bool.not_false, Bool.or_true] at h
    cases hf : f x
    · rfl
    · exact absurd hf.symm h
  | true =>
    left
    rw [hw] at h
    simp only [Bool.not_true, Bool.or_false] at h
    have heq : PEqualNP.MetaComplexity.circuitFun n
        { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩,
          output := C.output } x = PEqualNP.MetaComplexity.circuitFun n C x := by
      have hw' := hw
      rw [PEqualNP.Outside.L_meta_197_aux.wires_eq] at hw'
      have hlen : (List.ofFn x).length = n := List.length_ofFn
      have := PEqualNP.Outside.L_meta_197_aux.foldl_set_true C.gates (List.ofFn x) j
        (by rw [hlen]; exact hw')
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.Outside.L_meta_197_aux.wires_eq]
      rw [this]
    rwa [heq] at h
