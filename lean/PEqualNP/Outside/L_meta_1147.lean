import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1147

def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩,
    ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

lemma key : ∀ a b c d e f g h : Bool, circ.eval [a, b, c, d, e, f, g, h] =
    ((a && b) || (a && c) || (d && e) || (d && f) || (g && h)) := by
  decide

lemma mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1147

theorem PEqualNP.Outside.L_meta_1147 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x := by
  refine ⟨L_meta_1147.circ, L_meta_1147.mono, by decide, ?_⟩
  intro x
  exact L_meta_1147.key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
