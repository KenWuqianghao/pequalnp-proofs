import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1186

def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

lemma key : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : Bool, circ.eval [v0, v1, v2, v3, v4, v5, v6, v7] =
    ((v0 && v1) || (v0 && v2) || (v0 && v3) || (v1 && v2) || (v3 && v4) || (v3 && v5) || (v6 && v7)) := by
  decide

lemma mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1186

theorem PEqualNP.Outside.L_meta_1186 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x := by
  refine ⟨L_meta_1186.circ, L_meta_1186.mono, by decide, ?_⟩
  intro x
  exact L_meta_1186.key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
