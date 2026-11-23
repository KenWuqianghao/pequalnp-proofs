import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1192

def circ : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

lemma key : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : Bool, circ.eval [v0, v1, v2, v3, v4, v5, v6, v7] =
    ((v0 && v1) || (v0 && v2) || (v0 && v3) || (v1 && v4) || (v1 && v5) || (v2 && v6) || (v3 && v7)) := by
  decide

lemma mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1192

theorem PEqualNP.Outside.L_meta_1192 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) x := by
  refine ⟨L_meta_1192.circ, L_meta_1192.mono, by decide, ?_⟩
  intro x
  exact L_meta_1192.key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
