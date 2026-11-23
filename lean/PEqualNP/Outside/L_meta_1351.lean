import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1351

def rho (n : ℕ) (σ : Equiv.Perm (Fin n)) (a : ℕ) : ℕ :=
  if h : a < n then (σ ⟨a, h⟩ : ℕ) else a

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rn (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho n σ)⟩

lemma rho_lt (n : ℕ) (σ : Equiv.Perm (Fin n)) (a : ℕ) (h : a < n) : rho n σ a < n := by
  simp [rho, h]

lemma rho_ge (n : ℕ) (σ : Equiv.Perm (Fin n)) (a : ℕ) (h : ¬ a < n) : rho n σ a = a := by
  simp [rho, h]

lemma inv_step (n : ℕ) (σ : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ w w' : List Bool, w.length = w'.length → n ≤ w.length →
      (∀ a, w'.getD (rho n σ a) false = w.getD a false) →
      ∀ a, ((gs.map (rn n σ)).foldl stepF w').getD (rho n σ a) false =
        (gs.foldl stepF w).getD a false := by
  induction gs with
  | nil => intro w w' _ _ h a; exact h a
  | cons g gs ih =>
    intro w w' hl hn h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [stepF, hl]
    · simp [stepF]
      omega
    · intro a
      have hv : (rn n σ g).op.eval ((rn n σ g).inputs.map fun i => w'.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [rn, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact h i
      simp only [stepF]
      rw [hv]
      by_cases ha : a < n
      · have h1 := rho_lt n σ a ha
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h a
      · rw [rho_ge n σ a ha]
        by_cases ha2 : a < w.length
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ ha2]
          have := h a
          rwa [rho_ge n σ a ha] at this
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
            hl]

end PEqualNP.Outside.L_meta_1351

theorem PEqualNP.Outside.L_meta_1351 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (σ : Equiv.Perm (Fin n)), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun h => h.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + j⟩ (List.ofFn (x ∘ σ)) := by
  intro n gates σ
  refine ⟨gates.map (PEqualNP.Outside.L_meta_1351.rn n σ), ?_, ?_, ?_⟩
  · rw [List.map_map]
    rfl
  · rw [List.map_map]
    congr 1
    funext g
    simp [PEqualNP.Outside.L_meta_1351.rn]
  · intro j x
    have key := PEqualNP.Outside.L_meta_1351.inv_step n σ gates (List.ofFn (x ∘ σ)) (List.ofFn x)
      (by simp) (by simp) ?_ (n + j)
    · rw [PEqualNP.Outside.L_meta_1351.rho_ge n σ (n + j) (by omega)] at key
      exact key
    · intro a
      by_cases ha : a < n
      · simp [PEqualNP.Outside.L_meta_1351.rho, ha, List.getD_eq_getElem?_getD]
      · simp [PEqualNP.Outside.L_meta_1351.rho, ha, List.getD_eq_getElem?_getD]
