import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_229

abbrev orF (n : ℕ) : (Fin n → Bool) → Bool := fun x => decide (∃ i : Fin n, x i = true)

lemma orF_false {n : ℕ} {y : Fin n → Bool} (h : orF n y = false) : y = fun _ => false := by
  funext j
  by_contra hj
  have : ∃ i : Fin n, y i = true := ⟨j, by simpa using hj⟩
  simp [orF, this] at h

lemma orF_zero (n : ℕ) : orF n (fun _ => false) = false := by
  simp [orF]

lemma typed_pos {n : ℕ} {τ : (Fin n → Bool) → (Fin n → Bool) → ℕ}
    (hτ : IsTyping n (orF n) τ) {x y : Fin n → Bool} (hx : orF n x = true)
    (hy : orF n y = false) {i : Fin n} (hi : τ x y = (i : ℕ)) : x i = true := by
  obtain ⟨j, hj, hne⟩ := hτ x y hx hy
  have hji : j = i := Fin.ext (by omega)
  subst hji
  have hy0 := orF_false hy
  subst hy0
  simpa using hne

lemma matrix_false_eq_zero {n : ℕ} {τ : (Fin n → Bool) → (Fin n → Bool) → ℕ}
    (hτ : IsTyping n (orF n) τ) (i : Fin n) : typedMatrix n (orF n) τ i false = 0 := by
  ext x y
  simp only [typedMatrix, Matrix.zero_apply]
  split_ifs with h
  · obtain ⟨hx, hy, hi, hxi⟩ := h
    have := typed_pos hτ hx hy hi
    rw [hxi] at this
    exact absurd this (by simp)
  · rfl

lemma matrix_eq_vecMulVec {n : ℕ} (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (i : Fin n)
    (b : Bool) :
    typedMatrix n (orF n) τ i b =
      Matrix.vecMulVec (fun x => typedMatrix n (orF n) τ i b x (fun _ => false))
        (fun y => if y = (fun _ => false) then (1 : ℚ) else 0) := by
  ext x y
  simp only [Matrix.vecMulVec_apply]
  by_cases hy : y = (fun _ => false)
  · subst hy
    simp
  · simp only [hy, ↓reduceIte, mul_zero, typedMatrix]
    split_ifs with h
    · exact absurd (orF_false h.2.1) hy
    · rfl

lemma rank_le_one {n : ℕ} (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (i : Fin n) (b : Bool) :
    (typedMatrix n (orF n) τ i b).rank ≤ 1 := by
  rw [matrix_eq_vecMulVec τ i b]
  exact Matrix.rank_vecMulVec_le _ _

lemma one_le_rank_of_ne {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℚ) (x y : α)
    (h : M x y ≠ 0) : 1 ≤ M.rank := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hbot : LinearMap.range M.mulVecLin = ⊥ := by
    rw [Matrix.rank] at h0
    exact Submodule.finrank_eq_zero.mp h0
  have hmem : M.mulVecLin (Pi.single y 1) ∈ LinearMap.range M.mulVecLin := ⟨_, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  have := congrFun hmem x
  simp [Matrix.mulVec_single] at this
  exact h this

lemma one_le_rank_true {n : ℕ} {τ : (Fin n → Bool) → (Fin n → Bool) → ℕ}
    (hτ : IsTyping n (orF n) τ) (i : Fin n) : 1 ≤ (typedMatrix n (orF n) τ i true).rank := by
  classical
  let e : Fin n → Bool := fun j => decide (j = i)
  have he : orF n e = true := by
    simp only [orF, decide_eq_true_eq]
    exact ⟨i, by simp [e]⟩
  obtain ⟨j, hj, hne⟩ := hτ e (fun _ => false) he (orF_zero n)
  have hji : j = i := by
    by_contra h
    exact hne (by simp [e, h])
  subst hji
  apply one_le_rank_of_ne _ e (fun _ => false)
  simp [typedMatrix, he, orF_zero, hj, e]

end PEqualNP.Outside.L_meta_229

theorem PEqualNP.Outside.L_meta_229 : ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) n ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) := by
  classical
  intro n hn
  refine ⟨?_, ?_⟩
  · let τ : (Fin n → Bool) → (Fin n → Bool) → ℕ := fun x y =>
      if h : ∃ i : Fin n, x i ≠ y i then (h.choose : ℕ) else 0
    have hτ : IsTyping n (PEqualNP.Outside.L_meta_229.orF n) τ := by
      intro x y hx hy
      have hy0 := PEqualNP.Outside.L_meta_229.orF_false hy
      subst hy0
      obtain ⟨k, hk⟩ : ∃ k : Fin n, x k = true := by simpa using hx
      have h : ∃ i : Fin n, x i ≠ (fun _ => false) i := ⟨k, by simp [hk]⟩
      refine ⟨h.choose, ?_, h.choose_spec⟩
      simp only [τ]
      split_ifs with h'
      · rfl
      · exact absurd h h'
    refine ⟨τ, hτ, ?_⟩
    calc (∑ i : Fin n, ∑ b : Bool,
          (typedMatrix n (PEqualNP.Outside.L_meta_229.orF n) τ i b).rank)
        ≤ ∑ _i : Fin n, 1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Fintype.sum_bool, PEqualNP.Outside.L_meta_229.matrix_false_eq_zero hτ i,
            Matrix.rank_zero, add_zero]
          exact PEqualNP.Outside.L_meta_229.rank_le_one τ i true
      _ = n := by simp
  · rintro ⟨τ, hτ, hle⟩
    have hlow : n ≤ ∑ i : Fin n, ∑ b : Bool,
        (typedMatrix n (PEqualNP.Outside.L_meta_229.orF n) τ i b).rank := by
      calc n = ∑ _i : Fin n, 1 := by simp
        _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Fintype.sum_bool]
          have := PEqualNP.Outside.L_meta_229.one_le_rank_true hτ i
          omega
    change (∑ i : Fin n, ∑ b : Bool,
        (typedMatrix n (PEqualNP.Outside.L_meta_229.orF n) τ i b).rank) ≤ n - 1 at hle
    omega
