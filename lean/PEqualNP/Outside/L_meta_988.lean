import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_988

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hj : w - n < C.gates.length) :
    value C x w = (C.gates[w - n]).op.eval
      ((C.gates[w - n]).inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ r ∈ l, f r = true → f' r = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · intro hx
    simp only [GateOp.eval] at hx ⊢
    rw [List.all_eq_true] at hx ⊢
    intro b hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact h r hr (hx (f r) (List.mem_map.mpr ⟨r, hr, rfl⟩))
  · intro hx
    simp only [GateOp.eval] at hx ⊢
    rw [List.any_eq_true] at hx ⊢
    obtain ⟨b, hb, hbt⟩ := hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact ⟨f' r, List.mem_map.mpr ⟨r, hr, rfl⟩, h r hr hbt⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hxy : ∀ p, x p = true → x' p = true) (w : ℕ) :
    value C x w = true → value C x' w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · have h1 : value C x w = x ⟨w, hn⟩ := input_value C x ⟨w, hn⟩
      have h2 : value C x' w = x' ⟨w, hn⟩ := input_value C x' ⟨w, hn⟩
      rw [h1, h2]
      exact hxy _
    by_cases hw : w < n + C.gates.length
    · have hj : w - n < C.gates.length := by omega
      rw [gate_value C x w (by omega) hj, gate_value C x' w (by omega) hj]
      apply eval_mono _ (hG _ (List.getElem_mem hj)).1
      intro r _ hx
      by_cases hrw : r < w
      · simp only [hrw, if_true] at hx ⊢
        exact ih r hrw hx
      · simp [hrw] at hx
    · rw [missing_value C x w (by unfold Circuit.size; omega)]
      simp

def base {n : ℕ} (y : Finset (Fin n)) (p : Fin n) : Fin n → Bool :=
  fun v => decide (v ∈ y ∨ v = p)

open Classical in
noncomputable def Tf {n : ℕ} (S y : Finset (Fin n)) (F : (Fin n → Bool) → Bool) :
    Finset (Fin n) :=
  if (∀ x, F x = true → ∃ p ∈ S, x p = true) then S.filter (fun p => F (base y p) = true)
  else ∅

lemma mem_Tf {n : ℕ} (S y : Finset (Fin n)) (F : (Fin n → Bool) → Bool) (p : Fin n) :
    p ∈ Tf S y F ↔ (∀ x, F x = true → ∃ q ∈ S, x q = true) ∧ p ∈ S ∧ F (base y p) = true := by
  unfold Tf
  split_ifs with h
  · rw [Finset.mem_filter]
    exact ⟨fun hp => ⟨h, hp⟩, fun hp => hp.2⟩
  · constructor
    · intro hp
      simp at hp
    · intro hp
      exact absurd hp.1 h

lemma tf_true {n : ℕ} (S y : Finset (Fin n)) : Tf S y (fun _ => true) = ∅ := by
  ext p
  simp only [mem_Tf]
  constructor
  · rintro ⟨hs, -, -⟩
    exfalso
    obtain ⟨q, _, hq⟩ := hs (fun _ => false) (by simp)
    simp at hq
  · intro h
    simp at h

lemma tf_false {n : ℕ} (S y : Finset (Fin n)) : Tf S y (fun _ => false) = ∅ := by
  ext p
  simp only [mem_Tf]
  constructor
  · rintro ⟨-, -, h⟩
    simp at h
  · intro h
    simp at h

lemma tf_and {n : ℕ} (S y : Finset (Fin n)) (Fa Fb : (Fin n → Bool) → Bool)
    (ha : ∀ x x' : Fin n → Bool, (∀ p, x p = true → x' p = true) → Fa x = true → Fa x' = true)
    (hb : ∀ x x' : Fin n → Bool, (∀ p, x p = true → x' p = true) → Fb x = true → Fb x' = true) :
    Tf S y (fun x => Fa x && Fb x) ⊆ Tf S y Fa ∪ Tf S y Fb := by
  intro p hp
  simp only [mem_Tf, Bool.and_eq_true] at hp
  obtain ⟨hs, hpS, hF⟩ := hp
  rw [Finset.mem_union, mem_Tf, mem_Tf]
  by_contra hcon
  have hna : ¬ (∀ x, Fa x = true → ∃ q ∈ S, x q = true) :=
    fun h => hcon (Or.inl ⟨h, hpS, hF.1⟩)
  have hnb : ¬ (∀ x, Fb x = true → ∃ q ∈ S, x q = true) :=
    fun h => hcon (Or.inr ⟨h, hpS, hF.2⟩)
  push Not at hna hnb
  obtain ⟨xa, hxa, hxa'⟩ := hna
  obtain ⟨xb, hxb, hxb'⟩ := hnb
  have hA : Fa (fun v => xa v || xb v) = true :=
    ha xa _ (fun v hv => by simp [hv]) hxa
  have hB : Fb (fun v => xa v || xb v) = true :=
    hb xb _ (fun v hv => by simp [hv]) hxb
  obtain ⟨q, hqS, hq⟩ := hs (fun v => xa v || xb v) ⟨hA, hB⟩
  simp only [Bool.or_eq_true] at hq
  rcases hq with hq | hq
  · exact hxa' q hqS hq
  · exact hxb' q hqS hq

lemma tf_or {n : ℕ} (S y : Finset (Fin n)) (Fa Fb : (Fin n → Bool) → Bool) :
    Tf S y (fun x => Fa x || Fb x) ⊆ Tf S y Fa ∪ Tf S y Fb := by
  intro p hp
  simp only [mem_Tf, Bool.or_eq_true] at hp
  obtain ⟨hs, hpS, hF⟩ := hp
  rw [Finset.mem_union, mem_Tf, mem_Tf]
  rcases hF with hF | hF
  · exact Or.inl ⟨fun x hx => hs x (Or.inl hx), hpS, hF⟩
  · exact Or.inr ⟨fun x hx => hs x (Or.inr hx), hpS, hF⟩

lemma pure_gate {n : ℕ} (S y : Finset (Fin n)) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ((Fin n → Bool) → Bool))
    (hl : l.length ≤ 2)
    (hm : ∀ F ∈ l, ∀ x x' : Fin n → Bool, (∀ p, x p = true → x' p = true) →
      F x = true → F x' = true)
    (h2 : 2 ≤ (Tf S y (fun x => op.eval (l.map fun F => F x))).card) :
    ∃ Fa Fb, Fa ∈ l ∧ Fb ∈ l ∧
      Tf S y (fun x => op.eval (l.map fun F => F x)) ⊆ Tf S y Fa ∪ Tf S y Fb := by
  rcases l with _ | ⟨Fa, _ | ⟨Fb, _ | ⟨Fc, rest⟩⟩⟩
  · exfalso
    rcases hop with rfl | rfl
    · simp only [List.map_nil, GateOp.eval, List.all_nil] at h2
      rw [tf_true] at h2
      simp at h2
    · simp only [List.map_nil, GateOp.eval, List.any_nil] at h2
      rw [tf_false] at h2
      simp at h2
  · have e : (fun x => op.eval ([Fa].map fun F => F x)) = Fa := by
      funext x
      rcases hop with rfl | rfl <;> simp [GateOp.eval]
    rw [e]
    exact ⟨Fa, Fa, by simp, by simp, Finset.subset_union_left⟩
  · rcases hop with rfl | rfl
    · have e : (fun x => GateOp.and.eval ([Fa, Fb].map fun F => F x)) =
          fun x => Fa x && Fb x := by
        funext x
        simp [GateOp.eval]
      rw [e]
      exact ⟨Fa, Fb, by simp, by simp, tf_and S y Fa Fb (hm Fa (by simp)) (hm Fb (by simp))⟩
    · have e : (fun x => GateOp.or.eval ([Fa, Fb].map fun F => F x)) =
          fun x => Fa x || Fb x := by
        funext x
        simp [GateOp.eval]
      rw [e]
      exact ⟨Fa, Fb, by simp, by simp, tf_or S y Fa Fb⟩
  · simp at hl

lemma wire_gate {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S y : Finset (Fin n)) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.gates.length)
    (h2 : 2 ≤ (Tf S y (fun x => value C x w)).card) :
    ∃ a b : ℕ, Tf S y (fun x => value C x w) ⊆
        Tf S y (fun x => value C x a) ∪ Tf S y (fun x => value C x b) ∧
      (a < w ∨ Tf S y (fun x => value C x a) = ∅) ∧
      (b < w ∨ Tf S y (fun x => value C x b) = ∅) := by
  have hj : w - n < C.gates.length := by omega
  obtain ⟨g, hgdef⟩ : ∃ g, C.gates[w - n] = g := ⟨_, rfl⟩
  have hgmem : g ∈ C.gates := hgdef ▸ List.getElem_mem hj
  obtain ⟨hop, hlen⟩ := hG g hgmem
  let e : ℕ → ℕ := fun r => if r < w then r else n + C.size
  have hmiss : ∀ x : Fin n → Bool, value C x (n + C.size) = false :=
    fun x => missing_value C x _ le_rfl
  have he : ∀ r, e r < w ∨ Tf S y (fun x => value C x (e r)) = ∅ := by
    intro r
    by_cases hr : r < w
    · left
      simp [e, hr]
    · right
      have h0 : (fun x : Fin n → Bool => value C x (e r)) = fun _ => false := by
        funext x
        simp only [e, hr, ite_false, if_neg hr]
        exact hmiss x
      rw [h0]
      exact tf_false S y
  have hF : (fun x : Fin n → Bool => value C x w) =
      fun x : Fin n → Bool => g.op.eval ((g.inputs.map fun r => fun x' : Fin n → Bool =>
        value C x' (e r)).map fun F => F x) := by
    funext x
    rw [gate_value C x w hn hj, hgdef, List.map_map]
    congr 1
    congr 1
    funext r
    by_cases hr : r < w
    · simp [e, hr]
    · simp [e, hr, hmiss x]
  rw [hF] at h2 ⊢
  obtain ⟨Fa, Fb, hFa, hFb, hsub⟩ := pure_gate S y g.op hop _ (by simpa using hlen) (by
      intro F hF' x x' hxx'
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hF'
      exact value_mono C hG x x' hxx' (e r)) h2
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hFa
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hFb
  exact ⟨e a, e b, hsub, he a, he b⟩

lemma input_T {n : ℕ} (C : Circuit) (S y : Finset (Fin n)) (hd : Disjoint y S) (w : ℕ)
    (hw : w < n) : (Tf S y (fun x => value C x w)).card ≤ 1 := by
  have key : ∀ p ∈ Tf S y (fun x => value C x w), p = ⟨w, hw⟩ := by
    intro p hp
    simp only [mem_Tf] at hp
    obtain ⟨hs, _, hv⟩ := hp
    have hv' : value C (base y p) w = base y p ⟨w, hw⟩ := input_value C (base y p) ⟨w, hw⟩
    have hv2 : base y p ⟨w, hw⟩ = true := by rw [← hv']; exact hv
    simp only [base, decide_eq_true_eq] at hv2
    rcases hv2 with hv2 | hv2
    · exfalso
      have h1 : value C (fun v : Fin n => decide (v = ⟨w, hw⟩)) w =
          (fun v : Fin n => decide (v = ⟨w, hw⟩)) ⟨w, hw⟩ := input_value C _ ⟨w, hw⟩
      obtain ⟨q, hqS, hq⟩ := hs (fun v => decide (v = ⟨w, hw⟩)) (by rw [h1]; simp)
      simp only [decide_eq_true_eq] at hq
      subst hq
      exact Finset.disjoint_left.mp hd hv2 hqS
    · exact hv2.symm
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [key a ha, key b hb]

lemma cross {n : ℕ} (S1 S2 y1 y2 : Finset (Fin n)) (F : (Fin n → Bool) → Bool)
    (h1 : 2 ≤ (Tf S1 y1 F).card) (h2 : 2 ≤ (Tf S2 y2 F).card) (hint : (S1 ∩ S2).card ≤ 1) :
    ¬ Disjoint y1 S2 := by
  intro hdis
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (Tf S1 y1 F).card)
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < (Tf S2 y2 F).card)
  rw [mem_Tf] at hp hq hr
  have hs := hr.1
  have inS2 : ∀ u, F (base y1 u) = true → u ∈ S2 := by
    intro u hu
    obtain ⟨s, hsS, hs'⟩ := hs (base y1 u) hu
    simp only [base, decide_eq_true_eq] at hs'
    rcases hs' with hs' | hs'
    · exact absurd hsS (Finset.disjoint_left.mp hdis hs')
    · rw [← hs']
      exact hsS
  have hsub : ({p, q} : Finset (Fin n)) ⊆ S1 ∩ S2 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hp.2.1, inS2 _ hp.2.2⟩
    · exact Finset.mem_inter.mpr ⟨hq.2.1, inS2 _ hq.2.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hpq] at hc
  omega

lemma merge_step {α : Type} [DecidableEq α] (f : α → α) (S W U V : Finset α)
    (hW : W ⊆ U ∪ V) (hU : ∀ p ∈ U, ∀ q ∈ U, f p = f q) (hV : ∀ p ∈ V, ∀ q ∈ V, f p = f q) :
    ∃ h : α → α, (∀ p ∈ W, ∀ q ∈ W, h (f p) = h (f q)) ∧
      (S.image f).card ≤ (S.image (fun v => h (f v))).card + 1 := by
  rcases U.eq_empty_or_nonempty with hU0 | ⟨p0, hp0⟩
  · refine ⟨id, ?_, ?_⟩
    · intro p hp q hq
      have hp' := hW hp
      have hq' := hW hq
      simp only [hU0, Finset.empty_union] at hp' hq'
      exact hV p hp' q hq'
    · simp
  rcases V.eq_empty_or_nonempty with hV0 | ⟨q0, hq0⟩
  · refine ⟨id, ?_, ?_⟩
    · intro p hp q hq
      have hp' := hW hp
      have hq' := hW hq
      simp only [hV0, Finset.union_empty] at hp' hq'
      exact hU p hp' q hq'
    · simp
  refine ⟨fun c => if c = f q0 then f p0 else c, ?_, ?_⟩
  · have key : ∀ p ∈ W, (if f p = f q0 then f p0 else f p) = f p0 := by
      intro p hp
      rcases Finset.mem_union.mp (hW hp) with h | h
      · rw [hU p h p0 hp0]
        simp
      · rw [hV p h q0 hq0]
        simp
    intro p hp q hq
    show (if f p = f q0 then f p0 else f p) = (if f q = f q0 then f p0 else f q)
    rw [key p hp, key q hq]
  · calc (S.image f).card
        ≤ (insert (f q0) (S.image (fun v => if f v = f q0 then f p0 else f v))).card := by
          apply Finset.card_le_card
          intro c hc
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
          by_cases h : f v = f q0
          · rw [h]
            exact Finset.mem_insert_self _ _
          · apply Finset.mem_insert_of_mem
            exact Finset.mem_image.mpr ⟨v, hv, by simp [h]⟩
      _ ≤ _ := Finset.card_insert_le _ _

lemma color {α : Type} [DecidableEq α] (S : Finset α) (T : ℕ → Finset α) (n G : ℕ)
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ w, n ≤ w → w < n + G → 2 ≤ (T w).card →
      ∃ a b, T w ⊆ T a ∪ T b ∧ (a < w ∨ T a = ∅) ∧ (b < w ∨ T b = ∅)) :
    ∀ t, t ≤ G → ∃ f : α → α, (∀ w < n + t, ∀ p ∈ T w, ∀ q ∈ T w, f p = f q) ∧
      S.card ≤ (S.image f).card +
        ((Finset.range t).filter (fun j => 2 ≤ (T (n + j)).card)).card := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨id, ?_, ?_⟩
    · intro w hw p hp q hq
      exact Finset.card_le_one.mp (hin w (by omega)) p hp q hq
    · rw [Finset.image_id]
      omega
  | succ t ih =>
    intro ht
    obtain ⟨f, hf, hc⟩ := ih (by omega)
    have hmono : ∀ a, (a < n + t ∨ T a = ∅) → ∀ p ∈ T a, ∀ q ∈ T a, f p = f q := by
      intro a ha p hp q hq
      rcases ha with ha | ha
      · exact hf a ha p hp q hq
      · rw [ha] at hp
        simp at hp
    by_cases h2 : 2 ≤ (T (n + t)).card
    · obtain ⟨a, b, hsub, ha, hb⟩ := hgate (n + t) (by omega) (by omega) h2
      obtain ⟨h, hh, hcard⟩ :=
        merge_step f S (T (n + t)) (T a) (T b) hsub (hmono a ha) (hmono b hb)
      refine ⟨fun v => h (f v), ?_, ?_⟩
      · intro w hw p hp q hq
        by_cases hwt : w < n + t
        · show h (f p) = h (f q)
          rw [hf w hwt p hp q hq]
        · have hwe : w = n + t := by omega
          subst hwe
          exact hh p hp q hq
      · have hr : (Finset.range (t + 1)).filter (fun j => 2 ≤ (T (n + j)).card) =
            insert t ((Finset.range t).filter (fun j => 2 ≤ (T (n + j)).card)) := by
          rw [Finset.range_add_one, Finset.filter_insert, if_pos h2]
        rw [hr, Finset.card_insert_of_notMem (by simp)]
        omega
    · refine ⟨f, ?_, ?_⟩
      · intro w hw p hp q hq
        by_cases hwt : w < n + t
        · exact hf w hwt p hp q hq
        · have hwe : w = n + t := by omega
          subst hwe
          exact congrArg f (Finset.card_le_one.mp (by omega) p hp q hq)
      · have hle : ((Finset.range t).filter (fun j => 2 ≤ (T (n + j)).card)).card ≤
            ((Finset.range (t + 1)).filter (fun j => 2 ≤ (T (n + j)).card)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
          exact ⟨by omega, hj.2⟩
        omega

lemma per_set {α : Type} [DecidableEq α] (S : Finset α) (T : ℕ → Finset α) (n G o : ℕ)
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ w, n ≤ w → w < n + G → 2 ≤ (T w).card →
      ∃ a b, T w ⊆ T a ∪ T b ∧ (a < w ∨ T a = ∅) ∧ (b < w ∨ T b = ∅))
    (ho : T o = S) (ho' : o < n + G ∨ T o = ∅) :
    S.card ≤ ((Finset.range G).filter (fun j => 2 ≤ (T (n + j)).card)).card + 1 := by
  obtain ⟨f, hf, hc⟩ := color S T n G hin hgate G le_rfl
  rcases ho' with ho' | ho'
  · have him : (S.image f).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
      rw [← ho] at hp hq
      exact hf o ho' p hp q hq
    omega
  · rw [ho] at ho'
    rw [ho']
    simp

end PEqualNP.Outside.L_meta_988

theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  classical
  intro n m D S y C o hinter hdisj hG hsafe hfire hD
  let T : Fin m → ℕ → Finset (Fin n) := fun i w =>
    L_meta_988.Tf (S i) (y i) (fun x => L_meta_988.value C x w)
  let N : Fin m → ℕ := fun i =>
    ((Finset.range C.gates.length).filter (fun j => 2 ≤ (T i (n + j)).card)).card
  have hper : ∀ i, (S i).card ≤ N i + 1 := by
    intro i
    have hTo : T i (o i) = S i := by
      ext p
      simp only [T, L_meta_988.mem_Tf]
      constructor
      · intro h
        exact h.2.1
      · intro hp
        exact ⟨hsafe i, hp, hfire i p hp⟩
    apply L_meta_988.per_set (S i) (T i) n C.gates.length (o i)
    · intro w hw
      exact L_meta_988.input_T C (S i) (y i) (hdisj i) w hw
    · intro w hn hw h2
      exact L_meta_988.wire_gate C hG (S i) (y i) w hn hw h2
    · exact hTo
    · by_cases ho : o i < n + C.gates.length
      · exact Or.inl ho
      · right
        show L_meta_988.Tf (S i) (y i) (fun x => L_meta_988.value C x (o i)) = ∅
        have h0 : (fun x : Fin n → Bool => L_meta_988.value C x (o i)) = fun _ => false := by
          funext x
          exact L_meta_988.missing_value C x _ (by unfold PEqualNP.CircuitLowerBounds.Circuit.size; omega)
        rw [h0]
        exact L_meta_988.tf_false _ _
  have hJ : ∀ j, (Finset.univ.filter (fun i => 2 ≤ (T i (n + j)).card)).card ≤ D := by
    intro j
    apply hD
    intro i hi k hk hik
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hk
    exact L_meta_988.cross (S i) (S k) (y i) (y k) _ hi hk (hinter i k hik)
  have hswap : ∑ i, N i = ∑ j ∈ Finset.range C.gates.length,
      (Finset.univ.filter (fun i => 2 ≤ (T i (n + j)).card)).card := by
    simp only [N, Finset.card_filter]
    exact Finset.sum_comm
  calc ∑ i, (S i).card ≤ ∑ i, (N i + 1) := Finset.sum_le_sum (fun i _ => hper i)
    _ = ∑ i, N i + m := by rw [Finset.sum_add_distrib]; simp
    _ ≤ ∑ j ∈ Finset.range C.gates.length, D + m := by
        rw [hswap]
        gcongr with j _
        exact hJ j
    _ = D * C.gates.length + m := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
