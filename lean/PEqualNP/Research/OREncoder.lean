import Mathlib
import PEqualNP.Defs

/-!
# Exact gate complexity of binary OR encoders

Each input symbol has a distinct nonempty mask of output coordinates. On the
unit vector for that symbol, precisely its mask must be true. A gate is a
binary (or smaller) OR, and each output may select an arbitrary wire.

* `encoder_circuit_bound` counts live arcs and bounds the size from below.
  With n symbols, d pins and a singleton masks it gives 2n - a - d.
* `encoder_attains_bound_iff` characterizes equality when all singletons occur.
  Every nonsingleton must be a union of two strictly smaller masks in the family.
* `circuit_of_binary_decompositions` constructs a circuit of exactly 2(n-d)
  gates from such decompositions. It computes the union on arbitrary inputs.
* `full_encoder_exact` gives the exact size 2(2^d - 2 - d) for all nonempty
  proper masks in every dimension d ≥ 2.

For the lower bound, label each live wire by the outputs reachable from it.
The last occurrence of a nonsingleton label needs two outgoing arcs. At
equality every branch is accounted for, so its two outgoing arcs must together
realize a decomposition into smaller labels. For the upper bound, process
each mask before its two children, OR-ing its accumulator into each of theirs.
The singleton accumulators give the outputs.

The general circuit transposition principle is classical. See Stasys Jukna,
Boolean Function Complexity, chapter 1, p. 46 (Transposition Principle).
The four-output example is motivated by the PEqualNP task L-meta-12408.
-/

namespace PEqualNP.Research.OREncoder

-- A non-singleton output pattern must occur at a point where the signal splits.
-- Take its last occurrence: a unique outgoing wire would preserve that pattern.
private theorem or_last_split {α : Type*} [DecidableEq α] (L : Finset ℕ)
    (nxt : ℕ → Finset ℕ) (pin lab : ℕ → Finset α)
    (next_live : ∀ w ∈ L, nxt w ⊆ L)
    (forward : ∀ w ∈ L, ∀ g ∈ nxt w, w < g)
    (step : ∀ w ∈ L, lab w = pin w ∪ (nxt w).biUnion lab)
    {i : ℕ} (hi : i ∈ L) (many : 2 ≤ (lab i).card) :
    ∃ w ∈ L, lab w = lab i ∧ 2 ≤ (nxt w).card + (pin w).card := by
  classical
  let fiber := L.filter (fun w => lab w = lab i)
  have hiF : i ∈ fiber := Finset.mem_filter.mpr ⟨hi, rfl⟩
  have hF : fiber.Nonempty := ⟨i, hiF⟩
  let w := fiber.max' hF
  have hwF : w ∈ fiber := Finset.max'_mem _ _
  obtain ⟨hw, same⟩ := Finset.mem_filter.mp hwF
  refine ⟨w, hw, same, ?_⟩
  by_contra! small
  by_cases empty : nxt w = ∅
  · have eq : lab w = pin w := by simpa [empty] using step w hw
    rw [← eq, same] at small
    omega
  · obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have hn : 0 < (nxt w).card := Finset.card_pos.mpr ⟨g,hg⟩
    have noPin : pin w = ∅ := Finset.card_eq_zero.mp (by omega)
    have singleton : nxt w = {g} := by
      obtain ⟨h, eq⟩ := Finset.card_eq_one.mp (show (nxt w).card = 1 by omega)
      have hh : g = h := by simpa [eq] using hg
      simpa [hh] using eq
    have inherits : lab w = lab g := by simpa [noPin, singleton] using step w hw
    have hgF : g ∈ fiber := Finset.mem_filter.mpr ⟨next_live w hw hg, inherits.symm.trans same⟩
    exact (Nat.not_lt_of_ge (Finset.le_max' fiber g hgF)) (forward w hw g hg)

theorem or_transpose_account {α : Type*} [DecidableEq α] (L I : Finset ℕ)
    (nxt : ℕ → Finset ℕ) (pin lab : ℕ → Finset α) (m : ℕ)
    (inputs : I ⊆ L)
    (next_mem : ∀ w ∈ L, nxt w ⊆ L \ I)
    (forward : ∀ w ∈ L, ∀ g ∈ nxt w, w < g)
    (live : ∀ w ∈ L, (lab w).Nonempty)
    (step : ∀ w ∈ L, lab w = pin w ∪ (nxt w).biUnion lab)
    (fanin : ∀ g ∈ L \ I, (L.filter (fun w => g ∈ nxt w)).card ≤ 2)
    (pin_sum : ∑ w ∈ L, (pin w).card ≤ m)
    (distinct : Set.InjOn lab (↑I : Set ℕ)) :
    (I.card + (I.filter (fun i => 2 ≤ (lab i).card)).card ≤ (L \ I).card + m)
    ∧ ((L \ I).card + m ≤ I.card + (I.filter (fun i => 2 ≤ (lab i).card)).card →
      (∀ w ∈ L, (nxt w).card + (pin w).card ≤ 2) ∧
      ∀ w ∈ L, 2 ≤ (nxt w).card + (pin w).card → lab w ∈ I.image lab) := by
  classical
  let gates := L \ I
  let deg := fun w => (nxt w).card + (pin w).card
  let forks := L.filter (fun w => 2 ≤ deg w)
  let large := I.filter (fun i => 2 ≤ (lab i).card)
  have hcovered : large.image lab ⊆ forks.image lab := by
    intro pat hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hiI, hmany⟩ := Finset.mem_filter.mp hi
    obtain ⟨w, hw, same, split⟩ := or_last_split L nxt pin lab
      (fun u hu v hv => (Finset.mem_sdiff.mp (next_mem u hu hv)).1)
      forward step (inputs hiI) hmany
    exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, split⟩, same⟩
  have inj : Set.InjOn lab (↑large : Set ℕ) :=
    fun _ hi _ hj h => distinct (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 h
  have fork_count : large.card ≤ forks.card :=
    calc
      large.card = (large.image lab).card := (Finset.card_image_of_injOn inj).symm
      _ ≤ (forks.image lab).card := Finset.card_le_card hcovered
      _ ≤ _ := Finset.card_image_le
  have deg_pos (w : ℕ) (hw : w ∈ L) : 0 < deg w := by
    by_contra! h
    change (nxt w).card + (pin w).card ≤ 0 at h
    have hn : nxt w = ∅ := Finset.card_eq_zero.mp (by omega)
    have hp : pin w = ∅ := Finset.card_eq_zero.mp (by omega)
    have none : lab w = ∅ := by simpa [hn, hp] using step w hw
    exact (live w hw).ne_empty none
  have per_wire (w : ℕ) (hw : w ∈ L) :
      1 + (if 2 ≤ deg w then 1 else 0) ≤ deg w := by
    have pos := deg_pos w hw
    split <;> omega
  have lower : L.card + forks.card ≤ ∑ w ∈ L, deg w := by
    calc
      L.card + forks.card = ∑ w ∈ L, (1 + (if 2 ≤ deg w then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← Finset.card_filter]
        simp [forks]
      _ ≤ _ := Finset.sum_le_sum per_wire
  have double : ∑ w ∈ L, (nxt w).card = ∑ g ∈ gates, (L.filter (fun w => g ∈ nxt w)).card := by
    calc
      ∑ w ∈ L, (nxt w).card = ∑ w ∈ L, ∑ g ∈ gates, (if g ∈ nxt w then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro w hw
        have sub : gates.filter (fun g => g ∈ nxt w) = nxt w := by
          ext g
          simp only [Finset.mem_filter]
          exact ⟨And.right, fun h => ⟨next_mem w hw h, h⟩⟩
        rw [← Finset.card_filter, sub]
      _ = ∑ g ∈ gates, ∑ w ∈ L, (if g ∈ nxt w then 1 else 0) := Finset.sum_comm
      _ = _ := by simp only [Finset.card_filter]
  have edge_bound : ∑ w ∈ L, (nxt w).card ≤ 2 * gates.card := by
    rw [double]
    calc
      _ ≤ ∑ _g ∈ gates, 2 := Finset.sum_le_sum (fun g hg => fanin g hg)
      _ = _ := by simp [Nat.mul_comm]
  have upper : ∑ w ∈ L, deg w ≤ 2 * gates.card + m := by
    simpa only [deg, Finset.sum_add_distrib] using Nat.add_le_add edge_bound pin_sum
  have partition : L.card = gates.card + I.card := by
    exact (Finset.card_sdiff_add_card_eq_card inputs).symm
  constructor
  · change I.card + large.card ≤ gates.card + m
    omega
  intro budget
  change gates.card + m ≤ I.card + large.card at budget
  have same_count : large.card = forks.card := by omega
  have same_image : large.image lab = forks.image lab := by
    apply Finset.eq_of_subset_of_card_le hcovered
    rw [Finset.card_image_of_injOn inj, same_count]
    exact Finset.card_image_le
  constructor
  · intro w hw
    change deg w ≤ 2
    by_contra! many
    have strict : (∑ x ∈ L, (1 + (if 2 ≤ deg x then 1 else 0))) < ∑ x ∈ L, deg x := by
      apply Finset.sum_lt_sum per_wire
      exact ⟨w, hw, by simp [show 2 ≤ deg w by omega]; omega⟩
    rw [Finset.sum_add_distrib, ← Finset.card_filter] at strict
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at strict
    change L.card + forks.card < _ at strict
    omega
  · intro w hw fork
    have h : lab w ∈ forks.image lab := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw, fork⟩)
    rw [← same_image] at h
    obtain ⟨i, hi, same⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, same⟩

theorem or_transpose_bound {α : Type*} [DecidableEq α] (L I : Finset ℕ)
    (nxt : ℕ → Finset ℕ) (pin lab : ℕ → Finset α) (m : ℕ)
    (inputs : I ⊆ L)
    (next_mem : ∀ w ∈ L, nxt w ⊆ L \ I)
    (forward : ∀ w ∈ L, ∀ g ∈ nxt w, w < g)
    (live : ∀ w ∈ L, (lab w).Nonempty)
    (step : ∀ w ∈ L, lab w = pin w ∪ (nxt w).biUnion lab)
    (fanin : ∀ g ∈ L \ I, (L.filter (fun w => g ∈ nxt w)).card ≤ 2)
    (pin_sum : ∑ w ∈ L, (pin w).card ≤ m)
    (distinct : Set.InjOn lab (↑I : Set ℕ)) :
    I.card + (I.filter (fun i => 2 ≤ (lab i).card)).card ≤ (L \ I).card + m :=
  (or_transpose_account L I nxt pin lab m inputs next_mem forward live step fanin pin_sum distinct).1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- Earlier-wire evaluation, adapted from the current project's L_meta_1490.
namespace EncoderWires

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]


end EncoderWires

-- An operand is an edge precisely when the wire existed at read time.
def wireEdge (n : ℕ) (C : Circuit) (i j : ℕ) : Prop :=
  n ≤ j ∧ j < n + C.size ∧ i < j ∧ i ∈ (gateAt C (j - n)).inputs

instance (n : ℕ) (C : Circuit) : DecidableRel (wireEdge n C) :=
  fun i j => by unfold wireEdge; infer_instance

def onehotWire (n : ℕ) (C : Circuit) (p : Fin n) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false

theorem wireEdge_bounds {n : ℕ} {C : Circuit} {i j : ℕ} (h : wireEdge n C i j) :
    i < j ∧ n ≤ j ∧ j < n + C.size := ⟨h.2.2.1,h.1,h.2.1⟩

theorem wireEdge_fanin {n : ℕ} {C : Circuit}
    (ok : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (S : Finset ℕ) (j : ℕ) : (S.filter (fun i => wireEdge n C i j)).card ≤ 2 := by
  by_cases inside : n ≤ j ∧ j < n + C.size
  · have hk : j-n < C.gates.length := by change j-n < C.size; omega
    have sub : S.filter (fun i => wireEdge n C i j) ⊆ (gateAt C (j-n)).inputs.toFinset := by
      intro i hi
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2.2.2.2
    exact (Finset.card_le_card sub).trans
      (List.toFinset_card_le _ |>.trans (ok _ (EncoderWires.gateAt_mem hk)).2)
  · have none : S.filter (fun i => wireEdge n C i j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      exact inside ⟨h.1,h.2.1⟩
    simp [none]

private theorem gate_onehot {n : ℕ} (C : Circuit)
    (ok : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (p : Fin n) (j : ℕ) (hj : j < C.gates.length) :
    onehotWire n C p (n+j) = true ↔
      ∃ i ∈ (gateAt C j).inputs, i < n+j ∧ onehotWire n C p i = true := by
  change EncoderWires.val C _ (n+j) = true ↔ _
  rw [EncoderWires.val_gate (by simp) hj, (ok _ (EncoderWires.gateAt_mem hj)).1]
  simp [GateOp.eval, List.any_map, List.any_eq_true, onehotWire, EncoderWires.val]

theorem onehot_reach {n : ℕ} (C : Circuit)
    (ok : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (p : Fin n) (w : ℕ) :
    onehotWire n C p w = true ↔ w < n + C.size ∧
      Relation.ReflTransGen (wireEdge n C) p.val w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · have input : onehotWire n C p w = decide ((⟨w,hi⟩ : Fin n) = p) :=
        EncoderWires.val_ofFn C (fun q : Fin n => decide (q=p)) ⟨w,hi⟩
      rw [input,decide_eq_true_eq]
      constructor
      · intro eq
        have e : w = p.val := congrArg Fin.val eq
        rw [e]
        exact ⟨by have := p.isLt; omega,.refl⟩
      · rintro ⟨_,path⟩
        rcases path.cases_tail with same | ⟨i,_,last⟩
        · exact Fin.ext same
        · exact (Nat.not_le_of_lt hi last.1).elim
    · by_cases valid : w < n+C.size
      · let j := w-n
        have e : n+j=w := by dsimp [j]; omega
        have hj : j<C.gates.length := by change w-n<C.size; omega
        have step := gate_onehot C ok p j hj
        rw [e] at step
        rw [step]
        constructor
        · rintro ⟨i,hm,lt,on⟩
          exact ⟨valid,((ih i lt).mp on).2.tail ⟨by omega,valid,lt,hm⟩⟩
        · rintro ⟨_,path⟩
          rcases path.cases_tail with same | ⟨i,pre,last⟩
          · have := p.isLt; omega
          · have lt := last.2.2.1
            exact ⟨i,last.2.2.2,lt,(ih i lt).mpr ⟨by omega,pre⟩⟩
      · have off : onehotWire n C p w = false :=
          EncoderWires.val_ge (n := n) (by simp) (by change n+C.size ≤ w; omega)
        simp [off,valid]

-- Equality in the counting bound forces the last occurrence of each composite
-- label to be a union of two strictly smaller input labels.
theorem tight_decompose {α : Type*} [DecidableEq α] (L I : Finset ℕ)
    (nxt : ℕ → Finset ℕ) (pin lab : ℕ → Finset α)
    (next_live : ∀ w ∈ L, nxt w ⊆ L)
    (forward : ∀ w ∈ L, ∀ g ∈ nxt w, w < g)
    (step : ∀ w ∈ L, lab w = pin w ∪ (nxt w).biUnion lab)
    (live : ∀ w ∈ L, (lab w).Nonempty)
    (singletons : ∀ v : α, ({v} : Finset α) ∈ I.image lab)
    (degrees : ∀ w ∈ L, (nxt w).card + (pin w).card ≤ 2)
    (branch_input : ∀ w ∈ L, 2 ≤ (nxt w).card + (pin w).card → lab w ∈ I.image lab)
    (i : ℕ) (_hi : i ∈ I) (hi : i ∈ L) (many : 2 ≤ (lab i).card) :
    ∃ a ∈ I, ∃ b ∈ I, (lab a).card < (lab i).card ∧
      (lab b).card < (lab i).card ∧ lab i = lab a ∪ lab b := by
  classical
  have every (g : ℕ) (hg : g ∈ L) : lab g ∈ I.image lab := by
    have pos := Finset.card_pos.mpr (live _ hg)
    by_cases one : (lab g).card = 1
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp one
      exact hv ▸ singletons v
    · obtain ⟨w, hw, eq, bound⟩ := or_last_split L nxt pin lab next_live forward step hg (by omega)
      exact eq ▸ branch_input w hw bound
  let fiber := L.filter (fun g => lab g = lab i)
  have hiF : i ∈ fiber := Finset.mem_filter.mpr ⟨hi,rfl⟩
  let w := fiber.max' ⟨i,hiF⟩
  have hwF : w ∈ fiber := Finset.max'_mem _ _
  obtain ⟨hw, same⟩ := Finset.mem_filter.mp hwF
  let parts := (pin w).image (fun v => ({v} : Finset α)) ∪ (nxt w).image lab
  have bound : parts.card ≤ 2 := by
    calc
      parts.card ≤ ((pin w).image (fun v => ({v} : Finset α))).card + ((nxt w).image lab).card :=
        Finset.card_union_le _ _
      _ ≤ (pin w).card + (nxt w).card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ 2 := by simpa [Nat.add_comm] using degrees w hw
  have cover (v : α) : v ∈ lab i ↔ ∃ A ∈ parts, v ∈ A := by
    rw [← same, step w hw]
    simp only [parts, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro (h | ⟨g, hg, on⟩)
      · exact ⟨{v}, Or.inl ⟨v, h, rfl⟩, Finset.mem_singleton_self _⟩
      · exact ⟨lab g, Or.inr ⟨g, hg, rfl⟩, on⟩
    · rintro ⟨A, (⟨a, ha, rfl⟩ | ⟨g, hg, rfl⟩), on⟩
      · obtain rfl := Finset.mem_singleton.mp on
        exact Or.inl ha
      · exact Or.inr ⟨g, hg, on⟩
  have smaller (A : Finset α) (hA : A ∈ parts) :
      A.card < (lab i).card ∧ A ∈ I.image lab := by
    rcases Finset.mem_union.mp hA with h | h
    · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨by rw [Finset.card_singleton]; omega, singletons _⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h
      have ne : lab g ≠ lab i := by
        intro eq
        have hgf : g ∈ fiber := Finset.mem_filter.mpr ⟨next_live w hw hg,eq⟩
        exact (Nat.not_lt_of_ge (Finset.le_max' fiber g hgf)) (forward w hw g hg)
      have sub : lab g ⊆ lab i := fun v hv => (cover v).mpr ⟨lab g, hA, hv⟩
      exact ⟨Finset.card_lt_card (ssubset_of_subset_of_ne sub ne), every g (next_live w hw hg)⟩
  have partNE : parts.Nonempty := by
    obtain ⟨v,hv⟩ := live i hi
    obtain ⟨A,hA,_⟩ := (cover v).mp hv
    exact ⟨A,hA⟩
  have two : parts.card = 2 := by
    by_contra h
    have pos := Finset.card_pos.mpr partNE
    obtain ⟨A, eq⟩ := Finset.card_eq_one.mp (show parts.card = 1 by omega)
    have Aeq : lab i = A := by ext v; simpa [eq] using cover v
    have lt := (smaller A (by simp [eq])).1
    rw [Aeq] at lt
    omega
  obtain ⟨A, B, _, shape⟩ := Finset.card_eq_two.mp two
  have hA := smaller A (by simp [shape])
  have hB := smaller B (by simp [shape])
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA.2
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB.2
  refine ⟨a, ha, b, hb, hA.1, hB.1, ?_⟩
  ext v
  simpa [shape] using cover v

open PEqualNP.CircuitLowerBounds

-- Reachable output pins are the columns of the encoder, read backwards.
def HasBinaryDecompositions {d : ℕ} (n : ℕ) (targets : ℕ → Finset (Fin d)) : Prop :=
  ∀ i < n, 2 ≤ (targets i).card → ∃ a < n, ∃ b < n,
    (targets a).card < (targets i).card ∧ (targets b).card < (targets i).card ∧
    targets i = targets a ∪ targets b

theorem encoder_dag_account {n s m : ℕ} (E : ℕ → ℕ → Prop) [DecidableRel E]
    (out : Fin m → ℕ) (targets : ℕ → Finset (Fin m))
    (ordered : ∀ {i j}, E i j → i < j ∧ n ≤ j ∧ j < n+s)
    (binary : ∀ (S : Finset ℕ) (j : ℕ), (S.filter (fun i => E i j)).card ≤ 2)
    (spec : ∀ i < n, ∀ v, v ∈ targets i ↔ out v < n+s ∧ Relation.ReflTransGen E i (out v))
    (used : ∀ i < n, (targets i).Nonempty)
    (different : Set.InjOn targets (↑(Finset.range n) : Set ℕ)) :
    (n + ((Finset.range n).filter (fun i => 2 ≤ (targets i).card)).card ≤ s+m) ∧
    (s+m ≤ n + ((Finset.range n).filter (fun i => 2 ≤ (targets i).card)).card →
      (∀ v : Fin m, ∃ i < n, targets i = {v}) → HasBinaryDecompositions n targets) := by
  classical
  let lab (w : ℕ) := Finset.univ.filter (fun v : Fin m => out v < n+s ∧ Relation.ReflTransGen E w (out v))
  let pin (w : ℕ) := Finset.univ.filter (fun v : Fin m => out v = w)
  let L := (Finset.range (n+s)).filter (fun w => (lab w).Nonempty)
  let nxt (w : ℕ) := L.filter (E w)
  have lab_input (i : ℕ) (hi : i < n) : lab i = targets i := by
    ext v
    simpa [lab] using (spec i hi v).symm
  have inputs : Finset.range n ⊆ L := by
    intro i hi
    have ht := Finset.mem_range.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (lab_input i ht) ▸ used i ht⟩
  have next_mem (w : ℕ) (_ : w ∈ L) : nxt w ⊆ L \ Finset.range n := by
    intro j hj
    obtain ⟨hL,he⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_sdiff.mpr ⟨hL,fun h => (Nat.not_lt_of_ge (ordered he).2.1) (Finset.mem_range.mp h)⟩
  have step (w : ℕ) (hw : w ∈ L) : lab w = pin w ∪ (nxt w).biUnion lab := by
    ext v
    simp only [lab,pin,nxt,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_union,Finset.mem_biUnion]
    constructor
    · rintro ⟨hv,h⟩
      rcases h.cases_head with h | ⟨j,e,tail⟩
      · exact Or.inl h.symm
      · have hj : j ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ordered e).2.2,
            v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv,tail⟩⟩
        exact Or.inr ⟨j,⟨hj,e⟩,hv,tail⟩
    · rintro (hv | ⟨j,⟨_,e⟩,hv,tail⟩)
      · rw [hv]
        exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hw).1,.refl⟩
      · exact ⟨hv,tail.head e⟩
  have fanin (g : ℕ) (_ : g ∈ L \ Finset.range n) :
      (L.filter (fun w => g ∈ nxt w)).card ≤ 2 := by
    apply le_trans _ (binary L g)
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hl,hn⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hl,(Finset.mem_filter.mp hn).2⟩
  have pin_sum : ∑ w ∈ L, (pin w).card ≤ m := by
    simp only [pin, Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _v : Fin m, 1 := by
        apply Finset.sum_le_sum
        intro v _
        by_cases h : out v ∈ L <;> simp [Finset.sum_ite_eq,h]
      _ = _ := by simp
  have distinct : Set.InjOn lab (↑(Finset.range n) : Set ℕ) := by
    intro i hi j hj h
    exact different hi hj ((lab_input i (Finset.mem_range.mp hi)).symm.trans (h.trans (lab_input j (Finset.mem_range.mp hj))))
  have account := or_transpose_account L (Finset.range n) nxt pin lab m inputs next_mem
    (fun w _ g hg => (ordered (Finset.mem_filter.mp hg).2).1)
    (fun w hw => (Finset.mem_filter.mp hw).2) step fanin pin_sum distinct
  have eq : (Finset.range n).filter (fun i => 2 ≤ (lab i).card) =
      (Finset.range n).filter (fun i => 2 ≤ (targets i).card) := by
    apply Finset.filter_congr
    intro i hi
    rw [lab_input i (Finset.mem_range.mp hi)]
  have count : L.card ≤ n+s := by
    simpa using Finset.card_le_card (Finset.filter_subset (fun w => (lab w).Nonempty) (Finset.range (n+s)))
  constructor
  · have result := account.1
    rw [eq, Finset.card_sdiff_of_subset inputs, Finset.card_range] at result
    omega
  intro budget singleton_inputs
  have reverse : (L \ Finset.range n).card + m ≤
      (Finset.range n).card + ((Finset.range n).filter (fun i => 2 ≤ (lab i).card)).card := by
    rw [eq, Finset.card_sdiff_of_subset inputs, Finset.card_range]
    omega
  obtain ⟨degrees, branch_input⟩ := account.2 reverse
  have singles (v : Fin m) : ({v} : Finset (Fin m)) ∈ (Finset.range n).image lab := by
    obtain ⟨i,hi,h⟩ := singleton_inputs v
    exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,(lab_input i hi).trans h⟩
  intro i hi many
  have imem := Finset.mem_range.mpr hi
  obtain ⟨a,ha,b,hb,sa,sb,same⟩ := tight_decompose L (Finset.range n) nxt pin lab
    (fun _ _ _ e => (Finset.mem_filter.mp e).1)
    (fun _ _ _ e => (ordered (Finset.mem_filter.mp e).2).1) step
    (fun w hw => (Finset.mem_filter.mp hw).2) singles degrees branch_input
    i imem (inputs imem) (by rwa [lab_input i hi])
  refine ⟨a,Finset.mem_range.mp ha,b,Finset.mem_range.mp hb,?_⟩
  rw [← lab_input i hi, ← lab_input a (Finset.mem_range.mp ha), ← lab_input b (Finset.mem_range.mp hb)]
  exact ⟨sa,sb,same⟩

theorem encoder_dag_bound {n s m : ℕ} (E : ℕ → ℕ → Prop) [DecidableRel E]
    (out : Fin m → ℕ) (targets : ℕ → Finset (Fin m))
    (ordered : ∀ {i j}, E i j → i < j ∧ n ≤ j ∧ j < n+s)
    (binary : ∀ (S : Finset ℕ) (j : ℕ), (S.filter (fun i => E i j)).card ≤ 2)
    (spec : ∀ i < n, ∀ v, v ∈ targets i ↔ out v < n+s ∧ Relation.ReflTransGen E i (out v))
    (used : ∀ i < n, (targets i).Nonempty)
    (different : Set.InjOn targets (↑(Finset.range n) : Set ℕ)) :
    n + ((Finset.range n).filter (fun i => 2 ≤ (targets i).card)).card ≤ s+m :=
  (encoder_dag_account E out targets ordered binary spec used different).1

-- Distinct nonempty columns cost at least one live wire each. Every column
-- with two or more outputs requires an additional branch.
theorem encoder_circuit_bound {n m : ℕ} (C : Circuit)
    (ok : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (targets : ℕ → Finset (Fin m))
    (spec : ∀ p : Fin n, ∀ v, onehotWire n C p (out v) = true ↔ v ∈ targets p.val)
    (used : ∀ i < n, (targets i).Nonempty)
    (different : Set.InjOn targets (↑(Finset.range n) : Set ℕ)) :
    n + ((Finset.range n).filter (fun i => 2 ≤ (targets i).card)).card ≤ C.size + m := by
  apply encoder_dag_bound (wireEdge n C) out targets
    (fun e => wireEdge_bounds e) (wireEdge_fanin ok) _ used different
  intro i hi v
  exact (spec ⟨i,hi⟩ v).symm.trans (onehot_reach C ok ⟨i,hi⟩ (out v))

private def mask4 (i : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter (fun v => Nat.testBit (i+1) v.val)

theorem encoder_four_lower (C : Circuit)
    (ok : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (spec : ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, onehotWire 14 C p w = Nat.testBit (p.val + 1) v.val) :
    20 ≤ C.size := by
  classical
  choose out hout using spec
  have allUsed : ∀ p : Fin 14, (mask4 p.val).Nonempty := by decide +kernel
  have apart : ∀ i j : Fin 14, mask4 i.val = mask4 j.val → i = j := by decide +kernel
  have different : Set.InjOn mask4 (↑(Finset.range 14) : Set ℕ) := by
    intro i hi j hj h
    exact congrArg Fin.val (apart ⟨i,Finset.mem_range.mp hi⟩ ⟨j,Finset.mem_range.mp hj⟩ h)
  have bound := encoder_circuit_bound (n := 14) C ok out mask4
    (fun p v => by simp only [hout v p,mask4,Finset.mem_filter,Finset.mem_univ,true_and])
    (fun i h => allUsed ⟨i,h⟩) different
  have count : ((Finset.range 14).filter (fun i => 2 ≤ (mask4 i).card)).card = 10 := by decide +kernel
  rw [count] at bound
  omega

-- Distinct nonempty masks containing each singleton have exactly d singleton entries.
theorem encoder_nonsingletons {n d : ℕ} (targets : ℕ → Finset (Fin d))
    (used : ∀ i < n, (targets i).Nonempty)
    (different : Set.InjOn targets (↑(Finset.range n) : Set ℕ))
    (singletons : ∀ v : Fin d, ∃ i < n, targets i = {v}) :
    ((Finset.range n).filter (fun i => 2 ≤ (targets i).card)).card + d = n := by
  classical
  let singles := (Finset.range n).filter (fun i => (targets i).card = 1)
  have image_eq : singles.image targets =
      (Finset.univ : Finset (Fin d)).image (fun v => ({v} : Finset (Fin d))) := by
    ext p
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hi).2
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv.symm⟩
    · intro h
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨i, hi, heq⟩ := singletons v
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, by simp [heq]⟩, heq⟩
  have inj : Set.InjOn targets (↑singles : Set ℕ) :=
    fun _ hi _ hj eq => different (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 eq
  have singleton_inj : Function.Injective (fun v : Fin d => ({v} : Finset (Fin d))) := by
    intro a b eq
    change ({a} : Finset (Fin d)) = {b} at eq
    have h : a ∈ ({b} : Finset (Fin d)) := by rw [← eq]; simp
    simpa using h
  have sz : singles.card = d := by
    rw [← Finset.card_image_of_injOn inj, image_eq, Finset.card_image_of_injective _ singleton_inj]
    simp
  have big : Finset.range n \ singles = (Finset.range n).filter (fun i => 2 ≤ (targets i).card) := by
    ext i
    by_cases hi : i ∈ Finset.range n
    · have nz := Finset.card_pos.mpr (used i (Finset.mem_range.mp hi))
      simp only [Finset.mem_sdiff, Finset.mem_filter, singles, hi, true_and]
      omega
    · simp [hi]
  have hs : singles ⊆ Finset.range n := Finset.filter_subset _ _
  have part := Finset.card_sdiff_add_card_eq_card hs
  rw [big, sz, Finset.card_range] at part
  exact part

-- The complete punctured encoder uses one input for every nonempty proper subset.
theorem full_encoder_column_count {n d : ℕ} (hd : 2 ≤ d) (targets : ℕ → Finset (Fin d))
    (different : Set.InjOn targets (↑(Finset.range n) : Set ℕ))
    (all_masks : ∀ p : Finset (Fin d), p ∈ (Finset.range n).image targets ↔
      p.Nonempty ∧ p ≠ Finset.univ) : n + 2 = 2 ^ d := by
  classical
  let U : Finset (Fin d) := Finset.univ
  have une : U ≠ ∅ := by
    intro eq
    have hh := congrArg Finset.card eq
    simp [U] at hh
    omega
  have lhs : (Finset.range n).image targets = (U.powerset.erase ∅).erase U := by
    ext p
    rw [all_masks, Finset.mem_erase, Finset.mem_erase, Finset.mem_powerset]
    have sub : p ⊆ U := Finset.subset_univ _
    simp only [sub, and_true, Finset.nonempty_iff_ne_empty]
    exact and_comm
  have a : (∅ : Finset (Fin d)) ∈ U.powerset := by simp
  have b : U ∈ U.powerset.erase ∅ := Finset.mem_erase.mpr ⟨une, by simp⟩
  have h1 := Finset.card_erase_add_one a
  have h2 := Finset.card_erase_add_one b
  have sz : U.powerset.card = 2 ^ d := by simp [U]
  have hn : ((U.powerset.erase ∅).erase U).card = n := by
    rw [← lhs, Finset.card_image_of_injOn different, Finset.card_range]
  omega

theorem full_encoder_lower_of_count {n d s : ℕ} (hd : 2 ≤ d) (targets : ℕ → Finset (Fin d))
    (different : Set.InjOn targets (↑(Finset.range n) : Set ℕ))
    (all_masks : ∀ p : Finset (Fin d), p ∈ (Finset.range n).image targets ↔
      p.Nonempty ∧ p ≠ Finset.univ)
    (lower : n + ((Finset.range n).filter (fun i => 2 ≤ (targets i).card)).card ≤ s + d) :
    2 * (2 ^ d - 2 - d) ≤ s := by
  have used (i : ℕ) (hi : i < n) : (targets i).Nonempty :=
    ((all_masks _).mp (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))).1
  have singleton_mem (v : Fin d) : ∃ i < n, targets i = {v} := by
    have hp : ({v} : Finset (Fin d)) ≠ Finset.univ := by
      intro eq
      have h := congrArg Finset.card eq
      simp at h
      omega
    obtain ⟨i, hi, h⟩ := Finset.mem_image.mp ((all_masks _).mpr ⟨Finset.singleton_nonempty _, hp⟩)
    exact ⟨i, Finset.mem_range.mp hi, h⟩
  have nonsingles := encoder_nonsingletons _ used different singleton_mem
  have total := full_encoder_column_count hd _ different all_masks
  omega

theorem full_encoder_circuit_lower {n d : ℕ} (hd : 2 ≤ d)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ok : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2)
    (out : Fin d → ℕ) (targets : ℕ → Finset (Fin d))
    (spec : ∀ p : Fin n, ∀ v, onehotWire n C p (out v) = true ↔ v ∈ targets p.val)
    (different : Set.InjOn targets (↑(Finset.range n) : Set ℕ))
    (all_masks : ∀ p : Finset (Fin d), p ∈ (Finset.range n).image targets ↔
      p.Nonempty ∧ p ≠ Finset.univ) : 2 * (2 ^ d - 2 - d) ≤ C.size := by
  apply full_encoder_lower_of_count hd targets different all_masks
  exact encoder_circuit_bound C ok out targets spec
    (fun i hi => ((all_masks _).mp (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))).1) different

namespace EncoderTranspose

open PEqualNP.CircuitLowerBounds

abbrev Vertex (m : ℕ) := Fin m
abbrev Arc (m : ℕ) := Vertex m × Vertex m
abbrev Split (m : ℕ) := Vertex m × (Vertex m × Vertex m)

def send {m : ℕ} (w : Vertex m → Bool) (a : Arc m) : Vertex m → Bool :=
  Function.update w a.2 (w a.2 || w a.1)

def arcs {m : ℕ} (steps : List (Split m)) : List (Arc m) :=
  steps.flatMap fun s => [(s.1,s.2.1), (s.1,s.2.2)]

/-- A reverse schedule. Each removed node has union support; both children remain live. -/
inductive Plan {m d : ℕ} (S : Vertex m → Finset (Fin d)) :
    Finset (Vertex m) → List (Split m) → Finset (Vertex m) → Prop
  | done (live) : Plan S live [] live
  | step {live tail leaves v a b} (hv : v ∈ live) (ha : a ∈ live.erase v)
      (hb : b ∈ live.erase v) (union : S v = S a ∪ S b)
      (rest : Plan S (live.erase v) tail leaves) : Plan S live ((v,a,b)::tail) leaves

private def carries {m d : ℕ} (S : Vertex m → Finset (Fin d)) (live : Finset (Vertex m))
    (w : Vertex m → Bool) (k : Fin d) := ∃ i ∈ live, k ∈ S i ∧ w i = true

private theorem step_on {m : ℕ} (w : Vertex m → Bool) (v a b i : Vertex m)
    (ha : a ≠ v) (hb : b ≠ v) :
    send (send w (v,a)) (v,b) i = true ↔
      w i = true ∨ (i = a ∨ i = b) ∧ w v = true := by
  have hva : v ≠ a := Ne.symm ha
  have hvb : v ≠ b := Ne.symm hb
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hab : a = b <;>
      simp_all [send,Function.update, Bool.or_eq_true]

private theorem carries_step {m d : ℕ} (S : Vertex m → Finset (Fin d))
    (live : Finset (Vertex m)) (v a b : Vertex m) (hv : v ∈ live)
    (ha : a ∈ live.erase v) (hb : b ∈ live.erase v) (un : S v = S a ∪ S b)
    (w : Vertex m → Bool) (k : Fin d) :
    carries S live w k ↔ carries S (live.erase v) (send (send w (v,a)) (v,b)) k := by
  have av := (Finset.mem_erase.mp ha).1
  have bv := (Finset.mem_erase.mp hb).1
  constructor
  · rintro ⟨i,hi,hk,hw⟩
    by_cases eq : i = v
    · subst i
      rw [un,Finset.mem_union] at hk
      rcases hk with hk|hk
      · exact ⟨a,ha,hk,(step_on w v a b a av bv).mpr (Or.inr ⟨Or.inl rfl,hw⟩)⟩
      · exact ⟨b,hb,hk,(step_on w v a b b av bv).mpr (Or.inr ⟨Or.inr rfl,hw⟩)⟩
    · exact ⟨i,Finset.mem_erase.mpr ⟨eq,hi⟩,hk,(step_on w v a b i av bv).mpr (Or.inl hw)⟩
  · rintro ⟨i,hi,hk,hon⟩
    rcases (step_on w v a b i av bv).mp hon with hw|⟨eq,hw⟩
    · exact ⟨i,(Finset.mem_erase.mp hi).2,hk,hw⟩
    · refine ⟨v,hv,?_,hw⟩
      rw [un,Finset.mem_union]
      rcases eq with rfl|rfl
      · exact Or.inl hk
      · exact Or.inr hk

private theorem preserves {m d : ℕ} {S : Vertex m → Finset (Fin d)} {live leaves steps}
    (h : Plan S live steps leaves) (w : Vertex m → Bool) (k : Fin d) :
    carries S live w k ↔ carries S leaves ((arcs steps).foldl send w) k := by
  induction h generalizing w with
  | done => rfl
  | @step live tail leaves v a b hv ha hb un rest ih =>
    rw [carries_step S live v a b hv ha hb un w k]
    exact ih _

structure Program (m : ℕ) where
  gates : List Gate
  port : Vertex m → ℕ

private def wireStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [wireStep]; omega

def extend {m : ℕ} (p : Program m) (a : Arc m) : Program m :=
  ⟨p.gates ++ [⟨.or,[p.port a.2,p.port a.1]⟩],
    Function.update p.port a.2 (m + p.gates.length)⟩

def readP {m : ℕ} (p : Program m) (x : Vertex m → Bool) (i : Vertex m) :=
  ((p.gates.foldl wireStep (List.ofFn x)).getD (p.port i) false)

def BitsLegal (m : ℕ) (gs : List Gate) :=
  ∀ j (hj : j < gs.length), (gs[j]).op = GateOp.or ∧ (gs[j]).inputs.length = 2 ∧
    ∀ i ∈ (gs[j]).inputs, i < m+j

private def Good {m : ℕ} (p : Program m) :=
  BitsLegal m p.gates ∧ ∀ i, p.port i < m+p.gates.length

private lemma safeExtend {m : ℕ} (p : Program m) (a : Arc m) (h : Good p) :
    Good (extend p a) := by
  constructor
  · intro j hj
    by_cases hj' : j < p.gates.length
    · simpa only [extend,List.getElem_append_left hj'] using h.1 j hj'
    · have eq : j = p.gates.length := by simp [extend] at hj; omega
      subst j
      simp [extend, List.getElem_append_right (Nat.le_refl p.gates.length), h.2]
  · intro i
    by_cases e : i = a.2
    · simp [extend,Function.update,e]
    · have hi := h.2 i
      simp [extend,Function.update,e]
      omega

private theorem read_extend {m : ℕ} (p : Program m) (a : Arc m) (h : Good p)
    (x : Vertex m → Bool) :
    readP (extend p a) x = send (readP p x) a := by
  funext i
  let w := p.gates.foldl wireStep (List.ofFn x)
  have len : w.length = m+p.gates.length := by simp [w,fold_len]
  by_cases e : i = a.2
  · subst i
    change ((p.gates ++ [_]).foldl wireStep (List.ofFn x)).getD _ false = _
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    change (w ++ [_]).getD ((Function.update p.port a.2 (m+p.gates.length)) a.2) false = _
    rw [Function.update_self, ←len]
    simp [readP,send,w,GateOp.eval,List.getD_eq_getElem?_getD]
  · have lt : p.port i < w.length := by rw [len]; exact h.2 i
    change ((p.gates ++ [_]).foldl wireStep (List.ofFn x)).getD _ false = _
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    change (w ++ [_]).getD ((Function.update p.port a.2 (m+p.gates.length)) i) false = _
    rw [Function.update_of_ne e]
    simp [send,Function.update,e,readP,w,List.getD_eq_getElem?_getD,
      List.getElem?_append_left lt]

private theorem fold_safe {m : ℕ} (moves : List (Arc m)) (p : Program m) (h : Good p) :
    Good (moves.foldl extend p) ∧ (moves.foldl extend p).gates.length = p.gates.length+moves.length ∧
    ∀ x, readP (moves.foldl extend p) x = moves.foldl send (readP p x) := by
  induction moves generalizing p with
  | nil => exact ⟨h,by simp,by simp⟩
  | cons a tail ih =>
    obtain ⟨hs,hl,hr⟩ := ih (extend p a) (safeExtend p a h)
    refine ⟨hs,?_,?_⟩
    · rw [List.foldl_cons,hl]
      simp [extend]
      omega
    · intro x
      rw [List.foldl_cons,hr,read_extend p a h,List.foldl_cons]

/-- Transpose an arbitrary union decomposition. Every reverse arc contributes one binary OR. -/
theorem realizePlan {m d : ℕ} (S : Vertex m → Finset (Fin d))
    (steps : List (Split m)) (leaves : Finset (Vertex m)) (leaf : Fin d → Vertex m)
    (plan : Plan S Finset.univ steps leaves)
    (single : ∀ k i, (i ∈ leaves ∧ k ∈ S i) ↔ i = leaf k) :
    ∃ (C : Circuit) (out : Fin d → ℕ), BitsLegal m C.gates ∧ C.size = 2*steps.length ∧
      ∀ (x : Vertex m → Bool) (k : Fin d),
        (C.wires (List.ofFn x)).getD (out k) false = true ↔ ∃ i, k ∈ S i ∧ x i = true := by
  let initial : Program m := ⟨[],Fin.val⟩
  have hi : Good initial := ⟨by intro j hj; simp [initial] at hj, by intro i; exact i.isLt⟩
  let q := (arcs steps).foldl extend initial
  obtain ⟨hq,hl,hr⟩ := fold_safe (arcs steps) initial hi
  have count (ls : List (Split m)) : (arcs ls).length = 2 * ls.length := by
    induction ls with
    | nil => rfl
    | cons a ls ih =>
      change (arcs ls).length + 1 + 1 = 2 * (ls.length + 1)
      omega
  refine ⟨⟨q.gates,0⟩,fun k => q.port (leaf k),hq.1,?_,?_⟩
  · change ((arcs steps).foldl extend initial).gates.length = _
    simpa [initial,count] using hl
  · intro x k
    have base : readP initial x = x := by
      funext i
      simp [readP,initial,List.getD_eq_getElem?_getD]
    have sem : readP q x = (arcs steps).foldl send x := (hr x).trans (by rw [base])
    have inv := preserves plan x k
    rw [←sem] at inv
    change readP q x (leaf k) = true ↔ _
    constructor
    · intro hon
      have hm := (single k (leaf k)).mpr rfl
      have hstart := inv.mpr ⟨leaf k, hm.1,hm.2,hon⟩
      simpa [carries] using hstart
    · rintro ⟨i,hk,hx⟩
      obtain ⟨j,hj,hjk,hon⟩ := inv.mp ⟨i,Finset.mem_univ _,hk,hx⟩
      simpa [(single k j).mp ⟨hj,hjk⟩] using hon

-- A family decomposable into unions admits a schedule in decreasing cardinality.
-- At each step a largest remaining nonsingleton can be removed: both children
-- of every remaining decomposition are strictly smaller and therefore survive.
private theorem exists_plan_on {m d : ℕ} (S : Fin m → Finset (Fin d))
    (used : ∀ i, (S i).Nonempty) (live : Finset (Fin m))
    (split : ∀ i ∈ live, 2 ≤ (S i).card → ∃ a ∈ live, ∃ b ∈ live,
      (S a).card < (S i).card ∧ (S b).card < (S i).card ∧ S i = S a ∪ S b) :
    ∃ steps, Plan S live steps (live.filter (fun i => (S i).card = 1)) ∧
      steps.length = (live.filter (fun i => 2 ≤ (S i).card)).card := by
  classical
  induction live using Finset.strongInductionOn with
  | _ live ih =>
    by_cases big : ∃ i ∈ live, 2 ≤ (S i).card
    · obtain ⟨w,hw,hbig⟩ := big
      obtain ⟨v,hv,hmax⟩ := live.exists_max_image (fun i => (S i).card) ⟨w,hw⟩
      have kv : 2 ≤ (S v).card := hbig.trans (hmax w hw)
      have keep (i : Fin m) (hi : i ∈ live) (hs : (S i).card < (S v).card) :
          i ∈ live.erase v := by
        apply Finset.mem_erase.mpr
        exact ⟨fun hi => (Nat.lt_irrefl _ (hi ▸ hs)),hi⟩
      obtain ⟨a,ha,b,hb,hav,hbv,un⟩ := split v hv kv
      have remaining : ∀ i ∈ live.erase v, 2 ≤ (S i).card → ∃ c ∈ live.erase v, ∃ e ∈ live.erase v,
          (S c).card < (S i).card ∧ (S e).card < (S i).card ∧ S i = S c ∪ S e := by
        intro i hi hk
        have him := (Finset.mem_erase.mp hi).2
        obtain ⟨c,hc,e,he,hs,ht,hu⟩ := split i him hk
        exact ⟨c,keep c hc (lt_of_lt_of_le hs (hmax i him)),
          e,keep e he (lt_of_lt_of_le ht (hmax i him)),hs,ht,hu⟩
      obtain ⟨tail,p,hlen⟩ := ih (live.erase v) (Finset.erase_ssubset hv) remaining
      have keep_leaves : (live.erase v).filter (fun i => (S i).card = 1) =
          live.filter (fun i => (S i).card = 1) := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_erase]
        constructor
        · rintro ⟨⟨_,hm⟩,ks⟩; exact ⟨hm,ks⟩
        · rintro ⟨hm,ks⟩
          exact ⟨⟨fun h => by subst i; omega,hm⟩,ks⟩
      rw [keep_leaves] at p
      refine ⟨(v,a,b)::tail,.step hv (keep a ha hav) (keep b hb hbv) un p,?_⟩
      have same : (live.erase v).filter (fun i => 2 ≤ (S i).card) =
          (live.filter (fun i => 2 ≤ (S i).card)).erase v := by
        ext i
        simp [and_assoc]
      rw [List.length_cons,hlen,same]
      exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hv,kv⟩)
    · have one (i) (hi : i ∈ live) : (S i).card = 1 := by
        have pos := Finset.card_pos.mpr (used i)
        have lt : ¬ 2 ≤ (S i).card := fun h => big ⟨i,hi,h⟩
        omega
      have all_leaves : live.filter (fun i => (S i).card = 1) = live := Finset.filter_eq_self.mpr one
      have no_big : live.filter (fun i => 2 ≤ (S i).card) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact big ⟨i,(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2⟩
      rw [all_leaves,no_big]
      exact ⟨[],.done _,rfl⟩

theorem exists_encoder_plan {m d : ℕ} (S : Fin m → Finset (Fin d))
    (used : ∀ i, (S i).Nonempty) (different : Function.Injective S)
    (singletons : ∀ k, ∃ i, S i = {k})
    (split : ∀ i, 2 ≤ (S i).card → ∃ a b,
      (S a).card < (S i).card ∧ (S b).card < (S i).card ∧ S i = S a ∪ S b) :
    ∃ (steps : List (Split m)) (leaves : Finset (Fin m)) (leaf : Fin d → Fin m),
      Plan S Finset.univ steps leaves ∧ (∀ k i, (i ∈ leaves ∧ k ∈ S i) ↔ i = leaf k) ∧
      steps.length = (Finset.univ.filter (fun i => 2 ≤ (S i).card)).card := by
  classical
  obtain ⟨steps,hplan,hlen⟩ := exists_plan_on S used Finset.univ (by simpa using split)
  choose leaf hleaf using singletons
  refine ⟨steps,_,leaf,hplan,?_,hlen⟩
  intro k i
  constructor
  · rintro ⟨hm,hk⟩
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hm).2
    have eq : k=v := by simpa [hv] using hk
    subst v
    exact different (hv.trans (hleaf k).symm)
  · rintro rfl
    simp [hleaf]

-- Nonempty faces of a simplicial complex have the required decomposition.
theorem split_of_downclosed {m d : ℕ} (S : Fin m → Finset (Fin d))
    (down : ∀ i T, T.Nonempty → T ⊆ S i → ∃ j, S j=T) :
    ∀ i, 2 ≤ (S i).card → ∃ a b,
      (S a).card < (S i).card ∧ (S b).card < (S i).card ∧ S i = S a ∪ S b := by
  intro i hi
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < (S i).card)
  have hsz := Finset.card_erase_add_one hv
  obtain ⟨a,ha⟩ := down i ((S i).erase v) (Finset.card_pos.mp (by omega)) (Finset.erase_subset _ _)
  obtain ⟨b,hb⟩ := down i {v} (Finset.singleton_nonempty _) (Finset.singleton_subset_iff.mpr hv)
  refine ⟨a,b,?_,?_,?_⟩
  · rw [ha]; omega
  · rw [hb,Finset.card_singleton]; omega
  · rw [ha,hb,Finset.union_singleton,Finset.insert_erase hv]

theorem downclosed_of_proper_masks {m d : ℕ} (S : Fin m → Finset (Fin d))
    (all_masks : ∀ T, (∃ i, S i=T) ↔ T.Nonempty ∧ T ≠ Finset.univ) :
    ∀ i T, T.Nonempty → T ⊆ S i → ∃ j, S j=T := by
  intro i T hT hsub
  apply (all_masks T).mpr
  refine ⟨hT,?_⟩
  intro eq
  have proper := ((all_masks (S i)).mp ⟨i,rfl⟩).2
  rw [eq] at hsub
  exact proper (Finset.Subset.antisymm (Finset.subset_univ _) hsub)

end EncoderTranspose

def OrEncoderOnUnits {n d : ℕ} (targets : ℕ → Finset (Fin d)) (C : Circuit) : Prop :=
  (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
  ∃ out : Fin d → ℕ, ∀ p : Fin n, ∀ v,
    onehotWire n C p (out v) = true ↔ v ∈ targets p.val

private theorem fin_column_count {n d : ℕ} (targets : ℕ → Finset (Fin d)) :
    (Finset.univ.filter (fun i : Fin n => 2 ≤ (targets i.val).card)).card =
      ((Finset.range n).filter (fun i => 2 ≤ (targets i).card)).card := by
  classical
  let cols := Finset.univ.filter (fun i : Fin n => 2 ≤ (targets i.val).card)
  have e : cols.image Fin.val = (Finset.range n).filter (fun i => 2 ≤ (targets i).card) := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt,(Finset.mem_filter.mp hj).2⟩
    · intro hi
      obtain ⟨bound,big⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_image.mpr ⟨⟨i,Finset.mem_range.mp bound⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,big⟩,rfl⟩
  rw [← e,Finset.card_image_of_injective _ Fin.val_injective]

-- The constructed circuit computes the encoder simultaneously on arbitrary inputs.
theorem circuit_of_binary_decompositions {n d : ℕ} (T : ℕ → Finset (Fin d))
    (used : ∀ i < n, (T i).Nonempty)
    (distinct : Set.InjOn T (↑(Finset.range n) : Set ℕ))
    (single : ∀ k : Fin d, ∃ i < n, T i = {k})
    (split : HasBinaryDecompositions n T) :
    ∃ (C : Circuit) (out : Fin d → ℕ), EncoderTranspose.BitsLegal n C.gates ∧
      C.size = 2 * (n-d) ∧ ∀ (x : Fin n → Bool) k,
        (C.wires (List.ofFn x)).getD (out k) false = true ↔ ∃ i : Fin n, k ∈ T i.val ∧ x i = true := by
  classical
  let S (i : Fin n) := T i.val
  have inj : Function.Injective S := fun i j h => Fin.ext (distinct (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt) h)
  have singles (v : Fin d) : ∃ i : Fin n, S i = {v} := by
    obtain ⟨i,hi,h⟩ := single v
    exact ⟨⟨i,hi⟩,h⟩
  have divides (i : Fin n) (big : 2 ≤ (S i).card) :
      ∃ a b, (S a).card < (S i).card ∧ (S b).card < (S i).card ∧ S i = S a ∪ S b := by
    obtain ⟨a,ha,b,hb,sa,sb,e⟩ := split i.val i.isLt big
    exact ⟨⟨a,ha⟩,⟨b,hb⟩,sa,sb,e⟩
  obtain ⟨steps,leaves,leaf,plan,singleLeaf,length⟩ :=
    EncoderTranspose.exists_encoder_plan S (fun i => used i.val i.isLt) inj singles divides
  obtain ⟨C,out,legal,sz,eval⟩ := EncoderTranspose.realizePlan S steps leaves leaf plan singleLeaf
  refine ⟨C,out,legal,?_,eval⟩
  have h := encoder_nonsingletons T used distinct single
  rw [sz,length]
  change 2 * (Finset.univ.filter (fun i : Fin n => 2 ≤ (T i.val).card)).card = _
  rw [fin_column_count]
  omega

theorem encoder_attains_bound_iff {n d : ℕ} (T : ℕ → Finset (Fin d))
    (used : ∀ i < n, (T i).Nonempty)
    (distinct : Set.InjOn T (↑(Finset.range n) : Set ℕ))
    (single : ∀ k : Fin d, ∃ i < n, T i = {k}) :
    (∃ C : Circuit, OrEncoderOnUnits (n := n) T C ∧ C.size ≤ 2*(n-d)) ↔
      HasBinaryDecompositions n T := by
  constructor
  · rintro ⟨C,⟨ok,out,hspec⟩,budget⟩
    have spec (i : ℕ) (hi : i<n) (k : Fin d) :
        k ∈ T i ↔ out k < n+C.size ∧ Relation.ReflTransGen (wireEdge n C) i (out k) :=
      (hspec ⟨i,hi⟩ k).symm.trans (onehot_reach C ok ⟨i,hi⟩ (out k))
    have account := encoder_dag_account (wireEdge n C) out T (fun e => wireEdge_bounds e)
      (wireEdge_fanin ok) spec used distinct
    have count := encoder_nonsingletons T used distinct single
    exact account.2 (by omega) single
  · intro split
    obtain ⟨C,out,legal,sz,h⟩ := circuit_of_binary_decompositions T used distinct single split
    refine ⟨C,⟨?_,out,?_⟩,sz.le⟩
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
      exact ⟨(legal j hj).1,(legal j hj).2.1.le⟩
    · intro p k
      simpa [onehotWire] using h (fun q : Fin n => decide (q=p)) k

-- Specialization to all nonempty proper subsets of the bit positions.
theorem full_encoder_exact {n d : ℕ} (hd : 2 ≤ d) (T : ℕ → Finset (Fin d))
    (distinct : Set.InjOn T (↑(Finset.range n) : Set ℕ))
    (all_masks : ∀ X, X ∈ (Finset.range n).image T ↔ X.Nonempty ∧ X ≠ Finset.univ) :
    (∃ C : Circuit, OrEncoderOnUnits (n := n) T C ∧ C.size = 2*(2^d-2-d)) ∧
      (∀ C : Circuit, OrEncoderOnUnits (n := n) T C → 2*(2^d-2-d) ≤ C.size) := by
  classical
  have member (i : ℕ) (hi : i<n) := (all_masks (T i)).mp (Finset.mem_image_of_mem T (Finset.mem_range.mpr hi))
  have down (i : Fin n) (X : Finset (Fin d)) (hne : X.Nonempty) (sub : X ⊆ T i.val) :
      ∃ j : Fin n, T j.val = X := by
    have proper : X ≠ Finset.univ := by
      intro eq
      rw [eq] at sub
      exact (member i.val i.isLt).2 (Finset.Subset.antisymm (Finset.subset_univ _) sub)
    obtain ⟨j,hj,e⟩ := Finset.mem_image.mp ((all_masks X).mpr ⟨hne,proper⟩)
    exact ⟨⟨j,Finset.mem_range.mp hj⟩,e⟩
  have singles (k : Fin d) : ∃ i < n, T i = {k} := by
    have proper : ({k} : Finset (Fin d)) ≠ Finset.univ := by
      intro eq
      have card := congrArg Finset.card eq
      simp at card
      omega
    obtain ⟨i,hi,e⟩ := Finset.mem_image.mp ((all_masks {k}).mpr ⟨Finset.singleton_nonempty _,proper⟩)
    exact ⟨i,Finset.mem_range.mp hi,e⟩
  have divides : HasBinaryDecompositions n T := by
    intro i hi big
    obtain ⟨a,b,sa,sb,e⟩ := EncoderTranspose.split_of_downclosed (fun j : Fin n => T j.val) down ⟨i,hi⟩ big
    exact ⟨a.val,a.isLt,b.val,b.isLt,sa,sb,e⟩
  have low (C : Circuit) (hc : OrEncoderOnUnits (n := n) T C) : 2*(2^d-2-d) ≤ C.size := by
    obtain ⟨ok,out,h⟩ := hc
    exact full_encoder_circuit_lower hd C ok out T h distinct all_masks
  refine ⟨?_,low⟩
  obtain ⟨C,hc,hsize⟩ := (encoder_attains_bound_iff T (fun i hi => (member i hi).1) distinct singles).mpr divides
  have ncard := full_encoder_column_count hd T distinct all_masks
  have lo := low C hc
  exact ⟨C,hc,by omega⟩

-- Every dimension has an enumeration to which the exact encoder theorem applies.
theorem exists_full_encoder_enumeration (d : ℕ) (hd : 2 ≤ d) :
    ∃ T : ℕ → Finset (Fin d), Set.InjOn T (↑(Finset.range (2^d-2)) : Set ℕ) ∧
      ∀ X, X ∈ (Finset.range (2^d-2)).image T ↔ X.Nonempty ∧ X ≠ Finset.univ := by
  classical
  let U : Finset (Fin d) := Finset.univ
  let F := (U.powerset.erase ∅).erase U
  have proper (X : Finset (Fin d)) : X ∈ F ↔ X.Nonempty ∧ X ≠ Finset.univ := by
    simp only [F,Finset.mem_erase,Finset.mem_powerset]
    have sub : X ⊆ U := Finset.subset_univ _
    simp only [sub,and_true,Finset.nonempty_iff_ne_empty]
    exact and_comm
  have une : U ≠ ∅ := by
    intro e
    have he := congrArg Finset.card e
    simp [U] at he
    omega
  have empty_mem : (∅ : Finset (Fin d)) ∈ U.powerset := by simp
  have full_mem : U ∈ U.powerset.erase ∅ := Finset.mem_erase.mpr ⟨une,by simp⟩
  have first := Finset.card_erase_add_one empty_mem
  have second := Finset.card_erase_add_one full_mem
  have total : U.powerset.card = 2^d := by simp [U]
  have sz : Fintype.card ↥F = 2^d-2 := by
    rw [Fintype.card_coe]
    dsimp only [F]
    omega
  let e : ↥F ≃ Fin (2^d-2) := Fintype.equivFinOfCardEq sz
  let T (i : ℕ) : Finset (Fin d) := if h : i < 2^d-2 then (e.symm ⟨i,h⟩).val else ∅
  refine ⟨T,?_,?_⟩
  · intro i hi j hj same
    have bi := Finset.mem_range.mp hi
    have bj := Finset.mem_range.mp hj
    have same' : e.symm ⟨i,bi⟩ = e.symm ⟨j,bj⟩ := Subtype.ext (by simpa [T,bi,bj] using same)
    exact congrArg Fin.val (e.symm.injective same')
  · intro X
    rw [← proper]
    constructor
    · intro hit
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hit
      have bi := Finset.mem_range.mp hi
      simp [T,bi]
    · intro hX
      let q : ↥F := ⟨X,hX⟩
      refine Finset.mem_image.mpr ⟨(e q).val,Finset.mem_range.mpr (e q).isLt,?_⟩
      simp [T,q]

namespace FourBitExample

open PEqualNP.CircuitLowerBounds

private def encoder : Circuit :=
  ⟨[⟨.or, [1, 13]⟩,
   ⟨.or, [11, 13]⟩,
   ⟨.or, [0, 12]⟩,
   ⟨.or, [15, 12]⟩,
   ⟨.or, [3, 17]⟩,
   ⟨.or, [7, 17]⟩,
   ⟨.or, [16, 10]⟩,
   ⟨.or, [9, 10]⟩,
   ⟨.or, [14, 21]⟩,
   ⟨.or, [19, 21]⟩,
   ⟨.or, [20, 8]⟩,
   ⟨.or, [23, 8]⟩,
   ⟨.or, [24, 6]⟩,
   ⟨.or, [5, 6]⟩,
   ⟨.or, [22, 27]⟩,
   ⟨.or, [18, 27]⟩,
   ⟨.or, [26, 4]⟩,
   ⟨.or, [29, 4]⟩,
   ⟨.or, [30, 2]⟩,
   ⟨.or, [28, 2]⟩], 32⟩

private def outputs : Fin 4 → ℕ := ![32, 33, 31, 25]

theorem upper : ∃ C : Circuit,
    (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size = 20 ∧
    ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14,
      (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false =
        Nat.testBit (p.val + 1) v.val := by
  refine ⟨encoder, ?_, rfl, ?_⟩
  · intro g hg
    simp only [encoder, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩
  · have cert : ∀ v : Fin 4, ∀ p : Fin 14,
        (encoder.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD (outputs v) false =
          Nat.testBit (p.val + 1) v.val := by decide +kernel
    exact fun v => ⟨outputs v, cert v⟩

end FourBitExample

end PEqualNP.Research.OREncoder

theorem PEqualNP.Research.OREncoder : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 19 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false = Nat.testBit (p.val + 1) v.val) := by
  rintro ⟨C, ok, small, h⟩
  have lower := PEqualNP.Research.OREncoder.encoder_four_lower C ok h
  omega
