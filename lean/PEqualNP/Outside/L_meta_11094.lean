import Mathlib
import PEqualNP.Defs

-- A counterexample to L-meta-11094.
-- Start with the triangle on 0, 1, 4 and pendant edges 03 and 12.
-- Give vertex 0 additional independent copies with the same three neighbors.
-- For t copies the graph has 5+t vertices and 5+3*t edges.
-- Its displayed two-input AND/OR circuit is in top form, contains a dirty AND,
-- and has minimum size t+6. Thus twice the edge count exceeds size plus one by 5*t+3.
-- This is the negation of the posted conjecture.
-- The project already treats the triangle and bull in L_meta_931.g3 and
-- L_meta_931.g14. L_meta_5495 also treats one duplicated bull vertex.
-- The construction here supplies all t, the top-form and dirty-gate witnesses,
-- and the resulting obstruction to the uniform square-root error.
-- More generally, any connected n-vertex graph containing a triangle needs
-- at least n+1 gates in this model. Root a spanning tree at the contracted
-- triangle and remove leaves towards it. Each removed input is essential
-- and the remaining triangle keeps the restricted function nonconstant.
-- The restriction lemma costs one gate each time, leaving four for the triangle.
--
-- Here is a structural proof of the five-vertex base case.
-- In the output cone of a binary circuit with s gates and five essential inputs,
-- the number of outgoing uses in excess of one per non-output wire is s-4.
-- If s is at most five and each input has just one use, the first gate
-- exchanges its two inputs without changing the function. The bull has no
-- interchangeable pair: the only same-degree pairs are 0,1 and 2,3, and
-- vertices 3 and 1 respectively distinguish their members.
-- Otherwise one input has two uses and the cone is a tree with at most six
-- leaves. Setting the two pendant inputs to zero deletes at least two leaves.
-- The remaining function is majority on the three triangle vertices.
-- A monotone formula for majority needs at least five leaves. A one-leaf
-- child at the root can force the output by itself, which majority forbids.
-- With two leaves on each side and an OR root, each child must be the AND
-- of two distinct inputs to reject singletons. Two such children can accept
-- only two of the three positive pairs. The AND root follows by duality.
-- The formal proof fixes the pendant inputs using the same restriction lemma
-- and checks the eight input rows of three-variable majority.

namespace PEqualNP.Outside.L_meta_11094

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

-- Basic wire-evaluation lemmas follow the project's L_meta_1490.
namespace BullWires

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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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


end BullWires

def bullCopies (t : ℕ) (x : Fin (5+t) → Bool) : Bool :=
  decide (∃ i : Fin (5+t), (i.val = 0 ∨ 5 ≤ i.val) ∧ x i = true)

def bullValue (t : ℕ) (x : Fin (5+t) → Bool) : Bool :=
  (bullCopies t x || x ⟨1, by omega⟩) &&
    (x ⟨4, by omega⟩ ||
      ((bullCopies t x || x ⟨2, by omega⟩) && (x ⟨1, by omega⟩ || x ⟨3, by omega⟩)))

private def bullPrev (t k : ℕ) := if k = 0 then 0 else (5 + t) + (k-1)

private lemma bullPrev_lt (t k : ℕ) : bullPrev t k < (5+t)+k := by
  unfold bullPrev
  split <;> omega

private def bullGate (t j : ℕ) : Gate :=
  if j < t then ⟨.or, [bullPrev t j, 5+j]⟩ else
  match j-t with
  | 0 => ⟨.or, [bullPrev t t, 1]⟩
  | 1 => ⟨.or, [bullPrev t t, 2]⟩
  | 2 => ⟨.or, [1, 3]⟩
  | 3 => ⟨.and, [(5+t)+(t+1), (5+t)+(t+2)]⟩
  | 4 => ⟨.or, [4, (5+t)+(t+3)]⟩
  | _ => ⟨.and, [(5+t)+t, (5+t)+(t+4)]⟩

def bullCircuit (t : ℕ) : Circuit :=
  ⟨List.ofFn (fun j : Fin (t+6) => bullGate t j), (5+t)+(t+5)⟩

@[simp] theorem bull_size (t : ℕ) : (bullCircuit t).size = t+6 := by
  simp [Circuit.size, bullCircuit]

@[simp] private lemma bull_length (t : ℕ) : (bullCircuit t).gates.length = t+6 := by
  simp [bullCircuit]

private lemma bullAt (t j : ℕ) (hj : j < t+6) :
    gateAt (bullCircuit t) j = bullGate t j := by
  rw [BullWires.gateAt_eq (by simpa using hj)]
  simp only [bullCircuit, List.getElem_ofFn]

private lemma tailIndices {t j : ℕ} (h : t ≤ j) (h' : j < t+6) :
    j = t ∨ j = t+1 ∨ j = t+2 ∨ j=t+3 ∨ j=t+4 ∨ j=t+5 := by omega

private lemma bull_gate_ok (t j : ℕ) (hj : j < t+6) :
    ((bullGate t j).op = GateOp.and ∨ (bullGate t j).op = GateOp.or) ∧
    (∀ i ∈ (bullGate t j).inputs, i < (5+t)+j) ∧ (bullGate t j).inputs.length = 2 := by
  have hb := bullPrev_lt t t
  by_cases h : j < t
  · simp [bullGate, h, bullPrev_lt]
    omega
  · rcases tailIndices (by omega : t ≤ j) hj with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [bullGate, bullPrev_lt] <;> omega

theorem bull_ao (t : ℕ) : PEqualNP.TopForm.IsAO2 (5+t) (bullCircuit t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact (bull_gate_ok t i i.isLt).1
  · intro j hj i hi
    rw [bull_length] at hj
    rw [bullAt t j hj] at hi
    exact (bull_gate_ok t j hj).2.1 i hi
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact (bull_gate_ok t i i.isLt).2.2

private def bWire (t : ℕ) (x : Fin (5+t) → Bool) (i : ℕ) : Bool :=
  BullWires.val (bullCircuit t) (List.ofFn x) i

private lemma bInput (t : ℕ) (x : Fin (5+t) → Bool) (i : ℕ) (h : i < 5+t) :
    bWire t x i = x ⟨i,h⟩ := BullWires.val_ofFn _ _ ⟨i,h⟩

private lemma bGate (t : ℕ) (x : Fin (5+t) → Bool) (j : ℕ) (hj : j<t+6) :
    bWire t x ((5+t)+j) = (bullGate t j).op.eval ((bullGate t j).inputs.map (bWire t x)) := by
  unfold bWire
  rw [BullWires.val_gate (n:=5+t) (by simp) (by simpa), bullAt t j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((bull_gate_ok t j hj).2.1 i hi)]

private lemma copiesRange (t : ℕ) (x : Fin (5+t) → Bool) (k : ℕ) (hk : k ≤ t) :
    bWire t x (bullPrev t k) = true ↔
      ∃ i : Fin (5+t), (i.val = 0 ∨ 5 ≤ i.val ∧ i.val < 5+k) ∧ x i = true := by
  induction k with
  | zero =>
    rw [show bullPrev t 0 = 0 by rfl, bInput t x 0 (by omega)]
    constructor
    · exact fun h => ⟨⟨0, by omega⟩, Or.inl rfl, h⟩
    · rintro ⟨i, (hi|hi), hx⟩
      · have he : i = (⟨0, by omega⟩ : Fin (5+t)) := Fin.ext hi
        simpa [he] using hx
      · omega
  | succ k ih =>
    have hkt : k<t := by omega
    rw [show bullPrev t (k+1) = (5+t)+k by simp [bullPrev], bGate t x k (by omega)]
    simp only [bullGate, if_pos hkt, List.map_cons, List.map_nil, GateOp.eval,
      List.any_cons, id_eq, List.any_nil, Bool.or_false, Bool.or_eq_true]
    rw [ih (by omega), bInput t x (5+k) (by omega)]
    constructor
    · rintro (⟨i, hi, hx⟩|hx)
      · exact ⟨i, by omega, hx⟩
      · exact ⟨⟨5+k, by omega⟩, Or.inr ⟨by change 5 ≤ 5+k; omega, by simp⟩, hx⟩
    · rintro ⟨i,hi,hx⟩
      by_cases hi' : i.val = 5+k
      · right
        have he : i = (⟨5+k, by omega⟩ : Fin (5+t)) := Fin.ext hi'
        simpa [he] using hx
      · exact Or.inl ⟨i, by omega, hx⟩

private lemma copiesWire (t : ℕ) (x : Fin (5+t) → Bool) :
    bWire t x (bullPrev t t) = bullCopies t x := by
  apply Bool.eq_iff_iff.mpr
  rw [copiesRange t x t (by omega)]
  simp [bullCopies]

private lemma innerOut (t : ℕ) (x : Fin (5+t) → Bool) :
    bWire t x ((5+t)+(t+3)) =
        ((bullCopies t x || x ⟨2,by omega⟩) && (x ⟨1,by omega⟩ || x ⟨3,by omega⟩)) ∧
    bWire t x ((5+t)+(t+5)) = bullValue t x := by
  have h0 := bGate t x t (by omega)
  have h1 := bGate t x (t+1) (by omega)
  have h2 := bGate t x (t+2) (by omega)
  have h3 := bGate t x (t+3) (by omega)
  have h4 := bGate t x (t+4) (by omega)
  have h5 := bGate t x (t+5) (by omega)
  simp [bullGate, GateOp.eval, copiesWire, bInput t x 1 (by omega), bInput t x 2 (by omega),
    bInput t x 3 (by omega), bInput t x 4 (by omega)] at h0 h1 h2 h3 h4 h5
  constructor
  · simpa [h1,h2] using h3
  · simpa [h0,h1,h2,h3,h4,bullValue] using h5

theorem bull_sem (t : ℕ) : circuitFun (5+t) (bullCircuit t) = bullValue t := by
  funext x
  exact (innerOut t x).2

private lemma bConeOrder (n : ℕ) (C : Circuit) (i j : ℕ) (h : InCone n C i j) : i < j := by
  let valid (cs : List (List ℕ)) := ∀ j i, i ∈ cs.getD j [] → i < j
  have step (cs : List (List ℕ)) (g : Gate) (hs : valid cs) : valid (coneStep n cs g) := by
    intro j i hi
    by_cases hj : j < cs.length
    · apply hs j i
      simpa [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj] using hi
    · by_cases he : j = cs.length
      · subst j
        simp [coneStep, List.getD_eq_getElem?_getD] at hi
        obtain ⟨w, ⟨_,hw⟩, hwi⟩ := hi
        rcases hwi with rfl|hwi
        · omega
        · have hl := hs (w-n) i (by simpa [List.getD_eq_getElem?_getD] using hwi)
          omega
      · have hlen : (coneStep n cs g).length ≤ j := by simp [coneStep]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at hi
  have fold (gs : List Gate) (cs : List (List ℕ)) (hs : valid cs) :
      valid (gs.foldl (coneStep n) cs) := by
    induction gs generalizing cs with
    | nil => exact hs
    | cons g gs ih => exact ih _ (step cs g hs)
  exact fold C.gates [] (by simp [valid]) j i h

private lemma bull_and_cases (t j : ℕ) (hj : j < t+6)
    (hop : (gateAt (bullCircuit t) j).op = GateOp.and) : j=t+3 ∨ j=t+5 := by
  rw [bullAt t j hj] at hop
  by_cases h : j<t
  · simp [bullGate,h] at hop
  · rcases tailIndices (by omega : t ≤ j) hj with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [bullGate] at *

theorem bull_top_junk (t : ℕ) (G : SimpleGraph (Fin (5+t))) [DecidableRel G.Adj]
    (hG : graphFun G ∅ = bullValue t) :
    PEqualNP.TopForm.TopForm G (bullCircuit t) ∧ (PEqualNP.TopForm.junk G (bullCircuit t)).Nonempty := by
  let x : Fin (5+t) → Bool := fun i => decide (i.val=2 ∨ i.val=3)
  have hb : bullCopies t x = false := by
    simp only [bullCopies, decide_eq_false_iff_not, not_exists, not_and]
    intro i hi
    simp only [x, decide_eq_true_eq]
    omega
  have hbad : gateVal (5+t) (bullCircuit t) (t+3) x = true := by
    change bWire t x ((5+t)+(t+3)) = true
    rw [(innerOut t x).1, hb]
    simp [x]
  have hno : graphFun G ∅ x = false := by
    rw [hG]
    unfold bullValue
    rw [hb]
    simp [x]
  constructor
  · intro i hi j hj hoi hbelow hoj hcone
    have hlt := bConeOrder _ _ _ _ hcone
    rcases bull_and_cases t i (by simpa using hi) hoi with rfl|rfl
    · exact Bool.noConfusion ((hbelow x hbad).symm.trans hno)
    · simp only [bull_length] at hj
      omega
  · refine ⟨t+3, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by simp), ?_⟩⟩
    refine ⟨?_, by simp, x, hbad, hno⟩
    rw [bullAt t (t+3) (by omega)]
    simp [bullGate]

private def bullDir {t : ℕ} (i j : Fin (5+t)) : Prop :=
  ((i.val = 0 ∨ 5 ≤ i.val) ∧ (j.val = 1 ∨ j.val = 3 ∨ j.val = 4)) ∨
    (i.val = 1 ∧ (j.val = 2 ∨ j.val = 4))

def bullGraph (t : ℕ) : SimpleGraph (Fin (5+t)) where
  Adj i j := bullDir i j ∨ bullDir j i
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by intro i h; change bullDir i i ∨ bullDir i i at h; unfold bullDir at h; omega⟩

private lemma bullDistribution (a b c d e : Prop) :
    ((a ∧ (b ∨ d ∨ e)) ∨ (b ∧ (c ∨ e))) ↔
      ((a ∨ b) ∧ (e ∨ ((a ∨ c) ∧ (b ∨ d)))) := by tauto

set_option maxHeartbeats 600000 in
private lemma bull_graphFun (t : ℕ) [DecidableRel (bullGraph t).Adj] :
    graphFun (bullGraph t) ∅ = bullValue t := by
  funext x
  let p (k : ℕ) (hk : k < 5+t) : Fin (5+t) := ⟨k,hk⟩
  have atPoint (i : Fin (5+t)) (k : ℕ) (hk : k < 5+t) (hi : i.val = k)
      (hx : x i = true) : x (p k hk) = true := by
    have eq : i = p k hk := Fin.ext hi
    simpa [eq] using hx
  have oriented : (∃ i j, (bullGraph t).Adj i j ∧ x i = true ∧ x j = true) ↔
      ∃ i j, bullDir i j ∧ x i = true ∧ x j = true := by
    constructor
    · rintro ⟨i,j,(h|h),a,b⟩
      · exact ⟨i,j,h,a,b⟩
      · exact ⟨j,i,h,b,a⟩
    · rintro ⟨i,j,h,a,b⟩; exact ⟨i,j,Or.inl h,a,b⟩
  have edges : (∃ i j, bullDir i j ∧ x i = true ∧ x j = true) ↔
      ((∃ i : Fin (5+t), (i.val = 0 ∨ 5 ≤ i.val) ∧ x i = true) ∧
        (x (p 1 (by omega)) = true ∨ x (p 3 (by omega)) = true ∨ x (p 4 (by omega)) = true)) ∨
      (x (p 1 (by omega)) = true ∧ (x (p 2 (by omega)) = true ∨ x (p 4 (by omega)) = true)) := by
    constructor
    · rintro ⟨i,j,h,hi,hj⟩
      rcases h with ⟨hc,h1|h3|h4⟩ | ⟨h1,h2|h4⟩
      · exact Or.inl ⟨⟨i,hc,hi⟩,Or.inl (atPoint j _ _ h1 hj)⟩
      · exact Or.inl ⟨⟨i,hc,hi⟩,Or.inr (Or.inl (atPoint j _ _ h3 hj))⟩
      · exact Or.inl ⟨⟨i,hc,hi⟩,Or.inr (Or.inr (atPoint j _ _ h4 hj))⟩
      · exact Or.inr ⟨atPoint i _ _ h1 hi,Or.inl (atPoint j _ _ h2 hj)⟩
      · exact Or.inr ⟨atPoint i _ _ h1 hi,Or.inr (atPoint j _ _ h4 hj)⟩
    · rintro (⟨⟨i,hc,hi⟩,h1|h3|h4⟩|⟨hi,h2|h4⟩)
      · exact ⟨i,p 1 _,Or.inl ⟨hc,Or.inl rfl⟩,hi,h1⟩
      · exact ⟨i,p 3 _,Or.inl ⟨hc,Or.inr (Or.inl rfl)⟩,hi,h3⟩
      · exact ⟨i,p 4 _,Or.inl ⟨hc,Or.inr (Or.inr rfl)⟩,hi,h4⟩
      · exact ⟨p 1 _,p 2 _,Or.inr ⟨rfl,Or.inl rfl⟩,hi,h2⟩
      · exact ⟨p 1 _,p 4 _,Or.inr ⟨rfl,Or.inr rfl⟩,hi,h4⟩
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun, Finset.notMem_empty, false_and, exists_const, decide_false,
    Bool.false_or, decide_eq_true_eq, oriented, edges, bullValue, bullCopies,
    Bool.and_eq_true, Bool.or_eq_true, p]
  exact bullDistribution _ _ _ _ _

private lemma bull_hasEdge (t : ℕ) : ∃ i j, (bullGraph t).Adj i j :=
  ⟨⟨0,by omega⟩,⟨1,by omega⟩,Or.inl (Or.inl ⟨Or.inl rfl,Or.inl rfl⟩)⟩

private def bullEL (t : ℕ) (k : Fin (t+1)) : Fin (5+t) :=
  ⟨if k.val = 0 then 0 else 4+k.val, by split <;> omega⟩

private def bullEC (t : ℕ) (c : Fin 3) : Fin (5+t) :=
  ⟨if c.val = 0 then 1 else if c.val = 1 then 3 else 4, by split_ifs <;> omega⟩

private def bullET (t : ℕ) (c : Fin 2) : Fin (5+t) :=
  ⟨if c.val = 0 then 2 else 4, by split <;> omega⟩

private def bullEnds (t : ℕ) : (Fin (t+1) × Fin 3 ⊕ Fin 2) → Fin (5+t) × Fin (5+t)
  | .inl (k,c) => (bullEL t k, bullEC t c)
  | .inr c => (⟨1,by omega⟩, bullET t c)

private lemma bullEL_cases (t : ℕ) (k : Fin (t+1)) :
    (bullEL t k).val = 0 ∨ 5 ≤ (bullEL t k).val := by
  unfold bullEL
  split <;> simp_all <;> omega

private lemma bullEL_inj (t : ℕ) : Function.Injective (bullEL t) := by
  intro a b h
  have e := congrArg Fin.val h
  dsimp [bullEL] at e
  apply Fin.ext
  split_ifs at e <;> omega

private lemma bullEnds_dir (t : ℕ) (d : Fin (t+1) × Fin 3 ⊕ Fin 2) :
    bullDir (bullEnds t d).1 (bullEnds t d).2 := by
  rcases d with ⟨k,c⟩|c
  · apply Or.inl
    refine ⟨bullEL_cases t k, ?_⟩
    fin_cases c <;> simp [bullEnds, bullEC, bullET]
  · apply Or.inr
    refine ⟨rfl, ?_⟩
    fin_cases c <;> simp [bullEnds, bullEC, bullET]

private lemma bullEnds_inj (t : ℕ) : Function.Injective (bullEnds t) := by
  rintro (⟨i,c⟩|a) (⟨j,d⟩|b) eq
  · have hi : bullEL t i = bullEL t j := congrArg Prod.fst eq
    have hc : bullEC t c = bullEC t d := congrArg Prod.snd eq
    have hij := bullEL_inj t hi
    subst j
    have hcd : c = d := by
      have hv := congrArg Fin.val hc
      fin_cases c <;> fin_cases d <;> simp [bullEC] at hv ⊢
    subst d
    rfl
  · have h : (bullEL t i).val = 1 := congrArg (fun z => z.1.val) eq
    have := bullEL_cases t i
    omega
  · have h : 1 = (bullEL t j).val := congrArg (fun z => z.1.val) eq
    have := bullEL_cases t j
    omega
  · have h : bullET t a = bullET t b := congrArg Prod.snd eq
    have hv := congrArg Fin.val h
    fin_cases a <;> fin_cases b <;> simp [bullET] at hv ⊢

private lemma bullEnds_covers (t : ℕ) (u v : Fin (5+t)) (h : bullDir u v) :
    ∃ d, bullEnds t d = (u,v) := by
  rcases h with ⟨hu,hv⟩|⟨hu,hv⟩
  · have row : ∃ k, bullEL t k = u := by
      rcases hu with h0|hg
      · exact ⟨⟨0,by omega⟩, Fin.ext (by simpa [bullEL] using h0.symm)⟩
      · refine ⟨⟨u.val-4,by have := u.isLt; omega⟩, Fin.ext ?_⟩
        change (if u.val-4 = 0 then 0 else 4+(u.val-4)) = u.val
        split <;> omega
    obtain ⟨k,hk⟩ := row
    obtain ⟨c,hc⟩ : ∃ c, bullEC t c = v := by
      rcases hv with a|b|d
      · exact ⟨0, Fin.ext a.symm⟩
      · exact ⟨1, Fin.ext b.symm⟩
      · exact ⟨2, Fin.ext d.symm⟩
    exact ⟨.inl (k,c), Prod.ext hk hc⟩
  · have hu' : (⟨1,by omega⟩ : Fin (5+t)) = u := Fin.ext hu.symm
    rcases hv with h2|h4
    · exact ⟨.inr 0, Prod.ext hu' (Fin.ext h2.symm)⟩
    · exact ⟨.inr 1, Prod.ext hu' (Fin.ext h4.symm)⟩

private theorem bull_edges_exact (t : ℕ) : (bullGraph t).edgeSet.ncard = 5+3*t := by
  classical
  let f (d : Fin (t+1) × Fin 3 ⊕ Fin 2) : (bullGraph t).edgeSet :=
    ⟨s((bullEnds t d).1,(bullEnds t d).2), Or.inl (bullEnds_dir t d)⟩
  have inj : Function.Injective f := by
    intro a b h
    have e : s((bullEnds t a).1,(bullEnds t a).2) =
        s((bullEnds t b).1,(bullEnds t b).2) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp e with ⟨e1,e2⟩ | ⟨e1,e2⟩
    · exact bullEnds_inj t (Prod.ext e1 e2)
    · have h1 := bullEnds_dir t a
      have h2 := bullEnds_dir t b
      rw [e1,e2] at h1
      unfold bullDir at h1 h2
      omega
  have onto : Function.Surjective f := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      change bullDir u v ∨ bullDir v u at he
      rcases he with h|h
      · obtain ⟨d,hd⟩ := bullEnds_covers t u v h
        exact ⟨d, Subtype.ext (by simp [f,hd])⟩
      · obtain ⟨d,hd⟩ := bullEnds_covers t v u h
        exact ⟨d, Subtype.ext (by simp [f,hd,Sym2.eq_swap])⟩
  have card := Fintype.card_congr (Equiv.ofBijective f ⟨inj,onto⟩)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Set.fintypeCard_eq_ncard] at card
  omega

namespace LastInput

-- The wire representation and its induction are adapted from the checked L_meta_1527.
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma gate_rep {n m : ℕ} (ρ : (Fin n → Bool) → Fin m → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

lemma raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    (W gs x).getD i.val false = x i := by
  induction gs using List.reverseRecOn with
  | nil =>
    change (List.ofFn x).getD i.val false = x i
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]
  | append_singleton old g ih =>
    rw [W_val, if_neg (by have := i.isLt; omega)]
    exact ih

lemma raw_last {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (b : Bool) :
    (W gs (Fin.snoc x b)).getD n false = b :=
  (raw gs (Fin.snoc x b) (Fin.last n)).trans (Fin.snoc_last _ _)

lemma gate_uses_last {n : ℕ} (old new : List Gate) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) (read : n ∈ g.inputs)
    (h : ∀ t, Rep new (fun x : Fin n → Bool => (W old (Fin.snoc x false)).getD t false)) :
    Rep new (fun x : Fin n → Bool => g.op.eval (g.inputs.map fun i => (W old (Fin.snoc x false)).getD i false)) := by
  obtain ⟨op,l⟩ := g
  change l.length = 2 at hlen
  change n ∈ l at read
  change op = GateOp.and ∨ op = GateOp.or at hop
  obtain ⟨u,v,rfl⟩ := List.length_eq_two.mp hlen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at read
  rcases read with rfl | rfl <;> rcases hop with rfl | rfl
  · exact Or.inl ⟨false,fun x => by
      simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,raw_last]; simp⟩
  · exact rep_congr (fun x => by
      simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,raw_last]; simp) (h v)
  · exact Or.inl ⟨false,fun x => by
      simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,raw_last]; simp⟩
  · exact rep_congr (fun x => by
      simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,raw_last]; simp) (h u)

def freed (n : ℕ) (gs : List Gate) : ℕ := gs.countP (fun g => g.inputs.contains n)

lemma freed_pos (n : ℕ) (gs : List Gate) (used : ∃ g ∈ gs, n ∈ g.inputs) : 0 < freed n gs := by
  induction gs with
  | nil => simp at used
  | cons g rest ih =>
    by_cases h : n ∈ g.inputs
    · simp [freed,List.countP_cons,h]
    · have other : ∃ v ∈ rest, n ∈ v.inputs := by
        obtain ⟨v,hv,hr⟩ := used
        rcases List.mem_cons.mp hv with rfl | hv
        · contradiction
        · exact ⟨v,hv,hr⟩
      simpa [freed,List.countP_cons,h] using ih other

def LastInv (n : ℕ) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length + freed n old ≤ old.length ∧
    ∀ t, Rep new (fun x : Fin n → Bool => (W old (Fin.snoc x false)).getD t false)

lemma last_step (n : ℕ) (old : List Gate) (g : Gate) (fan : Fan g)
    (previous : LastInv n old) : LastInv n (old ++ [g]) := by
  obtain ⟨new,legal,back,budget,h⟩ := previous
  have one : ∃ new', Ext n new new' ∧ new'.length + freed n (old ++ [g]) ≤ (old ++ [g]).length ∧
      Rep new' (fun x : Fin n → Bool => g.op.eval (g.inputs.map fun i => (W old (Fin.snoc x false)).getD i false)) := by
    by_cases read : n ∈ g.inputs
    · refine ⟨new,Or.inl rfl,?_,gate_uses_last old new g fan.1 fan.2 read h⟩
      simpa [freed,List.countP_append,read,Nat.add_assoc] using Nat.succ_le_succ budget
    · obtain ⟨new',he,hr⟩ := gate_rep (fun x : Fin n → Bool => Fin.snoc x false) old new g.op g.inputs fan.1 (by rw [fan.2]) h
      refine ⟨new',he,?_,hr⟩
      have grow : new'.length ≤ new.length + 1 := by
        rcases he with rfl | ⟨a,rfl,_,_⟩ <;> simp
      have eq : freed n (old ++ [g]) = freed n old := by simp [freed,List.countP_append,read]
      rw [eq,List.length_append,List.length_singleton]
      omega
  obtain ⟨new',he,hbudget,hrep⟩ := one
  refine ⟨new',?_,?_,hbudget,?_⟩
  · rcases he with rfl | ⟨next,rfl,hnext,_⟩
    · exact legal
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact legal g hg
      · rwa [List.mem_singleton.mp hg]
  · rcases he with rfl | ⟨next,rfl,_,hb⟩
    · exact back
    · exact rb_snoc back hb
  · intro i
    by_cases ht : i = n+1+old.length
    · exact rep_congr (fun x => by rw [W_val,if_pos ht]) hrep
    · exact rep_congr (fun x => by rw [W_val,if_neg ht]) (rep_mono he _ (h i))

lemma last_empty (n : ℕ) : LastInv n [] := by
  refine ⟨[],by simp,(by intro j hj; simp at hj),by simp [freed],?_⟩
  intro j
  by_cases hj : j<n
  · refine Or.inr ⟨j,by simpa using hj,?_⟩
    intro x
    have h1 := raw ([] : List Gate) x ⟨j,hj⟩
    have h2 := raw ([] : List Gate) (Fin.snoc x false) (Fin.castSucc ⟨j,hj⟩)
    exact h1.trans (h2.trans (Fin.snoc_castSucc _ _ _)).symm
  · refine Or.inl ⟨false,fun x => ?_⟩
    by_cases he : j=n
    · subst j; exact raw_last [] x false
    · exact List.getD_eq_default _ _ (by rw [W_len,List.length_nil]; omega)

lemma last_inv (n : ℕ) (gs : List Gate) (ok : ∀ g ∈ gs, Fan g) : LastInv n gs := by
  induction gs using List.reverseRecOn with
  | nil => exact last_empty n
  | append_singleton old g ih =>
    exact last_step n old g (ok g (by simp)) (ih (fun v hv => ok v (by simp [hv])))

lemma no_reader {n : ℕ} (gs : List Gate) (none : ∀ g ∈ gs, n ∉ g.inputs) (x : Fin n → Bool) :
    ∀ i, i ≠ n → (W gs (Fin.snoc x false)).getD i false = (W gs (Fin.snoc x true)).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    by_cases valid : i<n
    · have h1 := raw ([] : List Gate) (Fin.snoc x false) (Fin.castSucc ⟨i,valid⟩)
      have h2 := raw ([] : List Gate) (Fin.snoc x true) (Fin.castSucc ⟨i,valid⟩)
      exact (h1.trans (Fin.snoc_castSucc _ _ _)).trans (h2.trans (Fin.snoc_castSucc _ _ _)).symm
    · rw [List.getD_eq_default _ _ (by rw [W_len,List.length_nil]; omega),
        List.getD_eq_default _ _ (by rw [W_len,List.length_nil]; omega)]
  | append_singleton old g ih =>
    have hp := ih (fun v hv => none v (by simp [hv]))
    intro i hi
    rw [W_val,W_val]
    split_ifs
    · congr 1
      exact List.map_congr_left (fun t ht => hp t (fun h => none g (by simp) (h ▸ ht)))
    · exact hp _ hi

end LastInput

open PEqualNP.CircuitLowerBounds in
theorem restrictLastFalse {n : ℕ} (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 (n+1) C)
    (depends : ∃ y : Fin n → Bool, C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y true)))
    (nonconst : ∃ y z : Fin n → Bool, C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc z false))) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size + 1 ≤ C.size ∧
      ∀ y : Fin n → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  classical
  obtain ⟨x,hx⟩ := depends
  obtain ⟨y,z,hyz⟩ := nonconst
  have out : C.output ≠ n := by
    intro eq
    apply hyz
    change (LastInput.W C.gates (Fin.snoc y false)).getD C.output false = (LastInput.W C.gates (Fin.snoc z false)).getD C.output false
    rw [eq,LastInput.raw_last,LastInput.raw_last]
  have used : ∃ g ∈ C.gates, n ∈ g.inputs := by
    by_contra! no
    exact hx (LastInput.no_reader C.gates no x C.output out)
  have saved : 0 < LastInput.freed n C.gates := by
    exact LastInput.freed_pos n C.gates used
  obtain ⟨new,fan,back,bound,h⟩ := LastInput.last_inv n C.gates
    (fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩)
  rcases h C.output with ⟨c,hc⟩ | ⟨j,_,rep⟩
  · exact (hyz ((hc y).trans (hc z).symm)).elim
  · exact ⟨⟨new,j⟩,⟨fun g hg => (fan g hg).1,back,fun g hg => (fan g hg).2⟩,
      (show new.length+1 ≤ C.gates.length by omega),rep⟩

namespace TriangleBase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

private abbrev Word := BitVec 8

-- Each column records the value of one wire on all eight input assignments.
private def cols : List Word := [170, 204, 240]

private def gate (a b r : Word) : Prop := r = a &&& b ∨ r = a ||| b

private def reach : ℕ → List Word → Prop
  | 0, ws => (232 : Word) ∈ 0 :: ws
  | k+1, ws => ∃ a ∈ 0 :: ws, ∃ b ∈ 0 :: ws, ∃ r, gate a b r ∧ reach k (ws ++ [r])

-- A state S is safe for k gates if no list of wires with values in S
-- can reach the majority column in k further gates.
private def safe (k : ℕ) (s : List Word) : Prop :=
  ∀ ws : List Word, (∀ v ∈ 0 :: ws, v ∈ s) → ¬reach k ws

private def allowed (s : List Word) (ns : List (List Word)) : List Word :=
  (ns.filter (fun q => s.all q.contains)).flatten

private def tests (s : List Word) (u : List Word) : Bool :=
  s.all (fun a => s.all (fun b => u.contains (a &&& b) && u.contains (a ||| b)))

private theorem next_safe {k : ℕ} {s u : List Word} {ns : List (List Word)}
    (certified : ∀ q ∈ ns, safe k q) (hu : allowed s ns = u) (test : tests s u = true) : safe (k+1) s := by
  intro ws hws hit
  obtain ⟨a,ha,b,hb,r,hr,hnext⟩ := hit
  have checks := List.all_eq_true.mp (List.all_eq_true.mp test a (hws _ ha)) b (hws _ hb)
  have hrmem : r ∈ u := by
    have both : u.contains (a &&& b) = true ∧ u.contains (a ||| b) = true := by simpa using checks
    rcases hr with rfl | rfl
    · exact List.contains_iff_mem.mp both.1
    · exact List.contains_iff_mem.mp both.2
  rw [← hu] at hrmem
  obtain ⟨q,hq,hqr⟩ := List.mem_flatten.mp hrmem
  obtain ⟨hqns,hsq⟩ := List.mem_filter.mp hq
  apply certified q hqns _ _ hnext
  intro z hz
  have oldOrNew : z ∈ 0 :: ws ∨ z = r := by
    simpa [List.mem_cons,List.mem_append,or_assoc] using hz
  rcases oldOrNew with old | rfl
  · exact List.contains_iff_mem.mp (List.all_eq_true.mp hsq _ (hws _ old))
  · exact hqr

private theorem zero_safe (s : List Word) (h : (232 : Word) ∉ s) : safe 0 s :=
  fun _ hs ht => h (hs _ ht)

private def sets0 : List (List Word) := [[0,128,136,160,168,170,192,200,204,224,234,236,238,240,248,250,252,254]]
private theorem node0_0 : safe 0 [0,128,136,160,168,170,192,200,204,224,234,236,238,240,248,250,252,254] :=
  zero_safe _ (by decide)
private theorem level0 : ∀ s ∈ sets0, safe 0 s := by
  intro s hs
  simp only [sets0,List.mem_cons,List.not_mem_nil,or_false] at hs
  subst s; exact node0_0
private def sets1 : List (List Word) := [[0,128,136,160,170,192,204,238,240,250,252,254], [0,128,136,160,168,170,204,236,238,240,252,254], [0,128,136,170,192,200,204,234,238,240,250,254], [0,128,136,160,168,170,204,240,248,250,252,254], [0,128,160,170,192,204,224,234,238,240,250,254]]
private theorem node1_0 : safe 1 [0,128,136,160,170,192,204,238,240,250,252,254] :=
  next_safe (u := [0,128,136,160,168,170,192,200,204,224,234,236,238,240,248,250,252,254]) level0 (by decide +kernel) (by decide +kernel)
private theorem node1_1 : safe 1 [0,128,136,160,168,170,204,236,238,240,252,254] :=
  next_safe (u := [0,128,136,160,168,170,192,200,204,224,234,236,238,240,248,250,252,254]) level0 (by decide +kernel) (by decide +kernel)
private theorem node1_2 : safe 1 [0,128,136,170,192,200,204,234,238,240,250,254] :=
  next_safe (u := [0,128,136,160,168,170,192,200,204,224,234,236,238,240,248,250,252,254]) level0 (by decide +kernel) (by decide +kernel)
private theorem node1_3 : safe 1 [0,128,136,160,168,170,204,240,248,250,252,254] :=
  next_safe (u := [0,128,136,160,168,170,192,200,204,224,234,236,238,240,248,250,252,254]) level0 (by decide +kernel) (by decide +kernel)
private theorem node1_4 : safe 1 [0,128,160,170,192,204,224,234,238,240,250,254] :=
  next_safe (u := [0,128,136,160,168,170,192,200,204,224,234,236,238,240,248,250,252,254]) level0 (by decide +kernel) (by decide +kernel)
private theorem level1 : ∀ s ∈ sets1, safe 1 s := by
  intro s hs
  simp only [sets1,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact node1_0
  · exact node1_1
  · exact node1_2
  · exact node1_3
  · exact node1_4
private def sets2 : List (List Word) := [[0,128,136,160,170,204,240,252,254], [0,128,170,192,204,238,240,250,254]]
private theorem node2_0 : safe 2 [0,128,136,160,170,204,240,252,254] :=
  next_safe (u := [0,128,136,160,170,192,204,238,240,250,252,254,0,128,136,160,168,170,204,236,238,240,252,254,0,128,136,160,168,170,204,240,248,250,252,254]) level1 (by decide +kernel) (by decide +kernel)
private theorem node2_1 : safe 2 [0,128,170,192,204,238,240,250,254] :=
  next_safe (u := [0,128,136,160,170,192,204,238,240,250,252,254,0,128,136,170,192,200,204,234,238,240,250,254,0,128,160,170,192,204,224,234,238,240,250,254]) level1 (by decide +kernel) (by decide +kernel)
private theorem level2 : ∀ s ∈ sets2, safe 2 s := by
  intro s hs
  simp only [sets2,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl
  · exact node2_0
  · exact node2_1
private def sets3 : List (List Word) := [[0,170,204,240]]
private theorem node3_0 : safe 3 [0,170,204,240] :=
  next_safe (u := [0,128,136,160,170,204,240,252,254,0,128,170,192,204,238,240,250,254]) level2 (by decide +kernel) (by decide +kernel)
private theorem level3 : ∀ s ∈ sets3, safe 3 s := by
  intro s hs
  simp only [sets3,List.mem_cons,List.not_mem_nil,or_false] at hs
  subst s; exact node3_0
private theorem cert : ¬reach 3 cols := node3_0 cols (by decide)

private def step (w : List Word) (g : Gate) : List Word :=
  let a := w.getD (g.inputs.getD 0 0) 0
  let b := w.getD (g.inputs.getD 1 0) 0
  w ++ [match g.op with | .and => a &&& b | _ => a ||| b]

private def bit (k : Fin 8) (w : Word) := w.getLsbD k.val

private theorem read (ws : List Word) (k : Fin 8) (i : ℕ) :
    (ws.map (bit k)).getD i false = bit k (ws.getD i 0) := by
  induction ws generalizing i with
  | nil => simp [bit, List.getD]
  | cons w ws ih => cases i <;> simp_all [List.getD]

private def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

private theorem step_bits (ws : List Word) (g : Gate) (ok : legal g) (k : Fin 8) :
    (step ws g).map (bit k) =
      ws.map (bit k) ++ [g.op.eval (g.inputs.map fun i => (ws.map (bit k)).getD i false)] := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hn⟩ := ok
  change ins.length = 2 at hn
  obtain ⟨a, b, rfl⟩ : ∃ a b, ins = [a,b] := by
    cases ins with
    | nil => simp at hn
    | cons a tail =>
      cases tail with
      | nil => simp at hn
      | cons b tail =>
        have h : tail = [] := by apply List.length_eq_zero_iff.mp; simp_all
        exact ⟨a, b, by simp [h]⟩
  change op = .and ∨ op = .or at hop
  rcases hop with rfl | rfl <;>
    simp [step, GateOp.eval, bit, List.getD] <;>
    cases ws[a]? <;> cases ws[b]? <;> simp [bit]

private theorem fold_bits (ws : List Word) (gs : List Gate) (ok : ∀ g ∈ gs, legal g)
    (k : Fin 8) :
    (gs.foldl step ws).map (bit k) =
      gs.foldl (fun bs g => bs ++ [g.op.eval (g.inputs.map fun i => bs.getD i false)]) (ws.map (bit k)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun z hz => ok z (by simp [hz])),
      step_bits ws g (ok g (by simp))]

private theorem getMem (ws : List Word) (i : ℕ) : ws.getD i 0 ∈ 0 :: ws := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact List.mem_cons_of_mem _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

private theorem pad (k : ℕ) (ws : List Word) (hit : (232 : Word) ∈ 0 :: ws) :
    reach k ws := by
  induction k generalizing ws with
  | zero => exact hit
  | succ k ih =>
    refine ⟨0, by simp, 0, by simp, 0, Or.inl (by decide), ih _ ?_⟩
    simpa using hit

private theorem fold_reach (k : ℕ) (gs : List Gate) (ws : List Word)
    (hk : gs.length ≤ k) (out : ℕ) (hit : (gs.foldl step ws).getD out 0 = 232) :
    reach k ws := by
  induction k generalizing ws gs with
  | zero =>
    have hn : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    change (232 : Word) ∈ 0 :: ws
    rw [← hit]
    apply getMem
  | succ k ih =>
    cases gs with
    | nil =>
      apply pad
      rw [← hit]
      apply getMem
    | cons g gs =>
      let a := ws.getD (g.inputs.getD 0 0) 0
      let b := ws.getD (g.inputs.getD 1 0) 0
      let r := match g.op with | .and => a &&& b | _ => a ||| b
      refine ⟨a, getMem _ _, b, getMem _ _, r, ?_, ih gs (ws ++ [r]) (by simpa using hk) hit⟩
      cases h : g.op <;> simp [r, h, gate]

theorem triangle_lower (C : Circuit) (hm : IsAO2 3 C)
    (hc : ∀ x : Fin 3 → Bool, circuitFun 3 C x =
      ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2))) : 4 ≤ C.size := by
  by_contra! small
  have ok : ∀ g ∈ C.gates, legal g := fun g h => ⟨hm.1 _ h, hm.2.2 _ h⟩
  apply cert
  apply fold_reach 3 C.gates cols (by change C.gates.length < 4 at small; omega) C.output
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let row : Fin 3 → Bool := fun i => bit ⟨k, hk⟩ (cols.getD i 0)
  have hrows : List.ofFn row = cols.map (bit ⟨k, hk⟩) := by
    rfl
  have hval := hc row
  change (C.wires (List.ofFn row)).getD C.output false = _ at hval
  rw [hrows] at hval
  unfold Circuit.wires at hval
  rw [← fold_bits _ _ ok, read] at hval
  change bit ⟨k, hk⟩ _ = _
  rw [hval]
  have htable : ∀ q : Fin 8,
      let x : Fin 3 → Bool := fun i => bit q (cols.getD i 0)
      ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) =
        (232 : Word).getLsbD q := by decide
  exact htable ⟨k, hk⟩

-- Rewire only the primary inputs. The numbers of gate wires do not change.
private def rewire {n : ℕ} (p : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then (p ⟨i,h⟩).val else i

private def rewireGate {n : ℕ} (p : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (rewire p)⟩

private def rewireCircuit {n : ℕ} (p : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rewireGate p),rewire p C.output⟩

private theorem rewire_ao {n : ℕ} (p : Fin n → Fin n) (C : Circuit) (hao : IsAO2 n C) :
    IsAO2 n (rewireCircuit p C) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    exact hao.1 v hv
  · intro j hj i hi
    have ht : j < C.gates.length := by simpa [rewireCircuit] using hj
    change i ∈ (((C.gates.map (rewireGate p)).getD j ⟨GateOp.or,[]⟩).inputs) at hi
    rw [List.getD_eq_getElem _ _ (by simpa using ht),List.getElem_map] at hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    have hh := hao.2.1 j ht a
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hh
    rw [List.getD_eq_getElem _ _ ht] at hh
    unfold rewire
    split
    · have := (p ⟨a,by assumption⟩).isLt; omega
    · exact hh ha
  · intro g hg
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    simpa [rewireGate] using hao.2.2 v hv

private theorem rewire_val {n : ℕ} (p : Fin n → Fin n) (gs : List Gate) (x : Fin n → Bool) :
    ∀ i, (LastInput.W (gs.map (rewireGate p)) x).getD (rewire p i) false =
      (LastInput.W gs (x ∘ p)).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    by_cases h : i < n
    · exact (LastInput.raw [] x (p ⟨i,h⟩)).trans (LastInput.raw [] (x ∘ p) ⟨i,h⟩).symm
        |> fun he => by simpa [rewire,h] using he
    · rw [show rewire p i = i by simp [rewire,h]]
      rw [List.getD_eq_default _ _ (by rw [LastInput.W_len]; simp_all),
        List.getD_eq_default _ _ (by rw [LastInput.W_len]; simp_all)]
  | append_singleton old g ih =>
    intro i
    simp only [List.map_append,List.map_cons,List.map_nil,LastInput.W_val,List.length_map]
    have pos : rewire p i = n + old.length ↔ i = n + old.length := by
      unfold rewire
      split
      · rename_i h
        have := (p ⟨i,h⟩).isLt; omega
      · rfl
    simp only [pos]
    split
    · change g.op.eval ((g.inputs.map (rewire p)).map _) = g.op.eval (g.inputs.map _)
      congr 1
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => ih i)
    · apply ih

private theorem removeLast {n : ℕ} (C : Circuit) (hao : IsAO2 (n+1) C) (f : (Fin (n+1) → Bool) → Bool)
    (hc : ∀ x, circuitFun (n+1) C x = f x)
    (dep : ∃ y : Fin n → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y true))
    (nc : ∃ y z : Fin n → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc z false)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size+1 ≤ C.size ∧
      ∀ y, circuitFun n D y = f (Fin.snoc y false) := by
  obtain ⟨a,ha⟩ := dep
  obtain ⟨b,c,hbc⟩ := nc
  have hv (x : Fin (n+1) → Bool) : C.eval (List.ofFn x) = f x := hc x
  obtain ⟨D,hD,hsize,hfun⟩ := restrictLastFalse C hao
    ⟨a,by simpa only [hv] using ha⟩ ⟨b,c,by simpa only [hv] using hbc⟩
  exact ⟨D,hD,hsize,fun y => (hfun y).trans (hc _)⟩

-- After moving vertex 4 to position 2, vertices 3 and 4 are pendant.
-- Fixing them to false leaves the triangle on the first three vertices.
private def swap24 : Fin 5 → Fin 5 := ![0,1,4,3,2]

private def onFive (x : Fin 5 → Bool) :=
  (x 0 || x 1) && (x 2 || ((x 0 || x 4) && (x 1 || x 3)))

private def onFour (x : Fin 4 → Bool) := onFive (Fin.snoc x false)
private def onThree (x : Fin 3 → Bool) := onFour (Fin.snoc x false)

end TriangleBase

open TriangleBase PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm in
theorem bull_lower (C : Circuit) (hao : IsAO2 5 C)
    (hc : ∀ x : Fin 5 → Bool, circuitFun 5 C x =
      ((x 0 || x 1) && (x 4 || ((x 0 || x 2) && (x 1 || x 3))))) : 6 ≤ C.size := by
  let R := rewireCircuit swap24 C
  have hv (x : Fin 5 → Bool) : circuitFun 5 R x = onFive x := by
    exact (rewire_val swap24 C.gates x C.output).trans (hc (x ∘ swap24))
  obtain ⟨D4,ok4,len4,four⟩ := removeLast R (rewire_ao swap24 C hao) onFive hv
    ⟨fun i => decide (i.val = 1),by decide⟩
    ⟨fun _ => false,fun _ => true,by decide⟩
  obtain ⟨D3,ok3,len3,three⟩ := removeLast D4 ok4 onFour four
    ⟨fun i => decide (i.val = 0),by decide⟩
    ⟨fun _ => false,fun _ => true,by decide⟩
  have table : ∀ x : Fin 3 → Bool, onThree x = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) := by decide
  have low := triangle_lower D3 ok3 (fun x => (three x).trans (table x))
  have same : R.size = C.size := by simp [R,rewireCircuit,Circuit.size]
  omega

private lemma copies_snoc (t : ℕ) (x : Fin (5+t) → Bool) (b : Bool) :
    bullCopies (t+1) (Fin.snoc (α := fun _ => Bool) x b) = (bullCopies t x || b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bullCopies,decide_eq_true_eq,Bool.or_eq_true]
  constructor
  · rintro ⟨j,hj,read⟩
    by_cases h : j.val < 5+t
    · let i : Fin (5+t) := ⟨j.val,h⟩
      have eq : j = i.castSucc := Fin.ext rfl
      rw [eq,Fin.snoc_castSucc] at read
      exact Or.inl ⟨i,hj,read⟩
    · have eq : j = Fin.last (5+t) := Fin.ext (by have := j.isLt; change j.val = 5+t; omega)
      rw [eq] at read
      exact Or.inr ((Fin.snoc_last (α := fun _ => Bool) b x).symm.trans read)
  · rintro (⟨i,hi,read⟩ | read)
    · exact ⟨i.castSucc,hi,(Fin.snoc_castSucc (α := fun _ => Bool) b x i).trans read⟩
    · exact ⟨Fin.last (5+t),Or.inr (by change 5 ≤ 5+t; omega),(Fin.snoc_last (α := fun _ => Bool) _ _).trans read⟩

private lemma snoc_at_bull (t j : ℕ) (hj : j < 5+t) (y : Fin (5+t) → Bool) (b : Bool) :
    Fin.snoc (α := fun _ => Bool) y b (⟨j,by omega⟩ : Fin (5+(t+1))) = y ⟨j,hj⟩ :=
  Fin.snoc_castSucc (α := fun _ => Bool) b y (⟨j,hj⟩ : Fin (5+t))

private lemma bull_snoc_zero (t : ℕ) (y : Fin (5+t) → Bool) :
    bullValue (t+1) (Fin.snoc (α := fun _ => Bool) y false) = bullValue t y := by
  simp only [bullValue,copies_snoc,Bool.or_false,snoc_at_bull t 1 (by omega),snoc_at_bull t 2 (by omega),
    snoc_at_bull t 3 (by omega),snoc_at_bull t 4 (by omega)]

private lemma bull_snoc_test (t : ℕ) (b : Bool) :
    bullValue (t+1) (Fin.snoc (α := fun _ => Bool) (fun i : Fin (5+t) => decide (i.val = 4)) b) = b := by
  let y := fun i : Fin (5+t) => decide (i.val = 4)
  change bullValue (t+1) (Fin.snoc (α := fun _ => Bool) y b) = b
  have off : bullCopies t y = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨i,hi,hit⟩ := of_decide_eq_true h
    have := (of_decide_eq_true hit : i.val = 4)
    omega
  simp only [bullValue,copies_snoc,off,Bool.false_or,snoc_at_bull t 1 (by omega),snoc_at_bull t 2 (by omega),
    snoc_at_bull t 3 (by omega),snoc_at_bull t 4 (by omega)]
  simp [y]

private lemma copies_base (x : Fin 5 → Bool) : bullCopies 0 x = x 0 := by
  apply Bool.eq_iff_iff.mpr
  change (decide (∃ i : Fin 5, (i.val = 0 ∨ 5 ≤ i.val) ∧ x i = true) = true) ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,hit⟩
    have ez : i = 0 := Fin.ext (by have := i.isLt; change i.val = 0; omega)
    simpa [ez] using hit
  · exact fun hit => ⟨0,Or.inl rfl,hit⟩

theorem bull_minimum (t : ℕ) (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 (5+t) C)
    (hc : circuitFun (5+t) C = bullValue t) : t+6 ≤ C.size := by
  induction t generalizing C with
  | zero =>
    apply bull_lower C hao
    intro x
    rw [show circuitFun 5 C x = bullValue 0 x from congrFun hc x]
    rw [bullValue,copies_base]
    rfl
  | succ t ih =>
    have val (x : Fin (5+(t+1)) → Bool) : C.eval (List.ofFn x) = bullValue (t+1) x := congrFun hc x
    have depends : ∃ y : Fin (5+t) → Bool, C.eval (List.ofFn (Fin.snoc (α := fun _ => Bool) y false)) ≠ C.eval (List.ofFn (Fin.snoc (α := fun _ => Bool) y true)) := by
      refine ⟨fun i => decide (i.val=4),?_⟩
      rw [val,val,bull_snoc_test,bull_snoc_test]
      decide
    have nonconst : ∃ y z : Fin (5+t) → Bool, C.eval (List.ofFn (Fin.snoc (α := fun _ => Bool) y false)) ≠ C.eval (List.ofFn (Fin.snoc (α := fun _ => Bool) z false)) := by
      refine ⟨fun _ => false,fun _ => true,?_⟩
      rw [val,val,bull_snoc_zero,bull_snoc_zero]
      simp [bullValue,bullCopies]
    obtain ⟨D,ok,save,same⟩ := restrictLastFalse C hao depends nonconst
    have eq : circuitFun (5+t) D = bullValue t := by
      funext y
      exact (same y).trans ((val _).trans (bull_snoc_zero t y))
    have low := ih D ok eq
    omega

private theorem bull_least (t : ℕ) [DecidableRel (bullGraph t).Adj] :
    TopForm.IsLeastAO (bullGraph t) (bullCircuit t) := by
  have hg := bull_graphFun t
  refine ⟨bull_ao t,(bull_sem t).trans hg.symm,?_⟩
  intro D hd hf
  rw [bull_size]
  exact bull_minimum t D hd (hf.trans hg)

-- The quantitative family is also available independently of the contradiction.
theorem bull_family (t : ℕ) [DecidableRel (bullGraph t).Adj] :
    (bullGraph t).edgeSet.ncard = 5+3*t ∧ (bullCircuit t).size = t+6 ∧
    TopForm.IsLeastAO (bullGraph t) (bullCircuit t) ∧
    TopForm.TopForm (bullGraph t) (bullCircuit t) ∧
    (TopForm.junk (bullGraph t) (bullCircuit t)).Nonempty := by
  exact ⟨bull_edges_exact t, bull_size t, bull_least t,
    bull_top_junk t _ (bull_graphFun t)⟩

end PEqualNP.Outside.L_meta_11094

-- Cloning one vertex gives a family whose edge surplus grows linearly.
theorem PEqualNP.Outside.L_meta_11094 : ¬ (
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj]
      (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ (x6 : Fin x2) (x7 : Fin x2), x3.Adj x6 x7) →
      PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 →
      (PEqualNP.TopForm.junk x3 x5).Nonempty →
      x3.edgeSet.ncard + x3.edgeSet.ncard ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt) := by
  classical
  rintro ⟨k,h⟩
  let t := (k+2)^2
  obtain ⟨he,hsz,hl,ht,hj⟩ := PEqualNP.Outside.L_meta_11094.bull_family t
  have bound := h _ _ _ (PEqualNP.Outside.L_meta_11094.bull_hasEdge t)
    hl ht hj
  rw [hsz,he] at bound
  have hs : Nat.sqrt (5+t+1) ≤ k+4 := by
    calc
      _ ≤ Nat.sqrt ((k+4)^2) := Nat.sqrt_le_sqrt (by dsimp [t]; nlinarith)
      _ = _ := by simp
  have hm := Nat.mul_le_mul_left k hs
  have hn : 2*(5+3*t) ≤ t+7+k*(k+4) := by omega
  dsimp [t] at hn
  nlinarith
