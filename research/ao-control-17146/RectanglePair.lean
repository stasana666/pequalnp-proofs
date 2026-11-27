import Std

namespace PEqualNP.Research.RectanglePair

structure Rectangle (α β : Type) where
  row : α → Bool
  col : β → Bool

def contains (r : Rectangle α β) (u : α) (v : β) : Bool :=
  r.row u && r.col v

def paired (r s : Rectangle α β) (u : α) (v : β) : Bool :=
  (r.row u || s.col v) && (s.row u || r.col v)

def Separated (r s : Rectangle α β) : Prop :=
  (∀ u, (r.row u && s.row u) = false) ∧
  (∀ v, (r.col v && s.col v) = false)

theorem pair_correct (r s : Rectangle α β) (h : Separated r s) (u : α) (v : β) :
    paired r s u v = (contains r u v || contains s u v) := by
  have hrow := h.1 u
  have hcol := h.2 v
  unfold paired contains
  cases h₁ : r.row u <;> cases h₂ : s.row u <;>
    cases h₃ : r.col v <;> cases h₄ : s.col v <;>
    simp_all

theorem cover_correct (pairs : List (Rectangle α β × Rectangle α β))
    (h : ∀ p ∈ pairs, Separated p.1 p.2) (u : α) (v : β) :
    pairs.any (fun p => paired p.1 p.2 u v) =
    pairs.any (fun p => contains p.1 u v || contains p.2 u v) := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    have hp : Separated p.1 p.2 := h p (by simp)
    have hps : ∀ q ∈ ps, Separated q.1 q.2 := by
      intro q hq
      exact h q (by simp [hq])
    simp only [List.any_cons, pair_correct p.1 p.2 hp u v, ih hps]

end PEqualNP.Research.RectanglePair
