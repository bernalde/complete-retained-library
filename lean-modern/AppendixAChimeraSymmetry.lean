module

public import AppendixAChimeraFourData

@[expose] public section

/-!
Pure symmetries of the complete four-cell hardware.  This module contains no
sample, quotient, branch assignment, cap conclusion, or generator assertion.
The two Boolean coordinates identify a cell; a transposition also swaps its
A/B shore, while preserving the index in Fin 4.
-/

noncomputable section

namespace AppendixAChimeraSymmetry

open AppendixAChimera AppendixAChimeraFour

abbrev Position := Bool × Bool

def cellPoint (p : Position) (x : Cell) : Phys4 :=
  (p.1, if p.2 then second x else first x)

def coordinates : (Position × Cell) ≃ Phys4 where
  toFun z := cellPoint z.1 z.2
  invFun u := match u.2 with
    | .inl x => ((u.1, false), x)
    | .inr x => ((u.1, true), x)
  left_inv := by
    rintro ⟨⟨r, c⟩, x⟩
    cases c <;> rfl
  right_inv := by
    rintro ⟨r, p⟩
    cases p <;> rfl

def swapShore (x : Cell) : Cell := (!x.1, x.2)

def shoreAction (b : Bool) (x : Cell) : Cell :=
  if b then swapShore x else x

@[simp] theorem shoreAction_pair (b s : Bool) (i : Fin 4) :
    shoreAction b (s, i) = (if b then !s else s, i) := by
  cases b <;> rfl

@[simp] theorem shoreAction_index (b : Bool) (x : Cell) :
    (shoreAction b x).2 = x.2 := by
  cases b <;> rfl

theorem shoreAction_comp (a b : Bool) (x : Cell) :
    shoreAction b (shoreAction a x) = shoreAction (Bool.xor a b) x := by
  rcases x with ⟨s, i⟩
  cases a <;> cases b <;> cases s <;> rfl

def shoreEquiv (b : Bool) : Cell ≃ Cell where
  toFun := shoreAction b
  invFun := shoreAction b
  left_inv := by
    rintro ⟨s, i⟩
    cases b <;> cases s <;> rfl
  right_inv := by
    rintro ⟨s, i⟩
    cases b <;> cases s <;> rfl

def lift (e : Position ≃ Position) (b : Bool) : Phys4 ≃ Phys4 :=
  coordinates.symm.trans ((Equiv.prodCongr e (shoreEquiv b)).trans coordinates)

@[simp] theorem lift_cellPoint (e : Position ≃ Position) (b : Bool)
    (p : Position) (x : Cell) :
    lift e b (cellPoint p x) = cellPoint (e p) (shoreAction b x) := by
  rcases p with ⟨r, c⟩
  cases c <;> rfl

def rowPosition : Position ≃ Position where
  toFun p := (!p.1, p.2)
  invFun p := (!p.1, p.2)
  left_inv := by rintro ⟨r, c⟩; cases r <;> rfl
  right_inv := by rintro ⟨r, c⟩; cases r <;> rfl

def columnPosition : Position ≃ Position where
  toFun p := (p.1, !p.2)
  invFun p := (p.1, !p.2)
  left_inv := by rintro ⟨r, c⟩; cases c <;> rfl
  right_inv := by rintro ⟨r, c⟩; cases c <;> rfl

def transposePosition : Position ≃ Position where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv := by rintro ⟨r, c⟩; rfl
  right_inv := by rintro ⟨r, c⟩; rfl

def rowFlip : Phys4 ≃ Phys4 := lift rowPosition false
def columnFlip : Phys4 ≃ Phys4 := lift columnPosition false
def transpose : Phys4 ≃ Phys4 := lift transposePosition true

@[simp] theorem rowFlip_cellPoint (p : Position) (x : Cell) :
    rowFlip (cellPoint p x) = cellPoint (!p.1, p.2) x :=
  lift_cellPoint rowPosition false p x

@[simp] theorem columnFlip_cellPoint (p : Position) (x : Cell) :
    columnFlip (cellPoint p x) = cellPoint (p.1, !p.2) x :=
  lift_cellPoint columnPosition false p x

@[simp] theorem transpose_cellPoint (p : Position) (x : Cell) :
    transpose (cellPoint p x) = cellPoint (p.2, p.1) (swapShore x) :=
  lift_cellPoint transposePosition true p x

theorem rowFlip_hardware (u v : Phys4) :
    Hardware4 (rowFlip u) (rowFlip v) ↔ Hardware4 u v := by
  obtain ⟨⟨p, x⟩, rfl⟩ := coordinates.surjective u
  obtain ⟨⟨q, y⟩, rfl⟩ := coordinates.surjective v
  change Hardware4 (rowFlip (cellPoint p x)) (rowFlip (cellPoint q y)) ↔
    Hardware4 (cellPoint p x) (cellPoint q y)
  rw [rowFlip_cellPoint, rowFlip_cellPoint]
  rcases p with ⟨r, c⟩
  rcases q with ⟨r', c'⟩
  cases r <;> cases c <;> cases r' <;> cases c' <;>
    simp [cellPoint, Hardware4, Hardware, OnA]

theorem columnFlip_hardware (u v : Phys4) :
    Hardware4 (columnFlip u) (columnFlip v) ↔ Hardware4 u v := by
  obtain ⟨⟨p, x⟩, rfl⟩ := coordinates.surjective u
  obtain ⟨⟨q, y⟩, rfl⟩ := coordinates.surjective v
  change Hardware4 (columnFlip (cellPoint p x)) (columnFlip (cellPoint q y)) ↔
    Hardware4 (cellPoint p x) (cellPoint q y)
  rw [columnFlip_cellPoint, columnFlip_cellPoint]
  rcases p with ⟨r, c⟩
  rcases q with ⟨r', c'⟩
  rcases x with ⟨s, i⟩
  rcases y with ⟨s', i'⟩
  cases r <;> cases c <;> cases r' <;> cases c' <;>
    cases s <;> cases s' <;>
    simp [cellPoint, Hardware4, Hardware, OnA, eq_comm]

theorem transpose_hardware (u v : Phys4) :
    Hardware4 (transpose u) (transpose v) ↔ Hardware4 u v := by
  obtain ⟨⟨p, x⟩, rfl⟩ := coordinates.surjective u
  obtain ⟨⟨q, y⟩, rfl⟩ := coordinates.surjective v
  change Hardware4 (transpose (cellPoint p x)) (transpose (cellPoint q y)) ↔
    Hardware4 (cellPoint p x) (cellPoint q y)
  rw [transpose_cellPoint, transpose_cellPoint]
  rcases p with ⟨r, c⟩
  rcases q with ⟨r', c'⟩
  rcases x with ⟨s, i⟩
  rcases y with ⟨s', i'⟩
  cases r <;> cases c <;> cases r' <;> cases c' <;>
    cases s <;> cases s' <;>
    simp [cellPoint, swapShore, Hardware4, Hardware, OnA, eq_comm]

/-- A hardware automorphism with a uniform action on local shores and indices. -/
structure Symmetry where
  physical : Phys4 ≃ Phys4
  position : Position ≃ Position
  flip : Bool
  cell_action : ∀ p x, physical (cellPoint p x) =
    cellPoint (position p) (shoreAction flip x)
  hardware : ∀ u v, Hardware4 (physical u) (physical v) ↔ Hardware4 u v

def Symmetry.refl : Symmetry where
  physical := Equiv.refl _
  position := Equiv.refl _
  flip := false
  cell_action := by intros; rfl
  hardware := by intros; rfl

/-- Apply `s` first and `t` second, following `Equiv.trans`. -/
def Symmetry.trans (s t : Symmetry) : Symmetry where
  physical := s.physical.trans t.physical
  position := s.position.trans t.position
  flip := Bool.xor s.flip t.flip
  cell_action := by
    intro p x
    change t.physical (s.physical (cellPoint p x)) =
      cellPoint (t.position (s.position p)) (shoreAction (Bool.xor s.flip t.flip) x)
    rw [s.cell_action, t.cell_action, shoreAction_comp]
  hardware := by
    intro u v
    exact (t.hardware (s.physical u) (s.physical v)).trans (s.hardware u v)

def rowSymmetry : Symmetry where
  physical := rowFlip
  position := rowPosition
  flip := false
  cell_action := lift_cellPoint rowPosition false
  hardware := rowFlip_hardware

def columnSymmetry : Symmetry where
  physical := columnFlip
  position := columnPosition
  flip := false
  cell_action := lift_cellPoint columnPosition false
  hardware := columnFlip_hardware

def transposeSymmetry : Symmetry where
  physical := transpose
  position := transposePosition
  flip := true
  cell_action := lift_cellPoint transposePosition true
  hardware := transpose_hardware

/-- Move `p` to the upper-left cell without changing local shores. -/
def normalizeFirst (p : Position) : Symmetry :=
  (if p.1 then rowSymmetry else Symmetry.refl).trans
    (if p.2 then columnSymmetry else Symmetry.refl)

/-- A horizontal pair is transposed after its first endpoint is normalized. -/
def pairNormalizer (p q : Position) : Symmetry :=
  if p.1 = q.1 then (normalizeFirst p).trans transposeSymmetry
  else normalizeFirst p

theorem pairNormalizer_first (p q : Position) :
    (pairNormalizer p q).position p = (false, false) := by
  rcases p with ⟨r, c⟩
  rcases q with ⟨r', c'⟩
  cases r <;> cases c <;> cases r' <;> cases c' <;>
    simp [pairNormalizer, normalizeFirst, Symmetry.trans, Symmetry.refl,
      rowSymmetry, columnSymmetry, transposeSymmetry,
      rowPosition, columnPosition, transposePosition]

theorem pairNormalizer_second (p q : Position) (hne : p ≠ q) :
    (pairNormalizer p q).position q = (true, false) ∨
    (pairNormalizer p q).position q = (true, true) := by
  rcases p with ⟨r, c⟩
  rcases q with ⟨r', c'⟩
  cases r <;> cases c <;> cases r' <;> cases c' <;>
    simp_all [pairNormalizer, normalizeFirst, Symmetry.trans, Symmetry.refl,
      rowSymmetry, columnSymmetry, transposeSymmetry,
      rowPosition, columnPosition, transposePosition]

theorem pairNormalizer_flip (p q : Position) :
    (pairNormalizer p q).flip = decide (p.1 = q.1) := by
  rcases p with ⟨r, c⟩
  rcases q with ⟨r', c'⟩
  cases r <;> cases c <;> cases r' <;> cases c' <;>
    rfl

theorem exists_pair_normalizer (p q : Position) (hne : p ≠ q) :
    ∃ s : Symmetry, s.position p = (false, false) ∧
      (s.position q = (true, false) ∨ s.position q = (true, true)) :=
  ⟨pairNormalizer p q, pairNormalizer_first p q, pairNormalizer_second p q hne⟩

/-- Restore canonical A-to-B order when a symmetry exchanges the shores. -/
def edgeAction (b : Bool) (e : Cell × Cell) : Cell × Cell :=
  if b then (swapShore e.2, swapShore e.1) else e

def edgeEquiv (b : Bool) : (Cell × Cell) ≃ (Cell × Cell) where
  toFun := edgeAction b
  invFun := edgeAction b
  left_inv := by
    rintro ⟨⟨s, i⟩, ⟨t, j⟩⟩
    cases b <;> cases s <;> cases t <;> rfl
  right_inv := by
    rintro ⟨⟨s, i⟩, ⟨t, j⟩⟩
    cases b <;> cases s <;> cases t <;> rfl

theorem edgeAction_canonical (b : Bool) (e : Cell × Cell)
    (h : e.1.1 = false ∧ e.2.1 = true) :
    (edgeAction b e).1.1 = false ∧ (edgeAction b e).2.1 = true := by
  cases b <;> simp [edgeAction, swapShore, h.1, h.2]

/-- The mapped physical edge is unchanged as an unordered pair of endpoints. -/
theorem edgeAction_images (s : Symmetry) (p : Position) (e : Cell × Cell) :
    (s.physical (cellPoint p e.1), s.physical (cellPoint p e.2)) =
      if s.flip then
        (cellPoint (s.position p) (edgeAction s.flip e).2,
          cellPoint (s.position p) (edgeAction s.flip e).1)
      else
        (cellPoint (s.position p) (edgeAction s.flip e).1,
          cellPoint (s.position p) (edgeAction s.flip e).2) := by
  rw [s.cell_action, s.cell_action]
  cases h : s.flip <;> simp [edgeAction, shoreAction, h]

end AppendixAChimeraSymmetry
