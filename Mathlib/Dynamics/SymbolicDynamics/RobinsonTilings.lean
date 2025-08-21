/-
  Robinson.lean
  --------------
  Specialization of Wang tilings to Z² for Robinson’s aperiodic SFT,
  reusing the general machinery from `WangTilings.lean`.
-/

import Mathlib.Dynamics.SymbolicDynamics.WangTilings

open Set
open SymbolicDynamics  -- bring the Wang-API namespaces into scope

namespace SymbolicDynamics
namespace Robinson

/-! # Oriented Robinson colors

We distinguish **horizontal** vs **vertical** edge colors at the type level to make
rotations/reflections type-safe and “obviously correct”.
-/

namespace Colors

inductive HCol | none | line | arrowL | arrowR
deriving DecidableEq, Repr

inductive VCol | none | line | arrowU | arrowD
deriving DecidableEq, Repr

/-- A single edge-color type, tagged by orientation. -/
inductive Col
| H : HCol → Col
| V : VCol → Col
deriving DecidableEq, Repr

/-- `Col` is inhabited (pick anything). -/
instance : Inhabited Col := ⟨Col.H HCol.none⟩

/-- Give `Col` the discrete topology. -/
instance : TopologicalSpace Col := ⊥
instance : DiscreteTopology Col := ⟨rfl⟩

/-- Build a tile from its four oriented edge colors (N,E,S,W). -/
def mkTile (n : VCol) (e : HCol) (s : VCol) (w : HCol) : WangTile Col :=
  fun d =>
    match d with
    | Dir.north => Col.V n
    | Dir.east  => Col.H e
    | Dir.south => Col.V s
    | Dir.west  => Col.H w

@[simp] lemma mkTile_north (n e s w) :
  (mkTile n e s w) Dir.north = Col.V n := rfl
@[simp] lemma mkTile_east (n e s w) :
  (mkTile n e s w) Dir.east  = Col.H e := rfl
@[simp] lemma mkTile_south (n e s w) :
  (mkTile n e s w) Dir.south = Col.V s := rfl
@[simp] lemma mkTile_west (n e s w) :
  (mkTile n e s w) Dir.west  = Col.H w := rfl

/-- 90° rotation on edge colors (H ↔ V, arrows reoriented). -/
private def rotHV : Col → Col
| Col.H HCol.none    => Col.V VCol.none
| Col.H HCol.line    => Col.V VCol.line
| Col.H HCol.arrowL  => Col.V VCol.arrowU
| Col.H HCol.arrowR  => Col.V VCol.arrowD
| Col.V VCol.none    => Col.H HCol.none
| Col.V VCol.line    => Col.H HCol.line
| Col.V VCol.arrowU  => Col.H HCol.arrowL
| Col.V VCol.arrowD  => Col.H HCol.arrowR

/-- Rotate a tile counterclockwise by 90°. -/
def rot90 (t : WangTile Col) : WangTile Col :=
  fun d =>
    match d with
    | Dir.north => rotHV (t Dir.east)
    | Dir.east  => rotHV (t Dir.south)
    | Dir.south => rotHV (t Dir.west)
    | Dir.west  => rotHV (t Dir.north)

def rot180 (t : WangTile Col) : WangTile Col := rot90 (rot90 t)
def rot270 (t : WangTile Col) : WangTile Col := rot90 (rot180 t)

/-- Reflect across a vertical axis (swap W/E, flip horizontal arrows). -/
private def reflH : Col → Col
| Col.H HCol.none   => Col.H HCol.none
| Col.H HCol.line   => Col.H HCol.line
| Col.H HCol.arrowL => Col.H HCol.arrowR
| Col.H HCol.arrowR => Col.H HCol.arrowL
| Col.V v           => Col.V v

def reflectX (t : WangTile Col) : WangTile Col :=
  fun d =>
    match d with
    | Dir.north => reflH (t Dir.north)
    | Dir.east  => reflH (t Dir.west)
    | Dir.south => reflH (t Dir.south)
    | Dir.west  => reflH (t Dir.east)

/-- Reflect across a horizontal axis (swap N/S, flip vertical arrows). -/
private def reflV : Col → Col
| Col.V VCol.none   => Col.V VCol.none
| Col.V VCol.line   => Col.V VCol.line
| Col.V VCol.arrowU => Col.V VCol.arrowD
| Col.V VCol.arrowD => Col.V VCol.arrowU
| Col.H h           => Col.H h

def reflectY (t : WangTile Col) : WangTile Col :=
  fun d =>
    match d with
    | Dir.north => reflV (t Dir.south)
    | Dir.east  => reflV (t Dir.east)
    | Dir.south => reflV (t Dir.north)
    | Dir.west  => reflV (t Dir.west)

end Colors

/-! ## Robinson tile set (to be supplied)

Pick your favorite Robinson variant. Define a **finite** set `Tiles` of `WangTile Colors.Col`.
You can start from a small seed list and close under the D₄ symmetries using the helpers above.
-/

open Colors

/-- Placeholder: put here your concrete finite set of Robinson tiles. -/
def Tiles : Finset (WangTile Col) :=
  (∅ : Finset (WangTile Col))   -- replace with the actual finite set

/-! ## The Robinson SFT on Z² -/

abbrev Alphabet := SymbolicDynamics.Alphabet (T := Tiles)

/-- Build `[Inhabited Alphabet]` from `h : Tiles.Nonempty`. (Not a typeclass instance.) -/
noncomputable def instAlphabet (h : Tiles.Nonempty) : Inhabited Alphabet :=
  ⟨⟨Classical.choose h, Classical.choose_spec h⟩⟩

/-- The Robinson nearest–neighbour SFT built on Z² from `Tiles`.

It *requires* the caller’s `[Inhabited Alphabet]` so everyone shares the same instance.
-/
noncomputable def RobinsonSFT (h : Tiles.Nonempty) [Inhabited Alphabet] :=
  NNWang (T := Tiles) h          -- or `NNWangZ2` if that's your constructor name

/-! ### Basic properties used everywhere -/

-- lemma closed (h : Tiles.Nonempty) [Inhabited Alphabet] :
--   IsClosed (RobinsonSFT h).carrier := by
--   classical
--   simpa using (RobinsonSFT h).isClosed

-- lemma shiftInvariant (h : Tiles.Nonempty) [Inhabited Alphabet] :
--   ∀ s x, x ∈ (RobinsonSFT h).carrier → shift s x ∈ (RobinsonSFT h).carrier := by
--   classical
--   simpa using (RobinsonSFT h).shiftInvariant

-- @[simp] lemma mem_iff (h : Tiles.Nonempty) [Inhabited Alphabet]
--     {x : FullShift Alphabet Z2} :
--   x ∈ (RobinsonSFT h).carrier ↔
--     ∀ g, matchesE (T := Tiles) (x g) (x (Z2.e1 * g)) ∧
--          matchesN (T := Tiles) (x g) (x (Z2.e2 * g)) := by
--   classical
--   -- use the pointwise NN lemma from your Wang file
--   simpa using SymbolicDynamics.mem_NNWangZ2_iff (T := Tiles) h (x := x)
-- end

end Robinson
end SymbolicDynamics
