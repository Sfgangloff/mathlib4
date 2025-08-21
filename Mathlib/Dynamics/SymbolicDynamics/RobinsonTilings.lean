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

/-- Build `[Inhabited Alphabet]` once, explicitly. -/
noncomputable def instAlphabet (h : Tiles.Nonempty) : Inhabited Alphabet :=
  ⟨⟨Classical.choose h, Classical.choose_spec h⟩⟩

/-- Robinson SFT with the instance **baked into the return type**. -/
noncomputable def RobinsonSFT (h : Tiles.Nonempty) :
    (let _ : Inhabited Alphabet := instAlphabet h;
     Subshift Alphabet Z2) := by
  classical
  letI : Inhabited Alphabet := instAlphabet h
  exact NNWang (T := Tiles) h   -- or NNWangZ2 if that's your constructor

/-- Alias for the carrier set with the **same** baked instance in the type. -/
noncomputable def RobinsonCarrier (h : Tiles.Nonempty) :
    (let _ : Inhabited Alphabet := instAlphabet h;
     Set (FullShift Alphabet Z2)) :=
by
  classical
  letI : Inhabited Alphabet := instAlphabet h
  -- now projection sees the instance in scope
  simpa using (RobinsonSFT (h := h)).carrier

/-! ### Basic properties used everywhere -/
/-- Closedness of the Robinson shift. -/
lemma closed (h : Tiles.Nonempty) :
  IsClosed (RobinsonCarrier (h := h)) := by
  classical
  -- install the *same* instance before projecting fields
  letI : Inhabited Alphabet := instAlphabet h
  -- now just reuse the SFT lemma and fold back to the carrier alias
  simpa [RobinsonCarrier] using (RobinsonSFT (h := h)).isClosed


/-- Shift invariance. -/
lemma shiftInvariant (h : Tiles.Nonempty) :
  ∀ s x, x ∈ RobinsonCarrier (h := h) →
         shift s x ∈ RobinsonCarrier (h := h) := by
  classical
  letI : Inhabited Alphabet := instAlphabet h
  simpa [RobinsonCarrier] using (RobinsonSFT (h := h)).shiftInvariant

/-- Pointwise NN membership along `e1`/`e2`. -/
@[simp] lemma mem_iff (h : Tiles.Nonempty) {x : FullShift Alphabet Z2} :
  (let _ : Inhabited Alphabet := instAlphabet h;
   x ∈ RobinsonCarrier (h := h)) ↔
    ∀ g, matchesE (T := Tiles) (x g) (x (Z2.e1 * g)) ∧
         matchesN (T := Tiles) (x g) (x (Z2.e2 * g)) := by
  classical
  -- First, rewrite the LHS to the SFT form with the same baked instance:
  change (let _ : Inhabited Alphabet := instAlphabet h;
          x ∈ (RobinsonSFT (h := h)).carrier) ↔ _
  -- Work under that exact instance:
  letI : Inhabited Alphabet := instAlphabet h

  -- side-condition needed by `mem_NNSFT_iff`: 1 ∉ Basis = {e1, e2}
  -- (reuse your proofs that 1 ≠ e1 and 1 ≠ e2)
  have h1 : (1 : Z2) ≠ Z2.e1 := by
    intro heq
    have h' : (0 : ℤ × ℤ) = (1, 0) := by
      simpa [Z2.e1] using congrArg Multiplicative.toAdd heq
    have : (0 : ℤ) = 1 := by simpa using congrArg Prod.fst h'
    exact Int.zero_ne_one this
  have h2 : (1 : Z2) ≠ Z2.e2 := by
    intro heq
    have h' : (0 : ℤ × ℤ) = (0, 1) := by
      simpa [Z2.e2] using congrArg Multiplicative.toAdd heq
    have : (0 : ℤ) = 1 := by simpa using congrArg Prod.snd h'
    exact Int.zero_ne_one this

  -- tiny helper to say an element not equal to either member of a 2-set is not in it
  have hId : (1 : Z2) ∉ Basis := by
    classical
    -- build ¬(1 = e1 ∨ 1 = e2) from h1, h2
    have hne : ¬ ((1 : Z2) = Z2.e1 ∨ (1 : Z2) = Z2.e2) := by
      intro h'
      cases h' with
      | inl h1eq => exact h1 h1eq
      | inr h2eq => exact h2 h2eq
    -- turn membership in {e1,e2} into that disjunction
    simpa [Basis, Finset.mem_insert, Finset.mem_singleton] using hne

  -- general NN membership: ∀ g s ∈ Basis, WangCompat s (x g) (x (s*g))
  have hx :
      x ∈ (NNSFT (A := Alphabet) (G := Z2)
                 (S := Basis) (E := WangCompat (T := Tiles))).carrier
        ↔ ∀ g s, s ∈ Basis → WangCompat (T := Tiles) s (x g) (x (s * g)) :=
    mem_NNSFT_iff (A := Alphabet) (G := Z2)
                  (S := Basis) (E := WangCompat (T := Tiles)) (x := x) hId

  -- unfold your `RobinsonSFT` and reduce the finite set {e1,e2}
  -- plus `WangCompat` at those two steps to get the desired pair of constraints
  simpa [Basis, WangCompat,
         Finset.mem_insert, Finset.mem_singleton] using hx

end Robinson
end SymbolicDynamics
