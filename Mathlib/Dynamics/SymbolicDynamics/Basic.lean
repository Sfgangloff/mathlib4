/-
Copyright (c) 2025 S. Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: S. Gangloff
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Symbolic dynamics on groups

This file develops a minimal API for symbolic dynamics over an arbitrary group `G`.
The ambient space is the full shift
`FullShift A G := G → A` (an `abbrev`), hence it inherits the product topology
from the Π-type. We define the right-translation action, cylinders, finite patterns,
their occurrences, forbidden sets, and subshifts (closed, shift-invariant subsets).
Basic topological statements (e.g. cylinders are clopen, occurrence sets are clopen,
forbidden sets are closed) are proved under discreteness assumptions on the alphabet.

The file is group-generic. Geometry specific to `ℤ^d` (boxes/cubes and the
box-based entropy) is kept in a separate specialization.

## Main definitions

* `FullShift A G := G → A`.
* `shift g x` — right translation: `(shift g x) h = x (h * g)`.
* `cylinder U x` — configurations agreeing with `x` on a finite set `U ⊆ G`.
* `Pattern A G` — finite support together with values on that support.
* `Pattern.occursIn p x g` — occurrence of `p` in `x` at translate `g`.
* `forbids F` — configurations avoiding every pattern in `F`.
* `Subshift A G` — closed, shift-invariant subsets of the full shift.

## Conventions

We use a **right** action of `G` on configurations:
`(shift g x) h = x (h * g)`. In additive notation (e.g. for `ℤ^d`) this is
`(shift v x) u = x (u + v)`.

## Implementation notes

* Since `FullShift A G` is an `abbrev` for `G → A`, instances such as
  `TopologicalSpace (FullShift A G)` and `Inhabited (FullShift A G)` are inherited
  automatically from the Π-type; no explicit instances are declared here.
* Openness/closedness results for cylinders and occurrence sets use
  `[DiscreteTopology A]`. The closedness proofs that enumerate values additionally
  require `[Fintype A]`, `[DecidableEq A]`, and `[DecidableEq G]` (for `Finset` manipulations
  and `Function.update`).
-/

noncomputable section
open Set Topology

namespace SymbolicDynamics

variable {A : Type*} [Fintype A] [Fintype A] [DecidableEq A] [Inhabited A]
variable {G : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Group G] [DecidableEq G]

/-! ## Full shift and shift action -/


/-- Full shift over a group `G` with alphabet `A` (product topology). -/
abbrev FullShift (A G) := G → A

/-- Right-translation shift: `(shift g x)(h) = x (h * g)`. -/
def shift (g : G) (x : FullShift A G) : FullShift A G :=
  fun h => x (h * g)

section ShiftAlgebra
variable {A G : Type*} [Group G]
@[simp] lemma shift_apply (g h : G) (x : FullShift A G) :
  shift g x h = x (h * g) := rfl

@[simp] lemma shift_one (x : FullShift A G) : shift (1 : G) x = x := by
  ext h; simp [shift]

lemma shift_mul (g₁ g₂ : G) (x : FullShift A G) :
  shift (g₁ * g₂) x = shift g₁ (shift g₂ x) := by
  ext h; simp [shift, mul_assoc]
end ShiftAlgebra

section ShiftTopology  -- add only topology on A
variable {A G : Type*} [Group G] [TopologicalSpace A]
lemma shift_continuous (g : G) : Continuous (shift (A:=A) (G:=G) g) := by
  -- coordinate projections are continuous; composition preserves continuity
  continuity
end ShiftTopology



/-! ## Cylinders -/

section CylindersDefs
variable {A G : Type*}

/-- Cylinder fixing `x` on the finite set `U`. -/
def cylinder (U : Finset G) (x : FullShift A G) : Set (FullShift A G) :=
  { y | ∀ i ∈ U, y i = x i }

lemma cylinder_eq_set_pi (U : Finset (G)) (x : G → A) :
  cylinder U x = Set.pi (↑U : Set (G)) (fun i => ({x i} : Set A)) := by
  ext y; simp [cylinder, Set.pi, Finset.mem_coe]

@[simp] lemma mem_cylinder {U : Finset G} {x y : FullShift A G} :
  y ∈ cylinder U x ↔ ∀ i ∈ U, y i = x i := Iff.rfl
end CylindersDefs

section CylindersOpen
variable {A G : Type*} [TopologicalSpace A] [DiscreteTopology A]
/-- Cylinders are open (and, dually, closed) when `A` is discrete. -/
lemma cylinder_is_open (U : Finset G) (x : G → A) :
  IsOpen (cylinder (A:=A) (G:=G) U x) := by
  classical
  have hopen : ∀ i ∈ (↑U : Set G), IsOpen ({x i} : Set A) := by
    intro i _; simp
  have hpi :
      IsOpen (Set.pi (s := (↑U : Set G))
                     (t := fun i => ({x i} : Set A))) :=
    isOpen_set_pi (U.finite_toSet) hopen
  simpa [cylinder_eq_set_pi (A:=A) (G:=G) U x] using hpi
end CylindersOpen

section CylindersClosed
variable {A G : Type*}
[TopologicalSpace A] [DiscreteTopology A]
lemma cylinder_is_closed (U : Finset G) (x : G → A) :
  IsClosed (cylinder (A:=A) (G:=G) U x) := by
  classical
  have hclosed : ∀ i ∈ (↑U : Set G), IsClosed ({x i} : Set A) := by
    intro i _; simp
  have hpi :
      IsClosed (Set.pi (s := (↑U : Set G))
                       (t := fun i => ({x i} : Set A))) :=
    isClosed_set_pi hclosed
  simpa [cylinder_eq_set_pi (A:=A) (G:=G) U x] using hpi
end CylindersClosed

/-! ## Patterns and occurrences -/

/-- A subshift is a closed, shift-invariant subset. -/
structure Subshift (A : Type*) [TopologicalSpace A] [Inhabited A] (G : Type*) [Group G] where
  /-- The underlying set of configurations. -/
  carrier : Set (FullShift A G)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier`. -/
  shiftInvariant : ∀ g : G, ∀ x ∈ carrier, shift (A:=A) (G:=G) g x ∈ carrier

/-- The full shift is a subshift. -/
example : Subshift A G :=
{ carrier := Set.univ,
  isClosed := isClosed_univ,
  shiftInvariant := by intro _ _ _; simp }


/-- A finite pattern: finite support in `G` and values on it. -/
structure Pattern (A : Type*) (G : Type*) [Group G] where
  /-- Finite support of the pattern. -/
  support : Finset G
  /-- The value (symbol) at each point of the support. -/
  data : support → A

/-- The domino supported on `{i,j}` with values `ai`,`aj`. -/
def domino {A G : Type*} [Group G] [DecidableEq G]
    (i j : G) (ai aj : A) : Pattern A G := by
  refine
  { support := ({i, j} : Finset G)
  , data := fun ⟨z, hz⟩ => if z = i then ai else aj }

/-- Occurrence of a pattern `p` in `x` at position `g`. -/
def Pattern.occursIn (p : Pattern A G) (x : FullShift A G) (g : G) : Prop :=
  ∀ (h) (hh : h ∈ p.support), x (h * g) = p.data ⟨h, hh⟩

/-- Configurations avoiding every pattern in `F`. -/
def forbids (F : Set (Pattern A G)) : Set (FullShift A G) :=
  { x | ∀ p ∈ F, ∀ g : G, ¬ p.occursIn x g }


section ShiftInvariance
variable {A G : Type*} [Group G]
/-- Shifts move occurrences as expected. -/
lemma occurs_shift (p : Pattern A G) (x : FullShift A G) (g h : G) :
  p.occursIn (shift h x) g ↔ p.occursIn x (g * h) := by
  constructor <;> intro H u hu <;> simpa [shift, mul_assoc] using H u hu

lemma forbids_shift_invariant (F : Set (Pattern A G)) :
  ∀ h : G, ∀ x ∈ forbids (A:=A) (G:=G) F, shift h x ∈ forbids F := by
  intro h x hx p hp g
  specialize hx p hp (g * h)
  -- contraposition
  contrapose! hx
  simpa [occurs_shift] using hx
end ShiftInvariance

/-- Extend a pattern by `default` away from its support (anchored at the origin). -/
def patternToOriginConfig (p : Pattern A G) : FullShift A G :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

/-- Translate a pattern to occur at `v`. -/
def patternToConfig (p : Pattern A G) (v : G) : FullShift A G :=
  shift (v⁻¹) (patternToOriginConfig p)

/-- Restrict a configuration to a finite support, seen as a pattern. -/
def patternFromConfig (x : G → A) (U : Finset (G)) : Pattern A G :=
  { support := U,
    data := fun i => x i.1 }

set_option linter.unusedSectionVars false in
lemma occurs_patternFromConfig
    (x : FullShift A G) (U : Finset G) (g : G) :
  (patternFromConfig (fun u => x (u * g)) U).occursIn x g := by
  intro u hu; rfl

section OccursAtEqCylinder
variable {A G : Type*} [Group G] [Inhabited A] [DecidableEq G]
/-- “Occurrence = cylinder translated by `g`”. -/
lemma occursAt_eq_cylinder (p : Pattern A G) (g : G) :
  { x | p.occursIn x g }
    = cylinder (p.support.image (· * g)) (patternToConfig p g) := by
  ext x
  constructor
  · intro H u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    dsimp [patternToConfig, patternToOriginConfig, shift]
    simp [dif_pos hw, H w hw]
  · intro H u hu
    have := H (u * g) (Finset.mem_image_of_mem _ hu)
    dsimp [patternToConfig, patternToOriginConfig, shift] at this
    simpa [add_neg_cancel_right, dif_pos hu] using this
end OccursAtEqCylinder

/-! ## Forbidden sets and subshifts -/

section OccSetsOpen
variable {A G : Type*} [Group G] [TopologicalSpace A] [DiscreteTopology A]
           [Inhabited A] [DecidableEq G]

/-- Occurrence sets are open. -/
lemma occursAt_open (p : Pattern A G) (g : G) :
    IsOpen { x | p.occursIn x g } := by
  rw [occursAt_eq_cylinder]; exact cylinder_is_open _ _

/-- Avoiding a fixed set of patterns is a closed condition. -/
lemma forbids_closed (F : Set (Pattern A G)) :
  IsClosed (forbids F) := by
  rw [forbids]
  have : {x | ∀ p ∈ F, ∀ v : G, ¬ p.occursIn x v}
       = ⋂ (p : Pattern A G) (h : p ∈ F), ⋂ (v : G), {x | ¬ p.occursIn x v} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter ?_;
  intro p; refine isClosed_iInter ?_;
  intro _; refine isClosed_iInter ?_;
  intro v; have : {x | ¬p.occursIn x v} = {x | p.occursIn x v}ᶜ := by ext x; simp
  simpa [this, isClosed_compl_iff] using occursAt_open p v

end OccSetsOpen

section OccSetsClosed
variable {A G : Type*} [Group G] [TopologicalSpace A] [DiscreteTopology A]
           [Inhabited A] [DecidableEq G]

/-- Occurrence sets are closed. -/
lemma occursAt_closed (p : Pattern A G) (g : G) :
    IsClosed { x | p.occursIn x g } := by
  rw [occursAt_eq_cylinder]; exact cylinder_is_closed _ _

end OccSetsClosed

/-- Subshift defined by forbidden patterns. -/
def X_F (F : Set (Pattern A G)) : Subshift A G :=
{ carrier := forbids F,
  isClosed := forbids_closed F,
  shiftInvariant := forbids_shift_invariant F }

/-- Subshift of finite type defined by a finite family of forbidden patterns. -/
def SFT (F : Finset (Pattern A G)) : Subshift A G :=
  X_F (F : Set (Pattern A G))

/-- Patterns with fixed support `U`. -/
def FixedSupport (A : Type*) (G : Type*) [Group G] (U : Finset G) :=
  { p : Pattern A G // p.support = U }

/-- `FixedSupport A G U ≃ (U → A)`; gives finiteness immediately. -/
def equivFun {U : Finset G} :
  FixedSupport A G U ≃ (U → A) where
  toFun   := fun p i => p.1.data ⟨i.1, by simp [p.2]⟩
  invFun  := fun f => ⟨{ support := U, data := f }, rfl⟩
  left_inv := by rintro ⟨p,hU⟩; apply Subtype.ext; cases hU; rfl
  right_inv := by intro f; rfl

instance fintypeFixedSupport {U : Finset G} :
    Fintype (FixedSupport A G U) := by
  classical exact Fintype.ofEquiv (U → A) (equivFun (A:=A) (G:=G) (U:=U)).symm

/-- Language on a finite set `U ⊆ G`: patterns obtained by restricting some `x ∈ X`. -/
def languageOn (X : Set (G → A)) (U : Finset G) : Set (Pattern A G) :=
  { p | ∃ x ∈ X, patternFromConfig x U = p }

/-- Cardinality of the finite-support language. -/
noncomputable def languageCardOn (X : Set (G → A)) (U : Finset G) : ℕ := by
  classical
  -- Image of a map into the finite type `FixedSupport A G U`
  let f : {x : G → A // x ∈ X} → FixedSupport A G U :=
    fun x => ⟨patternFromConfig x.1 U, rfl⟩
  have hfin : (Set.range f).Finite := (Set.finite_univ :
    (Set.univ : Set (FixedSupport A G U)).Finite)
    |>.subset (by intro y hy; simp)
  exact hfin.toFinset.card

/-- Number of patterns of a subshift on a finite shape `U`. -/
noncomputable def patternCountOn (Y : Subshift A G) (U : Finset G) : ℕ :=
  languageCardOn (A:=A) (G:=G) Y.carrier U

/-- A conjugacy between subshifts over the same group is a homeomorphism
that commutes with every shift. -/
structure Conjugacy {A : Type*} [TopologicalSpace A] [Inhabited A]
    {G : Type*} [Group G]
    (X Y : Subshift A G) where
-- The symbol ≃ₜ denotes topological conjugacy.
(toHomeo : {x // x ∈ X.carrier} ≃ₜ {y // y ∈ Y.carrier})
(commute : ∀ g : G, ∀ x : {x // x ∈ X.carrier},
  toHomeo (⟨shift (A:=A) (G:=G) g x.1,
            X.shiftInvariant g x.1 x.2⟩)
= ⟨shift (A:=A) (G:=G) g (toHomeo x).1,
   Y.shiftInvariant g (toHomeo x).1 (toHomeo x).2⟩)

section ConjugacyCoercions
variable {A G : Type*} [TopologicalSpace A] [Inhabited A] [Group G]
variable {X Y : Subshift A G}
@[simp] lemma Conjugacy.coe_apply {X Y} (φ : Conjugacy (A := A) (G := G) X Y)
    (x : {x // x ∈ X.carrier}) :
  (φ.toHomeo x : FullShift A G) = (φ.toHomeo x).1 := rfl
end ConjugacyCoercions

/-! ## Nearest-neighbor SFT on an arbitrary group

We fix a finite “neighbor set” `S : Finset G`. For each `s ∈ S` we prescribe
an edge predicate `E s : A → A → Prop` describing which symbol pairs are allowed
across the edge `{1, s}` (hence, at translate `g`, across `{g, s*g}`).
-/

section NNCore
variable {A G : Type*} [Group G] [DecidableEq G]

/-- The `{1, s}` domino with values `a` at `1` and `b` at `s`. -/
def domino_e_s (s : G) (a b : A) : Pattern A G :=
  domino (A:=A) (G:=G) (1 : G) s a b

/-- Occurrence of the `{1,s}` domino at position `g` pins the pair `(x g, x (s*g))`. -/
lemma occurs_domino_e_s_iff (s : G) (hs : s ≠ 1) (a b : A)
    (x : FullShift A G) (g : G) :
  (domino_e_s (A:=A) (G:=G) s a b).occursIn x g
    ↔ x g = a ∧ x (s * g) = b := by
  classical
  constructor
  · intro H
    -- Value of x on g according to hypothesis
    have h1 := H (1 : G) (by simp [domino_e_s, domino])
    -- Value of x on s * g according to hypothesis
    have h2 := H s       (by simp [domino_e_s, domino])
    -- unfold `data` at `1` and at `s`
    have hg  : x g = a := by simpa [domino_e_s, domino] using h1
    have hsg : x (s * g) = b := by simpa [domino_e_s, domino, hs] using h2
    exact ⟨hg, hsg⟩
  -- rintro is “intro + pattern matching”
  -- Introduces the antecedent of the implication and immediately splits the conjunction.
  -- Then u hu correspond to the quantifier in the second term of the implication.
  · rintro ⟨hg, hsg⟩ u hu
    -- Turns hu : u ∈ (domino_e_s …).support into `u ∈ {1, s}`
    -- `u ∈ {1, s}` gives `u = 1 ∨ u = s`
    -- rcases p with h | h pattern-matches on a proof p : P ∨ Q,
    -- splitting the goal into two subgoals:
    -- assuming h : u = 1,
    -- assuming h : u = s.
    rcases (by simpa [domino_e_s, domino] using hu) with h | h
    · subst h
      -- subst h takes an equality hypothesis (here h : u = 1 or h : u = s)
      -- and replaces every occurrence of u in the goal and context by the
      -- right-hand side, then clears h.
      simpa [one_mul, domino_e_s, domino] using hg
    · subst h
      -- one_mul is the standard lemma stating that the left identity
      -- 1 does nothing under multiplication:
      simpa [domino_e_s, domino, hs] using hsg


/-- The **nearest-neighbor forbidden set** for a finite neighbor set `S` and
edge predicates `E s` (only for `s ∈ S`). We forbid exactly those `{1,s}` dominoes
whose pair `(a,b)` violates `E s`. Using a `Set` avoids any need for decidable
equality on `Pattern`. -/
def NNForbidden
    (A G : Type*) [Group G] [DecidableEq G]
    (S : Finset G) (E : G → A → A → Prop) : Set (Pattern A G) :=
  { p | ∃ s ∈ S, ∃ a b : A, ¬ E s a b ∧
        p = domino_e_s (A:=A) (G:=G) s a b }

/-- The **nearest-neighbor SFT** generated by `S` and `E`. -/
def NNSFT
    (A : Type*) [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    (G : Type*) [Group G] [DecidableEq G]
    (S : Finset G) (E : G → A → A → Prop) : Subshift A G :=
  X_F (A:=A) (G:=G) (NNForbidden (A:=A) (G:=G) S E)

end NNCore

section NNSFT_char
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
variable {G : Type*} [Group G] [DecidableEq G]



set_option linter.unnecessarySimpa false in
/-- Membership characterization for the NN SFT when the identity is not a neighbor. -/
lemma mem_NNSFT_iff
    {S : Finset G} (hS : (1 : G) ∉ S)
    {E : G → A → A → Prop} {x : FullShift A G} :
  x ∈ (NNSFT (A:=A) (G:=G) S E).carrier
    ↔ ∀ g : G, ∀ s ∈ S, E s (x g) (x (s * g)) := by
  classical
  constructor
  · intro hx g s hs
    -- reasoning by contradiction
    by_contra h
    -- s ≠ 1, since 1 ∉ S
    have hs' : s ≠ (1 : G) := by
      intro h1;
      subst h1;
      exact hS hs
    -- The forbidden domino occurs at g
    have hocc :
      (domino_e_s (A:=A) (G:=G) s (x g) (x (s * g))).occursIn x g :=
      (occurs_domino_e_s_iff (A:=A) (G:=G) (s:=s) (hs:=hs') (a:=x g)
          (b:=x (s * g)) (x:=x) (g:=g)).mpr
        ⟨rfl, rfl⟩
    -- That domino is in the NN-forbidden set
    have hforb :
        domino_e_s (A:=A) (G:=G) s (x g) (x (s * g))
          ∈ NNForbidden (A:=A) (G:=G) S E :=
      ⟨s, hs, x g, x (s * g), h, rfl⟩
    -- Contradiction with membership in the subshift
    exact (hx _ hforb g) hocc
  · intro h
    intro p hp g hocc
    rcases hp with ⟨s, hs, a, b, hNot, rfl⟩
    have hs' : s ≠ (1 : G) := by intro h1; subst h1; exact hS hs
    have hpair :=
      (occurs_domino_e_s_iff (A:=A) (G:=G) (s:=s) (hs:=hs')
         (a:=a) (b:=b) (x:=x) (g:=g)).1 hocc
    rcases hpair with ⟨hg, hsg⟩
    exact hNot (by simpa [hg, hsg] using h g s hs)
end NNSFT_char


/-! ## Higher–block presentation over a group

Fix a finite “shape” `U : Finset G`. The block map at position `g : G`
sends a configuration `x : G → A` to its restriction on the right–translate `U * g`,
seen as a function `U → A` by `i ↦ x (i * g)` (right action convention).
-/


/-- The **block map** for a finite shape `U`.
At each `g : G` we record the `U`-window of `x` around `g`
as a function `U → A`, namely `i ↦ x (i * g)`. -/
def blockMap (U : Finset G) (x : FullShift A G) : G → (U → A) :=
  fun g i => x (i.1 * g)

section BlockMapApply
variable {A G : Type*} [Group G]

@[simp] lemma blockMap_apply (U : Finset G) (x : FullShift A G)
    (g : G) (i : U) :
  blockMap (A:=A) (G:=G) U x g i = x (i.1 * g) := rfl

end BlockMapApply

section
variable {A G : Type*} [Group G]
/-- The block map is a **sliding block code**: it commutes with the right shift. -/
@[simp] lemma blockMap_shift {U : Finset G} (s g : G) (x : FullShift A G) :
  blockMap (A:=A) (G:=G) U (shift (A:=A) (G:=G) s x) g
    = blockMap (A:=A) (G:=G) U x (g * s) := by
  ext i; simp [blockMap]; simp [mul_assoc]
end

section BlockMapContinuous
variable {A G : Type*} [Group G] [TopologicalSpace A]

/-- Continuity of the block map when `A` has a topology. -/
lemma blockMap_continuous (U : Finset G) :
  Continuous (fun x : FullShift A G => blockMap (A:=A) (G:=G) U x) := by
  -- product-of-coordinate maps; coordinates are continuous
  -- `((g,i) ↦ x (i*g))` is built from continuous evaluation
  classical
  -- `continuous_pi`: product of functions is continuous when each is continuous.
  apply continuous_pi ; intro g
  -- again `continuous_pi` over `i : U`
  apply continuous_pi  ; intro i
  -- the coordinate `(fun x => x (i*g))` is continuous
  simpa [blockMap] using (continuous_apply (i.1 * g))
end BlockMapContinuous

lemma image_blockMap_closed
    {A G : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A] [Inhabited A] [Group G]
    (X : Subshift A G) (U : Finset G) :
  IsClosed { y : FullShift (U → A) G | ∃ x ∈ X.carrier, y = blockMap (A:=A) (G:=G) U x } := by
  -- identify the set as an image
  have hset :
    { y : FullShift (U → A) G | ∃ x ∈ X.carrier, y = blockMap (A:=A) (G:=G) U x }
      = (fun x : FullShift A G => blockMap (A:=A) (G:=G) U x) '' X.carrier := by
    ext y; constructor
    · rintro ⟨x,hx,rfl⟩; exact ⟨x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩; exact ⟨x,hx,rfl⟩

  -- X closed in a compact product ⇒ X.carrier is compact
  have hXc : IsCompact X.carrier := X.isClosed.isCompact
  -- blockMap is continuous
  have hcont := blockMap_continuous (A:=A) (G:=G) U
  have himgC :
    IsCompact ((fun x : FullShift A G => blockMap (A:=A) (G:=G) U x) '' X.carrier) :=
    hXc.image hcont

  have hclosed_img :
    IsClosed ((fun x : FullShift A G => blockMap (A:=A) (G:=G) U x) '' X.carrier) :=
    himgC.isClosed

  simpa [hset] using hclosed_img

/-- **Higher–block factor** of a subshift `X` along `U`.
Carrier = image of `blockMap U` (so this is a factor subshift). -/
def higherBlock
    {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    {G : Type*} [Group G]
    (X : Subshift A G) (U : Finset G) : Subshift (U → A) G :=
{ carrier := { y | ∃ x ∈ X.carrier, y = blockMap (A:=A) (G:=G) U x }
, isClosed := image_blockMap_closed (A:=A) (G:=G) X U
, shiftInvariant := by
    intro s y hy
    obtain ⟨x, hxX, rfl⟩ := hy
    refine ⟨shift (A:=A) (G:=G) s x, X.shiftInvariant s x hxX, ?_⟩
    funext g i; simp [blockMap]
    simp [mul_assoc]
}

@[simp] lemma mem_higherBlock_iff
    {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    {G : Type*} [Group G]
    (X : Subshift A G) (U : Finset G) {y : FullShift (U → A) G} :
  y ∈ (higherBlock (A:=A) (G:=G) X U).carrier
    ↔ ∃ x ∈ X.carrier, y = blockMap (A:=A) (G:=G) U x :=
Iff.rfl

/-- The block map realizes `higherBlock X U` as a **factor** of `X`. -/
lemma blockMap_mem_higherBlock
    {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    {G : Type*} [Group G]
    (X : Subshift A G) (U : Finset G) {x : FullShift A G}
    (hx : x ∈ X.carrier) :
  blockMap (A:=A) (G:=G) U x ∈ (higherBlock (A:=A) (G:=G) X U).carrier :=
by
  exact ⟨x, hx, rfl⟩

/-- The block map is a **conjugacy candidate** onto its image (it commutes with shifts);
promote to a true conjugacy once you show it is a homeomorphism onto the image. -/
lemma blockMap_commutes_on_image
    {A : Type*} [TopologicalSpace A] [Inhabited A]
    {G : Type*} [Group G]
    (U : Finset G) (s g : G) (x : FullShift A G) :
  (blockMap (A:=A) (G:=G) U (shift (A:=A) (G:=G) s x)) g
    = (shift (A:=(U → A)) (G:=G) s (blockMap (A:=A) (G:=G) U x)) g := by
  -- equality of `U → A`-valued functions at each `g`
  funext i
  simp [blockMap,mul_assoc]


end SymbolicDynamics
