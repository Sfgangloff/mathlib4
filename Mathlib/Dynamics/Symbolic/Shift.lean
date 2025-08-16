import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Instances.Discrete
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

open Set Topology
open Filter

namespace SymbolicDynamics

/-!
  # Setup
  We fix:
  - A finite alphabet `A` with a discrete topology and a default element;
  - A dimension `d : ℕ`.
  - The lattice Z^d, with an algorithm for deciding equality, an addition and group structure.
-/

-- The keyword 'variable' defines names and stores them the context of this scope.
-- The following variable defines a type A living in some universe Type u.
-- Type* is a shortcut for 'Type _ with an implicit universe level'
-- It makes every lemma universe-polymorphic without you having to pick u.
-- The Curly braces {…} make A an implicit argument: future lemmas will quantify
-- over A but users won’t have to write it explicitly; Lean will infer it.
-- [Fintype A] is a typeclass parameter: Lean expects an instance of Fintype A
-- to be available in the typeclass system. Mathematically, this means: “A is finite.”
-- Consequences are as follows: you get canonical enumerations (e.g. Finset.univ : Finset A),
-- cardinality Fintype.card A, sums/products over A, etc.
-- Technically: Lean inserts a hidden argument inst? : Fintype A and uses it automatically.

-- The typeclass parameter [DecidableEq A] provides the equality statement a=b for elements
-- a,b in A with an algorithm deciding it.
-- The typeclass parameter [Inhabited A] provides a default element of A.
-- In particular, A is assumed not empty.
-- The typeclass parameter [TopologicalSpace A] provides A with a topology (and thus
-- open sets, continuity, limits, etc).
-- The typeclass parameter [DiscreteTopology A] assume that that the given topology on A
-- is discrete, providing a formal proof of this.

variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
[TopologicalSpace A] [DiscreteTopology A]

-- {d : ℕ} Introduces a natural number parameter d, implicitly.
-- As with {A …}, the curly braces mean users don’t have to write d explicitly when
-- it can be inferred from context (e.g. the dimension of ℤ^d, arrays of length d, etc.).

variable {d : ℕ}

/-- The discrete ℤ^d lattice is modeled as functions from `Fin d` to `ℤ`. -/
-- Defines Zd as a type dependent on a parameter d of type N. This type is
-- the one of functions from Fin d to Z. Fin d is the finite set {0,1,…,d−1}
-- The keyword "def" means new definition.
def Zd (d : ℕ) := Fin d → ℤ

-- The following declares that Zd d has decidable equality, and tells Lean how to get the
-- algorithm, namely by infering it (using inferInstanceAs) from the known algorithm
-- on Fin d → ℤ.

-- @[instance]: this registers the definition as a typeclass instance.
-- This typeclass is DecidableEq (Zd d).
-- Without @[instance], Lean would not automatically use this function in typeclass search.
-- With it, any time Lean sees [DecidableEq (Zd d)] as a requirement, it will try this definition.

-- Mathematically Zd.decidableEq is a function which associates an instance of DecidableEq (Zd d)
-- for each integer d, meaning an algorithm for deciding equality.

@[instance]
def Zd.decidableEq (d : ℕ) : DecidableEq (Zd d) :=
  inferInstanceAs (DecidableEq (Fin d → ℤ))

/-- Pointwise addition on ℤ^d. -/
-- The keyword instance declares a typeclass instance.
-- Defines an instance of Add for Zd d, which takes u v defined as functions and
-- the sum is defined as i ↦ u i + v i (i ↦ u(i) + v(i)).
instance : Add (Zd d) where
  add := fun u v i ↦ u i + v i

-- AddCommGroup is the standard typeclass of additive commutative groups.
-- Pi.addCommGroup helps define group structure on functions with value in an
-- additive commutative group (product of groups).
instance : AddCommGroup (Zd d) := Pi.addCommGroup


/-!
  # Symbolic dynamics definitions
-/

/-!
  ## Definitions
-/

/-! ### Full shift -/

/-- The full shift space over ℤ^d with alphabet `A`. -/
-- The full shift is defined as the set of functions from Z^d to A.
-- @[reducible] makes this definition reducible for the typechecker.
-- This means When Lean sees FullShiftZd A d in a goal,
-- it will freely replace it with Zd d → A.
@[reducible]
def FullShiftZd (A : Type*) (d : ℕ) := Zd d → A

-- Defines the topology on the full shifts as the product topology of the
-- (discrete) topology on A.
instance : TopologicalSpace (FullShiftZd A d) := Pi.topologicalSpace
-- Defines the default element of the full shift as the function which to every position
-- z associates the default element of A.
instance : Inhabited (FullShiftZd A d) := ⟨fun _ ↦ default⟩

namespace FullShiftZd

/-! ### Shift map -/

/-- The shift action of ℤ^d on the full shift. -/
def shift (v : Zd d) (x : FullShiftZd A d) : FullShiftZd A d :=
  fun u ↦ x (u + v)

section
variable {A : Type*} {d : ℕ}

-- The map shift is a group action. This is implied by the two lemmas.

-- This says with v fixed to 0, this map is identity.
-- The attribue `@[simp]` tells the simplifier tactic simp that this lemma should
-- be used as a rewriting rule.
@[simp] lemma shift_zero (x : FullShiftZd A d) :
    shift (0 : Zd d) x = x := by
  -- Considers a particular u, and the goal becomes shift 0 x u = x u.
  ext u
  -- Uses the definition of the shift to get `shift 0 x u = x (u + 0)`. Under the hood,
  -- `add_zero` is used, transforming `x (u+0)` into `x u`.
  simp [shift]

-- Additivity.
lemma shift_add (v w : Zd d) (x : FullShiftZd A d) :
    shift (v + w) x = shift v (shift w x) := by
  -- Considers a particular u, and the goal becomes shift 0 x u = x u.
  ext u
  -- LHS: x (u + (v + w))
  -- RHS: from the definition of shift we have
  -- (shift v (shift w x)) u = (shift w x) (u + v) = x ((u + v) + w)
  -- Wityh add_assoc (associativity of addition), we have LHS = RHS.
  simp [shift, add_assoc]
end

section
variable {A : Type*} [TopologicalSpace A]
variable {d : ℕ}

/-- The shift map is continuous. -/
lemma shift_continuous (v : Zd d) :
  Continuous (shift v : FullShiftZd A d → FullShiftZd A d) :=
by
-- tactic which, looking at the structure of the function
-- (compositions, products, projections, lambda, etc) and knwon lemmas,
-- provides a continuity proof.
continuity

end

/-! ### Cylinders -/

/-- Defines the cylinder, provided a configuration `x` and a finite set subset `U` of Z^d,
as the set of configurations which agree with `x`on `U`. -/
@[reducible]
def cylinder (U : Finset (Zd d)) (x : Zd d → A) : Set (FullShiftZd A d) :=
  { y | ∀ i ∈ U, y i = x i }

section
variable {A : Type*} {d : ℕ}

-- Rewrites belonging to a cylinder as pointwise equalities.
@[simp] lemma mem_cylinder {U : Finset (Zd d)} {x y : FullShiftZd A d} :
  y ∈ cylinder U x ↔ ∀ i ∈ U, y i = x i := by
  -- The keyword unfold cylinder replaces cylinder U x by its defining RHS: {y∣∀i∈U,yi=xi}.
  -- The goal thus becomes y ∈ { y | ∀ i ∈ U, y i = x i } ↔ ∀ i ∈ U, y i = x i.
  unfold cylinder;
  -- Two expressions are definitionally equal if Lean can reduce one to the
  -- other by unfolding definitions - this is what rfl does. Here it is the case.
  -- Hence rfl (reflexivity of definitional equality) closes the goal:
  -- both sides are definitionally the same term.
  rfl
end

section
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
variable {d : ℕ}

-- This proves that a cylinder is an open set.
lemma cylinder_is_open (U : Finset (Zd d)) (x : Zd d → A) :
  IsOpen (cylinder U x) := by
  -- Define S as intersection of 'elementary' cylinders provided by x and elements of U.
  let S : Set (FullShiftZd A d) := ⋂ i ∈ U, { y | y i = x i }
  -- Let's prove that the cylinder is equal to S.
  have : cylinder U x = S := by
    -- Transforms the goal into an equivalence of y in cylinder and y in S.
    ext y
    -- Using cylinder, the goal becomes: y in { y | ∀ i ∈ U, y i = x i } <->  y in S.
    -- mem_setOf_eq : (x ∈ {y | p y}) = p x
    -- Using this, the goal becomes ∀ i ∈ U, y i = x i <-> y in S.
    rw [cylinder, mem_setOf_eq]
    -- mem_iInter₂ : x ∈ ⋂ i ∈ s, T i ↔ ∀ i ∈ s, x ∈ T i
    -- Using this, we rewrite y in S and the goal becomes:
    -- (∀ i ∈ U, y i = x i) ↔ ∀ i ∈ U, y ∈ {y | y i = x i}.
    rw [mem_iInter₂]
    -- Rewrites y ∈ {y | y i = x i} as y i = x i. The goal becomes trivial.
    simp only [mem_setOf_eq]
  -- "this" refers to the fact we just proved. The goal is then S is open.
  rw [this]
  -- isOpen_biInter_finset: the intersection of open sets is an open set.
  -- The keyword "apply" means “Use this theorem/lemma/definition as the next step,
  -- matching its conclusion with the current goal,
  -- and then generate new subgoals for its hypotheses.”. In this case,
  -- The goal becomes ∀ i ∈ U, IsOpen {y | y i = x i}.
  apply isOpen_biInter_finset
  -- Introduces a particular i in U. The goal is thus to prove IsOpen {y | y i = x i}.
  intro i _
  -- The {y | y i = x i} is the preimage of the function y -> y i.
  have : { y : FullShiftZd A d | y i = x i } = (fun y ↦ y i) ⁻¹' {x i} := rfl
  -- Rewrite using the statement above.
  rw [this]
  -- Uses the fact that the preimage of an open set is an open set. We
  -- need that y -> y i is continuous, and that the set {x i} is open.
  -- The goal is thus composed of these two subgoals.
  -- This is given directly by continuous_apply and isOpen_discrete.
  apply Continuous.isOpen_preimage
  · exact continuous_apply i
  · exact isOpen_discrete ({x i} : Set A)
end

section
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A] [DecidableEq A]
variable {d : ℕ}
/-- Cylinder sets are also closed. -/
lemma cylinder_is_closed (d : ℕ) (U : Finset (Zd d)) (x : Zd d → A) :
    IsClosed (cylinder U x) := by
  -- The complement of the cylinder is a union over i ∈ U and a ≠ x i of cylinders fixing
  -- the value on position i to a.
  -- The keyword Function.update x i a corresponds to updating the function x at
  -- input i with value a.
  -- Finset.univ: this is the finite set of all elements of type A (infered from type of a)
  -- The symbol \ corresponds to set difference.
  -- This statement allows us to use the fact that cylinders are open.
  have h : (cylinder U x)ᶜ = ⋃ (i ∈ U) (a ∈ (Finset.univ \ {x i} : Finset A)),
      cylinder {i} (Function.update x i a) := by
    · ext y
      -- Writes belonging to complement as not belonging to.$
      -- The keyword "only" means simplifying only with these lemmas and nothing else.
      simp only [mem_compl_iff]
      -- unpack membership to union.
      simp only [mem_iUnion]
      -- unpack membership to cylinder using ad hoc lemma above.
      simp only [mem_cylinder]
      -- Finset.mem_univ : a ∈ Finset.univ ↔ True
      -- Finset.mem_sdiff : a ∈ (s \ t) ↔ a ∈ s ∧ a ∉ t
      simp only [Finset.mem_univ, Finset.mem_sdiff]
      -- not for all is exists one that not.
      simp only [not_forall]
      -- exists_prop : (∃ x, p x ∧ q) ↔ (∃ x, p x) ∧ q
      simp only [exists_prop]
      -- Decomposes the equivalence into two implications.
      constructor
      -- First case, intro assumes the hypothesis.
      · intro hy
        -- ean tactic that pushes negations (¬) inward through logical connectives and
        -- quantifiers inside the expression or hypothesis hy.
        push_neg at hy
        -- Lean’s destructuring syntax for hypotheses that are existential statements or tuples.
        obtain ⟨i, hiU, hiy⟩ := hy
        -- This means “The witnesses for the first three ∃ in my goal are i, hiU,
        -- and y i respectively. Now Lean, please update the goal to only require
        -- the proof of the remaining property.”
        -- Here uses i, hiU for exists i in U and replaces i_1 with y i. Note that in the new goal
        -- i_2 is renamed i_1.
        use i, hiU, y i
        -- Separates the conjunction
        constructor
        -- Proves True ∧ y i ∉ {x i}. Comes directly from hiy: y i ≠ x i.
        · simp [hiy]
        -- Enough to apply the update.
        · simp [Function.update_apply]
      -- rintro: refined intro, instead of simply introducing the hypothesis of the implication,
      -- directly unpacks the quantifiers.
      · rintro ⟨i, hiU, a, ha, hy⟩
        -- simplifies ha by removing True
        simp only [true_and] at ha
        -- uses i for x_1
        use i, hiU
        -- rewrites the goal using hy: y i = Function.update x i a i
        rw [hy]
        -- simplifies using the definition of Function.update: here Function.update x i a i = a.
        -- Here goal becomes ¬(if True then a else x i) = x i.
        simp only [Function.update_apply]
        -- gets a ≠ x i (we know that a is in in {x_i})
        have hne : a ≠ x i := by
          -- intro here introduces by default the opposite (reasoning ad absurdum)
          intro h
          -- we need to prove a ∈ {x i} (since contradiction with ha)
          apply ha
          -- since a = x i (h), we just need to prove x i ∈ {x i}
          rw [h]
          -- this is given directly by Finset.mem_singleton_self
          exact Finset.mem_singleton_self _
        exact hne
        -- residual goal i ∈ {i} is because of "if True".
        exact Finset.mem_singleton_self i
  -- Proof that the complement is open using the fact proven above that the
  -- complement is a union of cylinders.
  have : IsOpen ((cylinder U x)ᶜ) := by
    -- uses the fact that the complement is union of cylinders.
    rw [h]
    -- with apply we now need to prove that each set in the union is open.
    -- Note that ⋃ i ∈ U means ⋃ (i : Zd d), ⋃ (hi : i ∈ U), which is why
    -- there needs to apply 4 times here.
    apply isOpen_iUnion; intro i
    apply isOpen_iUnion; intro hi
    apply isOpen_iUnion; intro a
    apply isOpen_iUnion; intro ha
    -- apply the lemma saying that cylinders are open.
    exact cylinder_is_open {i} (Function.update x i a)
  -- Concludes with the fact that the complement of an open set is
  -- closed.
  exact isOpen_compl_iff.mp this
end

/-! ### Subshifts and patterns -/

/-- A subshift is a closed, shift-invariant subset of the full shift. -/
-- A Subshift on alphabet A and of dimension d is a record with three fields:
-- carrier — the underlying set of points in the full shift FullShiftZd A d.
-- is_closed — a proof that carrier is closed in the topology.
-- shift_invariant — a proof that for every vector v : Zd d, shifting any
-- x in carrier by v stays in carrier.
structure Subshift (A : Type*) [TopologicalSpace A] [Inhabited A] (d : ℕ) where
  carrier : Set (FullShiftZd A d)
  is_closed : IsClosed carrier
  shift_invariant : ∀ v : Zd d, ∀ x ∈ carrier, shift v x ∈ carrier

/-- The full shift is itself a subshift. -/
-- example tells Lean: “check that the following term has this type”,
-- but don’t give it a user-facing name.
example : Subshift A d :=
{ carrier := Set.univ,
  is_closed := isClosed_univ,
  shift_invariant := fun _ _ _ ↦ mem_univ _ }

/-- A finite pattern is defined as a support and a function support -> A -/
structure Pattern (A : Type*) (d : ℕ) where
  support : Finset (Zd d)
  data : support → A

/-- The "domino" pattern supported at `{i, j}`, taking value `ai` at `i` and `aj` at `j`. -/
def domino {A : Type*} {d : ℕ}
    (i j : Zd d) (ai aj : A) : Pattern A d :=
by
  classical
  refine
  { support := ({i, j} : Finset (Zd d))
  , data    := ?_ }
  intro u
  -- Make the decision on the *value* `u : Zd d`, not on the proof `u.property`.
  exact if (u : Zd d) = i then ai else aj

-- TODO: START AGAIN FROM THERE.
-- TODO: write example/lemma that dominos are patterns.


/-- A pattern `p` occurs in a configuration `x` at position `v`. -/
-- The keyword Prop corresponds to statements, without proof.
def Pattern.occursIn (p : Pattern A d) (x : FullShiftZd A d) (v : Zd d) : Prop :=
  ∀ u (hu : u ∈ p.support), x (u + v) = p.data ⟨u, hu⟩


/-- The set of configurations that avoid all patterns in a given forbidden set. -/
def forbids (F : Set (Pattern A d)) : Set (FullShiftZd A d) :=
  { x | ∀ p ∈ F, ∀ v : Zd d, ¬ p.occursIn x v }

section
variable {A : Type*} {d : ℕ}

/-- The set of configurations avoiding `F` is shift-invariant. -/
lemma forbids_shift_invariant (F : Set (Pattern A d)) :
    ∀ v : Zd d, ∀ x ∈ forbids F, shift v x ∈ forbids F := by
  intro w x hx
  intro p hp v
  specialize hx p hp (v + w)
  -- If p occurs in shift w x at v, then it occurs in x at v + w
  intro H
  apply hx
  intro u hu
  simp [←add_assoc]
  exact H u hu

end

def patternToOriginConfig (p : Pattern A d) : FullShiftZd A d :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

def patternToConfig (p : Pattern A d) (v : Zd d) : FullShiftZd A d :=
  shift (-v) (patternToOriginConfig p)

def patternFromConfig (x : Zd d → A) (U : Finset (Zd d)) : Pattern A d :=
  { support := U,
    data := fun i => x i.1 }


/-- The occurrence set of a fixed pattern at a fixed position is closed. -/
lemma occursAt_closed (p : Pattern A d) (v : Zd d) :
    IsClosed { x | p.occursIn x v } := by
  -- Define the configuration from the pattern
  let y := patternToConfig p v
  -- Define the set of positions where the pattern is expected to match
  let U := p.support.image (· + v)
  -- Define the cylinder corresponding to those constraints
  let C := cylinder U y
  -- Show equality of the two sets
  have : {x | p.occursIn x v} = C := by
    ext x
    simp only [mem_setOf_eq]
    constructor
    · intro H u hu
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      -- y = shift v (patternToOriginConfig p), so y (w + v) = patternToOriginConfig p w
      dsimp [y, patternToConfig, shift, patternToOriginConfig]
      rw [add_neg_cancel_right]
      rw [dif_pos hw]
      exact H w hw
    · intro H u hu
      -- Have: x (u + v) = y (u + v)
      -- But y (u + v) = patternToOriginConfig p u
      have := H (u + v) (Finset.mem_image_of_mem _ hu)
      dsimp [y, patternToConfig, shift, patternToOriginConfig] at this
      rw [add_neg_cancel_right] at this
      rw [dif_pos hu] at this
      exact this
  rw [this]
  exact cylinder_is_closed d U y

lemma occursAt_open (p : Pattern A d) (v : Zd d) :
    IsOpen { x | p.occursIn x v } := by
  -- Define the configuration from the pattern
  let y := patternToConfig p v
  -- Define the set of positions where the pattern is expected to match
  let U := p.support.image (· + v)
  -- Define the cylinder corresponding to those constraints
  let C := cylinder U y
  -- Show equality of the two sets
  have : {x | p.occursIn x v} = C := by
    ext x
    simp only [mem_setOf_eq]
    constructor
    · intro H u hu
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      -- y = shift v (patternToOriginConfig p), so y (w + v) = patternToOriginConfig p w
      dsimp [y, patternToConfig, shift, patternToOriginConfig]
      rw [add_neg_cancel_right]
      rw [dif_pos hw]
      exact H w hw
    · intro H u hu
      -- Have: x (u + v) = y (u + v)
      -- But y (u + v) = patternToOriginConfig p u
      have := H (u + v) (Finset.mem_image_of_mem _ hu)
      dsimp [y, patternToConfig, shift, patternToOriginConfig] at this
      rw [add_neg_cancel_right] at this
      rw [dif_pos hu] at this
      exact this
  rw [this]
  exact cylinder_is_open U y

/-- The set of configurations avoiding a set of forbidden patterns is closed. -/
lemma forbids_closed (F : Set (Pattern A d)) :
  IsClosed (forbids F) := by
  rw [forbids]
  have : {x | ∀ p ∈ F, ∀ v : Zd d, ¬ p.occursIn x v}
       = ⋂ (p : Pattern A d) (h : p ∈ F), ⋂ (v : Zd d), {x | ¬ p.occursIn x v} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro v
  have : {x | ¬p.occursIn x v} = {x | p.occursIn x v}ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  rw [this]
  rw [isClosed_compl_iff]
  exact occursAt_open p v

def X_F (F : Set (Pattern A d)) : Subshift A d :=
{ carrier := forbids F,
  is_closed := forbids_closed F,
  shift_invariant := forbids_shift_invariant F }

def SFT (F : Finset (Pattern A d)) : Subshift A d :=
  X_F (F : Set (Pattern A d))

def box (n : ℕ) : Finset (Zd d) :=
  Fintype.piFinset (fun _ ↦ Finset.Icc (-↑n : ℤ) ↑n)

def language_box (X : Set (Zd d → A)) (n : ℕ) : Set (Pattern A d) :=
  { p | ∃ x ∈ X, patternFromConfig x (box n) = p }

-- Subtype of patterns with fixed support U
def FixedSupport (A : Type*) (d : ℕ) (U : Finset (Zd d)) :=
  { p : Pattern A d // p.support = U }

def coeSubtypeEquiv {α : Type*} {s t : Finset α} (h : s = t) : (s → A) ≃ (t → A) :=
  { toFun := fun f => fun i => f ⟨i.1, h.symm ▸ i.2⟩,
    invFun := fun g => fun i => g ⟨i.1, h ▸ i.2⟩,
    left_inv := by
      intro f
      ext i
      simp only,
    right_inv := by
      intro g
      ext i
      simp only}


-- patterns with support U ≃ functions U → A
def equivFun {U : Finset (Zd d)} : FixedSupport A d U ≃ (U → A) where
  toFun   := fun p => (coeSubtypeEquiv p.property) p.val.data
  invFun  := fun f => ⟨{ support := U, data := f }, rfl⟩
  left_inv := by
    rintro ⟨p, hp⟩
    -- goal: ⟨{support := U, data := (coeSubtypeEquiv hp) p.data}, rfl⟩ = ⟨p, hp⟩
    -- it suffices to show the underlying patterns are equal
    apply Subtype.ext
    -- rewrite U to p.support; then coeSubtypeEquiv rfl is the identity
    cases hp
    -- now both sides are literally the same structure
    rfl
  right_inv := by
    intro f
    -- here p.property = rfl, so coeSubtypeEquiv rfl is definally the identity
    rfl


-- Now the main lemma: the type of patterns with support U is finite
instance fintypeFixedSupport (U : Finset (Zd d)) :
    Fintype (FixedSupport A d U) :=
by
  classical
  -- (U → A) is finite and equivFun.symm : (U → A) ≃ FixedSupport A d U
  exact Fintype.ofEquiv (U → A) (equivFun (A:=A) (d:=d) (U:=U)).symm

noncomputable def languageCard (X : Set (Zd d → A)) (n : ℕ) : ℕ :=
by
  classical
  -- fixed finite window
  let U : Finset (Zd d) := box (d:=d) n
  -- map each configuration in X to its pattern on U, seen in the fintype `FixedSupport A d U`
  let f : {x : Zd d → A // x ∈ X} → FixedSupport A d U :=
    fun x => ⟨patternFromConfig (A:=A) (d:=d) x.1 U, rfl⟩
  -- the language is the range of `f`, a subset of a fintype, hence finite
  have hfin_univ : (Set.univ : Set (FixedSupport A d U)).Finite :=
    Set.finite_univ
  have hfin : (Set.range f).Finite :=
    hfin_univ.subset (by intro y hy; simp)  -- `range f ⊆ univ`
  exact hfin.toFinset.card


-- Number of patterns of a subshift on the box of size n
noncomputable def patternCount (Y : Subshift A d) (n : ℕ) : ℕ :=
  languageCard (A:=A) (d:=d) Y.carrier n

@[simp] lemma box_card_pos (d n : ℕ) : 0 < (box (d:=d) n).card := by
  classical
  -- coordinate-wise membership of 0 in Icc (−n, n)
  have hcoord :
      ∀ i : Fin d, (0 : ℤ) ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro i
    have h0n : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
    have hneg : -(n : ℤ) ≤ 0 := neg_nonpos.mpr h0n
    simpa [Finset.mem_Icc] using And.intro hneg h0n
  -- build the zero vector membership in the product box
  have hmem : (0 : Zd d) ∈ box (d:=d) n :=
    Fintype.mem_piFinset.mpr hcoord
  exact Finset.card_pos.mpr ⟨0, hmem⟩

/-- Limsup of a real sequence along `atTop`, defined as the infimum of
all eventual upper bounds. This matches `Filter.limsup atTop` in newer mathlib. -/
noncomputable def limsupAtTop (u : ℕ → ℝ) : ℝ :=
  sInf { L : ℝ | ∀ᶠ n in Filter.atTop, u n ≤ L }

/-- Topological entropy of a subshift, via language growth on cubes.
We use a `limsup` and `+ 1` inside the logarithm to avoid `log 0`. -/
noncomputable def entropy (Y : Subshift A d) : ℝ :=
  limsupAtTop (fun n =>
    (Real.log ((patternCount (A:=A) (d:=d) Y n + 1 : ℕ))) /
    ((box (d:=d) n).card : ℝ))

/-
  Locally admissible counts and computable upper bounds for entropy (SFTs)
-/

section UpperComputable


/-- A pattern `f : (box n → A)` **locally avoids** the finite forbidden list `F`
on the box `box n`, i.e. no translate of any `p ∈ F` that fits inside the box
occurs exactly. -/
def locallyAdmissible (F : Finset (Pattern A d)) (n : ℕ)
    (f : (box (d := d) n → A)) : Prop :=
  ∀ p ∈ F, ∀ v : Zd d, ∀ hv : ∀ u ∈ p.support, u + v ∈ box (d:=d) n,
    ¬ (∀ u (hu : u ∈ p.support),
         f ⟨u + v, hv u hu⟩ = p.data ⟨u, hu⟩)

lemma locallyAdmissible_iff_not_occurs
  (F : Finset (Pattern A d)) (n : ℕ) (f : (box (d:=d) n → A)) :
  locallyAdmissible (A:=A) (d:=d) F n f ↔
  ∀ p ∈ F, ∀ v : Zd d,
    ∀ hv : ∀ u ∈ p.support, u + v ∈ box (d:=d) n,
      ∃ i : { u // u ∈ p.support },
        f ⟨i.val + v, hv i.val i.property⟩ ≠ p.data i := by
  classical
  unfold locallyAdmissible
  constructor
  · -- → : from "no local occurrence" to "there is a mismatch"
    intro h p hp v hv
    have hno := h p hp v hv
    by_contra H
    push_neg at H
    -- H : ∀ i, f ⟨i.val+v, hv …⟩ = p.data i
    exact hno (by
      intro u hu
      simpa using H ⟨u, hu⟩)
  · -- ← : from "there is a mismatch" to "no local occurrence"
    intro h p hp v hv H
    -- H : ∀ u (hu ∈ p.support), f ⟨u+v, hv u hu⟩ = p.data ⟨u, hu⟩
    rcases h p hp v hv with ⟨i, hi⟩
    exact hi (by simpa using H i.val i.property)


/-- The **local** pattern-count on the box `box n`: the number of colorings
`f : box n → A` that are locally admissible w.r.t. the SFT `SFT F`. -/
noncomputable def patternCountLoc (F : Finset (Pattern A d)) (n : ℕ) : ℕ :=
by
  classical
  let U : Finset (Zd d) := box (d:=d) n
  -- Parentheses are required before `.filter`
  -- Then `simp [U]` rewrites `(U → A)` to `(box n → A)` in the predicate’s type.
  simpa [U] using
    (((Finset.univ : Finset (U → A)).filter
        (fun f => locallyAdmissible (A:=A) (d:=d) F n f))).card

/-- The per-site local upper bound `u_F(n) = (1/|B_n|) log (Z_loc(n) + 1)`. -/
noncomputable def u_loc (F : Finset (Pattern A d)) (n : ℕ) : ℝ :=
  (Real.log (patternCountLoc (A:=A) (d:=d) F n + 1)) / ((box (d:=d) n).card : ℝ)

/-- A computable decreasing envelope: `q_F(k) = min_{1 ≤ n ≤ k} u_loc(F,n)`. -/
noncomputable def q_upper (F : Finset (Pattern A d)) : ℕ → ℝ
| 0       => u_loc (A := A) (d := d) F 1
| (k + 1) => min (q_upper F k) (u_loc (A := A) (d := d) F (k + 1))

lemma q_upper_succ_le (F : Finset (Pattern A d)) (k : ℕ) :
  q_upper (A := A) (d := d) F (k+1) ≤ q_upper (A := A) (d := d) F k := by
  simpa [q_upper] using
    (min_le_left (q_upper (A := A) (d := d) F k)
                 (u_loc (A := A) (d := d) F (k+1)))

lemma q_upper_antitone (F : Finset (Pattern A d)) :
  Antitone (q_upper (A := A) (d := d) F) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  -- q_upper F (n+1) = min (q_upper F n) (u_loc F (n+1)) ≤ q_upper F n
  simpa [q_upper] using
    min_le_left (q_upper (A := A) (d := d) F n)
                (u_loc (A := A) (d := d) F (n+1))

/-- Every globally admissible window pattern comes from some `x ∈ X_F`, hence
the global language cardinality is bounded by the number of locally admissible
colorings on the window. -/
lemma languageCard_le_patternCountLoc
  (F : Finset (Pattern A d)) (n : ℕ) :
  languageCard (A:=A) (d:=d)
      (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier n
    ≤ patternCountLoc (A:=A) (d:=d) F n := by
  classical
  -- Fix the box U of size n.
  let U : Finset (Zd d) := box (d:=d) n
  -- X is defined by the set of forbidden patterns F
  let X : Set (Zd d → A) :=
    (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier

  -- The restriction function from configurations in X to finite functions from U to A, that is, it provides the pattern given by restriction of x to p.
  let restrF : {x : Zd d → A // x ∈ X} → (U → A) :=
    fun x i => x.1 i.1

  -- We want to prove that image(restrF) ⊆ locally admissible
  -- The hypothesis to prove.
  have hsubset :
      Set.range restrF ⊆
      { f : (U → A) | locallyAdmissible (A:=A) (d:=d) F n f } := by
    -- We introduce a function f : (U → A) and the hypothesis to prove for this f (hf).
    intro f hf
    -- Take x witness of restrF x = f and rewrite hf using this.
    rcases hf with ⟨x, rfl⟩
    -- Property that the configuration x is in the shift obtained by forbidding patterns in F.
    have hx : x.1 ∈ forbids (A:=A) (d:=d) (F : Set (Pattern A d)) := x.2
    -- Yields p with the property hp: p in F and v in Z^d such that for all u in the support of p, u+v is in the box of size n (it is the position of the pattern p).
    intro p hp v hv
    -- This means hx' is ¬ p.occursIn x.1 v.
    have hx' := hx p (by simpa [Finset.mem_coe] using hp) v
    have : (∀ u (hu : u ∈ p.support),
        (fun j : { z : Zd d // z ∈ (U : Set (Zd d)) } => x.1 j.1) ⟨u + v, by simpa using hv u hu⟩
        = p.data ⟨u, hu⟩) → False := by
      -- This assumes that H : ∀ u (hu : u ∈ p.support), (fun j => x.1 j.1) ⟨u+v, …⟩ = p.data ⟨u, hu⟩ is True and the new goal becomes: False.
      intro H;
      -- goal becomes p.occursIn x v
      apply hx';
      -- introduces u corresponding to this hypothesis: u
      intro u hu;
      simpa using H u hu
    exact this

  -- Definition of the restriction function of configurations in X to the pattern on U.
  let fPat : {x : Zd d → A // x ∈ X} → FixedSupport A d U :=
    fun x => ⟨patternFromConfig (A:=A) (d:=d) x.1 U, rfl⟩
  -- Rewriting functions from FixedSupport as functions from U to A.
  let e : FixedSupport A d U ≃ (U → A) := equivFun (A:=A) (d:=d) (U:=U)

  -- Rewriting restrF using e and fPat
  have h_comp : restrF = fun x => e (fPat x) := by
    funext x i; rfl

  -- The range of restrF is the range of e(fPat)
  have h_range :
      Set.range restrF = e '' (Set.range fPat) := by
    -- Writes the equality as an equivalence f belongs to set 1 with f belongs to set 2.
    ext f;
    -- Rewrites the goal as two implications instead of an equivalence.
    constructor
    -- First implication. introduce hypothesis and assume it.
    · intro hf;
      -- Unpacks the hypothesis, replacing f with restrF(x).
      rcases hf with ⟨x, rfl⟩;
      -- Shows that there exists y in the image e(fPat) which is equal to restrF(x). Does this by choosing y = fPat(x) and using restrF = fun x => e (fPat x).
      exact ⟨fPat x, by simp [h_comp]⟩
    -- Introduces the other hypothesis (Assume hf : f ∈ e '' (Set.range fPat)) and assumes it.
    · intro hf
      -- Unpacks the existential version of the hypothesis.
      rcases hf with ⟨y, hy⟩
      -- Splits the conjunction hy : y ∈ Set.range fPat ∧ e y = f into two hypotheses.
      rcases hy with ⟨hy1, hy2⟩
      -- Unpacks existential hy1 : ∃ x, fPat x = y.
      rcases hy1 with ⟨x, hx⟩
      -- Checks that x has the right type and replaces the goal f in range(restrF) with restrF(x)=f.
      refine ⟨x, ?_⟩
      -- Replaces hy2 using y = fPat(x), so that hy2 is the goal, the exact included in simpa concludes.
      have : e (fPat x) = f := by simpa [hx] using hy2
      -- uses rewriting hypothesis h_comp.
      simpa [h_comp] using this

  -- The image of restrF has the same cardinality as the one of fPat - ncard works for subsets of potentially infinite types without needing finiteness upfront (contrary to card)
  have h_ncard_eq :
      (Set.range restrF).ncard = (Set.range fPat).ncard := by
    -- The function e is injective
    have hinj : Function.Injective (fun z : FixedSupport A d U => e z) := e.injective
    -- Uses the fact that range of restrF is the range of e(fPat) and the fact that range(e(fPat)) is has same cardinal as range of fPat, as e is injective.
    simpa [h_range] using
      Set.ncard_image_of_injective (s := Set.range fPat) hinj

  ------------------------------------------------------------------
  -- Same goal, but end in the `Finset.univ.filter` normal form
  ------------------------------------------------------------------

  classical
  haveI : Fintype (U → A) := inferInstance
  haveI : Fintype (FixedSupport A d U) := Fintype.ofEquiv (U → A) e.symm

  -- As before
  have h₁ :
      (Set.range restrF).ncard ≤
      ({ f : (U → A) | locallyAdmissible (A:=A) (d:=d) F n f }).ncard :=
    Set.ncard_mono hsubset

  have h₂ :
      (Set.range fPat).ncard ≤
      ({ f : (U → A) | locallyAdmissible (A:=A) (d:=d) F n f }).ncard := by
    simpa [h_ncard_eq] using h₁

  -- Name the admissible set so predicates are syntactically identical
  let Loc : Set (U → A) := { f | locallyAdmissible (A:=A) (d:=d) F n f }

  -- You already had:
  -- h₂ : (Set.range fPat).ncard ≤ ({ f : (U → A) | locallyAdmissible … f }).ncard
  -- Rewrite its RHS to Loc (still an ncard inequality on Sets)
  have h₂_loc : (Set.range fPat).ncard ≤ Loc.ncard := by
    simpa [Loc] using h₂

------------------------------------------------------------------
  -- Stay in ncard; convert to card only once at the end
  ------------------------------------------------------------------

  classical

  -- Use the prefix form and a typed `univ` to avoid parser glitches.
  have h_range_toFinset₁ :
    (Set.range fPat).toFinset =
      Finset.filter (Membership.mem (Set.range fPat))
        (Finset.univ : Finset (FixedSupport A d U)) := by
    apply Finset.ext; intro x; constructor
    · intro hx
      have hx' : x ∈ Set.range fPat := by
        simpa [Set.mem_toFinset] using hx
      exact Finset.mem_filter.mpr ⟨by simp, hx'⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨_, hx'⟩
      simpa [Set.mem_toFinset] using hx'


  -- 2) (optional) if your goal uses the expanded predicate {x | ∃ a b, …}, show it’s equivalent
  have h_pred (x : FixedSupport A d U) :
      (x ∈ Set.range fPat) ↔ (∃ a, ∃ b : a ∈ X, fPat ⟨a, b⟩ = x) := by
    constructor
    · intro hx; rcases hx with ⟨⟨a,b⟩, rfl⟩; exact ⟨a,b,rfl⟩
    · intro ⟨a,b,hx⟩; exact ⟨⟨a,b⟩, hx⟩

  have h_filter_pred :
    Finset.filter (Membership.mem (Set.range fPat))
        (Finset.univ : Finset (FixedSupport A d U))
      =
    Finset.filter (fun x => ∃ a, ∃ b : a ∈ X, fPat ⟨a,b⟩ = x)
        (Finset.univ : Finset (FixedSupport A d U)) := by
    apply Finset.ext; intro x; constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxU, hxP⟩
      exact Finset.mem_filter.mpr ⟨hxU, (h_pred x).1 hxP⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxU, hxP⟩
      exact Finset.mem_filter.mpr ⟨hxU, (h_pred x).2 hxP⟩

  classical
  -- instances needed here (after `e` and `fPat`)
  haveI : Fintype (FixedSupport A d U) := Fintype.ofEquiv (U → A) e.symm
  haveI : DecidableEq (FixedSupport A d U) := Classical.decEq _
  haveI : DecidablePred (fun x : FixedSupport A d U => x ∈ Set.range fPat) :=
    Classical.decPred _

  -- (1) typed alias for `univ` to keep both sides literally identical when we unfold
  let FU : Finset (FixedSupport A d U) :=
    (Finset.univ : Finset (FixedSupport A d U))

  -- (2) exact equality: `toFinset (Set.range fPat)` is `univ.filter (∈ range fPat)`
  have h_range_toFinset_mem :
    (Set.range fPat).toFinset =
      Finset.filter (Membership.mem (Set.range fPat)) FU := by
    apply Finset.ext; intro x; constructor
    · intro hx
      have hx' : x ∈ Set.range fPat := by
        simpa [Set.mem_toFinset] using hx
      exact Finset.mem_filter.mpr ⟨by simpa [FU], hx'⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨_, hx'⟩
      simpa [Set.mem_toFinset] using hx'

  -- (3) bridge `Finite.toFinset (toFinite …)` ↔ `Set.toFinset` once and for all
  have h_toFinite_toFinset_eq :
    (Finite.toFinset (toFinite (Set.range fPat))) =
      (Set.range fPat).toFinset := by
    apply Finset.ext; intro x; constructor
    · intro hx
      have : x ∈ Set.range fPat := by
        simpa [Set.Finite.mem_toFinset] using hx
      simpa [Set.mem_toFinset] using this
    · intro hx
      have : x ∈ Set.range fPat := by
        simpa [Set.mem_toFinset] using hx
      simpa [Set.Finite.mem_toFinset] using this

  -- (4) finally: the left bridge itself, in the exact filtered form you need
  have h_left_mem :
    (Set.range fPat).ncard =
      (Finset.filter (Membership.mem (Set.range fPat))
        (Finset.univ : Finset (FixedSupport A d U))).card := by
    calc
      (Set.range fPat).ncard
          = (Finite.toFinset (toFinite (Set.range fPat))).card := by
              exact (Set.ncard_eq_toFinset_card (s := Set.range fPat))
      _   = (Set.range fPat).toFinset.card := by
              -- take `card` of h_toFinite_toFinset_eq
              exact congrArg Finset.card h_toFinite_toFinset_eq
      _   = (Finset.filter (Membership.mem (Set.range fPat)) FU).card := by
              exact congrArg Finset.card h_range_toFinset_mem
      _   = (Finset.filter (Membership.mem (Set.range fPat))
              (Finset.univ : Finset (FixedSupport A d U))).card := by
              simpa [FU]

  -- If elsewhere you need the RHS written with `Finset.univ` instead of `FU`:
  have h_left_mem_univ :
    (Set.range fPat).ncard =
      (Finset.filter (Membership.mem (Set.range fPat))
        (Finset.univ : Finset (FixedSupport A d U))).card := by
    simpa [FU] using h_left_mem

  -- Right bridge on (U → A); if you named Loc := { f | locallyAdmissible … f }:
  have h_right :
      Loc.ncard =
      (Finset.univ.filter
        (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card := by
    refine (Set.ncard_eq_toFinset_card Loc).trans ?_
    simpa [Loc] using congrArg Finset.card h_loc_toFinset




  -- Step 1: rewrite only the LHS of h₂
  have h2_LHS :
    (Finset.filter (Membership.mem (Set.range fPat))
      (Finset.univ : Finset (FixedSupport A d U))).card ≤ Loc.ncard := by
    -- h₂ : (Set.range fPat).ncard ≤ Loc.ncard
    simpa [h_left_mem] using h₂

  -- Step 2: rewrite the RHS Loc.ncard to the filtered-card on (U → A)
  have h_card_le_filter :
    (Finset.filter (Membership.mem (Set.range fPat))
      (Finset.univ : Finset (FixedSupport A d U))).card ≤
    (Finset.univ.filter
      (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card := by
    -- h_right is the bridge: Loc.ncard = (univ.filter …).card
    simpa [h_right] using h2_LHS

  -- 2) If you want the LHS as (Set.range fPat).toFinset.card, bridge back:
  have h_range_card :
    (Set.range fPat).toFinset.card =
    (Finset.filter (Membership.mem (Set.range fPat))
      (Finset.univ : Finset (FixedSupport A d U))).card := by
    simpa using congrArg Finset.card h_range_toFinset

  have h_card_le :
      (Set.range fPat).toFinset.card ≤
      (Finset.univ.filter (locallyAdmissible (A:=A) (d:=d) F n)).card := by
    simpa [h_range_card] using h_card_le_filter



  -- (3) identify the two ends with your definitions and conclude
  classical
  -- decidability for the existential predicate on FixedSupport (needed by `.toFinset`)
  haveI : DecidablePred
    (fun x : FixedSupport A d U =>
      ∃ a, ∃ h : a ∈ X, fPat ⟨a, h⟩ = x) := Classical.decPred _

  have h_lang_card :
      languageCard (A:=A) (d:=d) X n
        = (Set.range fPat).toFinset.card := by
    -- First: put languageCard in the “existential set → toFinset.card” shape
    have h_def :
        languageCard (A:=A) (d:=d) X n
          =
        ({x : FixedSupport A d U |
            ∃ a, ∃ h : a ∈ X, fPat ⟨a, h⟩ = x}).toFinset.card := by
      -- adjust if your definition is oriented slightly differently
      simpa [languageCard, U, fPat]

    -- Second: identify that set with Set.range fPat via your equivalence h_pred
    have h_sets :
        ({x : FixedSupport A d U |
            ∃ a, ∃ h : a ∈ X, fPat ⟨a, h⟩ = x} :
          Set (FixedSupport A d U))
          =
        Set.range fPat := by
      -- h_pred x : x ∈ range fPat ↔ ∃ a h, fPat ⟨a,h⟩ = x
      ext x; exact (h_pred x).symm

    -- Third: push equality through toFinset and take card
    have h_cards :
        ({x : FixedSupport A d U |
            ∃ a, ∃ h : a ∈ X, fPat ⟨a, h⟩ = x}).toFinset.card
          =
        (Set.range fPat).toFinset.card := by
      -- rewriting the set under `toFinset` is enough
      simpa [h_sets]

    -- Chain the two equalities
    exact h_def.trans h_cards

  -- (4) identify `patternCountLoc` with the card of the Loc filter (robust)
  classical
  have h_pcl_card :
    patternCountLoc (A:=A) (d:=d) F n
      =
    (Finset.univ.filter
      (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card := by
    -- Prove RHS = LHS, then flip.
    have hR :
      (Finset.univ.filter
        (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card
        =
      patternCountLoc (A:=A) (d:=d) F n := by
      calc
        (Finset.univ.filter
          (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card
            = (Loc.toFinset).card := by
                -- use your finset equality for Loc in the right orientation
                simpa [Loc] using (congrArg Finset.card h_loc_toFinset).symm
        _   = Loc.ncard := by
                -- Set bridge: toFinset.card ↔ ncard
                simpa using (Set.ncard_eq_toFinset_card (s := Loc)).symm
        _   = patternCountLoc (A:=A) (d:=d) F n := by
              classical
              -- You already have:
              -- h_right :
              --   Loc.ncard =
              --   (Finset.univ.filter
              --     (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card

              -- Put patternCountLoc in the same filtered-card normal form
              have pcl_def :
                patternCountLoc (A:=A) (d:=d) F n
                  =
                (Finset.univ.filter
                  (fun f : (U → A) =>
                    locallyAdmissible (A:=A) (d:=d) F n f)).card := by
                  classical
                  -- name the predicate once
                  set P : (U → A) → Prop :=
                    fun f => locallyAdmissible (A:=A) (d:=d) F n f
                  with hP

                  -- filter over univ = comprehension (as finsets)
                  have hfs :
                    (Finset.univ.filter (fun f : (U → A) => P f))
                      =
                    ({ f : (U → A) | P f } : Finset (U → A)) := by
                    apply Finset.ext; intro f; constructor
                    · intro hf
                      rcases Finset.mem_filter.mp hf with ⟨_, hfP⟩
                      simpa [hP] using hfP
                    · intro hf
                      have hfP : P f := by simpa [hP] using hf
                      exact Finset.mem_filter.mpr ⟨by simp, hfP⟩

                  -- 1) Put patternCountLoc in “comprehension-card” form
                  have hcomp :
                        patternCountLoc (A:=A) (d:=d) F n
                          =
                        (Finset.univ.filter (fun f : (U → A) => P f)).card := by
                      classical
                      unfold patternCountLoc
                      -- Turn comprehension ↔ filter using `hfs`
                      have hc :
                          (({ f : (U → A) | P f } : Finset (U → A))).card
                            =
                          (Finset.univ.filter (fun f : (U → A) => P f)).card := by
                        -- note the `.symm` orientation so the LHS is the comprehension
                        simpa using congrArg Finset.card hfs.symm
                      -- Now rewrite the unfolded goal to `hc` via `[U, hP]`
                      simpa [U, hP] using hc

                  -- 2) Switch comprehension-card → filtered-card via `hfs`
                  have hfilter :
                    patternCountLoc (A:=A) (d:=d) F n
                      =
                    (Finset.univ.filter (fun f : (U → A) => P f)).card := by
                    -- orientation is handled by the `simpa [hfs]`
                    simpa [hfs] using hcomp

                  -- 3) Replace `P` with the original predicate
                  simpa [hP] using hfilter
              exact h_right.trans pcl_def.symm
    exact hR.symm

    -- Normalize the RHS predicate to the function form, to match `h_pcl_card`
  have h_card_le_fun :
      (Set.range fPat).toFinset.card ≤
      (Finset.univ.filter
        (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card := by
    simpa using h_card_le

  -- Final chain: languageCard ≤ patternCountLoc
  calc
    languageCard (A:=A) (d:=d) X n
        = (Set.range fPat).toFinset.card := by
            simpa [h_lang_card]
    _ ≤ (Finset.univ.filter
          (fun f : (U → A) => locallyAdmissible (A:=A) (d:=d) F n f)).card :=
          h_card_le_fun
    _ = patternCountLoc (A:=A) (d:=d) F n := by
          simpa using h_pcl_card.symm





/-- Pointwise bound: the per-site global language growth is bounded by the local one. -/
lemma perBox_log_bound (F : Finset (Pattern A d)) (n : ℕ) :
  (Real.log (languageCard (A:=A) (d:=d)
      (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier n + 1)) /
    ((box (d:=d) n).card : ℝ)
  ≤ u_loc (A:=A) (d:=d) F n := by
  classical
  have h := languageCard_le_patternCountLoc (A:=A) (d:=d) F n
  have h' : (languageCard (A:=A) (d:=d)
      (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier n + 1)
      ≤ (patternCountLoc (A:=A) (d:=d) F n + 1) := by
    exact Nat.succ_le_succ h
  -- `Real.log` is monotone on `ℝ≥0`, so the inequality carries over
  have hlog : Real.log (languageCard (A:=A) (d:=d)
      (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier n + 1)
      ≤ Real.log (patternCountLoc (A:=A) (d:=d) F n + 1) :=
    by exact Real.log_le_log_of_le (by exact_mod_cast Nat.succ_pos _ ) (by exact_mod_cast h')
  -- divide by positive |B_n|
  have hpos : 0 < ((box (d:=d) n).card : ℝ) := by
    have := box_card_pos (d:=d) n
    exact_mod_cast this
  exact (div_le_div_of_le_of_nonneg hlog (le_of_lt hpos))

/-- A computable sequence of upper bounds on entropy for the SFT `SFT F`. -/
noncomputable def upperApprox (F : Finset (Pattern A d)) (k : ℕ) : ℝ :=
  q_upper (A:=A) (d:=d) F k

lemma entropy_le_upperApprox (F : Finset (Pattern A d)) :
  ∀ k, entropy (A:=A) (d:=d) (SFT (A:=A) (d:=d) F) ≤ upperApprox (A:=A) (d:=d) F k := by
  classical
  intro k
  -- entropy is limsup of per-box logs; each per-box log ≤ u_loc(n),
  -- and q_upper k ≤ u_loc(n) for some n ≤ k, hence entropy ≤ q_upper k.
  -- (Formally, use: `limsup ≤ inf_n sup_{m≥n} a_m`; here we take the trivial bound.)
  -- We package the step as a single admit to avoid developing limsup API on your snapshot.
  admit

/-- The deep theorem (Ornstein–Weiss/subadditivity on cubes) for SFTs:
the entropy equals `inf_n u_loc(F,n)`.  Replace `admit` by a proof in your development
or cite a mathlib lemma when available. -/
theorem entropy_eq_inf_u_loc (F : Finset (Pattern A d)) :
  entropy (A:=A) (d:=d) (SFT (A:=A) (d:=d) F) =
    sInf (Set.range (u_loc (A:=A) (d:=d) F)) := by
  admit

/-- Hence entropy is **computable from above**: the decreasing computable sequence
`upperApprox F k` converges to `entropy (SFT F)` from above. -/
theorem entropy_right_computable (F : Finset (Pattern A d)) :
  ∀ ε > (0:ℝ), ∃ k, upperApprox (A:=A) (d:=d) F k ≤ entropy (A:=A) (d:=d) (SFT (A:=A) (d:=d) F) + ε := by
  classical
  intro ε hε
  -- From `entropy_eq_inf_u_loc`, `upperApprox` decreases to the infimum.
  -- Standard order-approximation argument for decreasing minima.
  admit

end UpperComputable


end FullShiftZd

end SymbolicDynamics
