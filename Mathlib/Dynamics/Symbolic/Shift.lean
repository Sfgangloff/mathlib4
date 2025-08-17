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
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Defs

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


/-! # Full shift -/

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

/-! # Shift map -/

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

/-! # Cylinders and dimension 0 topology -/

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

/-! # Subshifts and patterns -/

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
  -- In general, `refine e` checks that the expression e has type T, but allow some parts of e
  -- to contain holes (goals) that will be filled later.
  -- refine { ... } starts building the structure, leaving a hole ?_ for the data field.
  -- ?_ is a named hole (technically: a metavariable with a fresh name).
  -- Each occurrence of ?_ is a new, independent goal.
  -- On the other hand, _ is an implicit placeholder.Lean will try to infer it
  -- immediately using type inference and existing information.
  refine
  { support := ({i, j} : Finset (Zd d))
  , data := fun ⟨z, hz⟩ => if z = i then ai else aj }


/-- A pattern `p` occurs in a configuration `x` at position `v`. -/
-- The keyword Prop corresponds to statements, without proof.
def Pattern.occursIn (p : Pattern A d) (x : FullShiftZd A d) (v : Zd d) : Prop :=
  ∀ u (hu : u ∈ p.support), x (u + v) = p.data ⟨u, hu⟩

/-! # Defining subshifts by forbidden patterns -/


/-- The set of configurations that avoid all patterns in a given forbidden set. -/
def forbids (F : Set (Pattern A d)) : Set (FullShiftZd A d) :=
  { x | ∀ p ∈ F, ∀ v : Zd d, ¬ p.occursIn x v }


section
variable {A : Type*} {d : ℕ}

lemma occurs_shift (p : Pattern A d) (x : FullShiftZd A d) (v w : Zd d) :
  Pattern.occursIn p (shift w x) v ↔ Pattern.occursIn p x (v + w) := by
  constructor
  · intro h u hu
    -- The tactic add_assoc helps rewrite (a + b) + c into a + (b+c).
    -- The arrow reverses the tactic, going from a + (b+c) to (a + b) + c.
    simp [← add_assoc]
    exact h u hu
  · intro h u hu
    simp [shift,add_assoc]
    exact h u hu

/-- The set of configurations avoiding `F` is shift-invariant. -/
lemma forbids_shift_invariant (F : Set (Pattern A d)) :
    ∀ v : Zd d, ∀ x ∈ forbids F, shift v x ∈ forbids F := by
  intro w x hx
  intro p hp v
  -- The tactic specialize is a way of applying a hypothesis to some arguments.
  -- Here it is applied to hx: x ∈ forbids F, which means ∀ p ∈ F, ∀ v : Zd d, ¬ p.occursIn x v.
  -- So after this, hx becomes : ¬ p.occursIn x (v+w)
  specialize hx p hp (v + w)
  -- The goal is ¬p.occursIn (shift w x) v.
  -- The keyword contrapose hx assumes the contrary of the goal and tries to prove not hx.
  -- The goal becomes the contrary of hx p.occursIn x (v+w) and hx becomes the contrary of the goal.
  -- Note that contrapose! also simplifies the double negation, using pushneg.
  contrapose! hx
  -- We can use directly occurs_shift in reverse.
  -- While rw [lemma] means rewrite using the equality lemma, rwa [lemma] means
  -- rw [lemmas]; assumption, trying to close the goal using the assumption (implicit).
  rwa [← occurs_shift]
end


/-- The following allows to transform a pattern into a configuration of the full shift
by extending with the default symbol of A, and reciprocally to obtain a pattern by
restriction -/

def patternToOriginConfig (p : Pattern A d) : FullShiftZd A d :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

def patternToConfig (p : Pattern A d) (v : Zd d) : FullShiftZd A d :=
  shift (-v) (patternToOriginConfig p)

def patternFromConfig (x : Zd d → A) (U : Finset (Zd d)) : Pattern A d :=
  { support := U,
    data := fun i => x i.1 }


-- TODO: would be simpler maybe to define occurs at by restriction, as well as cylinder definition
-- so that occurs at is exactly the cylinder.
-- Furthermore, is patternToOriginConfig really needed ?
-- TODO: Rename defs and lemmas.

set_option linter.unusedSectionVars false
lemma occursAt_eq_cylinder (p : Pattern A d) (v : Zd d) :
  { x | p.occursIn x v }
    = cylinder (p.support.image (· + v)) (patternToConfig p v) := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro H u hu
    -- Finset.mem_image: y ∈ s.image f ↔ ∃ x ∈ s, f x = y
    -- The .mp applies the  forwards direction of the equivalence, thus
    -- transforming hu into an existential statement
    -- The tactic obtain destructures data. ⟨...⟩ is constructor notation
    -- for subtypes / sigma types.
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    -- dsimp means definitional simplification - only unfolds definitions.
    dsimp [patternToConfig]
    dsimp [patternToOriginConfig,shift]
    -- Adding v and -v cancels.
    rw [add_neg_cancel_right]
    -- Applies the positive condition in the if then else.
    rw [dif_pos hw]
    exact H w hw
  · intro H u hu
    -- Introduces a hypothesis without a name (it is only used with "this").
    -- Finset.mem_image_of_mem: x in S -> f(x) in f(S).
    have := H (u + v) (Finset.mem_image_of_mem _ hu)
    dsimp [patternToConfig, patternToOriginConfig, shift] at this
    rw [add_neg_cancel_right, dif_pos hu] at this
    exact this

lemma occursAt_closed (p : Pattern A d) (v : Zd d) :
    IsClosed { x | p.occursIn x v } := by
  rw [occursAt_eq_cylinder]
  exact cylinder_is_closed d _ _

lemma occursAt_open (p : Pattern A d) (v : Zd d) :
    IsOpen { x | p.occursIn x v } := by
  rw [occursAt_eq_cylinder]
  exact cylinder_is_open _ _

/-- The set of configurations avoiding a set of forbidden patterns is closed. -/
lemma forbids_closed (F : Set (Pattern A d)) :
  IsClosed (forbids F) := by
  rw [forbids]
  -- Writing forbids F as an intersection.
  have : {x | ∀ p ∈ F, ∀ v : Zd d, ¬ p.occursIn x v}
       = ⋂ (p : Pattern A d) (h : p ∈ F), ⋂ (v : Zd d), {x | ¬ p.occursIn x v} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  -- The following steps reduce the goal to proving that {x | ¬ p.occursIn x v} is closed.
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

/-! Definition of a subshift by forbidden patterns -/
def X_F (F : Set (Pattern A d)) : Subshift A d :=
{ carrier := forbids F,
  is_closed := forbids_closed F,
  shift_invariant := forbids_shift_invariant F }

/-! Definition of subshift of finite type as obtained by a finite set of forbidden patterns -/
def SFT (F : Finset (Pattern A d)) : Subshift A d :=
  X_F (F : Set (Pattern A d))

/-! ## Size n box language and entropy -/

/-! Definition of the box [-n,n]^d -/
def box (n : ℕ) : Finset (Zd d) :=
  -- Finset.Icc a b : integer interval between a and b
  -- ↑n : Z makes the integer n ∈ N into an element of Z.
  Fintype.piFinset (fun _ ↦ Finset.Icc (-↑n : ℤ) ↑n)

/-! The set of patterns on [-n,n]^d which appear in a configuration of X. -/
def language_box (X : Set (Zd d → A)) (n : ℕ) : Set (Pattern A d) :=
  { p | ∃ x ∈ X, patternFromConfig x (box n) = p }

-- Subtype of patterns which corresponds to the ones having (fixed) support U.
def FixedSupport (A : Type*) (d : ℕ) (U : Finset (Zd d)) :=
  -- The notation {x : α // P x} is a subtype, more general than a set defined by a property.
  -- It keeps track of proofs.
  { p : Pattern A d // p.support = U }

-- Patterns with support U ≃ functions U → A
-- The notation ≃ corresponds to a bijective function packed with its inverse.
set_option linter.unnecessarySimpa false
def equivFun {U : Finset (Zd d)} : FixedSupport A d U ≃ (U → A) where
  -- p : { q : Pattern A d // q.support = U }
  -- p.val.data : p.val.support → A
  -- given i : U, turn it into an element of p.support via p.property
  toFun := fun p => fun i =>
    p.val.data ⟨i.1, by simpa [p.property] using i.2⟩
  invFun := fun f => ⟨{ support := U, data := f }, rfl⟩
  left_inv := by
    rintro ⟨p, hp⟩
    -- Subtype.ext says: two subtype elements have the same underlying value,
    -- then they are equal in the subtype.
    apply Subtype.ext
    -- After rewriting U to p.support, the data functions are defeq
    cases hp
    rfl
  right_inv := by
    intro f
    rfl




-- Now the main lemma: the type of patterns with support U is finite
instance fintypeFixedSupport (U : Finset (Zd d)) :
    Fintype (FixedSupport A d U) :=
by
  -- The keyword classical corresponds to a local import of classical
  -- logics axioms (ecluded middle for instance).
  classical
  -- For e an equivalence, e.symm is the reverse equivalence.
  -- Fintype α means Lean can enumerate all elements of α — i.e. α is a finite type.
  -- Fintype.ofEquiv: deduces finiteness of a type from equivalence to another and
  -- finiteness of this other type.
  exact Fintype.ofEquiv (U → A) (equivFun (A:=A) (d:=d) (U:=U)).symm


-- The keyword "concomputable" means “I know this thing cannot be reduced to a computable program,
-- and that’s fine because I only want it for reasoning, not computation.”
noncomputable def languageCard (X : Set (Zd d → A)) (n : ℕ) : ℕ :=
by
  classical
  -- Sets U the finite box of size 2n.
  let U : Finset (Zd d) := box (d:=d) n
  -- map each configuration in X to its pattern on U, seen in the fintype `FixedSupport A d U`
  let f : {x : Zd d → A // x ∈ X} → FixedSupport A d U :=
    fun x => ⟨patternFromConfig (A:=A) (d:=d) x.1 U, rfl⟩
  -- The codomain of `f` is finite.
  have hfin_univ : (Set.univ : Set (FixedSupport A d U)).Finite :=
    Set.finite_univ
  -- Thus the image of f is finite.
  have hfin : (Set.range f).Finite :=
    hfin_univ.subset (by intro y hy; simp)  -- `range f ⊆ univ`
  -- Define the value of languageCard as the cardinal of range f.
  exact hfin.toFinset.card


-- Number of patterns of a subshift on the box of size n
noncomputable def patternCount (Y : Subshift A d) (n : ℕ) : ℕ :=
  languageCard (A:=A) (d:=d) Y.carrier n


-- TODO: START AGAIN FROM THERE.

-- States that the box [-n,n]^d is not empty: this used to divide by its cardinality in the
-- definition of topological entropy.
@[simp] lemma box_card_pos (d n : ℕ) : 0 < (box (d:=d) n).card := by
  classical
  -- The integer interval [-n,n] contains 0.
  have hcoord :
      ∀ i : Fin d, (0 : ℤ) ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro i
    -- Nat.zero_le : ∀ n : ℕ, 0 ≤ n
    --variant of exact that automatically inserts coercions (casts) between related number types.
    -- Here, Lean applies Nat.cast_le (the fact that if a≤b in naturals, then ↑a≤↑b in integers)
    -- to turn the proof of 0≤n in ℕ into a proof of 0≤n in ℤ.
    have h0n : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
    -- neg_nonpos : neg_nonpos : ∀ {a : ℤ}, 0 ≤ a ↔ -a ≤ 0
    have hneg : -(n : ℤ) ≤ 0 := neg_nonpos.mpr h0n
    simp [Finset.mem_Icc]
  -- build the zero vector membership in the product box
  have hmem : (0 : Zd d) ∈ box (d:=d) n :=
    Fintype.mem_piFinset.mpr hcoord
  exact Finset.card_pos.mpr ⟨0, hmem⟩

/-- Limsup of a real sequence along `atTop`, defined as the infimum of
all eventual upper bounds. This matches `Filter.limsup atTop` in newer mathlib. -/
noncomputable def limsupAtTop (u : ℕ → ℝ) : ℝ :=
  -- Filter.atTop means for a neighborhood of infinity.
  -- sInf stands for “set infimum”.
  sInf { L : ℝ | ∀ᶠ n in Filter.atTop, u n ≤ L }

/-- Topological entropy of a subshift, via language growth on cubes.
We use a `limsup` and `+ 1` inside the logarithm to avoid `log 0`. -/
noncomputable def entropy (Y : Subshift A d) : ℝ :=
  limsupAtTop (fun n =>
    (Real.log ((patternCount (A:=A) (d:=d) Y n + 1 : ℕ))) /
    ((box (d:=d) n).card : ℝ))




end FullShiftZd

end SymbolicDynamics
