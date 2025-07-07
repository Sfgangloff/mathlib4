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


open Set Topology

namespace SymbolicDynamics

/-!
  ## Setup
  We fix:
  - a finite alphabet `A` with a discrete topology;
  - a dimension `d : ℕ` representing the ℤ^d lattice.
-/

variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable [TopologicalSpace A] [DiscreteTopology A]
variable {d : ℕ}

/-- The discrete ℤ^d lattice is modeled as functions from `Fin d` to `ℤ`. -/
def Zd (d : ℕ) := Fin d → ℤ

@[instance]
def Zd.decidableEq (d : ℕ) : DecidableEq (Zd d) :=
  inferInstanceAs (DecidableEq (Fin d → ℤ))

/-- Pointwise addition on ℤ^d. -/
instance : Add (Zd d) where
  add := fun u v i ↦ u i + v i

instance : AddCommGroup (Zd d) := Pi.addCommGroup

/-- The full shift space over ℤ^d with alphabet `A`. -/
@[reducible]
def FullShiftZd (A : Type*) (d : ℕ) := Zd d → A

instance : TopologicalSpace (FullShiftZd A d) := Pi.topologicalSpace
instance : Inhabited (FullShiftZd A d) := ⟨fun _ ↦ default⟩

namespace FullShiftZd

/-! ### Shift map -/

/-- The shift action of ℤ^d on the full shift. -/
def shift (v : Zd d) (x : FullShiftZd A d) : FullShiftZd A d :=
  fun n ↦ x (n + v)

/-- Shift by 0 leaves a configuration unchanged. -/
lemma shift_zero (x : FullShiftZd A d) : shift 0 x = x := by
  funext n; simp [shift, add_zero]

/-- Shift composition: shifting by `v` then by `w` is shifting by `v + w`. -/
lemma shift_add (v w : Zd d) (x : FullShiftZd A d) :
    shift (v + w) x = shift v (shift w x) := by
  funext n; simp [shift, add_assoc]

/-- The cylinder set fixing `x` on a finite set `U` of coordinates. -/
@[reducible]
def cylinder (U : Finset (Zd d)) (x : Zd d → A) : Set (FullShiftZd A d) :=
  { y | ∀ i ∈ U, y i = x i }

/-- Membership condition for cylinder sets. -/
lemma mem_cylinder {U : Finset (Zd d)} {x y : Zd d → A} :
    y ∈ cylinder U x ↔ ∀ i ∈ U, y i = x i := by
  unfold cylinder; rfl

lemma cylinder_is_open (U : Finset (Zd d)) (x : Zd d → A) :
  IsOpen (cylinder U x) := by
  let S : Set (FullShiftZd A d) := ⋂ i ∈ U, { y | y i = x i }
  have : cylinder U x = S := by
    ext y
    rw [cylinder, mem_setOf_eq, mem_iInter₂]
    simp only [mem_setOf_eq]
  rw [this]
  apply isOpen_biInter_finset
  intro i _
  -- Now prove {y | y i = x i} is open by writing it as a preimage
  have : { y : FullShiftZd A d | y i = x i } = (fun y ↦ y i) ⁻¹' {x i} := rfl
  rw [this]
  apply Continuous.isOpen_preimage
  · exact continuous_apply i
  · exact isOpen_discrete ({x i} : Set A)

/-- Cylinder sets are also closed. -/
lemma cylinder_is_closed (d : ℕ) (U : Finset (Zd d)) (x : Zd d → A) :
    IsClosed (cylinder U x) := by
  -- The complement of the cylinder is a union over i ∈ U and a ≠ x i of cylinders fixing i to a
  have h : (cylinder U x)ᶜ = ⋃ (i ∈ U) (a ∈ (Finset.univ \ {x i} : Finset A)),
      cylinder {i} (Function.update x i a) := by
    · ext y
      simp only [mem_compl_iff, mem_iUnion, mem_cylinder, Finset.mem_univ, Finset.mem_sdiff,
not_forall, exists_prop]
      constructor
      · intro hy
        push_neg at hy
        obtain ⟨i, hiU, hiy⟩ := hy
        use i, hiU, y i
        constructor
        · simp [hiy]
        · simp [Function.update_apply]
      · rintro ⟨i, hiU, a, ha, hy⟩
        simp only [true_and] at ha
        use i, hiU
        rw [hy]
        simp only [Function.update_apply]
        have hne : a ≠ x i := by
          intro h
          apply ha
          rw [h]
          exact Finset.mem_singleton_self _
        exact hne
        exact Finset.mem_singleton_self i
  have : IsOpen ((cylinder U x)ᶜ) := by
    rw [h]
    apply isOpen_iUnion; intro i
    apply isOpen_iUnion; intro hi
    apply isOpen_iUnion; intro a
    apply isOpen_iUnion; intro ha
    exact cylinder_is_open {i} (Function.update x i a)
  exact isOpen_compl_iff.mp this

/-- The shift map is continuous. -/
lemma shift_continuous (v : Zd d) :
  Continuous (shift v : FullShiftZd A d → FullShiftZd A d) :=
by continuity

/-! ### Subshifts and patterns -/

/-- A subshift is a closed, shift-invariant subset of the full shift. -/
structure Subshift (A : Type*) [TopologicalSpace A] [Inhabited A] (d : ℕ) where
  carrier : Set (FullShiftZd A d)
  is_closed : IsClosed carrier
  shift_invariant : ∀ v : Zd d, ∀ x ∈ carrier, shift v x ∈ carrier

/-- The full shift is itself a subshift. -/
example : Subshift A d :=
{ carrier := Set.univ,
  is_closed := isClosed_univ,
  shift_invariant := fun _ _ _ ↦ mem_univ _ }

/-- A finite pattern with support and associated values. -/
structure Pattern (A : Type*) (d : ℕ) where
  support : Finset (Zd d)
  data : support → A

/-- A pattern `p` occurs in a configuration `x` at position `v`. -/
def Pattern.occursIn (p : Pattern A d) (x : FullShiftZd A d) (v : Zd d) : Prop :=
  ∀ u (hu : u ∈ p.support), x (u + v) = p.data ⟨u, hu⟩

/-- The set of configurations that avoid all patterns in a given forbidden set. -/
def forbids (F : Set (Pattern A d)) : Set (FullShiftZd A d) :=
  { x | ∀ p ∈ F, ∀ v : Zd d, ¬ p.occursIn x v }

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

def patternToOriginConfig (p : Pattern A d) : FullShiftZd A d :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

def patternToConfig (p : Pattern A d) (v : Zd d) : FullShiftZd A d :=
  shift (-v) (patternToOriginConfig p)


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
  Fintype.piFinset (λ _ ↦ Finset.Icc (-↑n : ℤ) ↑n)

-- def language_box (X : Set (FullShiftZd A d)) (n : ℕ) : Set (Pattern A d) :=
--   { p | ∃ (h : p.support = box n), ∃ x ∈ X, ∃ v : Zd d,
--       ∀ i ∈ box n, x (i + v) = p.data ⟨i, Eq.symm h ▸ ‹i ∈ box n›⟩ }


end FullShiftZd

end SymbolicDynamics
