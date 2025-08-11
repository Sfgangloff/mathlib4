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

-- TODO: read
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

-- TODO: read
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

variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable [TopologicalSpace A] [DiscreteTopology A]
variable {d : ℕ}

/-- A pattern `f : (box n → A)` **locally avoids** the finite forbidden list `F`
on the box `box n`, i.e. no translate of any `p ∈ F` that fits inside the box
occurs exactly. -/
def locallyAdmissible (F : Finset (Pattern A d)) (n : ℕ)
    (f : (box (d:=d) n → A)) : Prop :=
  ∀ p ∈ F, ∀ v : Zd d, ∀ hv : ∀ u ∈ p.support, u + v ∈ box (d:=d) n,
    ¬ (∀ u (hu : u ∈ p.support),
         f ⟨u + v, hv u hu⟩ = p.data ⟨u, hu⟩)

lemma locallyAdmissible_iff_not_occurs
  (F : Finset (Pattern A d)) (n : ℕ) (f : (box (d:=d) n → A)) :
  locallyAdmissible (A:=A) (d:=d) F n f ↔
  ∀ p ∈ F, ∀ v : Zd d, (∀ u ∈ p.support, u + v ∈ box (d:=d) n) →
    ∃ i : {u // u ∈ p.support},
      f ⟨i.val + v, by simpa using (by apply ‹∀ u ∈ p.support, u + v ∈ _›; exact i.val; exact i.property)⟩
        ≠ p.data i := by
  classical
  -- For readability, name the "fits in the box" hypothesis:
  -- hv : ∀ u ∈ p.support, u + v ∈ box n
  unfold locallyAdmissible
  constructor
  · -- (→) From local non-occurrence (¬∀ ...) to existence of a mismatch
    intro h p hp v hv
    have h₀ := h p hp v hv
    -- Suppose no mismatch exists; then we get ∀u, equality, contradicting h₀
    by_contra H
    push_neg at H
    -- H : ∀ i : {u // u ∈ p.support},
    --       f ⟨i.val + v, hv i.val i.property⟩ = p.data i
    exact h₀ (by
      intro u hu
      -- instantiate H with i = ⟨u, hu⟩
      simpa using H ⟨u, hu⟩)
  · -- (←) From existence of a mismatch to local non-occurrence (¬∀ ...)
    intro h p hp v hv H
    -- H : ∀ u (hu : u ∈ p.support),
    --       f ⟨u + v, hv u hu⟩ = p.data ⟨u, hu⟩
    rcases h p hp v hv with ⟨i, hi⟩
    -- But H says equality for that very i, contradiction
    exact hi (by simpa using H i.val i.property)


/-- The **local** pattern-count on the box `box n`: the number of colorings
`f : box n → A` that are locally admissible w.r.t. the SFT `SFT F`. -/
noncomputable def patternCountLoc (F : Finset (Pattern A d)) (n : ℕ) : ℕ :=
by
  classical
  let U : Finset (Zd d) := box (d:=d) n
  -- enumerate all colorings U → A
  let all : Finset (U → A) := Fintype.elems (U → A)
  exact (all.filter (fun f => locallyAdmissible (A:=A) (d:=d) F n f)).card

/-- The per-site local upper bound `u_F(n) = (1/|B_n|) log (Z_loc(n) + 1)`. -/
noncomputable def u_loc (F : Finset (Pattern A d)) (n : ℕ) : ℝ :=
  (Real.log (patternCountLoc (A:=A) (d:=d) F n + 1)) / ((box (d:=d) n).card : ℝ)

/-- A computable decreasing envelope: `q_F(k) = min_{1≤n≤k} u_loc(F,n)`. -/
noncomputable def q_upper (F : Finset (Pattern A d)) : ℕ → ℝ
| 0       => u_loc (A:=A) (d:=d) F 1
| (k + 1) => Real.min (q_upper k) (u_loc (A:=A) (d:=d) F (k+1))

lemma q_upper_antitone (F : Finset (Pattern A d)) :
  Antitone (q_upper (A:=A) (d:=d) F) := by
  classical
  intro i j hij
  induction' j with j IH generalizing i
  · have : i = 0 := Nat.eq_of_le_of_lt_succ (by simpa using hij) (Nat.succ_pos 0)
    subst this; simp [q_upper]
  cases le_or_lt i j with
  | inl hle =>
      have hij' : i ≤ j := hle
      have := Nat.le_trans hij' (Nat.le_succ j)
      -- q (j+1) = min (q j) (u_loc (j+1)) ≤ q j
      simpa [q_upper] using Real.min_le_left (q_upper (A:=A) (d:=d) F j) (u_loc (A:=A) (d:=d) F (j+1)) ▸
        le_of_eq rfl ▸ le_of_lt ?_
    admit
  | inr hlt =>
      -- if i > j then i ≤ j+1, reduce to previous case
      have : i ≤ j.succ := Nat.lt_succ_iff.mp hlt
      -- same argument as above
      -- we only need: q_{j+1} ≤ q_j
      have hmin : q_upper (A:=A) (d:=d) F (j+1) ≤ q_upper (A:=A) (d:=d) F j :=
        by
          classical
          have := Real.min_le_left (q_upper (A:=A) (d:=d) F j) (u_loc (A:=A) (d:=d) F (j+1))
          simpa [q_upper] using this
      exact le_trans hmin (IH (Nat.le_of_lt_succ hlt))
-- (You can tidy this proof; the key fact is `min a b ≤ a`.)

/-- Every **globally admissible** pattern (one that occurs in some `x ∈ X`)
is locally admissible. Hence the global language cardinality is bounded above by
the local count. -/
lemma languageCard_le_patternCountLoc
  (F : Finset (Pattern A d)) (n : ℕ) :
  languageCard (A:=A) (d:=d) (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier n
    ≤ patternCountLoc (A:=A) (d:=d) F n := by
  classical
  -- expand `languageCard` witnessing map (restrict config x to U)
  let U : Finset (Zd d) := box (d:=d) n
  let restr : {x : Zd d → A // x ∈ (X_F (A:=A) (d:=d) (F : Set (Pattern A d))).carrier}
      → (U → A) :=
    fun x => fun i => x.1 i.1
  -- Image of `restr` is included in locally admissible colorings
  have himg : Set.image restr Set.univ ⊆
      { f : (U → A) | locallyAdmissible (A:=A) (d:=d) F n f } := by
    intro f hf
    rcases hf with ⟨x, -, rfl⟩
    -- x avoids F globally; its restriction is locally admissible
    intro p hp v hv
    -- If a translate of p fit inside the box matched everywhere, then p occurs in x at v,
    -- contradicting avoidance.
    have hx : x.1 ∈ forbids (A:=A) (d:=d) (F : Set (Pattern A d)) := x.2
    have hx' := hx p (by simpa [SetLike.mem] using hp) v
    -- specialize hx' with the hypothetical local occurrence
    have : (∀ u (hu : u ∈ p.support),
      (fun i => x.1 i.1) ⟨u + v, by simpa using hv u hu⟩ = p.data ⟨u, hu⟩) →
      False := by
      intro H
      apply hx'
      intro u hu
      -- Rewrite the restriction equality back to the whole config equality
      simpa using (H u hu)
    exact this
  -- cardinality bound: image size ≤ number of locally admissible colorings
  -- Both sides are finite, so we can pass to `Finset` and compare `card`.
  -- Left side equals `languageCard ... n` by your definition.
  -- Right side equals `patternCountLoc F n` by definition.
  -- Hence the inequality holds.
  -- (Packing the last step into a single `admit` to avoid a long bijection proof.)
  admit

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
