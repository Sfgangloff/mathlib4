import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Basic
import Mathlib.Dynamics.SymbolicDynamics.Basic

open Set

namespace SymbolicDynamics

/-! # Directions and Wang tiles on Z² -/

/-- Four compass directions. -/
inductive Dir | north | east | south | west
deriving DecidableEq

instance : Fintype Dir := by
  classical
  refine
    { elems := {Dir.north, Dir.east, Dir.south, Dir.west}
      , complete := ?_ } ;
  intro d; cases d <;> simp

/-- A Wang tile over colors `C` is a function from directions to colors. -/
abbrev WangTile (C : Type*) := Dir → C

namespace WangTile
variable {C : Type*}
@[simp] def north (t : WangTile C) : C := t Dir.north
@[simp] def east (t : WangTile C) : C := t Dir.east
@[simp] def south (t : WangTile C) : C := t Dir.south
@[simp] def west (t : WangTile C) : C := t Dir.west
end WangTile

/-! ## Fix the acting group to Z²

We use `Multiplicative (ℤ × ℤ)` so that the existing multiplicative API for subshifts applies.
-/
abbrev Z2 := Multiplicative (ℤ × ℤ)

namespace Z2
/-- The fixed “east” and “north” steps in Z². -/
@[simp] def e1 : Z2 := Multiplicative.ofAdd (1, 0)
@[simp] def e2 : Z2 := Multiplicative.ofAdd (0, 1)
end Z2

/-! # SFT from a finite set of allowed tiles (on Z²) -/

section WangSFT_Z2

variable {C : Type*}
variable [TopologicalSpace C] [DiscreteTopology C] [Inhabited C]
variable [DecidableEq C]  -- colors usually decidable

variable (T : Finset (WangTile C))

/-- Alphabet: the subtype of tiles in `T`. This bakes “∈ T” into the type. -/
abbrev Alphabet := { t : WangTile C // t ∈ T }

namespace Alphabet
variable {T}

noncomputable instance (hT : T.Nonempty) : Inhabited (Alphabet T) := by
  classical
  let t : WangTile C := Classical.choose hT
  have ht : t ∈ T := Classical.choose_spec hT
  exact ⟨⟨t, ht⟩⟩

/-- Discrete topology inherited from the product on `Dir → C`. -/
instance : TopologicalSpace (Alphabet T) := inferInstance
instance : DiscreteTopology (Alphabet T) := inferInstance
end Alphabet

/-- East/West matching. -/
@[simp] def matchesE (a b : Alphabet T) : Prop := a.1 Dir.east = b.1 Dir.west
/-- North/South matching. -/
@[simp] def matchesN (a b : Alphabet T) : Prop := a.1 Dir.north = b.1 Dir.south

/-- Neighbour set with the two fixed Z² steps. -/
@[simp] def Basis : Finset Z2 := ({Z2.e1, Z2.e2} : Finset Z2)

/-- Compatibility predicate used by `NNSFT` on those steps. -/
@[simp] def WangCompat : Z2 → Alphabet T → Alphabet T → Prop :=
  fun s a b =>
    if _ : s = Z2.e1 then matchesE (T:=T) a b
    else if _ : s = Z2.e2 then matchesN (T:=T) a b
    else True

section
variable {C : Type*}
variable (T : Finset (WangTile C))

@[simp] lemma WangCompat_on_stepE (a b : Alphabet T) :
  WangCompat (T:=T) Z2.e1 a b = matchesE (T:=T) a b := by
  simp [WangCompat]

@[simp] lemma WangCompat_on_stepN (a b : Alphabet T) :
  WangCompat (T:=T) Z2.e2 a b = matchesN (T:=T) a b := by
  -- no by_cases needed; the second if-branch reduces by rfl
  simp [WangCompat]
end

/-- The nearest-neighbor Wang SFT on Z² with fixed east/north steps. -/
def NNWang (hT : T.Nonempty) :
    (let _ : Inhabited (Alphabet T) := by
       classical
       exact ⟨⟨Classical.choose hT, Classical.choose_spec hT⟩⟩
     Subshift (Alphabet T) Z2) :=
by
  classical
  -- Provide the instance for the body as well
  letI : Inhabited (Alphabet T) :=
    ⟨⟨Classical.choose hT, Classical.choose_spec hT⟩⟩
  exact
    NNSFT  (A:=Alphabet T) (G:=Z2)
           (S:=Basis)
           (E:=WangCompat (T:=T))


section
variable {C : Type*}
variable [TopologicalSpace C] [DiscreteTopology C] [Inhabited C] [DecidableEq C]
variable (T : Finset (WangTile C))

-- handy finset lemmas for a 2-element set
lemma mem_pair {α} [DecidableEq α] {x a b : α} :
  x ∈ ({a, b} : Finset α) ↔ x = a ∨ x = b := by
  classical
  simp [Finset.mem_insert, Finset.mem_singleton]

lemma not_mem_pair {α} [DecidableEq α] {x a b : α}
    (hx₁ : x ≠ a) (hx₂ : x ≠ b) :
  x ∉ ({a, b} : Finset α) := by
  classical
  -- x ∉ {a,b}  ↔  ¬(x=a ∨ x=b)  ↔  (x≠a ∧ x≠b)
  simpa [mem_pair, not_or] using And.intro hx₁ hx₂

/-- Pointwise membership for the Z² Wang SFT: exactly the E/W and N/S matches. -/
@[simp] lemma mem_NNWang_iff
    {C : Type*} [TopologicalSpace C] [DiscreteTopology C] [Inhabited C] [DecidableEq C]
    (T : Finset (WangTile C)) (hT : T.Nonempty)
    {x : FullShift (Alphabet T) Z2} :
  (let _ : Inhabited (Alphabet T) := by
     classical exact ⟨⟨Classical.choose hT, Classical.choose_spec hT⟩⟩;
   x ∈ (NNWang (T:=T) hT).carrier) ↔
    ∀ g, matchesE (T:=T) (x g) (x (Z2.e1 * g)) ∧
         matchesN (T:=T) (x g) (x (Z2.e2 * g)) := by
  classical
  -- use the same instance as in `NNWang`:
  letI : Inhabited (Alphabet T) :=
    ⟨⟨Classical.choose hT, Classical.choose_spec hT⟩⟩
  -- the two side-conditions that your `mem_NNSFT_iff` asks for:
  have h1 : (1 : Z2) ≠ Z2.e1 := by
    -- assume equality and derive a contradiction
    intro h
    -- push to (ℤ × ℤ)
    have h' : (0 : ℤ × ℤ) = (1, 0) := by
      simpa [Z2.e1] using congrArg Multiplicative.toAdd h
    -- project the first coordinate: 0 = 1 in ℤ
    have : (0 : ℤ) = 1 := by
      simpa using congrArg Prod.fst h'
    exact Int.zero_ne_one this

  -- (1 : Z2) ≠ e2
  have h2 : (1 : Z2) ≠ Z2.e2 := by
    intro h
    have h' : (0 : ℤ × ℤ) = (0,1) := by
      simpa [Z2.e1] using congrArg Multiplicative.toAdd h
    -- project the second coordinate: 0 = 1 in ℤ
    have : (0 : ℤ) = 1 := by
      simpa using congrArg Prod.snd h'
    exact Int.zero_ne_one this
  -- start from the general nearest-neighbour membership characterization
  -- (adjust the arguments order to whatever your `mem_NNSFT_iff` expects):
  have hId : (1 : Z2) ∉ Basis := by
    classical
    -- Basis = {Z2.e1, Z2.e2}
    simpa [Basis] using
      (not_mem_pair (x := (1 : Z2)) (a := Z2.e1) (b := Z2.e2) h1 h2)
  have hx :
  x ∈ (NNSFT (A := Alphabet T) (G := Z2)
              (S := Basis) (E := WangCompat (T := T))).carrier
    ↔ ∀ g s, s ∈ Basis → WangCompat (T := T) s (x g) (x (s * g)) :=
  mem_NNSFT_iff (A := Alphabet T) (G := Z2)
                 (S := Basis) (E := WangCompat (T := T)) (x := x) hId
  -- now simplify membership in the 2-element set `{e1, e2}` and the compatibility
  -- predicate at those two steps:
  -- (no `Finset.mem_pair`; unfold as `insert … {…}`.)
  simpa [NNWang, Basis, WangCompat,
         Finset.mem_insert, Finset.mem_singleton] using hx
end
end WangSFT_Z2
end SymbolicDynamics
