/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: S. Gangloff
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Constructions
import Mathlib.Logic.Equiv.Defs
import Mathlib.Dynamics.SymbolicDynamics.Basic   -- your group-generic core

/-!
# 1D edge shifts and finite-type presentation via dominoes

We work over `ℤ` (encoded as `Multiplicative ℤ` to reuse the group-generic API).
Given a directed graph on the alphabet `A` (as a relation `E : A → A → Prop`), the **edge
shift** consists of all bi-infinite walks `x : ℤ → A` satisfying `E (x n) (x (n+1))` for
every `n`. Under `[DiscreteTopology A]`, this is a subshift. When `A` is finite and `E`
is decidable, it is an **SFT** obtained by forbidding the dominoes whose edge is not in `E`.
-/

noncomputable section
open Set Topology

namespace SymbolicDynamics
namespace Z1
open Multiplicative

/-- The step element `τ = ofAdd 1` so that the neighbor of `g` is `τ * g`
(i.e. index `n+1` from `n`). -/
-- Multiplicative is a type synonym that lets you reinterpret an
-- additive structure as a multiplicative one.
-- Multiplicative.ofAdd 1 takes 1 from the additive structure and transforms
-- it into an element of the multiplicative one.
-- Multiplicative version of Z is needed as the core API is written for multiplicative groups.
@[simp] def tau : Multiplicative ℤ := Multiplicative.ofAdd 1

/-- Edge shift from an adjacency **relation** `R : A → A → Prop`.
Alphabet is the vertex set `A`; constraint is `R (x g) (x (τ * g))`. -/
def edgeShiftRel
    (A : Type*) [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    (R : A → A → Prop) :
    Subshift A (Multiplicative ℤ) :=
  -- nearest-neighbor SFT with S = {τ} and E ignoring the `s`-argument
  NNSFT (A:=A) (G:=Multiplicative ℤ) ({tau} : Finset (Multiplicative ℤ))
        (fun (_ : Multiplicative ℤ) a b => R a b)

/-- Membership characterization for `edgeShiftRel`. -/
lemma mem_edgeShiftRel_iff
    {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    (R : A → A → Prop)
    {x : FullShift A (Multiplicative ℤ)} :
  x ∈ (edgeShiftRel (A:=A) R).carrier
    ↔ ∀ g : Multiplicative ℤ, R (x g) (x (tau * g)) := by
  classical
  -- side condition for mem_NNSFT_iff: 1 ∉ {τ}
  have hS : (1 : Multiplicative ℤ) ∉ ({tau} : Finset (Multiplicative ℤ)) := by
    -- 1 ≠ τ (apply toAdd and simplify to 0 ≠ 1)
    have hne : (1 : Multiplicative ℤ) ≠ tau := by
      -- Turns the goal into false and assume hne.
      intro h;
      -- congrArg f h turns an equality h : x = y into f x = f y.
      have := congrArg Multiplicative.toAdd h; simp at this
    simpa [Finset.mem_singleton] using hne
  -- now specialize mem_NNSFT_iff and let simp collapse the singleton {τ}
  simpa [edgeShiftRel, Finset.mem_singleton, tau] using
    (mem_NNSFT_iff (A:=A) (G:=Multiplicative ℤ)
      (S := {tau}) (E := fun _ a b => R a b) (x := x) (hS := hS))

/-- Edge shift from a **finite set of allowed edges** `R ⊆ A × A`. -/
def edgeShiftPairs
    (A : Type*) [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    (R : Set (A × A)) :
    Subshift A (Multiplicative ℤ) :=
  edgeShiftRel (A:=A) (fun a b => (a, b) ∈ R)

/-- Membership characterization for `edgeShiftPairs`. -/
lemma mem_edgeShiftPairs_iff
    {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    (R : Set (A × A))
    {x : FullShift A (Multiplicative ℤ)} :
  x ∈ (edgeShiftPairs (A:=A) R).carrier
    ↔ ∀ g : Multiplicative ℤ, (x g, x (tau * g)) ∈ R := by
  classical
  -- `edgeShiftPairs` is just `edgeShiftRel (fun a b => (a,b) ∈ R)`
  simpa [edgeShiftPairs] using
    (mem_edgeShiftRel_iff (A:=A) (R:=fun a b => (a, b) ∈ R) (x:=x))

end Z1
end SymbolicDynamics
