/-
Copyright (c) 2024 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Analysis.SpecialFunctions.Exp


/-!
# Quantum Key Distribution Sifting

Sifting is a step in quantum key distribution post-processing.

It involves discarding those sent-key-symbols (of Alice's raw key) and
detection events (of Bob's raw key) where the preparation basis does not match the detection basis.


## Tags

QKD, quantum, key, distribution, sifting, post-processing

-/


namespace Sifting   ---------------------------------------------------------------------------

open Nat BigOperators Finset Real

@[aesop safe [constructors, cases]]
inductive State where
  | H
  | V
  | P
  | M
  | h
  | v
  | p
  | m
deriving DecidableEq, Inhabited, Fintype

namespace State  ----------------------------------------------------------------------------- State


-- How to print a State
def ofChar : Char -> Option State
  | 'H' => H
  | 'V' => V
  | 'P' => P
  | 'M' => M
  | 'h' => h
  | 'v' => v
  | 'p' => p
  | 'm' => m
  | _ => none

-- How to print a State
def repr : State -> String
  | H => "H"
  | V => "V"
  | P => "P"
  | M => "M"
  | h => "h"
  | v => "v"
  | p => "p"
  | m => "m"

instance instReprState : Repr State where
  reprPrec s _ := State.repr s

instance isntStateToString : ToString State where
  toString s := Repr.reprPrec s 1 |> toString

-- Mapping to Natural numbers (don't need this at all?)
def toNat : State -> Nat
  | H => 0
  | V => 1
  | P => 2
  | M => 3
  | h => 4
  | v => 5
  | p => 6
  | m => 7

def toFin (s : State) : Fin 8 := ⟨toNat s, by cases s <;> decide⟩

def Fin.toState : Fin 8 -> State
  | ⟨0, _⟩ => H
  | ⟨1, _⟩ => V
  | ⟨2, _⟩ => P
  | ⟨3, _⟩ => M
  | ⟨4, _⟩ => h
  | ⟨5, _⟩ => v
  | ⟨6, _⟩ => p
  | ⟨7, _⟩ => m

lemma injective_toFin : Function.Injective toFin := by
  intro s1 s2 _
  cases s1 <;> cases s2 <;> try contradiction; <;> rfl

/-- there are finitely many states -/
instance instFinite : Finite State :=
  Finite.of_injective toFin injective_toFin

example : toFin ∘ Fin.toState = id := by
  funext ⟨n, _⟩
  simp! ; rw [toFin, Sifting.State.Fin.toState.eq_def]
  split <;> simp! <;> case _ h1 => simp at h1; rw [←h1]

example : Fin.toState ∘ toFin = id := by
  funext s;
  simp_all only [Function.comp_apply, id_eq]
  aesop

lemma bijective_tostate_toFin : Function.Bijective (Fin.toState ∘ toFin) := by
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Function.comp_apply]
  apply Eq.refl

def bit : State -> Bool
  | State.H | State.h | State.P | State.p => true
  | State.V | State.v | State.M | State.m => false

def basis : State -> Bool
  | State.H | State.V | State.h | State.v => true
  | State.P | State.M | State.p | State.m => false

def isDecoy : State -> Bool
  | State.H | State.V | State.P | State.M => false
  | State.h | State.v | State.p | State.m => true

def toSignal : State -> State
  | State.h => State.H
  | State.v => State.V
  | State.p => State.P
  | State.m => State.M
  | state => state

abbrev isSameBasis (s t : State) : Bool := (basis s == basis t)
abbrev isSameBit (s t : State) : Bool := (bit s == bit t)
abbrev isError (s t : State) : Bool := (isSameBasis s t) && (bit s != bit t)

@[simp]
theorem toSignal_not_isDecoy (s : State) : (toSignal s).isDecoy = false := by cases s <;> simp!

end State

open State

--  -------------------------------------------------------------------------------------- Counting

def helperCountP
    (v1 v2 : Array State)
    (currcount curr_idx : ℕ)
    (h : v1.size = v2.size)
    (comparator : State -> State -> Bool) :=
  if _ : curr_idx < v1.size then
    have : curr_idx < v2.size := by rw [←h]; assumption  -- proof: index into v2 is valid
    if comparator v1[curr_idx] v2[curr_idx] then
      helperCountP v1 v2 (currcount + 1) (curr_idx + 1) h comparator
    else helperCountP v1 v2 (currcount) (curr_idx + 1) h comparator
  else
    currcount
termination_by v1.size - curr_idx

def countErrors (v1 v2 : Array State) (h : v1.size = v2.size) : Nat :=
  helperCountP v1 v2 0 0 h isError

def countBasisMatches (v1 v2 : Array State) (h : v1.size = v2.size) : Nat :=
  helperCountP v1 v2 0 0 h (fun s t => basis s == basis t)

def countState (v : Array State) (s : State) : Nat :=
  helperCountP v v 0 0 (by rfl) (fun vs _ ↦ vs == s)

def QBER (v1 v2 : Array State) (h : v1.size = v2.size) : ℚ :=
  (countErrors v1 v2 h) / (countBasisMatches v1 v2 h)


-- ----------------------------------------------------------------------------------------- Sifting


def siftBasisHelper
    (v1 bases_like curr_sifted : Array State) (i : ℕ) (h : v1.size = bases_like.size) :=
  if idxvalid : i < v1.size then
    have : i < bases_like.size := by rw [←h]; assumption
    if isSameBasis v1[i] bases_like[i] then
      siftBasisHelper v1 bases_like (curr_sifted ++ #[v1[i]]) (i+1) h
    else
      siftBasisHelper v1 bases_like curr_sifted (i+1) h
  else
    curr_sifted
termination_by v1.size - i

def siftBasis (v1 bases_like : Array State) (h : v1.size = bases_like.size) : Array State :=
  if _ : v1.size = 0 then
    #[]
  else
    siftBasisHelper v1 bases_like #[] 0 h


-- ---------------------------------------------------------------------------------------- Theorems
variable {α : Type*}

@[simp] -- why doesn't this already exist???
lemma ofIdx_zero_Array_cons (v : Array α) (s:α):
  { data := s :: v.data : Array α }[0] = s := by rfl


lemma one_lt_succ_nonzero {b : Nat} (h : b ≠ 0) : 1 < succ b := by
  have : 0 < b := by exact Nat.pos_of_ne_zero h
  linarith

-- TODO more theorems!!!


end Sifting   ---------------------------------------------------------------------------
