import Ruby
import TwoSorter

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby

/-
Batcher's bitonic merger is a bitonic merger which takes an input vector of length 2^(n+1).
The first half of the input vector, size 2^n, should have increasing values.
The second half of the input vector, size 2^n, should have decreasing values.
The result of the bitonic merger is a sorted vector of length 2^(n+1), which represents the inputs
merged and sorted into increasing order.
-/
def BATCHER_BITONIC_MERGER (n : Nat) (ngt0 : n > 0) := BFLY (TWO_SORTER_FLAT n ngt0)

def twoSorterNat : Rel (List.Vector Nat 2) (List.Vector Nat 2) :=
  fun input output =>
    output.get ⟨0, by omega⟩ = min (input.get ⟨0, by omega⟩) (input.get ⟨1, by omega⟩) ∧
    output.get ⟨1, by omega⟩ = max (input.get ⟨0, by omega⟩) (input.get ⟨1, by omega⟩)

/- A 4-input Batcher's bitonic merger for n-bit words.
   Takes a 4-element vector (2^(1+1) = 4) of Nat values and produces a sorted 4-element vector.
   Unrolling BFLY at degree 1:
     BFLY r 1 = ILV (BFLY r 0) ⨾ EVENS r = ILV r ⨾ EVENS r
   i.e. unriffle, sor
   t each half of 2, riffle, then compare-swap adjacent pairs.
-/
def BATCHER_BITONIC_MERGER_4 :
    Rel (List.Vector Nat 4) (List.Vector Nat 4) :=
  have h : 2 ^ (1 + 1) = 4 := by norm_num
  h ▸ BFLY twoSorterNat 1


/-
  Concrete example: BATCHER_BITONIC_MERGER_4 maps the bitonic input [3, 5, 8, 2]
  to the sorted output [2, 3, 5, 8].

  Input:                 [3, 5, 8, 2]     (bitonic: ascending [3,5,8], descending [8,2])
  After UNRIFFLE:        [3, 8, 5, 2]     (CHOP → UNZIP → UNHALVE)
  After TWO sort:        [3, 8, 2, 5]     (HALVE, sort each half [3,8]→[3,8], [5,2]→[2,5], UNHALVE)
  After RIFFLE:          [3, 2, 8, 5]     (HALVE → ZIP → UNCHOP)
  After EVENS sort:      [2, 3, 5, 8]     (CHOP, sort pairs [3,2]→[2,3], [8,5]→[5,8], UNCHOP)
-/
section BMM4_Example

private def bmm4_input  : List.Vector Nat 4 := ⟨[3, 5, 8, 2], rfl⟩
private def bmm4_output : List.Vector Nat 4 := ⟨[2, 3, 5, 8], rfl⟩

example : BATCHER_BITONIC_MERGER_4 bmm4_input bmm4_output := by
  show (ILV twoSorterNat ⨾ EVENS twoSorterNat) bmm4_input bmm4_output
  -- mid = [3, 2, 8, 5] (after ILV, before EVENS)
  refine ⟨⟨[3, 2, 8, 5], rfl⟩, ?_, ?_⟩
  · -- ILV = UNRIFFLE ⨾ TWO twoSorterNat ⨾ RIFFLE
    -- after_unriffle = [3, 8, 5, 2], after_two = [3, 8, 2, 5]
    refine ⟨⟨[3, 8, 5, 2], rfl⟩, ?_, ⟨[3, 8, 2, 5], rfl⟩, ?_, ?_⟩
    · -- UNRIFFLE = CHOP ⨾ UNZIP ⨾ UNHALVE
      refine ⟨⟨[⟨[3, 5], rfl⟩, ⟨[8, 2], rfl⟩], rfl⟩, ?_, ⟨[⟨[3, 8], rfl⟩, ⟨[5, 2], rfl⟩], rfl⟩, ?_, ?_⟩
      · intro i j; fin_cases i <;> fin_cases j <;> rfl
      · intro j i; fin_cases j <;> fin_cases i <;> rfl
      · exact ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
    · -- TWO = HALVE ⨾ MAP twoSorterNat ⨾ UNHALVE
      refine ⟨⟨[⟨[3, 8], rfl⟩, ⟨[5, 2], rfl⟩], rfl⟩, ?_, ⟨[⟨[3, 8], rfl⟩, ⟨[2, 5], rfl⟩], rfl⟩, ?_, ?_⟩
      · exact ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
      · intro i; fin_cases i <;> exact ⟨by decide, by decide⟩
      · exact ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
    · -- RIFFLE = HALVE ⨾ ZIP ⨾ UNCHOP
      refine ⟨⟨[⟨[3, 8], rfl⟩, ⟨[2, 5], rfl⟩], rfl⟩, ?_, ⟨[⟨[3, 2], rfl⟩, ⟨[8, 5], rfl⟩], rfl⟩, ?_, ?_⟩
      · exact ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
      · intro i j; fin_cases i <;> fin_cases j <;> rfl
      · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · -- EVENS = CHOP ⨾ MAP twoSorterNat ⨾ UNCHOP
    refine ⟨⟨[⟨[3, 2], rfl⟩, ⟨[8, 5], rfl⟩], rfl⟩, ?_, ⟨[⟨[2, 3], rfl⟩, ⟨[5, 8], rfl⟩], rfl⟩, ?_, ?_⟩
    · intro i j; fin_cases i <;> fin_cases j <;> rfl
    · intro i; fin_cases i <;> exact ⟨by decide, by decide⟩
    · intro i j; fin_cases i <;> fin_cases j <;> rfl

end BMM4_Example

/-
Correctness of Batcher's bitonic merger:
Given a bitonic input (first half ascending, second half descending),
the output is sorted (non-decreasing).
Helper: the word value of the i-th element of a vector at time t.
-/
def wordVal {n k : Nat} (v : List.Vector (List.Vector Bit n) k) (i : Fin k) (t : Nat) : Nat :=
  (vectorToBitVec (List.Vector.map (fun x => x t) (v.get i))).toNat

/- A vector of words is sorted (non-decreasing by word value at time t). -/
def IsSorted {n k : Nat} (v : List.Vector (List.Vector Bit n) k) (t : Nat) : Prop :=
  ∀ (i j : Fin k), i.val ≤ j.val → wordVal v i t ≤ wordVal v j t

-- A vector of words is bitonic at time t: first half ascending, second half descending.
def IsBitonic {n m : Nat} (v : List.Vector (List.Vector Bit n) (2 ^ (m + 1))) (t : Nat) : Prop :=
  (∀ (i j : Fin (2 ^ (m + 1))), i.val ≤ j.val → j.val < 2 ^ m →
    wordVal v i t ≤ wordVal v j t) ∧
  (∀ (i j : Fin (2 ^ (m + 1))), 2 ^ m ≤ i.val → i.val ≤ j.val →
    wordVal v j t ≤ wordVal v i t)



-- Base case: TWO_SORTER_FLAT sorts any 2-element input (which is trivially bitonic).
private theorem bfly_base_case (n : Nat) (ngt0 : n > 0)
    (input output : List.Vector (List.Vector Bit n) 2) (t : Nat)
    (h_merger : BATCHER_BITONIC_MERGER n ngt0 0 input output) :
    IsSorted output t := by
  unfold IsSorted wordVal
  have h_correct := TWO_SORTER_FLAT_correct n ngt0 input output t h_merger
  obtain ⟨h_min, h_max⟩ := h_correct
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-
Correctness of Batcher's bitonic merger:
Given a bitonic input (first half ascending, second half descending),
the output is sorted (non-decreasing).
BFLY r (m+1) = h ▸ (ILV (BFLY r m) ⨾ EVENS r)
The proof requires three key properties of Batcher's algorithm:
1. UNRIFFLE applied to a bitonic sequence produces two bitonic subsequences
   (the even-indexed and odd-indexed elements each form a bitonic sequence).
2. By the inductive hypothesis, BFLY r m sorts each bitonic half.
3. After RIFFLE (interleaving the two sorted halves) and EVENS r
   (compare-swap on adjacent pairs), the result is sorted.
   This follows from the "0-1 principle" and properties of bitonic sequences.
-/
theorem BATCHER_BITONIC_MERGER_correct : ∀ (n : Nat) (ngt0 : n > 0) (m : Nat)
    (input output : List.Vector (List.Vector Bit n) (2 ^ (m + 1))) (t : Nat),
  IsBitonic input t →
  BATCHER_BITONIC_MERGER n ngt0 m input output →
  IsSorted output t := by
  intro n ngt0 m
  induction m with
  | zero =>
    intro input output t h_bitonic h_merger
    exact bfly_base_case n ngt0 input output t h_merger
  | succ m ih =>
    intro input output t h_bitonic h_merger
    sorry

end Ruby
