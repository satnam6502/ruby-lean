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

/-
Correctness of Batcher's bitonic merger:
Given a bitonic input (first half ascending, second half descending),
the output is sorted (non-decreasing).
Helper: the word value of the i-th element of a vector at time t.
-/
def wordVal {n k : Nat} (v : List.Vector (List.Vector Bit n) k) (i : Fin k) (t : Nat) : Nat :=
  (vectorToBitVec (List.Vector.map (fun x => x t) (v.get i))).toNat

-- A vector of words is sorted (non-decreasing by word value at time t).
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
