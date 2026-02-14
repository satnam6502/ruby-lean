import Ruby
import TwoSorter

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby

-- Batcher's bitonic merger is a bitonic merger which takes an input vector of length 2^(n+1).
-- The first half of the input vector, size 2^n, should have increasing values.
-- The second half of the input vector, size 2^n, should have decreasing values.
-- The result of the bitonic merger is a sorted vector of length 2^(n+1), which represents the inputs
-- merged and sorted into increasing order.
def BATCHER_BITONIC_MERGER (n : Nat) (ngt0 : n > 0) := BFLY (TWO_SORTER_FLAT n ngt0)

-- Correctness of Batcher's bitonic merger:
-- Given a bitonic input (first half ascending, second half descending),
-- the output is sorted (non-decreasing).
theorem BATCHER_BITONIC_MERGER_correct : ∀ (n : Nat) (ngt0 : n > 0) (m : Nat)
    (input output : List.Vector (List.Vector Bit n) (2 ^ (m + 1))) (t : Nat),
  let wordVal := fun (v : List.Vector (List.Vector Bit n) (2 ^ (m + 1)))
                     (i : Fin (2 ^ (m + 1))) =>
    (vectorToBitVec (List.Vector.map (fun x => x t) (v.get i))).toNat
  -- Pre-condition: input is bitonic (first half ascending, second half descending)
  (∀ (i j : Fin (2 ^ (m + 1))), i.val ≤ j.val → j.val < 2 ^ m →
    wordVal input i ≤ wordVal input j) →
  (∀ (i j : Fin (2 ^ (m + 1))), 2 ^ m ≤ i.val → i.val ≤ j.val →
    wordVal input j ≤ wordVal input i) →
  -- The merger relates input to output
  BATCHER_BITONIC_MERGER n ngt0 m input output →
  -- Post-condition: output is sorted (non-decreasing)
  (∀ (i j : Fin (2 ^ (m + 1))), i.val ≤ j.val →
    wordVal output i ≤ wordVal output j) := by
    sorry

end Ruby
