import Ruby
import Comparator
import Mux

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby

def TWO_SORTER (n : Nat) (ngt0 : n > 0) : Rel (List.Vector (Bit × Bit) n) (List.Vector (Bit × Bit) n) :=
  fun ab out =>
    ∃ (a_gt_b not_a_gt_b : Bit),
      COMPARATOR n ngt0 ab a_gt_b ∧
      INV a_gt_b not_a_gt_b ∧
      ∀ (i : Fin n),
        MUX2_1 (a_gt_b, ((ab.get i).1, (ab.get i).2)) (out.get i).1 ∧
        MUX2_1 (not_a_gt_b, ((ab.get i).1, (ab.get i).2)) (out.get i).2

-- Correctness of the TWO_SORTER: for n-bit unsigned inputs a and b, the first output
-- component is min(a, b) and the second output component is max(a, b).
theorem TWO_SORTER_correct : ∀ (n : Nat) (ngt0 : n > 0) (a b : List.Vector Bit n)
    (out : List.Vector (Bit × Bit) n) (t : Nat),
  TWO_SORTER n ngt0 (List.Vector.zipWith (fun x y => (x, y)) a b) out →
  let a' := vectorToBitVec (List.Vector.map (fun x => x t) a)
  let b' := vectorToBitVec (List.Vector.map (fun x => x t) b)
  let min_out := vectorToBitVec (List.Vector.map (fun p => p.1 t) out)
  let max_out := vectorToBitVec (List.Vector.map (fun p => p.2 t) out)
  min_out.toNat = Nat.min a'.toNat b'.toNat ∧
  max_out.toNat = Nat.max a'.toNat b'.toNat := by
  intro n ngt0 a b out t h_two_sorter
  obtain ⟨a_gt_b, not_a_gt_b, h_comparator, h_inv, h_mux⟩ := h_two_sorter;
  -- By definition of `COMPARATOR`, we know that `a_gt_b` is true if and only if `a > b`.
  have h_comparator_true : a_gt_b t = true ↔ (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) a)).toNat > (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) b)).toNat := by
    exact COMPARATOR_correct n ngt0 a b a_gt_b t h_comparator;
  by_cases h : a_gt_b t <;> simp_all +decide [ Ruby.INV ];
  · have h_out : ∀ (i : Fin n), (out.get i).1 t = b.get i t ∧ (out.get i).2 t = a.get i t := by
      intro i; specialize h_mux i; unfold Ruby.MUX2_1 at h_mux; aesop;
    have h_out : List.Vector.map (fun p => p.1 t) out = List.Vector.map (fun x => x t) b ∧ List.Vector.map (fun p => p.2 t) out = List.Vector.map (fun x => x t) a := by
      constructor <;> ext i <;> aesop;
    grind;
  · -- By definition of `MUX2_1`, we know that `out.get i`.1 = a.get i and `out.get i`.2 = b.get i for all `i`.
    have h_mux_eq : ∀ i : Fin n, (out.get i).1 t = a.get i t ∧ (out.get i).2 t = b.get i t := by
      intro i; specialize h_mux i; unfold Ruby.MUX2_1 at h_mux; aesop;
    constructor <;> congr! 1;
    · congr! 1;
      ext i; simp +decide [ h_mux_eq ] ;
    · congr! 1;
      ext i; aesop;

-- TWO_SORTER_FLAT wraps TWO_SORTER to work on a 2-element vector of n-bit words
-- rather than an n-element vector of bit-pairs.
-- It transposes the input (2×n → n×2), applies TWO_SORTER, then transposes back (n×2 → 2×n).
def TWO_SORTER_FLAT (n : Nat) (ngt0 : n > 0) : Rel (List.Vector (List.Vector Bit n) 2)
                                                   (List.Vector (List.Vector Bit n) 2) :=
  fun input output =>
    ∃ (pairs_in pairs_out : List.Vector (Bit × Bit) n),
      -- Zip the two n-bit words into n bit-pairs: pairs_in[i] = (word0[i], word1[i])
      (∀ i : Fin n, pairs_in.get i = ((input.get ⟨0, by omega⟩).get i,
                                       (input.get ⟨1, by omega⟩).get i)) ∧
      -- Apply TWO_SORTER on the bit-pairs
      TWO_SORTER n ngt0 pairs_in pairs_out ∧
      -- Unzip the bit-pairs back into two n-bit words
      (∀ i : Fin n, (output.get ⟨0, by omega⟩).get i = (pairs_out.get i).1) ∧
      (∀ i : Fin n, (output.get ⟨1, by omega⟩).get i = (pairs_out.get i).2)

-- Correctness of TWO_SORTER_FLAT: the output word at index 0 is min(a, b)
-- and the output word at index 1 is max(a, b).
theorem TWO_SORTER_FLAT_correct : ∀ (n : Nat) (ngt0 : n > 0)
    (input output : List.Vector (List.Vector Bit n) 2) (t : Nat),
  TWO_SORTER_FLAT n ngt0 input output →
  let a' := vectorToBitVec (List.Vector.map (fun x => x t) (input.get ⟨0, by omega⟩))
  let b' := vectorToBitVec (List.Vector.map (fun x => x t) (input.get ⟨1, by omega⟩))
  let min_out := vectorToBitVec (List.Vector.map (fun x => x t) (output.get ⟨0, by omega⟩))
  let max_out := vectorToBitVec (List.Vector.map (fun x => x t) (output.get ⟨1, by omega⟩))
  min_out.toNat = Nat.min a'.toNat b'.toNat ∧
  max_out.toNat = Nat.max a'.toNat b'.toNat := by
  intro n ngt0 input output t h
  obtain ⟨pairs_in, pairs_out, h_zip, h_sorter, h_out0, h_out1⟩ := h
  -- Show pairs_in is the zipWith of input words
  have h_pairs : pairs_in = List.Vector.zipWith (fun x y => (x, y))
      (input.get ⟨0, by omega⟩) (input.get ⟨1, by omega⟩) := by
    ext i : 1; rw [h_zip i]; simp +decide [List.Vector.zipWith, List.Vector.get]
  rw [h_pairs] at h_sorter
  -- Apply TWO_SORTER_correct
  have h_correct := TWO_SORTER_correct n ngt0 _ _ pairs_out t h_sorter
  -- Show output vectors equal projected pairs_out
  have hv0 : List.Vector.map (fun x => x t) (output.get ⟨0, by omega⟩) =
             List.Vector.map (fun p => p.1 t) pairs_out := by
    ext i; simp only [List.Vector.get_map]; exact congr_fun (h_out0 i) t
  have hv1 : List.Vector.map (fun x => x t) (output.get ⟨1, by omega⟩) =
             List.Vector.map (fun p => p.2 t) pairs_out := by
    ext i; simp only [List.Vector.get_map]; exact congr_fun (h_out1 i) t
  simp only [hv0, hv1]
  exact h_correct

end Ruby
