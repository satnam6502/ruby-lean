import Ruby
import Subtractor

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby

-- A COMPARATOR uses a SUBTRACTOR to determine if a > b for two unsigned n-bit inputs.
-- The carry-in to the SUBTRACTOR is set to const0. With cin = 0, the SUBTRACTOR computes:
--   a + 2^n = b + diff + 2^n * borrowOut + 1
-- The borrowOut signal is 1 (true) iff a > b.
def COMPARATOR (n : Nat) (ngt0 : n > 0) : Rel (List.Vector (Bit × Bit) n) Bit :=
  fun ab a_gt_b => ∃ diff, SUBTRACTOR n ngt0 (const0, ab) (diff, a_gt_b)

theorem COMPARATOR_correct : ∀ (n : Nat) (ngt0 : n > 0) (a b : List.Vector Bit n) (a_gt_b : Bit) (t : Nat),
  COMPARATOR n ngt0 (List.Vector.zipWith (fun x y => (x, y)) a b) a_gt_b →
  let a' := vectorToBitVec (List.Vector.map (fun x => x t) a)
  let b' := vectorToBitVec (List.Vector.map (fun x => x t) b)
  (a_gt_b t = true ↔ a'.toNat > b'.toNat) := by
    intro n ngt0 a b a_gt_b t h
    simp only [COMPARATOR] at h
    obtain ⟨diff, h_sub⟩ := h
    have h_eq := SUBTRACTOR_correct n ngt0 const0 a_gt_b a b diff t h_sub
    simp [const0] at h_eq
    set a' := vectorToBitVec (List.Vector.map (fun x => x t) a)
    set b' := vectorToBitVec (List.Vector.map (fun x => x t) b)
    set diff' := vectorToBitVec (List.Vector.map (fun x => x t) diff)
    have ha : a'.toNat < 2 ^ n := a'.isLt
    have hb : b'.toNat < 2 ^ n := b'.isLt
    have hd : diff'.toNat < 2 ^ n := diff'.isLt
    constructor
    · intro h_true
      simp [h_true] at h_eq
      omega
    · intro h_gt
      match hc : a_gt_b t with
      | true => rfl
      | false =>
        exfalso
        simp [hc] at h_eq
        omega

end Ruby
