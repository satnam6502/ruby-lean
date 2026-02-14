import Ruby
import Adder

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby

-- A full subtractor cell is a FULL_ADDER with the b input inverted.
-- This exploits the two's complement identity: a - b = a + ~b + 1.
-- The SND (SND INV) combinator inverts just the b component of (cin, (a, b)).
def FULL_SUBTRACTOR := SND (SND INV) ⨾ FULL_ADDER

-- A ripple-borrow subtractor is made by making a COL of FULL_SUBTRACTORs.
-- To compute a - b, the carry-in must be set to const1 (representing the +1
-- in the identity a - b = a + ~b + 1).
-- borrowOut = 1 indicates no borrow (a >= b in unsigned).
def SUBTRACTOR (n : Nat) (ngt0 : n > 0) : Rel (Bit × List.Vector (Bit × Bit) n) (List.Vector Bit n × Bit) :=
    COL ngt0 FULL_SUBTRACTOR


/-
Correctness of the SUBTRACTOR circuit.

The SUBTRACTOR internally inverts the b input before feeding to the FULL_ADDER at each
bit position, so the circuit computes:
  a + ~b + cin = diff + 2^n * borrowOut
where ~b is the bitwise complement of b with value 2^n - 1 - b.

Rearranging to avoid natural number subtraction:
  a + 2^n + cin = b + diff + 2^n * borrowOut + 1

When the carry-in is set to const1 (cin = 1), this gives:
  a + 2^n + 1 = b + diff + 2^n * borrowOut + 1
i.e.  a + 2^n = b + diff + 2^n * borrowOut

So if a ≥ b: borrowOut = 1 and diff = a - b.
   if a < b: borrowOut = 0 and diff = a - b + 2^n (wraps around).
-/
noncomputable section AristotleLemmas

theorem FULL_SUBTRACTOR_eq (cin : Ruby.Bit) (a b : Ruby.Bit) (sum cout : Ruby.Bit) :
  Ruby.FULL_SUBTRACTOR (cin, (a, b)) (sum, cout) ↔
  Ruby.FULL_ADDER (cin, (a, fun t => !(b t))) (sum, cout) := by
    constructor <;> intro h;
    · obtain ⟨ x, hx ⟩ := h;
      unfold Ruby.SND at hx;
      simp_all +decide [ funext_iff, Ruby.INV ];
      convert hx.2 using 1; aesop;
    · use (cin, a, fun t => !b t);
      exact ⟨ by unfold Ruby.SND Ruby.INV; aesop, h ⟩

theorem vectorToBitVec_not (n : Nat) (v : List.Vector Bool n) :
  (Ruby.vectorToBitVec (List.Vector.map (fun x => !x) v)).toNat = 2^n - 1 - (Ruby.vectorToBitVec v).toNat := by
    -- The sum of the terms (if !v[i] then 2^i.val else 0) over all i is (2^n - 1) - sum of 2^i.val where v[i] is true.
    have h_sum_neg : ∑ i : Fin n, (if !v.get i then 2^i.val else 0) = (2^n - 1) - ∑ i : Fin n, (if v.get i then 2^i.val else 0) := by
      have h_sum_neg : ∑ i : Fin n, (if !v.get i then 2^i.val else 0) = ∑ i : Fin n, 2^i.val - ∑ i : Fin n, (if v.get i then 2^i.val else 0) := by
        exact eq_tsub_of_add_eq ( by rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by cases v.get ‹_› <;> simp +decide );
      rw [ h_sum_neg, ← Finset.sum_range ];
      rw [ Nat.geomSum_eq ] <;> norm_num;
    unfold Ruby.vectorToBitVec; simp +decide ;
    convert congr_arg ( · % 2 ^ n ) h_sum_neg using 1;
    · grind +ring;
    · rw [ Nat.mod_eq_of_lt ];
      · rw [ Nat.mod_eq_of_lt ];
        exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( Nat.sub_lt ( by norm_num ) ( by norm_num ) );
      · refine' lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => _ ) _;
        use fun i => 2 ^ ( i : ℕ );
        · split_ifs <;> norm_num;
        · exact Nat.recOn n ( by norm_num ) fun n ih => by norm_num [ Fin.sum_univ_castSucc, pow_succ' ] at * ; linarith;

theorem COL_map_input {α β γ : Type} (n : Nat) (ngt0 : n > 0) (R : Rel (α × β) (γ × α)) (f : β → β) :
  ∀ (cin : α) (v : List.Vector β n) (out : List.Vector γ n × α),
  COL ngt0 (fun (a, b) (c, d) => R (a, f b) (c, d)) (cin, v) out ↔
  COL ngt0 R (cin, List.Vector.map f v) out := by
    -- We'll use induction on `n` to prove the equivalence.
    induction' n with n ih;
    · contradiction;
    · rcases n with ( _ | n ) <;> simp_all +decide [ Ruby.COL ];
      unfold Ruby.BELOW; aesop;

theorem SUBTRACTOR_iff_ADDER_inv (n : Nat) (ngt0 : n > 0) (cin : Ruby.Bit) (a b : List.Vector Ruby.Bit n) (out : List.Vector Ruby.Bit n × Ruby.Bit) :
  Ruby.SUBTRACTOR n ngt0 (cin, List.Vector.zipWith (fun x y => (x, y)) a b) out ↔
  Ruby.ADDER n ngt0 (cin, List.Vector.zipWith (fun x y => (x, fun t => !(y t))) a b) out := by
    have h_sub_add : Ruby.SUBTRACTOR n ngt0 (cin, List.Vector.zipWith (fun x y => (x, y)) a b) out ↔ Ruby.COL ngt0 (fun (a, b) (c, d) => Ruby.FULL_ADDER (a, (b.1, fun t => !b.2 t)) (c, d)) (cin, List.Vector.zipWith (fun x y => (x, y)) a b) out := by
      -- By definition of `FULL_SUBTRACTOR`, we know that `FULL_SUBTRACTOR (cin, (a, b)) (sum, carryOut)` is equivalent to `FULL_ADDER (cin, (a, fun t => !b t)) (sum, carryOut)`.
      have h_eq : ∀ (cin : Ruby.Bit) (a b : Ruby.Bit) (sum cout : Ruby.Bit), Ruby.FULL_SUBTRACTOR (cin, (a, b)) (sum, cout) ↔ Ruby.FULL_ADDER (cin, (a, fun t => !b t)) (sum, cout) := by
        exact fun cin a b sum cout ↦ FULL_SUBTRACTOR_eq cin a b sum cout;
      unfold Ruby.SUBTRACTOR;
      convert Iff.rfl using 3 ; aesop;
    -- Apply the lemma that allows us to map a function over the input vector.
    have h_map : Ruby.COL ngt0 (fun (a, b) (c, d) => Ruby.FULL_ADDER (a, b.1, fun t => !b.2 t) (c, d)) (cin, List.Vector.zipWith (fun x y => (x, y)) a b) out ↔ Ruby.COL ngt0 (fun (a, b) (c, d) => Ruby.FULL_ADDER (a, b) (c, d)) (cin, List.Vector.map (fun (x, y) => (x, fun t => !y t)) (List.Vector.zipWith (fun x y => (x, y)) a b)) out := by
      convert Ruby.COL_map_input n ngt0 _ _ _ _ _ using 1;
      grind;
    convert h_sub_add.trans h_map using 1;
    congr! 2;
    simp +decide [ List.Vector.zipWith, List.Vector.map ]

end AristotleLemmas

theorem SUBTRACTOR_correct : ∀ (n : Nat) (ngt0 : n > 0) (cin borrowOut : Bit) (a b diff : List.Vector Bit n) (t : Nat),
   SUBTRACTOR n ngt0 (cin, List.Vector.zipWith (fun x y => (x, y)) a b) (diff, borrowOut) →
   let a' := vectorToBitVec (List.Vector.map (fun x => x t) a)          -- a' is the BitVec value of a at time t
   let b' := vectorToBitVec (List.Vector.map (fun x => x t) b)          -- b' is the BitVec value of b at time t
   let diff' := vectorToBitVec (List.Vector.map (fun x => x t) diff)    -- diff' is the BitVec value of diff at time t
   let cin' := if cin t then 1 else 0                                    -- cin' as a Nat
   let borrowOut' := if borrowOut t then 1 else 0                        -- borrowOut' as a Nat
   a'.toNat + 2^n + cin' = b'.toNat + diff'.toNat + 2^n * borrowOut' + 1 := by
     intros n ngt0 cin borrowOut a b diff t h_subtractor
     obtain ⟨h_adder, h_inv⟩ : Ruby.ADDER n ngt0 (cin, List.Vector.zipWith (fun x y => (x, fun t => !(y t))) a b) (diff, borrowOut) ∧ True := by
       convert h_subtractor using 1;
       rw [ Ruby.SUBTRACTOR_iff_ADDER_inv ];
       simp +zetaDelta at *;
     have := Ruby.ADDER_correct n ngt0 cin borrowOut a (List.Vector.map (fun x => fun t => !x t) b) diff t ?_ <;> norm_num at *;
     · have h_inv : (Ruby.vectorToBitVec (List.Vector.map (fun x => !x t) b)).toNat = 2^n - 1 - (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) b)).toNat := by
         convert Ruby.vectorToBitVec_not n ( List.Vector.map ( fun x => x t ) b ) using 1;
         congr! 2;
         ext i; simp +decide ;
       grind;
     · convert h_adder using 1;
       simp +zetaDelta at *;
       ext i; simp +decide [ List.Vector.get ] ;
       · simp +decide [ List.Vector.zipWith ];
       · simp +decide [ List.Vector.get ];
         simp +decide [ List.Vector.zipWith ];
         simp +decide [ List.Vector.map ];
         cases b ; aesop


end Ruby
