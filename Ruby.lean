/-
  This module defines a DSL for the design and verification of synchronous digital circuits
  inspired by the relational hardware description language Ruby developed by Geraint Jones and
  Mary Sheeran.
-/

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby

abbrev Bit := Nat → Bool

-- A wire that has a constant value of false.
  def const0 (_ : Nat) : Bool := false

-- A wire that has a constant value of true.
  def const1 (_ : Nat) : Bool := true

-- An invertor is a gate that relates the output b to the negation of the input a.
  def INV : Rel (Nat → Bool) (Nat → Bool) := fun a b => ∀ t, b t = !(a t)

example : INV const0 const1 := by simp [INV, const0, const1]

example : INV const1 const0 := by simp [INV, const0, const1]

-- An AND gate is a gate that relates the output c to the logical conjunction of the inputs a and b.
  def AND : Rel (Bit × Bit) Bit := fun (a, b) c => ∀ t, c t = ((a t) && (b t))

example : AND (const0, const0) const0 := by simp [AND, const0]

example : AND (const0, const1) const0 := by simp [AND, const0, const1]

example : AND (const1, const0) const0 := by simp [AND, const0, const1]

example : AND (const1, const1) const1 := by simp [AND, const1]

-- An NAND gate is a gate that relates the output c to the logical negation of the conjunction of the inputs a and b.
  def NAND : Rel (Bit × Bit) Bit := fun (a, b) c => ∀ t, c t = !((a t) && (b t))

-- An OR gate is a gate that relates the output c to the logical disjunction of the inputs a and b.
  def OR : Rel (Bit × Bit) Bit := fun (a, b) c => ∀ t, c t = ((a t) || (b t))

example : OR (const0, const0) const0 := by simp [OR, const0]

example : OR (const0, const1) const1 := by simp [OR, const0, const1]

example : OR (const1, const0) const1 := by simp [OR, const0, const1]

example : OR (const1, const1) const1 := by simp [OR, const1]

-- A NOR gate is a gate that relates the output c to the logical negation of the disjunction of the inputs a and b.
  def NOR : Rel (Bit × Bit) Bit := fun (a, b) c => ∀ t, c t = !((a t) || (b t))

-- An XOR gate is a gate that relates the output c to the logical exclusive-or of the inputs a and b.
  def XOR : Rel (Bit × Bit) Bit :=
    fun (a, b) c => ∀ t, c t = (xor (a t) (b t))

example : XOR (const0, const0) const0 := by simp [XOR, const0]

example : XOR (const0, const1) const1 := by simp [XOR, const0, const1]

example : XOR (const1, const0) const1 := by simp [XOR, const0, const1]

example : XOR (const1, const1) const0 := by simp [XOR, const0, const1]

-- A XNOR gate is a gate that relates the output c to the logical negation of the exclusive-or of the inputs a and b.
  def XNOR : Rel (Bit × Bit) Bit :=
    fun (a, b) c => ∀ t, c t = !(xor (a t) (b t))

-- Define an infix left-to-rightoperator for sequential composition of relations (circuits).
  infixr:60 " ⨾ " => Relation.Comp

-- Parallel composition: (a, c) relates to (b, d) iff R a b ∧ S c d
  def parComp (R : Rel α β) (S : Rel γ δ) : Rel (α × γ) (β × δ) :=
    fun (a, c) (b, d) => R a b ∧ S c d

infixr:55 " ‖ " => parComp

-- Define a NAND gate by serially composing an AND gate and an INV gate.
  def alt_NAND := AND ⨾ INV

-- Prove that the NAND gate has the correct behaviour.
  theorem alt_NAND_correct : ∀ (a b c : Bit) (t : Nat), alt_NAND (a, b) c → c t = !((a t) && (b t)) := by
    intro a b c t h
    simp only [alt_NAND, Relation.Comp, AND, INV] at h
    obtain ⟨d, hd1, hd2⟩ := h
    rw [hd2 t, hd1 t]

def alt2_NAND : Rel ((Nat → Bool) × (Nat → Bool)) (Nat → Bool) := fun (a, b) c => ∃ x, AND (a, b) x ∧ INV x c

-- Define a unit delay element for which the output is related to the input one clock cycle ago.
  -- A default value defines the output at t=0 (i.e. the reset value).
  def DELAY {α : Type} : α → Rel (Nat → α) (Nat → α) :=
    fun resetValue a b => ∀ t, if t = 0 then b 0 = resetValue else b t = a (t - 1)

/-  Define a loop combinator for expressing feedback loops for sequential circuits.
      This combinator relates values (a, b) on the input to a circuit r to (c, d) of the outout of circuit r.
      The combinator works by bending the wire in the second element of the output pair back to the second
      elemment of the input pair i.e. b and d are the same wire.
      r is a circuit that ralates a pair to a pair and it must be contain at least one sequential element
      along the feedback path to represent a valid synchronous circuit.

             ------------------
             |                |
             |   ----------   |
             |   |        |   |
  b :  β     ----|        |---- d : β
                 |   r    |
  a : α      ----|        |---- c : γ
                 |        |
                 ----------
  -/
  def LOOP {α β γ : Type} : (Rel (α × β) (γ × β)) → Rel (α × β) (γ × β) :=
    fun r (a, b) (c, d) => r (a, b) (c, d) ∧ b = d

-- The FORK combinator duplicates the input wire, returning a pair of wires each of which are equal to the input wire.
  def FORK {α : Type} : Rel (α) (α × α) := fun x (y, z) => y = x ∧ z = x

def SWAP {α β : Type} : Rel (α × β) (β × α) := fun (a, b) (c, d) => c = b ∧ d = a

example : FORK const1 (const1, const1) := by simp [FORK]

example : FORK const0 (const0, const0) := by simp [FORK]

-- The FST combinator applies the first higher order circuit argument to the first element of a pair. The second element is left unchanged.
  def FST {α β γ : Type} : Rel α γ → Rel (α × β) (γ × β) := fun r (a, b) (c, d) => r a c ∧ d = b

-- The SND combinator appllies the first higher order circuit argument to the second element of a pair. The first element is left unchanged.
  def SND {α β γ : Type} : Rel β γ → Rel (α × β) (α × γ) := fun r (a, b) (c, d) => r b d ∧ a = c

-- The below combinator places the circuit r below the circuit s, composing them with a vertical wire.
def BELOW {α β γ δ ε ζ θ : Type} : Rel (α × β) (δ × θ) → Rel (θ ×  γ) (ε × ζ) → Rel (α × (β × γ)) ((δ × ε) × ζ) := fun r s (a, (b, c)) ((d, e), f) => ∃ h, r (a, b) (d, h) ∧ s (h, c) (e, f)

-- The COL combinator stamps out n copies of a circuit r, placing them vertically below each other, composing them with vertical wires.
def COL {α β γ : Type} {n : Nat} : n > 0 → Rel (α × β) (γ × α) → Rel (α × List.Vector β n) (List.Vector γ n × α) := fun _ r (a, b) (c, d) => match n with
  | 1 => r (a, List.Vector.get b ⟨0, Nat.zero_lt_one⟩) (List.Vector.get c ⟨0, Nat.zero_lt_one⟩, d)
  | n + 2 => BELOW r (COL (Nat.succ_pos n) r) (a, (List.Vector.head b, List.Vector.tail b)) ((List.Vector.head c, List.Vector.tail c), d)

-- HALVE splits a 2n-element vector into a 2-element vector of n-element halves.
-- Half 0 contains elements at indices 0..n-1, half 1 contains elements at indices n..2n-1.
def HALVE {n : Nat} : Rel (List.Vector α (2 * n)) (List.Vector (List.Vector α n) 2) :=
  fun v halves =>
    (∀ (i : Fin n), (halves.get ⟨0, by omega⟩).get i = v.get ⟨i.val, by omega⟩) ∧
    (∀ (i : Fin n), (halves.get ⟨1, by omega⟩).get i = v.get ⟨n + i.val, by omega⟩)

-- UNHALVE is the inverse of HALVE: it concatenates a 2-element vector of n-element halves
-- back into a single 2n-element vector.
def UNHALVE {n : Nat} : Rel (List.Vector (List.Vector α n) 2) (List.Vector α (2 * n)) :=
  fun halves v =>
    (∀ (i : Fin n), v.get ⟨i.val, by omega⟩ = (halves.get ⟨0, by omega⟩).get i) ∧
    (∀ (i : Fin n), v.get ⟨n + i.val, by omega⟩ = (halves.get ⟨1, by omega⟩).get i)

-- ZIP transposes a 2×n structure into an n×2 structure.
-- Given 2 vectors of length n, it produces n vectors of length 2,
-- where the j-th element of the i-th output vector is the i-th element of the j-th input vector.
def ZIP {n : Nat} : Rel (List.Vector (List.Vector α n) 2) (List.Vector (List.Vector α 2) n) :=
  fun halves zipped =>
    ∀ (i : Fin n) (j : Fin 2),
      (zipped.get i).get j = (halves.get j).get i

-- UNZIP transposes an n×2 structure into a 2×n structure (inverse of ZIP).
def UNZIP {n : Nat} : Rel (List.Vector (List.Vector α 2) n) (List.Vector (List.Vector α n) 2) :=
  fun zipped halves =>
    ∀ (j : Fin 2) (i : Fin n),
      (halves.get j).get i = (zipped.get i).get j

-- Break a vector of length 2 * n into a vector of n sub-vectors each of length 2.
-- Element j of the i-th sub-vector is v[2*i + j].
def CHOP {n : Nat} : Rel (List.Vector α (2 * n)) (List.Vector (List.Vector α 2) n) :=
  fun v pairs =>
    ∀ (i : Fin n) (j : Fin 2),
      (pairs.get i).get j = v.get ⟨2 * i.val + j.val, by omega⟩

-- UNCHOP is the inverse of CHOP: it flattens n sub-vectors of length 2 back into a vector of length 2*n.
def UNCHOP {n : Nat} : Rel (List.Vector (List.Vector α 2) n) (List.Vector α (2 * n)) :=
  fun pairs v =>
    ∀ (i : Fin n) (j : Fin 2),
      v.get ⟨2 * i.val + j.val, by omega⟩ = (pairs.get i).get j

-- MAP lifts a relation r to operate element-wise on vectors.
-- It relates an input vector to an output vector where the relation r holds between
-- each corresponding pair of elements.
def MAP {n : Nat} (r : Rel α β) : Rel (List.Vector α n) (List.Vector β n) :=
  fun v w => ∀ (i : Fin n), r (v.get i) (w.get i)

def RIFFLE {n : Nat} : Rel (List.Vector α (2 * n)) (List.Vector α (2 * n))
  := HALVE ⨾ ZIP ⨾ UNCHOP

def UNRIFFLE {n : Nat} : Rel (List.Vector α (2 * n)) (List.Vector α (2 * n))
  := CHOP ⨾ UNZIP ⨾ UNHALVE

-- TWO applies r independently to each of the two halves of a 2n-element vector.
def TWO {n : Nat} (r : Rel (List.Vector α n) (List.Vector α n)) : Rel (List.Vector α (2 * n)) (List.Vector α (2 * n))
  := HALVE ⨾ MAP r ⨾ UNHALVE

def ILV {n : Nat} (r : Rel (List.Vector α n) (List.Vector α n)) : Rel (List.Vector α (2 * n)) (List.Vector α (2 * n))
  := UNRIFFLE ⨾ TWO r ⨾ RIFFLE

-- CONCAT flattens a vector of n vectors (each of length m) into a single vector of length n*m.
-- Element (i, j) of the input (the j-th element of the i-th inner vector) maps to index i*m + j
-- in the output.
def CONCAT : Rel (List.Vector (List.Vector α m) n) (List.Vector α (n*m)) :=
  fun vv w =>
    ∀ (i : Fin n) (j : Fin m),
      w.get ⟨i.val * m + j.val, by nlinarith [i.isLt, j.isLt]⟩ = (vv.get i).get j

-- EVENS applies a circuit r independently to each adjacent pair of elements in a 2n-element vector.
-- It chops the input into n pairs of 2, applies r to each pair, and flattens back.
def EVENS {n : Nat} (r : Rel (List.Vector α 2) (List.Vector α 2)) : Rel (List.Vector α (2 * n)) (List.Vector α (2 * n)) :=
  CHOP ⨾ MAP r ⨾ UNCHOP

-- BFLY is a butterfly pattern that can be used to implement Batcher's bitonic merger.
-- A degree n=0 butrerfly is the base case, applying just r on 2^(1+n) inputs ie. 2 inputs to 2 outputs.
-- A degree n butterfly takes 2^(1+n) inputs and produces 2^(1+n) outputs.
def BFLY (r : Rel (List.Vector α 2) (List.Vector α 2)) :
    (n : Nat) → Rel (List.Vector α (2 ^ (n + 1))) (List.Vector α (2 ^ (n + 1)))
  | 0 => r
  | n + 1 =>
    have h : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
    h ▸ (ILV (BFLY r n) ⨾ EVENS r)

-- To help specify a theorem about the correctness of the ADDER we define a function that converts a Vector of Bool to a BitVec.
def vectorToBitVec (v : List.Vector Bool n) : BitVec n :=
  let val := Finset.univ.sum (fun (i : Fin n) => if List.Vector.get v i then 2^i.val else 0)
  BitVec.ofNat n val

/-
The value of a BitVec of size 1.
-/
theorem vectorToBitVec_one (x : Bool) (v : List.Vector Bool 1) :
  v = List.Vector.cons x List.Vector.nil →
  (Ruby.vectorToBitVec v).toNat = if x then 1 else 0 := by
    native_decide +revert

/-
The value of a BitVec formed from a cons vector is the head plus twice the tail.
-/
theorem vectorToBitVec_cons {n : Nat} (x : Bool) (xs : List.Vector Bool n) :
  (Ruby.vectorToBitVec (List.Vector.cons x xs)).toNat = (if x then 1 else 0) + 2 * (Ruby.vectorToBitVec xs).toNat := by
    unfold Ruby.vectorToBitVec; norm_num [Fin.sum_univ_succ, pow_succ']; ring_nf
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    norm_num [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _]
    rw [← Finset.mul_sum _ _ _, Nat.add_mod, Nat.mul_mod_mul_left]
    have hlt := Nat.mod_lt (∑ i : Fin n with xs.get i = true, 2 ^ (↑i : ℕ)) (show 0 < 2 ^ n by positivity)
    split_ifs <;> norm_num <;> (rw [Nat.mod_eq_of_lt]; linarith)

/-
Decomposition of vectorToBitVec into head and tail.
-/
theorem vectorToBitVec_head_tail {n : Nat} (v : List.Vector Bool (n + 1)) :
  (Ruby.vectorToBitVec v).toNat = (if List.Vector.head v then 1 else 0) + 2 * (Ruby.vectorToBitVec (List.Vector.tail v)).toNat := by
    convert Ruby.vectorToBitVec_cons _ _;
    cases v ; aesop

/-
Value of empty vector BitVec.
-/
theorem vectorToBitVec_nil (v : List.Vector Bool 0) :
  (Ruby.vectorToBitVec v).toNat = 0 := by
    rfl

/-
Value of singleton vector BitVec using head.
-/
theorem vectorToBitVec_one_head (v : List.Vector Bool 1) :
  (Ruby.vectorToBitVec v).toNat = if List.Vector.head v then 1 else 0 := by
    native_decide +revert

end Ruby
