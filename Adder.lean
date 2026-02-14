import Ruby

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby

-- TO help verify ADDER is correct, let us first define a function to model a ripple
-- carry adder and prove it correct.

def half_adder : Bool × Bool → Bool × Bool := fun (a, b) => (a && b, xor a b)

def full_adder : Bool × (Bool × Bool) → Bool × Bool := fun (cin, (a, b)) =>
  let (c1, s1) := half_adder (a, b)
  let (c2, sum) := half_adder (cin, s1)
  let cout := c1 || c2
  (cout, sum)

def ripple_carry_adder : (n : Nat) → n > 0 → Bool × List.Vector (Bool × Bool) n →
    List.Vector Bool n × Bool
  | 1, _, (cin, ab) =>
    let (cout, s) := full_adder (cin, ab.get ⟨0, by omega⟩)
    (⟨[s], rfl⟩, cout)
  | n + 2, _, (cin, ab) =>
    let (c0, s0) := full_adder (cin, ab.head)
    let (rest, cout) := ripple_carry_adder (n + 1) (Nat.succ_pos n) (c0, ab.tail)
    (List.Vector.cons s0 rest, cout)

-- A half adder is made by duplicating the input and sending each fork to the parallel composition of AND and XOR.
def HALF_ADDER := FORK ⨾ (AND ‖ XOR)

macro "gate_simp" : tactic => `(tactic| simp [Relation.Comp, parComp, HALF_ADDER, FORK, AND, XOR, OR, const0, const1])

example : HALF_ADDER (const0, const0) (const0, const0) := by gate_simp

example : HALF_ADDER (const0, const1) (const0, const1) := by gate_simp

example : HALF_ADDER (const1, const0) (const0, const1) := by gate_simp

example : HALF_ADDER (const1, const1) (const1, const0) := by gate_simp

theorem HALF_ADDER_correct : ∀ (a b sum carry : Nat → Bool), HALF_ADDER (a, b) (carry, sum) →
       (∀ t, (sum t = xor (a t) (b t)) ∧ (carry t = ((a t) && (b t)))) := by
    intro a b sum carry h
    simp only [HALF_ADDER, Relation.Comp, parComp, FORK, AND, XOR] at h
    obtain ⟨⟨x1, x2⟩, ⟨rfl, rfl⟩, hAnd, hXor⟩ := h
    intro t
    exact ⟨hXor t, hAnd t⟩

-- To help define a full-adder in point-free style we need combinators to perform some wire reorganization.
  def REORG1 {α β γ : Type} : Rel (α × (β × γ)) (β × (α × γ)) := fun (cin, (c1, s1)) (c1', (cin', s1')) => c1 = c1' ∧ cin = cin' ∧ s1 = s1'

def REORG2 {α β γ : Type} : Rel (α × (β × γ)) ((α × β) × γ) := fun (c1, (c2, sum)) ((c1', c2'), sum') => c1 = c1' ∧ c2 = c2' ∧ sum = sum'

example : REORG1 (0, (1, 2)) (1, (0, 2)) := by simp [REORG1]

-- Swap the two carries
  example : REORG2 (0, (1, 2)) ((0, 1), 2) := by simp [REORG2]

-- Move two carries into first tuple

/-
Arithmetic correctness of a full adder in terms of natural numbers.
-/
theorem full_adder_bool_arith (a b cin sum cout : Bool) :
  (sum = xor a (xor b cin)) →
  (cout = ((a && b) || (cin && (xor a b)))) →
  (if a then 1 else 0) + (if b then 1 else 0) + (if cin then 1 else 0) =
  (if sum then 1 else 0) + 2 * (if cout then 1 else 0) := by
    grind

  -- A full-adder can be defined by composing two half-adders and then composing with an OR gate.
  def FULL_ADDER := SND HALF_ADDER ⨾ REORG1 ⨾ SND HALF_ADDER ⨾ REORG2 ⨾ FST OR ⨾ SWAP

-- example : FULL_ADDER (const0, (const0, const0)) (const0, const0) := by simp [Relation.Comp, parComp, HALF_ADDER, FULL_ADDER, REORG1, REORG2, FST, SND, OR, const0]

  -- A helper that decomposes FULL_ADDER into its internal half-adder wires.
  private theorem full_adder_wires :
      ∀ (a b cin sum carryOut : Nat → Bool),
      FULL_ADDER (cin, (a, b)) (sum, carryOut) →
      ∃ c1 s1 c2, HALF_ADDER (a, b) (c1, s1) ∧ HALF_ADDER (cin, s1) (c2, sum) ∧ OR (c1, c2) carryOut := by
    intro a b cin sum carryOut h
    simp only [FULL_ADDER, Relation.Comp] at h
    obtain ⟨⟨w1a, w1b, w1c⟩, hSND1, ⟨w2a, w2b, w2c⟩, hREORG1, ⟨w3a, w3b, w3c⟩, hSND2,
            ⟨⟨w4a, w4b⟩, w4c⟩, hREORG2, ⟨w5a, w5b⟩, hFST, hSWAP⟩ := h
    simp only [SND] at hSND1 hSND2
    simp only [REORG1] at hREORG1
    simp only [REORG2] at hREORG2
    simp only [FST] at hFST
    simp only [SWAP] at hSWAP
    obtain ⟨hHA1, rfl⟩ := hSND1
    obtain ⟨rfl, rfl, rfl⟩ := hREORG1
    obtain ⟨hHA2, rfl⟩ := hSND2
    obtain ⟨rfl, rfl, rfl⟩ := hREORG2
    obtain ⟨hOR, rfl⟩ := hFST
    obtain ⟨rfl, rfl⟩ := hSWAP
    exact ⟨w1b, w1c, w3b, hHA1, hHA2, hOR⟩

-- A proof that the FULL_ADDER circuit implements the correct behaviour of a full-adder.
  theorem FULL_ADDER_sum_correct : ∀ (a b cin sum carryOut : Nat → Bool) (t : Nat), FULL_ADDER (cin, (a, b)) (sum, carryOut) →
        sum t      = xor (a t) (xor (b t) (cin t)) := by
    intro a b cin sum carryOut t h
    obtain ⟨c1, s1, c2, hHA1, hHA2, _⟩ := full_adder_wires a b cin sum carryOut h
    have h1 := HALF_ADDER_correct a b s1 c1 hHA1
    have h2 := HALF_ADDER_correct cin s1 sum c2 hHA2
    rw [(h2 t).1, (h1 t).1]
    cases a t <;> cases b t <;> cases cin t <;> rfl

  theorem FULL_ADDER_carry_correct : ∀ (a b cin sum carryOut : Nat → Bool) (t : Nat), FULL_ADDER (cin, (a, b)) (sum, carryOut) →
       carryOut t = (a t && b t) || (cin t) && (xor (a t) (b t)) := by
    intro a b cin sum carryOut t h
    obtain ⟨c1, s1, c2, hHA1, hHA2, hOR⟩ := full_adder_wires a b cin sum carryOut h
    have h1 := HALF_ADDER_correct a b s1 c1 hHA1 t
    have h2 := HALF_ADDER_correct cin s1 sum c2 hHA2 t
    simp only [OR] at hOR
    simp only [hOR t, h1.1, h1.2, h2.2]
    set x := a t; set y := b t; set z := cin t
    cases x <;> cases y <;> cases z <;> rfl

  -- A proof that the FULL_ADDER circuit implements the correct behaviour of a full-adder.
  theorem FULL_ADDER_correct : ∀ (a b cin sum carryOut : Nat → Bool), FULL_ADDER (cin, (a, b)) (sum, carryOut) →
       (∀ t, sum t      = xor (a t) (xor (b t) (cin t)) ∧
             carryOut t = (a t && b t) || (cin t) && (xor (a t) (b t))) := by
    intro a b cin sum carryOut h t
    obtain ⟨c1, s1, c2, hHA1, hHA2, hOR⟩ := full_adder_wires a b cin sum carryOut h
    have h1 := HALF_ADDER_correct a b s1 c1 hHA1 t
    have h2 := HALF_ADDER_correct cin s1 sum c2 hHA2 t
    simp only [OR] at hOR
    simp only [hOR t, h1.1, h1.2, h2.1, h2.2]
    set x := a t; set y := b t; set z := cin t
    cases x <;> cases y <;> cases z <;> rfl

def FULL_ADDER_alt : Rel ((Nat → Bool) × ((Nat → Bool) × (Nat → Bool))) ((Nat → Bool) × (Nat → Bool)) := fun (cin, (a, b)) (sum, carryOut) =>
      ∃ c1 c2 s1, HALF_ADDER (a, b) (c1, s1) ∧
                  HALF_ADDER (cin, s1) (c2, sum) ∧
                  OR (c1, c2) carryOut

theorem FULL_ADDER_alt_correct : ∀ (a b cin sum carryOut : Nat → Bool) (t : Nat), FULL_ADDER_alt (cin, (a, b)) (sum, carryOut) →
       (sum t = xor (a t) (xor (b t) (cin t))) ∧ (carryOut t = ((a t && b t) || ((cin t) && (xor (a t) (b t))))) := by
    intro a b cin sum carryOut t h
    simp only [FULL_ADDER_alt] at h
    obtain ⟨c1, c2, s1, hHA1, hHA2, hOR⟩ := h
    have h1 := HALF_ADDER_correct a b s1 c1 hHA1
    have h2 := HALF_ADDER_correct cin s1 sum c2 hHA2
    simp only [OR] at hOR
    constructor
    · rw [(h2 t).1, (h1 t).1]
      cases a t <;> cases b t <;> cases cin t <;> rfl
    · rw [hOR t, (h1 t).2, (h2 t).2, (h1 t).1]

-- A ripple-carry adder is made by making a COL of FULL_ADDERs.
/-

│
                                  │ carryOut
                                  │
                               ┌──┴──────────┐
                               │             │
      aₙ₋₁ bₙ₋₁ ──────────────→ │ FULL_ADDER  │──→ sumₙ₋₁
                               │  (bit n-1)  │
                               └──┬──────────┘
                                  │
                                  │ carry
                                  │
                                  ⋮
                                  │
                               ┌──┴──────────┐
                               │             │
        a₂  b₂  ──────────────→│ FULL_ADDER  │──→ sum₂
                               │   (bit 2)   │
                               └──┬──────────┘
                                  │
                                  │ carry
                                  │
                               ┌──┴──────────┐
                               │             │
        a₁  b₁  ──────────────→│ FULL_ADDER  │──→ sum₁
                               │   (bit 1)   │
                               └──┬──────────┘
                                  │
                                  │ carry
                                  │
                               ┌──┴──────────┐
                               │             │
        a₀  b₀  ──────────────→│ FULL_ADDER  │──→ sum₀
                               │   (bit 0)   │
                               └──┬──────────┘
                                  │
                                  │ cin
                                  │
                                  ▲


Key:
- Carry flows upward from cin (bottom) through each stage
- LSB (bit 0) at bottom, MSB (bit n-1) at top
- Each FULL_ADDER: (cin, (a, b)) → (cout, sum)
- Final carryOut emerges from top (overflow bit)
-/

def ADDER (n : Nat) (ngt0 : n > 0) : Rel (Bit × List.Vector (Bit × Bit) n) (List.Vector Bit n × Bit) :=
    COL ngt0 FULL_ADDER

/-
Correctness of 1-bit ADDER.
-/
theorem ADDER_correct_1 (cin carryOut : Bit) (a b sum : List.Vector Bit 1) (t : Nat) :
   ADDER 1 Nat.zero_lt_one (cin, List.Vector.zipWith (fun x y => (x, y)) a b) (sum, carryOut) →
   let a' := vectorToBitVec (List.Vector.map (fun x => x t) a)
   let b' := vectorToBitVec (List.Vector.map (fun x => x t) b)
   let sum' := vectorToBitVec (List.Vector.map (fun x => x t) sum)
   let cin' := if cin t then 1 else 0
   let carryOut' := if carryOut t then 1 else 0
   a'.toNat + b'.toNat + cin' = sum'.toNat + 2^1 * carryOut' := by
     intro h
     obtain ⟨h_sum, h_carry⟩ := h;
     obtain ⟨ h_sum, h_carry ⟩ := h_carry; obtain ⟨ h_sum', h_carry' ⟩ := h_sum; obtain ⟨ h_sum'', h_carry'' ⟩ := h_carry; obtain ⟨ h_sum''', h_carry''' ⟩ := h_carry'; simp_all +decide ;
     rcases a with ⟨ _ | ⟨ a, _ | ⟨ a, _ | a ⟩ ⟩ ⟩ <;> rcases b with ⟨ _ | ⟨ b, _ | ⟨ b, _ | b ⟩ ⟩ ⟩ <;> simp_all +decide [ List.Vector.zipWith ];
     all_goals cases ‹List.length _ = 1›;
     · contradiction;
     · rcases h_sum with ⟨ c, d, e ⟩ ; rcases h_sum'' with ⟨ c', d', e' ⟩ ; simp_all +decide [ Relation.Comp, Ruby.SND, Ruby.FST, Ruby.HALF_ADDER, Ruby.OR, Ruby.SWAP ] ;
       rcases h_sum' with ⟨ a, b, c, d, h₁, h₂ ⟩ ; rcases h_carry'' with ⟨ h₃, a', b', c', ⟨ ⟨ ⟨ a'', b'', c'', d'', h₄, h₅ ⟩, rfl ⟩, a''', b''', h₆, h₇ ⟩ ⟩ ; simp_all +decide [Ruby.FORK,
         Ruby.parComp, Ruby.AND, Ruby.XOR] ;
       rcases h₆ with ⟨ h₆, h₇ ⟩ ; rcases h₃ with ⟨ h₈, h₉ ⟩ ; simp_all +decide ;
       rcases sum with ⟨ _ | ⟨ sum, _ | ⟨ sum, _ | sum ⟩ ⟩ ⟩ <;> simp_all +decide [ List.Vector.map ] ;
       · contradiction;
       · simp_all +decide [ List.Vector.head, Ruby.vectorToBitVec ];
         simp_all +decide [ List.Vector.get ];
         grind;
       · grind;
       · grind +ring;
     · grind +ring;
     · grind +ring

/-
Inductive step for ADDER correctness.
-/
theorem ADDER_correct_step (n : Nat) (ngt0 : n > 0) :
  (∀ (cin carryOut : Bit) (a b sum : List.Vector Bit n) (t : Nat),
     ADDER n ngt0 (cin, List.Vector.zipWith (fun x y => (x, y)) a b) (sum, carryOut) →
     (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) a)).toNat +
     (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) b)).toNat +
     (if cin t then 1 else 0) =
     (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) sum)).toNat +
     2 ^ n * (if carryOut t then 1 else 0)) →
  ∀ (cin carryOut : Bit) (a b sum : List.Vector Bit (n + 1)) (t : Nat),
    ADDER (n + 1) (Nat.succ_pos n) (cin, List.Vector.zipWith (fun x y => (x, y)) a b) (sum, carryOut) →
    (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) a)).toNat +
    (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) b)).toNat +
    (if cin t then 1 else 0) =
    (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) sum)).toNat +
    2 ^ (n + 1) * (if carryOut t then 1 else 0) := by
      intro h cin carryOut a b sum t h_adder
      -- Decompose the (n+1)-bit ADDER into a FULL_ADDER for the head and an n-bit ADDER for the tail.
      obtain ⟨c1, h_full_adder⟩ : ∃ c1, FULL_ADDER (cin, (List.Vector.head a, List.Vector.head b)) (List.Vector.head sum, c1) ∧ ADDER n ngt0 (c1, List.Vector.zipWith (fun x y => (x, y)) (List.Vector.tail a) (List.Vector.tail b)) (List.Vector.tail sum, carryOut) := by
        rcases a with ⟨ _ | ⟨ a_head, a_tail ⟩ ⟩ <;> rcases b with ⟨ _ | ⟨ b_head, b_tail ⟩ ⟩ <;> norm_num at * <;>
          try cases ‹ [].length = n + 1 ›
        unfold ADDER at h_adder; rcases n with ( _ | n ) <;> simp_all +decide [ Ruby.COL ]
        · contradiction
        · unfold Ruby.BELOW at h_adder; aesop
      -- Apply the full adder correctness theorem to get the equation for the head.
      have h_head : (if List.Vector.head a t then 1 else 0) + (if List.Vector.head b t then 1 else 0) + (if cin t then 1 else 0) = (if List.Vector.head sum t then 1 else 0) + 2 * (if c1 t then 1 else 0) := by
        have := h_full_adder.1;
        obtain ⟨ h₁, h₂, h₃ ⟩ := full_adder_wires _ _ _ _ _ this;
        rcases h₃ with ⟨ c2, h₃, h₄, h₅ ⟩ ; simp_all +decide [ Ruby.HALF_ADDER, Ruby.OR ] ;
        rcases h₃ with ⟨ x, hx₁, hx₂ ⟩ ; rcases h₄ with ⟨ y, hy₁, hy₂ ⟩ ; simp_all +decide [ Ruby.FORK, Ruby.parComp, Ruby.AND, Ruby.XOR ] ;
        cases a.head t <;> cases b.head t <;> cases cin t <;> simp +decide [ * ];
      -- Apply the inductive hypothesis to get the equation for the tail.
      have h_tail : (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) (List.Vector.tail a))).toNat + (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) (List.Vector.tail b))).toNat + (if c1 t then 1 else 0) = (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) (List.Vector.tail sum))).toNat + 2 ^ n * (if carryOut t then 1 else 0) := by
        exact h _ _ _ _ _ _ h_full_adder.2;
      -- Apply the vectorToBitVec_head_tail theorem to decompose the vectorToBitVec of the head and tail.
      have h_decomp : (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) a)).toNat = (if List.Vector.head a t then 1 else 0) + 2 * (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) (List.Vector.tail a))).toNat ∧
                         (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) b)).toNat = (if List.Vector.head b t then 1 else 0) + 2 * (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) (List.Vector.tail b))).toNat ∧
                         (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) sum)).toNat = (if List.Vector.head sum t then 1 else 0) + 2 * (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) (List.Vector.tail sum))).toNat := by
                           apply_rules [ And.intro, Ruby.vectorToBitVec_head_tail ];
                           · convert Ruby.vectorToBitVec_head_tail _ using 1;
                             cases a ; aesop;
                           · convert Ruby.vectorToBitVec_head_tail _ using 1;
                             cases b ; aesop;
                           · convert Ruby.vectorToBitVec_head_tail _ using 1;
                             cases sum ; aesop;
      grind +ring

theorem ADDER_correct : ∀ (n : Nat) (ngt0 : n > 0) (cin carryOut : Bit) (a b sum : List.Vector Bit n) (t : Nat),
   ADDER n ngt0 (cin, List.Vector.zipWith (fun x y => (x, y)) a b) (sum, carryOut) →
   let a' := vectorToBitVec (List.Vector.map (fun x => x t) a)     -- a' is the BitVec value of a at time t
   let b' := vectorToBitVec (List.Vector.map (fun x => x t) b)     -- b' is the BitVec value of b at time t
   let sum' := vectorToBitVec (List.Vector.map (fun x => x t) sum) -- sum' is the BitVec value of sum at time t
   let cin' := if cin t then 1 else 0                              -- cin' as a Nat
   let carryOut' := if carryOut t then 1 else 0                    -- carryOut' as a Nat
   a'.toNat + b'.toNat + cin' = sum'.toNat + 2^n * carryOut' := by
     intro n ngt0;
     induction' n, Nat.succ_le.mpr ngt0 using Nat.le_induction with n ih;
     · exact fun cin carryOut a b sum t a_1 ↦
       let a' := vectorToBitVec (List.Vector.map (fun x ↦ x t) a);
       let b' := vectorToBitVec (List.Vector.map (fun x ↦ x t) b);
       let sum' := vectorToBitVec (List.Vector.map (fun x ↦ x t) sum);
       let cin' := if cin t = true then 1 else 0;
       let carryOut' := if carryOut t = true then 1 else 0;
       ADDER_correct_1 cin carryOut a b sum t a_1;
     · exact Ruby.ADDER_correct_step n ih ( by tauto )

end Ruby
