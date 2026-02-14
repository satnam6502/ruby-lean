import Ruby

namespace Ruby

  -- A DECODER circuit takes an n-bit input vector representing a natural
  -- number between i in the range 0..2^n-1 and returns 2^n output wires, where only one wire
  -- is high (1 or true) and all the other wires are low (0 or false). The wire
  -- that is high is the wire at the i^th position.
  --
  -- Base case (n=0): The single output is always high (const1).
  -- Recursive case (n+1): INV the head select bit s to get not_s.
  -- Recursively DECODER the tail bits to get 2^n sub-decoder outputs.
  -- For each sub-decoder output sub[k], AND it with not_s to produce output[2k]
  -- and AND it with s to produce output[2k+1].
  def DECODER : Rel (List.Vector Bit n) (List.Vector Bit (2^n)) :=
    match n with
    | 0 => fun _ out => out.get ⟨0, by omega⟩ = const1
    | n + 1 => fun v out =>
      have h : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      ∃ (not_s : Bit) (sub : List.Vector Bit (2^n)),
        INV v.head not_s ∧
        DECODER v.tail sub ∧
        ∀ (k : Fin (2^n)),
          AND (sub.get k, not_s) (out.get ⟨2 * k.val, by omega⟩) ∧
          AND (sub.get k, v.head) (out.get ⟨2 * k.val + 1, by omega⟩)

 -- Correctness of the DECODER: output wire i is high at time t if and only if
  -- the input vector represents the number i at time t.
  theorem DECODER_correct {n : Nat} (v : List.Vector Bit n) (out : List.Vector Bit (2^n)) :
    DECODER v out →
    ∀ (i : Fin (2^n)) (t : Nat),
      out.get i t = ((vectorToBitVec (List.Vector.map (fun x => x t) v)).toNat == i.val) := by
    induction' n with n ih;
    · simp +zetaDelta at *;
      unfold Ruby.DECODER;
      cases out ; aesop;
    · intro h i t;
      obtain ⟨not_s, sub, h_inv, h_dec, h_and⟩ := h;
      -- By definition of `vectorToBitVec`, we can split the vector into the head and the tail.
      have h_split : (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) v)).toNat = (if v.head t then 1 else 0) + 2 * (Ruby.vectorToBitVec (List.Vector.map (fun x => x t) v.tail)).toNat := by
        convert vectorToBitVec_head_tail _ using 1;
        cases v ; aesop;
      -- By definition of `Fin`, we can split `i` into its even and odd components.
      obtain ⟨k, hk⟩ : ∃ k : Fin (2^n), i = ⟨2 * k.val, by omega⟩ ∨ i = ⟨2 * k.val + 1, by omega⟩ := by
        rcases Nat.even_or_odd' i with ⟨ k, hk | hk ⟩ <;> [ exact ⟨ ⟨ k, by linarith [ Fin.is_lt i, pow_succ' 2 n ] ⟩, Or.inl <| Fin.ext <| by linarith ⟩ ; exact ⟨ ⟨ k, by linarith [ Fin.is_lt i, pow_succ' 2 n ] ⟩, Or.inr <| Fin.ext <| by linarith ⟩ ];
      cases hk <;> simp_all +decide [ Ruby.AND ];
      · split_ifs <;> simp_all +decide [ Ruby.INV ];
        · omega;
        · specialize ih v.tail sub h_dec k t ; aesop;
      · grind

end Ruby
