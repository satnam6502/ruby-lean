import Ruby


import Mathlib.Tactic.GeneralizeProofs

namespace Ruby

def fir_spec {n : Nat}
    (coeffs : List.Vector Nat n) (x : ℕ → ℤ) : ℕ → ℤ :=
  fun t => Finset.univ.sum fun i : Fin n =>
    if t < i.val then 0 else coeffs.get i * x (t - i.val)

def ADD_INT : Rel ((ℕ → ℤ) × (ℕ → ℤ)) (ℕ → ℤ) :=
  fun ab o => ∀t, o t = ab.1 t + ab.2 t

def MUL_INT : Rel ((ℕ → ℤ) × (ℕ → ℤ)) (ℕ → ℤ) :=
  fun ab o => ∀t, o t = ab.1 t * ab.2 t

def ROW1D {α : Type} {n : Nat} : n > 0 → List.Vector (Rel α α) n → Rel α α :=
  fun _ v => match n with
  | 1 => v.get ⟨0, Nat.zero_lt_one⟩
  | n + 2 => v.head ⨾ ROW1D (Nat.succ_pos n) v.tail

def FIR_TAP : ℤ → Rel ((ℕ → ℤ) × (ℕ → ℤ)) ((ℕ → ℤ) × (ℕ → ℤ)) := fun coief (xin, yout) (xout, yin) =>
  ∃ xin', DELAY (0 : ℤ) xin xin' ∧
          MUL_INT (xin', coief) xout ∧
          ADD_INT (xout, yin) yout

def ZERO (_ : ℕ) : ℤ  := 0

def SEMISYSTOLIC_FIR {n : Nat} (ngt0 : n > 0) (coeffs : List.Vector ℤ n) :
    Rel (ℕ → ℤ) (ℕ → ℤ) := fun xin yout =>
  let taps := List.Vector.ofFn (fun i : Fin n => FIR_TAP (coeffs.get i))
  ∃ xout, ROW1D ngt0 taps (xin, yout) (xout, ZERO)

/-- Intermediate "x" signal at position i in the semisystolic FIR chain.
    Position 0 is the original input. Position i+1 is the delayed and
    coefficient-scaled version of position i. -/
def semisystolic_chain {n : Nat} (coeffs : List.Vector ℤ n) (xin : ℕ → ℤ) :
    (i : Nat) → ℕ → ℤ
  | 0 => xin
  | i + 1 => fun t =>
    if t = 0 then 0
    else if h : i < n then coeffs.get ⟨i, h⟩ * semisystolic_chain coeffs xin i (t - 1)
    else 0

/-- Specification for the semisystolic pipelined FIR filter.
    The output at time t is the sum of the chain signals at positions
    1 through n, where each chain signal is the delayed, cumulatively
    coefficient-scaled input. -/
def semisystolic_fir_spec {n : Nat} (coeffs : List.Vector ℤ n) (xin : ℕ → ℤ) : ℕ → ℤ :=
  fun t => Finset.univ.sum fun i : Fin n =>
    semisystolic_chain coeffs xin (i.val + 1) t

/-- A single FIR_TAP with coefficient c relates the x output to the
    delayed and scaled input, and the y output to the sum of the
    x output and the y input from the next stage. -/
lemma fir_tap_spec (c : ℤ) (xin yout xout yin : ℕ → ℤ)
    (h : FIR_TAP c (xin, yout) (xout, yin)) :
    (∀ t, xout t = if t = 0 then 0 else c * xin (t - 1)) ∧
    (∀ t, yout t = xout t + yin t) := by
  obtain ⟨xin', h_delay, h_mul, h_add⟩ := h
  dsimp [DELAY, MUL_INT, ADD_INT] at h_delay h_mul h_add
  constructor
  · intro t
    by_cases ht : t = 0
    · subst ht
      have hd : xin' 0 = 0 := by have := h_delay 0; rwa [if_pos rfl] at this
      rw [if_pos rfl, h_mul 0, hd, zero_mul]
    · have hd : xin' t = xin (t - 1) := by have := h_delay t; rwa [if_neg ht] at this
      rw [if_neg ht, h_mul t, hd, mul_comm]
  · exact h_add

/-- The ROW1D chain of FIR_TAPs produces x and y signals matching
    the semisystolic_chain specification: the threaded x signal at the
    end equals semisystolic_chain at position n, and the y output equals
    the y input plus the sum of chain signals at positions 1 through n. -/
lemma row1d_chain_spec {n : Nat} (ngt0 : n > 0) (coeffs : List.Vector ℤ n)
    (xin yout xout yin : ℕ → ℤ)
    (h : ROW1D ngt0 (List.Vector.ofFn (fun i : Fin n => FIR_TAP (coeffs.get i)))
         (xin, yout) (xout, yin)) :
    (∀ t, xout t = semisystolic_chain coeffs xin n t) ∧
    (∀ t, yout t = yin t +
      Finset.univ.sum fun i : Fin n => semisystolic_chain coeffs xin (i.val + 1) t) := by
  revert h yout xout yin xin coeffs ngt0 n; (
  intros n ngt0 coeffs xin yout xout yin h; induction' n with n ih generalizing xin yout xout yin <;> simp_all +decide [ Fin.sum_univ_succ ] ;
  · contradiction;
  · rcases n with ( _ | n ) <;> simp_all +decide [ List.ofFn_succ ];
    · obtain ⟨ xin', hxin', hxout, hyout ⟩ := h;
      simp_all +decide [ Ruby.MUL_INT, Ruby.ADD_INT, Ruby.semisystolic_chain ];
      simp_all +decide [ mul_comm, Ruby.DELAY ];
      grind +ring;
    · -- Let's simplify the goal using the definition of `ROW1D`.
      obtain ⟨xout', yout', hxout', hyout'⟩ : ∃ xout' yout', Ruby.FIR_TAP (coeffs.get ⟨0, by linarith⟩) (xin, yout) (xout', yout') ∧ Ruby.ROW1D (Nat.succ_pos n) (List.Vector.ofFn (fun i : Fin (n + 1) => Ruby.FIR_TAP (coeffs.get ⟨i.val + 1, by linarith [Fin.is_lt i]⟩))) (xout', yout') (xout, yin) := by
        have h_row1d : Ruby.ROW1D (Nat.succ_pos (n + 1)) (List.Vector.ofFn (fun i : Fin (n + 2) => Ruby.FIR_TAP (coeffs.get i))) (xin, yout) (xout, yin) → ∃ xout' yout', Ruby.FIR_TAP (coeffs.get ⟨0, by linarith⟩) (xin, yout) (xout', yout') ∧ Ruby.ROW1D (Nat.succ_pos n) (List.Vector.ofFn (fun i : Fin (n + 1) => Ruby.FIR_TAP (coeffs.get ⟨i.val + 1, by linarith [Fin.is_lt i]⟩))) (xout', yout') (xout, yin) := by
          intro h_row1d
          obtain ⟨xout', yout', hxout', hyout'⟩ : ∃ xout' yout', Ruby.FIR_TAP (coeffs.get ⟨0, by linarith⟩) (xin, yout) (xout', yout') ∧ Ruby.ROW1D (Nat.succ_pos n) (List.Vector.ofFn (fun i : Fin (n + 1) => Ruby.FIR_TAP (coeffs.get ⟨i.val + 1, by linarith [Fin.is_lt i]⟩))) (xout', yout') (xout, yin) := by
            have h_row1d_def : Ruby.ROW1D (Nat.succ_pos (n + 1)) (List.Vector.ofFn (fun i : Fin (n + 2) => Ruby.FIR_TAP (coeffs.get i))) = Ruby.FIR_TAP (coeffs.get ⟨0, by linarith⟩) ⨾ Ruby.ROW1D (Nat.succ_pos n) (List.Vector.ofFn (fun i : Fin (n + 1) => Ruby.FIR_TAP (coeffs.get ⟨i.val + 1, by linarith [Fin.is_lt i]⟩))) := by
              exact?
            exact h_row1d_def ▸ h_row1d |> fun ⟨ x, hx ⟩ => ⟨ _, _, hx.1, hx.2 ⟩ ;
          generalize_proofs at *; aesop;
        generalize_proofs at *; aesop;
      have := fir_tap_spec ( coeffs.get ⟨ 0, by linarith ⟩ ) xin yout xout' yout' hxout';
      specialize ih ( List.Vector.ofFn fun i : Fin ( n + 1 ) => coeffs.get ⟨ i.val + 1, by linarith [ Fin.is_lt i ] ⟩ ) xout' yout' xout yin ; simp_all +decide [ Fin.sum_univ_succ ] ;
      -- By definition of `semisystolic_chain`, we can rewrite the goal in terms of the chain signals.
      have h_chain : ∀ i : Fin (n + 1), ∀ t, Ruby.semisystolic_chain (List.Vector.ofFn fun (i : Fin (n + 1)) => coeffs.get ⟨(↑i : ℕ) + 1, by linarith [ Fin.is_lt i ] ⟩) xout' (i.val + 1) t = Ruby.semisystolic_chain coeffs xin (i.val + 2) t := by
        intro i t; induction' i using Fin.inductionOn with i IH generalizing t; simp +decide [ *, Ruby.semisystolic_chain ] ;
        simp +decide [ *, Ruby.semisystolic_chain ] at IH ⊢;
        specialize IH ( t - 1 ) ; rcases t with ( _ | _ | t ) <;> simp +decide [ * ] at IH ⊢ ;
        grind;
      refine' ⟨ fun t => _, fun t => _ ⟩ <;> simp_all +decide [ Fin.forall_fin_succ, Fin.sum_univ_succ ] ; ring!;
      · by_cases hn : n = 0 <;> simp_all +decide [ add_comm, add_left_comm, add_assoc ];
        convert h_chain.2 ⟨ n - 1, Nat.sub_lt ( Nat.pos_of_ne_zero hn ) zero_lt_one ⟩ t using 1 <;> cases n <;> trivial;
      · rw [ show Ruby.semisystolic_chain coeffs xin 1 t = if t = 0 then 0 else coeffs.head * xin ( t - 1 ) from ?_ ] ; ring!;
        -- By definition of `Ruby.semisystolic_chain`, we know that for `i = 1`, the chain signal is the coefficient times the delayed input.
        simp [Ruby.semisystolic_chain] at *);

/-- The semisystolic FIR circuit is correct: for any input signal xin,
    if SEMISYSTOLIC_FIR relates xin to yout, then yout agrees pointwise
    with the specification semisystolic_fir_spec. -/
theorem semisystolic_fir_correct {n : Nat} (ngt0 : n > 0) (coeffs : List.Vector ℤ n)
    (xin yout : ℕ → ℤ) (h : SEMISYSTOLIC_FIR ngt0 coeffs xin yout) :
    ∀ t, yout t = semisystolic_fir_spec coeffs xin t := by
  unfold SEMISYSTOLIC_FIR at h
  obtain ⟨xout, h_row⟩ := h
  have ⟨_, h_y⟩ := row1d_chain_spec ngt0 coeffs xin yout xout ZERO h_row
  intro t
  rw [h_y t]
  simp [ZERO, semisystolic_fir_spec]

/-- After n pipeline cycles (one per tap/DELAY register), the output of the
    semisystolic FIR circuit matches the standard FIR specification fir_spec.
    The nat_coeffs are the Nat-valued coefficients used by fir_spec;
    the circuit operates on their ℤ casts. -/
theorem semisystolic_fir_pipeline_correct {n : Nat} (ngt0 : n > 0)
    (nat_coeffs : List.Vector Nat n)
    (xin yout : ℕ → ℤ)
    (h : SEMISYSTOLIC_FIR ngt0
      (List.Vector.ofFn fun i => (↑(nat_coeffs.get i) : ℤ)) xin yout) :
    ∀ t, yout (t + n) = fir_spec nat_coeffs xin t := by
  sorry

end Ruby
