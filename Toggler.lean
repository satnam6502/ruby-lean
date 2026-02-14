import Ruby

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby

  -- The TOGGLER circuit will invert its current internal state when its enable input is true.
  -- If the input is always high (true), then the output at time t is the negation of the output at time t-1.
  def TOGGLER := LOOP (AND ⨾ INV ⨾ DELAY false ⨾ FORK)

  -- The TOGGLER circuit should have an output that toggles between false and true on successive clock cycles.
  theorem TOGGLER_correct : ∀ t, ∃ b c, TOGGLER (const1, b) (c, b) ↔ c (t + 1) = !(c t) := by
  intros t;
  by_contra! h;
  cases h ( fun n => if n = t then Bool.true else Bool.false ) ( fun n => if n = t then Bool.true else Bool.false ) <;> simp_all +decide [ Ruby.TOGGLER ];
  cases h ( fun n => if n = t then Bool.true else Bool.false ) ( fun n => if n = t then Bool.false else Bool.true ) <;> simp_all +decide [ Ruby.LOOP ];
  rename_i h₁ h₂op;
  cases h ( fun n => if n = t then Bool.true else Bool.false ) ( fun n => if n = t then Bool.false else Bool.false ) <;> simp_all +decide [ Relation.Comp ];
  obtain ⟨ b, hb₁, b₁, hb₂, b₂, hb₃, hb₄ ⟩ := ‹_›; specialize h₁ b hb₁ b₁ hb₂ b₂ hb₃; specialize h₂op b hb₁ b₁ hb₂ b₂ hb₃; simp_all +decide [ Ruby.FORK ] ;

end Ruby
