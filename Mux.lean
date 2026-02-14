import Ruby

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby

-- A 2-to-1 multiplexor that selects between two data inputs based on a select signal.
-- When sel is false, output is a (first data input); when sel is true, output is b (second data input).
def MUX2_1 : Rel (Bit × (Bit × Bit)) Bit :=
  fun (sel, (a, b)) out => ∀ t, out t = if sel t then b t else a t

-- A TWO_SORTER uses a COMPARATOR to determine if a > b, then uses two MUX2_1 instances
-- to route the min to the first output and the max to the second output.
-- The first MUX2_1 uses the comparator output as select (to pick the smaller value):
--   when a > b (sel = true), min = b; when a ≤ b (sel = false), min = a.
-- The second MUX2_1 uses the inverted comparator output via INV (to pick the larger value):
--   when a > b (sel_inv = false), max = a; when a ≤ b (sel_inv = true), max = b.
--
--                                            ┌───────────────────────┐
--                                            │                       │
--   (aᵢ, bᵢ) ──┬──→ COMPARATOR ──→ a_gt_b ─┼──→ MUX2_1(a_gt_b)    ──→ minᵢ
--               │                     │      │
--               │                    INV     │
--               │                     │      │
--               │                     v      │
--               └────────────── not_a_gt_b ──┼──→ MUX2_1(not_a_gt_b) ──→ maxᵢ
--                                            │                       │
--                                            └───────────────────────┘
--

end Ruby
