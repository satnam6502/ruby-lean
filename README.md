# ruby-lean
An experimental implementation of Ruby in Lean.

## Implementing circuits
When asked to implement a circuit, use the library of basic circuit building blocks like `INV`, `AND`, `NAND`, `OR`, `XOR` and `XNOR` and the unit-delay element `DELAY` (which corresponds to a flip-flop) by composing them with combinators in point-free APL-style.

Use the relational composition ⨾ to connect the output of one circuit to the input of another circuit e.g. `NOR := OR ⨾ NOT`.

Use the parallel composition combinator ‖ to combine two circuits in parallel, with the composite circuit relating the input tuple (cross product) to the output tuple (cross product) e.g. HALF_ADDER := FORK ⨾ (AND ‖ XOR).

