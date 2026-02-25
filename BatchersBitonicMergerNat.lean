import Ruby
import TwoSorter

import Mathlib
import Mathlib.Data.Rel
import Mathlib.Logic.Relation

namespace Ruby


def twoSorterNat : Rel (List.Vector Nat 2) (List.Vector Nat 2) :=
  fun input output =>
    output.get ⟨0, by omega⟩ = min (input.get ⟨0, by omega⟩) (input.get ⟨1, by omega⟩) ∧
    output.get ⟨1, by omega⟩ = max (input.get ⟨0, by omega⟩) (input.get ⟨1, by omega⟩)

/-
Batcher's bitonic merger is a bitonic merger which takes an input vector of length 2^(n+1).
The first half of the input vector, size 2^n, should have increasing values.
The second half of the input vector, size 2^n, should have decreasing values.
The result of the bitonic merger is a sorted vector of length 2^(n+1), which represents the inputs
merged and sorted into increasing order.
-/
def BATCHER_BITONIC_MERGER_NAT := BFLY twoSorterNat


/- A 4-input Batcher's bitonic merger for n-bit words.
   Takes a 4-element vector (2^(1+1) = 4) of Nat values and produces a sorted 4-element vector.
   Unrolling BFLY at degree 1:
     BFLY r 1 = ILV (BFLY r 0) ⨾ EVENS r = ILV r ⨾ EVENS r
   i.e. unriffle, sort each half of 2, riffle, then compare-swap adjacent pairs.
-/
def BATCHER_BITONIC_MERGER_NAT_4 :
    Rel (List.Vector Nat 4) (List.Vector Nat 4) := BATCHER_BITONIC_MERGER_NAT 1


/-
  Concrete example: BATCHER_BITONIC_MERGER_4 maps the bitonic input [3, 5, 8, 2]
  to the sorted output [2, 3, 5, 8].

  Input:                 [3, 5, 8, 2]     (bitonic: ascending [3,5,8], descending [8,2])
  After UNRIFFLE:        [3, 8, 5, 2]     (CHOP → UNZIP → UNHALVE)
  After TWO sort:        [3, 8, 2, 5]     (HALVE, sort each half [3,8]→[3,8], [5,2]→[2,5], UNHALVE)
  After RIFFLE:          [3, 2, 8, 5]     (HALVE → ZIP → UNCHOP)
  After EVENS sort:      [2, 3, 5, 8]     (CHOP, sort pairs [3,2]→[2,3], [8,5]→[5,8], UNCHOP)
-/
section BMM4_Example

private def bmm4_input  : List.Vector Nat 4 := ⟨[3, 5, 8, 2], rfl⟩
private def bmm4_output : List.Vector Nat 4 := ⟨[2, 3, 5, 8], rfl⟩

example : BATCHER_BITONIC_MERGER_NAT_4 bmm4_input bmm4_output := by
  show (ILV twoSorterNat ⨾ EVENS twoSorterNat) bmm4_input bmm4_output
  -- mid = [3, 2, 8, 5] (after ILV, before EVENS)
  refine ⟨⟨[3, 2, 8, 5], rfl⟩, ?_, ?_⟩
  · -- ILV = UNRIFFLE ⨾ TWO twoSorterNat ⨾ RIFFLE
    -- after_unriffle = [3, 8, 5, 2], after_two = [3, 8, 2, 5]
    refine ⟨⟨[3, 8, 5, 2], rfl⟩, ?_, ⟨[3, 8, 2, 5], rfl⟩, ?_, ?_⟩
    · -- UNRIFFLE = CHOP ⨾ UNZIP ⨾ UNHALVE
      refine ⟨⟨[⟨[3, 5], rfl⟩, ⟨[8, 2], rfl⟩], rfl⟩, ?_, ⟨[⟨[3, 8], rfl⟩, ⟨[5, 2], rfl⟩], rfl⟩, ?_, ?_⟩
      · intro i j; fin_cases i <;> fin_cases j <;> rfl
      · intro j i; fin_cases j <;> fin_cases i <;> rfl
      · exact ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
    · -- TWO = HALVE ⨾ MAP twoSorterNat ⨾ UNHALVE
      refine ⟨⟨[⟨[3, 8], rfl⟩, ⟨[5, 2], rfl⟩], rfl⟩, ?_, ⟨[⟨[3, 8], rfl⟩, ⟨[2, 5], rfl⟩], rfl⟩, ?_, ?_⟩
      · exact ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
      · intro i; fin_cases i <;> exact ⟨by decide, by decide⟩
      · exact ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
    · -- RIFFLE = HALVE ⨾ ZIP ⨾ UNCHOP
      refine ⟨⟨[⟨[3, 8], rfl⟩, ⟨[2, 5], rfl⟩], rfl⟩, ?_, ⟨[⟨[3, 2], rfl⟩, ⟨[8, 5], rfl⟩], rfl⟩, ?_, ?_⟩
      · exact ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
      · intro i j; fin_cases i <;> fin_cases j <;> rfl
      · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · -- EVENS = CHOP ⨾ MAP twoSorterNat ⨾ UNCHOP
    refine ⟨⟨[⟨[3, 2], rfl⟩, ⟨[8, 5], rfl⟩], rfl⟩, ?_, ⟨[⟨[2, 3], rfl⟩, ⟨[5, 8], rfl⟩], rfl⟩, ?_, ?_⟩
    · intro i j; fin_cases i <;> fin_cases j <;> rfl
    · intro i; fin_cases i <;> exact ⟨by decide, by decide⟩
    · intro i j; fin_cases i <;> fin_cases j <;> rfl

end BMM4_Example

/- A vector of Nats is sorted (non-decreasing). -/
def IsSorted {k : Nat} (v : List.Vector Nat k) : Prop :=
  ∀ (i j : Fin k), i.val ≤ j.val → v.get i ≤ v.get j

/- A vector of Nats is bitonic: first half ascending, second half descending. -/
def IsBitonicNat {m : Nat} (v : List.Vector Nat (2 ^ (m + 1))) : Prop :=
  (∀ (i j : Fin (2 ^ (m + 1))), i.val ≤ j.val → j.val < 2 ^ m →
    v.get i ≤ v.get j) ∧
  (∀ (i j : Fin (2 ^ (m + 1))), 2 ^ m ≤ i.val → i.val ≤ j.val →
    v.get j ≤ v.get i)

-- Base case: twoSorterNat sorts any 2-element input.
private theorem bfly_base_case_nat
    (input output : List.Vector Nat 2)
    (h_merger : BATCHER_BITONIC_MERGER_NAT 0 input output) :
    IsSorted output := by
  unfold IsSorted
  intro i j hij
  unfold BATCHER_BITONIC_MERGER_NAT BFLY at h_merger
  obtain ⟨h_min, h_max⟩ := h_merger
  fin_cases i <;> fin_cases j <;> simp_all

/-
Correctness of Batcher's bitonic merger (Nat version):
Given a bitonic input, the output is sorted (non-decreasing).
Batcher's Bitonic Merger via the Butterfly Network
1. Wiring Combinators
We work with sequences of length n=2kn = 2^k
n=2k and define the following combinators. Let x=[x0,x1,…,xn−1]\mathbf{x} = [x_0, x_1, \ldots, x_{n-1}]
x=[x0​,x1​,…,xn−1​].

two f — applies f independently to each half:
two  f  [x0,…,xn−1]=f  [x0,…,xn/2−1]+ ⁣ ⁣+f  [xn/2,…,xn−1]\texttt{two}\; f\; [x_0, \ldots, x_{n-1}] = f\;[x_0, \ldots, x_{n/2-1}] \mathbin{+\!\!+} f\;[x_{n/2}, \ldots, x_{n-1}]twof[x0​,…,xn−1​]=f[x0​,…,xn/2−1​]++f[xn/2​,…,xn−1​]
riffle (perfect shuffle) — interleaves the two halves:
riffle  [a0,…,am−1,  b0,…,bm−1]=[a0,b0,a1,b1,…,am−1,bm−1]\texttt{riffle}\;[a_0, \ldots, a_{m-1},\; b_0, \ldots, b_{m-1}] = [a_0, b_0, a_1, b_1, \ldots, a_{m-1}, b_{m-1}]riffle[a0​,…,am−1​,b0​,…,bm−1​]=[a0​,b0​,a1​,b1​,…,am−1​,bm−1​]
unriffle (inverse shuffle) — separates even-indexed and odd-indexed elements:
unriffle  [x0,x1,x2,x3,…]=[x0,x2,x4,…]+ ⁣ ⁣+[x1,x3,x5,…]\texttt{unriffle}\;[x_0, x_1, x_2, x_3, \ldots] = [x_0, x_2, x_4, \ldots] \mathbin{+\!\!+} [x_1, x_3, x_5, \ldots]unriffle[x0​,x1​,x2​,x3​,…]=[x0​,x2​,x4​,…]++[x1​,x3​,x5​,…]
These are mutual inverses: riffle∘unriffle=unriffle∘riffle=id\texttt{riffle} \circ \texttt{unriffle} = \texttt{unriffle} \circ \texttt{riffle} = \text{id}
riffle∘unriffle=unriffle∘riffle=id.

ilv f (interleave) — applies f to even-indexed and odd-indexed sub-sequences independently, then reassembles:
ilv  f=riffle∘two  f∘unriffle\texttt{ilv}\; f = \texttt{riffle} \circ \texttt{two}\; f \circ \texttt{unriffle}ilvf=riffle∘twof∘unriffle
Equivalently: separate into evens and odds, apply ff
f to each, riffle back together.

evens f — applies a 2-input function f to each consecutive pair:
evens  f  [x0,x1,x2,x3,…]=[f(x0,x1),  f(x2,x3),  …]\texttt{evens}\; f\; [x_0, x_1, x_2, x_3, \ldots] = [f(x_0, x_1),\; f(x_2, x_3),\; \ldots]evensf[x0​,x1​,x2​,x3​,…]=[f(x0​,x1​),f(x2​,x3​),…]
cswap — the compare-and-swap primitive:
cswap(a,b)=(min⁡(a,b),  max⁡(a,b))\texttt{cswap}(a, b) = (\min(a,b),\; \max(a,b))cswap(a,b)=(min(a,b),max(a,b))
So evens  cswap\texttt{evens\;cswap}
evenscswap is a layer of parallel compare-swaps on adjacent pairs.


2. Key Property of ilv
Lemma (ilv distributes over composition):
ilv(f∘g)=ilv  f∘ilv  g\texttt{ilv}(f \circ g) = \texttt{ilv}\;f \circ \texttt{ilv}\;gilv(f∘g)=ilvf∘ilvg
*Proof.* Since two(f∘g)=two  f∘two  g\texttt{two}(f \circ g) = \texttt{two}\;f \circ \texttt{two}\;g
two(f∘g)=twof∘twog (applying a composition to each half is the same as applying each in turn), we have:

ilv(f∘g)=riffle∘two(f∘g)∘unriffle=riffle∘two  f∘two  g∘unriffle\texttt{ilv}(f \circ g) = \texttt{riffle} \circ \texttt{two}(f \circ g) \circ \texttt{unriffle} = \texttt{riffle} \circ \texttt{two}\;f \circ \texttt{two}\;g \circ \texttt{unriffle}ilv(f∘g)=riffle∘two(f∘g)∘unriffle=riffle∘twof∘twog∘unriffle
Inserting id=unriffle∘riffle\text{id} = \texttt{unriffle} \circ \texttt{riffle}
id=unriffle∘riffle between the two applications of
two:
=riffle∘two  f∘unriffle∘riffle∘two  g∘unriffle=ilv  f∘ilv  g□= \texttt{riffle} \circ \texttt{two}\;f \circ \texttt{unriffle} \circ \texttt{riffle} \circ \texttt{two}\;g \circ \texttt{unriffle} = \texttt{ilv}\;f \circ \texttt{ilv}\;g \qquad \square=riffle∘twof∘unriffle∘riffle∘twog∘unriffle=ilvf∘ilvg□
We write ilvj  f\texttt{ilv}^j\;f
ilvjf for jj
j-fold nesting: ilv0  f=f\texttt{ilv}^0\;f = f
ilv0f=f, ilvj+1  f=ilv(ilvj  f)\texttt{ilv}^{j+1}\;f = \texttt{ilv}(\texttt{ilv}^j\;f)
ilvj+1f=ilv(ilvjf).


3. The Bitonic Merger as a Butterfly
Define the bitonic merger recursively:
bmerge  0=evens  cswap\texttt{bmerge}\;0 = \texttt{evens\;cswap}bmerge0=evenscswap
bmerge  (k+1)=evens  cswap∘ilv(bmerge  k)\texttt{bmerge}\;(k{+}1) = \texttt{evens\;cswap} \circ \texttt{ilv}(\texttt{bmerge}\;k)bmerge(k+1)=evenscswap∘ilv(bmergek)
Here bmerge  k\texttt{bmerge}\;k
bmergek operates on 2k+12^{k+1}
2k+1 elements.

By the distributivity lemma, unfolding the recursion yields:
bmerge  k=evens  cswap∘ilv(evens  cswap)∘ilv2(evens  cswap)∘⋯∘ilvk(evens  cswap)\texttt{bmerge}\;k = \texttt{evens\;cswap} \circ \texttt{ilv}(\texttt{evens\;cswap}) \circ \texttt{ilv}^2(\texttt{evens\;cswap}) \circ \cdots \circ \texttt{ilv}^k(\texttt{evens\;cswap})bmergek=evenscswap∘ilv(evenscswap)∘ilv2(evenscswap)∘⋯∘ilvk(evenscswap)
This is a butterfly network of depth k+1k{+}1
k+1: each stage ilvj(evens  cswap)\texttt{ilv}^j(\texttt{evens\;cswap})
ilvj(evenscswap) is a layer of parallel compare-swaps at stride 2j2^j
2j. The stages proceed from coarsest stride (rightmost, applied first) to finest (leftmost, applied last).


4. What Each Stage Does
Claim: ilvj(evens  cswap)\texttt{ilv}^j(\texttt{evens\;cswap})
ilvj(evenscswap) performs parallel compare-and-swaps between elements at distance 2j2^j
2j.

*Proof by induction on jj
j.*

Base (j=0j = 0
j=0): evens  cswap\texttt{evens\;cswap}
evenscswap compares pairs (x0,x1),(x2,x3),…(x_0, x_1), (x_2, x_3), \ldots
(x0​,x1​),(x2​,x3​),…, i.e., at distance 20=12^0 = 1
20=1. ✓

Step: Assume ilvj(evens  cswap)\texttt{ilv}^j(\texttt{evens\;cswap})
ilvj(evenscswap) compares at distance 2j2^j
2j on a sequence of length nn
n. Consider ilvj+1(evens  cswap)\texttt{ilv}^{j+1}(\texttt{evens\;cswap})
ilvj+1(evenscswap) on a sequence of length 2n2n
2n:


Unriffle: sends element at position ii
i to position i/2i/2
i/2 (if ii
i even) or n+(i−1)/2n + (i{-}1)/2
n+(i−1)/2 (if ii
i odd). Even-indexed elements form the first half; odd-indexed form the second.

**Two** (ilvj(evens  cswap))(\texttt{ilv}^j(\texttt{evens\;cswap}))
(ilvj(evenscswap)): By hypothesis, within each half of nn
n elements, this compares elements at distance 2j2^j
2j *within that half*.

Riffle: re-interleaves the halves.

An element originally at position 2p2p
2p (even) goes to position pp
p in the first half, gets compared with the element at position p+2jp + 2^j
p+2j in the first half, which originally came from position 2(p+2j)=2p+2j+12(p + 2^j) = 2p + 2^{j+1}
2(p+2j)=2p+2j+1. After riffle, these return to positions 2p2p
2p and 2p+2j+12p + 2^{j+1}
2p+2j+1, which are indeed at distance 2j+12^{j+1}
2j+1. The same argument applies to odd-indexed elements. □\square
□
Thus the rightmost stage ilvk(evens  cswap)\texttt{ilv}^k(\texttt{evens\;cswap})
ilvk(evenscswap) is the
half-cleaner: it compares each xix_i
xi​ with xi+n/2x_{i + n/2}
xi+n/2​ where n=2k+1n = 2^{k+1}
n=2k+1.


5. Bitonic Sequences and the 0-1 Principle
Definition. A sequence is bitonic if it monotonically increases then monotonically decreases (or is a cyclic rotation thereof).
0-1 Principle. A comparator network sorts all inputs iff it sorts all 0-1 inputs. Therefore it suffices to prove bmerge\texttt{bmerge}
bmerge correctly merges bitonic 0-1 sequences.

Observation. A 0-1 sequence is bitonic iff it contains at most two "blocks" — i.e., at most two maximal runs of identical values when viewed cyclically. Concretely, it has one of these forms (up to rotation):
0a 1b 0cor1a 0b 1c0^a\, 1^b\, 0^c \qquad \text{or} \qquad 1^a\, 0^b\, 1^c0a1b0cor1a0b1c

6. The Half-Cleaner Lemma
Lemma. Let x=[x0,…,xn−1]\mathbf{x} = [x_0, \ldots, x_{n-1}]
x=[x0​,…,xn−1​] be a bitonic 0-1 sequence of length n=2mn = 2m
n=2m. After applying the half-cleaner ilvk(evens  cswap)\texttt{ilv}^k(\texttt{evens\;cswap})
ilvk(evenscswap), which compares (xi,xi+m)(x_i, x_{i+m})
(xi​,xi+m​) for i=0,…,m−1i = 0, \ldots, m{-}1
i=0,…,m−1 and places min⁡\min
min in position ii
i, max⁡\max
max in position i+mi + m
i+m:

(a) The lower half L=[min⁡(xi,xi+m)]i=0m−1L = [\min(x_i, x_{i+m})]_{i=0}^{m-1}
L=[min(xi​,xi+m​)]i=0m−1​ is bitonic.

(b) The upper half U=[max⁡(xi,xi+m)]i=0m−1U = [\max(x_i, x_{i+m})]_{i=0}^{m-1}
U=[max(xi​,xi+m​)]i=0m−1​ is bitonic.

(c) Every element of LL
L is ≤\leq
≤ every element of UU
U (separation).

*Proof.* Since x\mathbf{x}
x is a bitonic 0-1 sequence, it has at most two transitions. Consider the lower half Li=min⁡(xi,xi+m)L_i = \min(x_i, x_{i+m})
Li​=min(xi​,xi+m​) and upper half Ui=max⁡(xi,xi+m)U_i = \max(x_i, x_{i+m})
Ui​=max(xi​,xi+m​).

Separation (c): Count the number of 1s. Let s=∑xis = \sum x_i
s=∑xi​. Among each compared pair (xi,xi+m)(x_i, x_{i+m})
(xi​,xi+m​), the min contributes a 1 to LL
L only when
both xi=1x_i = 1
xi​=1 and xi+m=1x_{i+m} = 1
xi+m​=1. Let dd
d be the number of indices ii
i where both are 1. Then LL
L has dd
d ones and UU
U has s−ds - d
s−d ones.

Now we claim UU
U contains *all* mm
m of its positions as 1 before LL
L gets any — more precisely, d≤s−dd \leq s - d
d≤s−d, i.e., LL
L has at most as many 1s as UU
U. This holds because dd
d counts "overlap" of the 1-block with its mm
m-shift, and by the bitonic structure, this overlap is at most half the total 1s. But the stronger claim is that if LL
L contains *any* 0, then UU
U does not contain *any* 0, or equivalently: if Li=0L_i = 0
Li​=0 for some ii
i, then either xi=0x_i = 0
xi​=0 or xi+m=0x_{i+m} = 0
xi+m​=0, and the max Ui=max⁡(xi,xi+m)U_i = \max(x_i, x_{i+m})
Ui​=max(xi​,xi+m​) could still be 0 or 1.

The clean way to see separation: In a bitonic 0-1 sequence with ss
s ones, the half-cleaner produces LL
L with min⁡(s,m)−(m−min⁡(s,m))+\min(s, m) - (m - \min(s,m))^+
min(s,m)−(m−min(s,m))+… Actually, let me give the cleaner combinatorial argument.

Consider the mm
m pairs (xi,xi+m)(x_i, x_{i+m})
(xi​,xi+m​). Each pair contributes (0,0), (0,1), (1,0), or (1,1). Let α,β,γ,δ\alpha, \beta, \gamma, \delta
α,β,γ,δ count these four types respectively. Then:


LL
L has γ+δ\gamma + \delta
γ+δ zeros... no. Li=min⁡(xi,xi+m)L_i = \min(x_i, x_{i+m})
Li​=min(xi​,xi+m​), so Li=1L_i = 1
Li​=1 iff the pair is (1,1), i.e., type δ\delta
δ. So LL
L has δ\delta
δ ones.

Ui=max⁡(xi,xi+m)U_i = \max(x_i, x_{i+m})
Ui​=max(xi​,xi+m​), so Ui=0U_i = 0
Ui​=0 iff the pair is (0,0), i.e., type α\alpha
α. So UU
U has m−αm - \alpha
m−α ones.


Separation (max⁡(L)≤min⁡(U)\max(L) \leq \min(U)
max(L)≤min(U)) is equivalent to:
if δ>0\delta > 0
δ>0 then α=0\alpha = 0
α=0. That is, if any pair is (1,1), then no pair is (0,0).
This follows from bitonicity. The 1s in x\mathbf{x}
x form a contiguous arc (cyclically). If some pair (xi,xi+m)(x_i, x_{i+m})
(xi​,xi+m​) is (1,1), then positions ii
i and i+mi+m
i+m are both in the 1-block. If another pair (xj,xj+m)(x_j, x_{j+m})
(xj​,xj+m​) is (0,0), then positions jj
j and j+mj+m
j+m are both in the 0-block. But positions {i,i+m,j,j+m}\{i, i+m, j, j+m\}
{i,i+m,j,j+m} are evenly interlaced around the cycle (with ii
i and jj
j in [0,m)[0,m)
[0,m) and i+mi+m
i+m, j+mj+m
j+m in [m,2m)[m, 2m)
[m,2m)). Having both {i,i+m}\{i, i+m\}
{i,i+m} all-one and {j,j+m}\{j, j+m\}
{j,j+m} all-zero with this interlacing requires the 1-block and 0-block to each span across both halves, which forces at least
three transitions — contradicting bitonicity (which allows at most two). □\square
□ for (c).

Bitonicity of halves (a,b): We need LL
L and UU
U to each be bitonic, i.e., each has at most two runs in 0-1.

Li=min⁡(xi,xi+m)L_i = \min(x_i, x_{i+m})
Li​=min(xi​,xi+m​) and Ui=max⁡(xi,xi+m)U_i = \max(x_i, x_{i+m})
Ui​=max(xi​,xi+m​). Consider the sequence of pairs (xi,xi+m)(x_i, x_{i+m})
(xi​,xi+m​) for i=0,…,m−1i = 0, \ldots, m-1
i=0,…,m−1. Since x\mathbf{x}
x is bitonic, the "upper" subsequence x0,…,xm−1x_0, \ldots, x_{m-1}
x0​,…,xm−1​ has at most two runs (it's a contiguous window of a bitonic sequence), and similarly xm,…,x2m−1x_m, \ldots, x_{2m-1}
xm​,…,x2m−1​.

Taking pointwise min of two sequences each with at most two transitions: the min changes value only when one of the inputs changes value. However, the crucial constraint from bitonicity is that the overall structure limits the number of transitions in LL
L to at most two:

The 1s in LL
L occur exactly at positions ii
i where both xi=1x_i = 1
xi​=1 and xi+m=1x_{i+m} = 1
xi+m​=1. This is the intersection of two "arcs" on the index circle (the 1-positions in the first half and the 1-positions in the second half, shifted by mm
m). The intersection of two arcs on a circle is either empty, one arc, or two arcs — hence at most two contiguous blocks. So LL
L is bitonic. The argument for UU
U (union of arcs via max) is symmetric. □\square
□ for (a,b).


7. Correctness of the Butterfly (Main Theorem)
Theorem. bmerge  k\texttt{bmerge}\;k
bmergek sorts any bitonic input of length n=2k+1n = 2^{k+1}
n=2k+1.

*Proof by induction on kk
k, using the 0-1 principle (so we consider only 0-1 inputs).*

Base (k=0k = 0
k=0, n=2n = 2
n=2): bmerge  0=evens  cswap\texttt{bmerge}\;0 = \texttt{evens\;cswap}
bmerge0=evenscswap. A bitonic sequence of length 2 is any pair; cswap\texttt{cswap}
cswap sorts it. ✓

Step (k+1k + 1
k+1): Assume bmerge  k\texttt{bmerge}\;k
bmergek correctly sorts any bitonic sequence of length 2k+12^{k+1}
2k+1.

We have bmerge  (k+1)=evens  cswap∘ilv(bmerge  k)\texttt{bmerge}\;(k{+}1) = \texttt{evens\;cswap} \circ \texttt{ilv}(\texttt{bmerge}\;k)
bmerge(k+1)=evenscswap∘ilv(bmergek).

Given a bitonic 0-1 input x\mathbf{x}
x of length n=2k+2n = 2^{k+2}
n=2k+2:

Stage 1 (rightmost in the unfolded butterfly): The innermost operation of ilv(bmerge  k)\texttt{ilv}(\texttt{bmerge}\;k)
ilv(bmergek), when we expand bmerge  k\texttt{bmerge}\;k
bmergek, starts with ilvk+1(evens  cswap)\texttt{ilv}^{k+1}(\texttt{evens\;cswap})
ilvk+1(evenscswap) — the half-cleaner at stride n/2n/2
n/2. By the Half-Cleaner Lemma, this produces separated bitonic halves.

But we can reason more directly using the recursive form: ilv(bmerge  k)\texttt{ilv}(\texttt{bmerge}\;k)
ilv(bmergek) unriffles x\mathbf{x}
x into even-indexed and odd-indexed subsequences e\mathbf{e}
e and o\mathbf{o}
o (each of length 2k+12^{k+1}
2k+1), applies bmerge  k\texttt{bmerge}\;k
bmergek to each, then riffles the results.

Key sub-lemma: If x\mathbf{x}
x is bitonic, then both e\mathbf{e}
e (even-indexed elements) and o\mathbf{o}
o (odd-indexed elements) are bitonic.

*Proof of sub-lemma:* A bitonic 0-1 sequence has at most two transitions. The even-indexed subsequence samples every other element. Two transitions in the full sequence produce at most two transitions in the even subsequence (sub-sampling can merge transitions but cannot create new ones). □\square
□
By the inductive hypothesis, bmerge  k\texttt{bmerge}\;k
bmergek correctly sorts e\mathbf{e}
e and o\mathbf{o}
o (each bitonic of length 2k+12^{k+1}
2k+1).

After riffle, we have the sorted even-indexed elements interleaved with the sorted odd-indexed elements. The result is a sequence where y2i=ei′y_{2i} = e'_i
y2i​=ei′​ (sorted evens) and y2i+1=oi′y_{2i+1} = o'_i
y2i+1​=oi′​ (sorted odds), with both e′e'
e′ and o′o'
o′ sorted.

Stage 2: The final evens  cswap\texttt{evens\;cswap}
evenscswap compares each pair (y2i,y2i+1)=(ei′,oi′)(y_{2i}, y_{2i+1}) = (e'_i, o'_i)
(y2i​,y2i+1​)=(ei′​,oi′​).

Claim: After this final compare-swap layer, the entire sequence is sorted.
To see this for 0-1 sequences: e′e'
e′ and o′o'
o′ are each sorted (ascending), so each is a sequence 0a1m−a0^a 1^{m-a}
0a1m−a and 0b1m−b0^b 1^{m-b}
0b1m−b. After riffle and pairwise compare-swap, position 2i2i
2i gets min⁡(ei′,oi′)\min(e'_i, o'_i)
min(ei′​,oi′​) and position 2i+12i+1
2i+1 gets max⁡(ei′,oi′)\max(e'_i, o'_i)
max(ei′​,oi′​). The resulting sequence is:

min⁡(e0′,o0′),  max⁡(e0′,o0′),  min⁡(e1′,o1′),  max⁡(e1′,o1′),  …\min(e'_0, o'_0),\; \max(e'_0, o'_0),\; \min(e'_1, o'_1),\; \max(e'_1, o'_1),\; \ldotsmin(e0′​,o0′​),max(e0′​,o0′​),min(e1′​,o1′​),max(e1′​,o1′​),…
Since e′e'
e′ and o′o'
o′ are both of the form 0∗1∗0^*1^*
0∗1∗, the mins form 0max⁡(a,b)1m−max⁡(a,b)0^{\max(a,b)} 1^{m - \max(a,b)}
0max(a,b)1m−max(a,b) and the maxs form 0min⁡(a,b)1m−min⁡(a,b)0^{\min(a,b)} 1^{m - \min(a,b)}
0min(a,b)1m−min(a,b), and interleaving them preserves sorted order. Concretely: at each position ii
i, once both ei′=1e'_i = 1
ei′​=1 and oi′=1o'_i = 1
oi′​=1, all subsequent positions also have both equal to 1; before that point, the pair-wise min/max correctly sequences the 0s before the 1s. □\square
□

8. The Butterfly Structure, Summarized
The complete butterfly for bmerge  k\texttt{bmerge}\;k
bmergek is:

evens  cswap⏟stride 1∘ilv(evens  cswap)⏟stride 2∘ilv2(evens  cswap)⏟stride 4∘⋯∘ilvk(evens  cswap)⏟stride 2k\underbrace{\texttt{evens\;cswap}}_{\text{stride } 1} \circ \underbrace{\texttt{ilv}(\texttt{evens\;cswap})}_{\text{stride } 2} \circ \underbrace{\texttt{ilv}^2(\texttt{evens\;cswap})}_{\text{stride } 4} \circ \cdots \circ \underbrace{\texttt{ilv}^k(\texttt{evens\;cswap})}_{\text{stride } 2^k}stride 1evenscswap​​∘stride 2ilv(evenscswap)​​∘stride 4ilv2(evenscswap)​​∘⋯∘stride 2kilvk(evenscswap)​​
Each ilvj\texttt{ilv}^j
ilvj wraps jj
j layers of perfect shuffle / inverse shuffle around the base compare-swap layer, creating the characteristic butterfly wiring pattern: stage jj
j connects each element ii
i to element i⊕2ji \oplus 2^j
i⊕2j (where ⊕\oplus
⊕ denotes XOR on indices). Data flows from right to left through k+1k+1
k+1 stages, with the stride halving at each stage — exactly the topology of a butterfly (or hypercube) network.

The recursion bmerge  (k+1)=evens  cswap∘ilv(bmerge  k)\texttt{bmerge}\;(k{+}1) = \texttt{evens\;cswap} \circ \texttt{ilv}(\texttt{bmerge}\;k)
bmerge(k+1)=evenscswap∘ilv(bmergek) captures how each level of the butterfly wraps the previous level inside an
ilv, with a fresh layer of adjacent compare-swaps at the output. The perfect shuffle is the wiring between stages: unriffle routes elements to the two recursive sub-problems, and riffle collects the results, which is precisely the cross-wiring in a butterfly diagram.
-/
theorem BATCHER_BITONIC_MERGER_NAT_correct : ∀ (m : Nat)
    (input output : List.Vector Nat (2 ^ (m + 1))),
  IsBitonicNat input →
  BATCHER_BITONIC_MERGER_NAT m input output →
  IsSorted output := by
  intro m
  induction m with
  | zero =>
    intro input output h_bitonic h_merger
    exact bfly_base_case_nat input output h_merger
  | succ m ih =>
    intro input output h_bitonic h_merger
    sorry

end Ruby
