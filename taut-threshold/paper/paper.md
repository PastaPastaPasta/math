# The alternation-trading calculus for TAUTOLOGY versus NTS stops exactly at ∛4: a kernel-checked proof

**PastaPastaPasta** · November 2026

*Markdown rendering of `paper.tex`, which is the reference version.*

## Abstract

Williams \[W13, §6\] set up a calculus of alternation-trading proofs for showing that TAUTOLOGY has no nondeterministic algorithm running in time $`n^c`$ and space $`n^{o(1)}`$. Diehl, van Melkebeek and Williams \[DvMW11\] gave proofs in this calculus for every $`c<\sqrt[3]{4}\approx 1.5874`$. Williams conjectured that no proof in the calculus works for any $`c>\sqrt[3]{4}`$ (Conjecture 6.8 of \[W13\]) and proved that none works for $`c\ge\varphi\approx 1.618`$ (Theorem 6.9).

We prove Conjecture 6.8 for a formalisation, in Lean 4 with Mathlib, of the calculus of \[W13, §6\] (Lemmas 6.1 and 6.2 in the line format of \[W13, §2\]). The formalised rule set contains the merging of a new block into an adjacent block of the same type, which \[W13\] uses in its displayed speedups, the combining of two adjacent blocks of the same type anywhere in a line (the identity of \[W13, §2\]) and its converse, and also the variants that a literal reading of the printed lemmas allows: a speedup that opens a block next to one of the same type without merging, lines that do not alternate, an in-place flip of a matching kernel, and a flip of a quantifier-free kernel. For every $`c`$ with $`c^3\ge 4`$, including $`c=\sqrt[3]{4}`$, no sequence of rule applications in this rule set takes a line $`A`$ to $`\neg A`$ or to any line componentwise below $`\neg A`$, and no normal-form proof exists. Together with a Lean re-proof of the \[DvMW11\] construction, this shows that for $`c\ge 1`$ the formalised calculus has a normal-form proof if and only if $`c^3<4`$. The impossibility proof uses a potential function with two line types and a first-return induction on proofs.

*What is kernel-checked:* both directions of this threshold, for the formal rule sets, including the reduction of arbitrary proofs to normal form (the analogue of \[W13, Theorem 6.6\], whose proof \[W13\] omits). *What is not machine-checked:* that the formal rules cover the published calculus (a modelling claim, which we compare rule by rule on paper in Table 1; Section 9 lists the remaining reading points, among them that $`n^{o(1)}`$ terms are dropped from the exponents), and soundness of the calculus itself (which is published, not formalised). Conjecture 6.8 refers to “alternation-trading proofs” in the sense of \[W13\], whose rules are fixed only informally there; our theorem is about the formalised rule set. The result is a limit on one proof calculus. It says nothing about lower bounds for TAUTOLOGY proved by other methods.

## 1. Introduction

**Background.**

Fortnow and van Melkebeek \[FvM00\] showed that TAUTOLOGY cannot be solved in time $`n^{\sqrt2-o(1)}`$ by a nondeterministic algorithm using $`n^{o(1)}`$ space. Williams \[W13\] cast proofs of this kind (“alternation-trading proofs”) as sequences of rule applications whose exponents can be optimised by linear programming, and used computer search to find better proofs. Generalising the proofs found, Diehl, van Melkebeek and Williams \[DvMW11\] obtained the exponent $`\sqrt[3]{4}`$; Williams presents the argument as Theorem 6.7 of \[W13\]. Exhaustive search over short proofs led to Conjecture 6.8 of \[W13\]:

> There is no alternation trading proof that $`\mathsf{coNTIME}[n]\not\subseteq\mathsf{NTS}[n^c]`$, for any $`c>\sqrt[3]{4}`$.

\[W13\] proves that no proof exists for $`c\ge\varphi`$ (Theorem 6.9). For the analogous problem of SAT versus deterministic time and $`n^{o(1)}`$ space, Buss and Williams \[BW15\] proved that the calculus stops at $`2\cos(\pi/7)`$. Buss’s 2013 survey \[B13\] states, after recalling the $`\sqrt[3]{4}`$ bound, that extending the methods of \[BW15\] to show that $`\sqrt[3]{4}`$ is optimal for alternation-trading proofs “has not been attempted yet and so it remains an open problem”.

**Results.**

We work with a formalisation of the calculus of \[W13, §6\], described in Section 2. Result numbers of the form $`x.y`$ (Lemma 6.1, Theorem 6.6, …) always refer to \[W13\]; our own results are numbered $`1,2,3,\dots`$ Page numbers, equation numbers and quotations from \[W13\] refer to the author copy cited in the bibliography. All statements below are Lean theorems; the names are those of the accompanying Lean library (namespace `PastaMath.TautThreshold`).

- **Impossibility** (Theorem 2; `TW.no_proofX`, `TW.no_nfX`, with corollaries `TW.no_proofXE`, `TW.no_literal_proof`, `TW.no_literal_proofE`, `TW.no_nf`). Let $`c`$ be real with $`c^3\ge4`$. For every line $`A`$ (any number of quantifier blocks, any real parameters, alternating or not) and every $`N\ge1`$, there is no sequence of $`N`$ rule applications of the extended rule set from $`A`$ to its complement $`\neg A`$, or to any line $`B\le\neg A`$ (Definition 1). There is no normal-form proof.

- **Normal form** (Theorem 3; `TW.normal_form`, `TW.normal_formE`, `TW.normal_formX`). For every $`c`$, a proof of $`A\subseteq\neg A`$ with at least two lines yields a normal-form proof in the same calculus.

- **Threshold** (Theorem 4; `TDL.nf_exists`, `TDL.threshold_literal`). For $`c\ge1`$, a normal-form proof using the exact merging rules exists if and only if $`c^3<4`$.

So Conjecture 6.8 holds for the formalised calculus, and also at $`c=\sqrt[3]{4}`$ itself. Section 9 lists exactly what is kernel-checked and what rests on modelling choices.

**Novelty.**

We are not aware of a prior proof. Buss’s 2013 survey \[B13\] lists the question as open, and the TOCT author copy of \[W13\] calls Conjecture 6.8 “still open”. Our literature search was not exhaustive.

**AI assistance.**

The proofs and the Lean formalisation were produced with Anthropic’s Claude models under the author’s direction. The kernel-checked Lean proofs are the primary evidence for the theorems about the formal calculus; this text explains them and states what they do and do not establish.

## 2. The calculus

### 2.1 Lines

Write $`\mathsf{NTS}[n^a]=\mathsf{NTISP}[n^{a},n^{o(1)}]`$ and $`\mathsf{coNTS}[n^a]`$ for its complement class \[W13, §6.1\]. The hypothesis is $`H_c`$: $`\mathrm{TAUT}\in\mathsf{NTS}[n^c]`$. By \[W13, Theorem 3.1\] it gives $`\mathsf{coNTIME}[n]\subseteq\mathsf{NTS}[n^{c+o(1)}]`$.

A *line* is a class
``` math
(Q_1\, n^{g_1})^{o_1}\,(Q_2\, n^{g_2})^{o_2}\cdots(Q_m\, n^{g_m})^{o_m}\; K[n^{a}],
```
with quantifiers $`Q_i\in\{\exists,\forall\}`$, guess exponents $`g_i\ge0`$ (where $`n^0`$ means $`\log n`$), input constraints $`o_i`$ (the $`i`$-th block passes on $`n^{o_i}`$ bits; \[W13\] writes $`b_{i+1}`$), a kernel type $`K\in\{\mathsf{NTS},\mathsf{coNTS}\}`$ and a kernel exponent $`a`$. The input to the first block has length $`n`$, so the input constraint in front of block 1 is $`1`$. For a block list $`Q`$ let $`\mathrm{pin}(Q)`$ be the input constraint of its innermost block, and $`\mathrm{pin}(\emptyset)=1`$. A line with $`m=0`$ is *quantifier-free*. A kernel is *matching* if its type agrees with the innermost quantifier ($`\mathsf{NTS}`$ under $`\exists`$, $`\mathsf{coNTS}`$ under $`\forall`$) and *opposite* otherwise. The *complement* $`\neg A`$ of a line $`A`$ swaps every quantifier and the kernel type and keeps all exponents.

### 2.2 Rules

The rules are \[W13, Lemmas 6.1 and 6.2\]. Throughout, $`Q`$ is a block list and $`b=\mathrm{pin}(Q)`$.

- **Speedup** (Lemma 6.1 with space $`n^{o(1)}`$). For $`b\ge1`$, $`a\ge1`$, $`x\ge0`$:
  ``` math
  Q\,\mathsf{NTS}[n^a]\subseteq Q\,(\exists\, n^{x})^{\max(b,x)}(\forall\,\log n)^{b}\,\mathsf{NTS}[n^{a-x}],
  ```
  and dually $`Q\,\mathsf{coNTS}[n^a]\subseteq Q\,(\forall\, n^{x})^{\max(b,x)}(\exists\,\log n)^{b}\,\mathsf{coNTS}[n^{a-x}]`$. If the innermost block of $`Q`$ already has the new first quantifier, \[W13\] merges the two blocks (\[W13, §2\]: adjacent blocks of the same type “can” be combined); for example, if $`Q=Q'(\exists\, n^{g})^{o}`$ then the result is $`Q'(\exists\, n^{\max(g,x)})^{\max(o,x)}(\forall\,\log n)^{o}\,\mathsf{NTS}[n^{a-x}]`$, as in \[W13, eq. (14)\]. Read literally, Lemma 6.1 also permits keeping the two blocks apart.

- **Slowdown** (Lemma 6.2, under $`H_c`$).

  1.  $`Q\,(\exists\, n^{g})^{o}\,\mathsf{NTS}[n^{a}]\subseteq Q\,\mathsf{coNTS}[n^{c\max(g,a,o,b)}]`$;

  2.  $`Q\,(\forall\, n^{g})^{o}\,\mathsf{coNTS}[n^{a}]\subseteq Q\,\mathsf{NTS}[n^{c\max(g,a,o,b)}]`$;

  3.  $`Q\,(\exists\, n^{g})^{o}\,\mathsf{coNTS}[n^{a}]\subseteq Q\,(\exists\, n^{g})^{o}\,\mathsf{NTS}[n^{c\max(a,o)}]`$;

  4.  $`Q\,(\forall\, n^{g})^{o}\,\mathsf{NTS}[n^{a}]\subseteq Q\,(\forall\, n^{g})^{o}\,\mathsf{coNTS}[n^{c\max(a,o)}]`$.

  Rules (1)/(2) remove (“pop”) the innermost block over a matching kernel. Rules (3)/(4) flip an opposite kernel.

- **Combining** (\[W13, §2\]). “By simple properties of nondeterminism and conondeterminism, we can combine adjacent quantifier blocks that are of the same type, e.g., $`(\exists\, n^a)^a(\exists\, n^b)^b\,\mathsf{DTS}[n^c]=(\exists\, n^{\max\{a,b\}})^b\,\mathsf{DTS}[n^c]`$.” \[W13\] uses this inside its speedups (above) and also as a separate step: the last inclusion of the derivation on p. A:27 turns $`(\exists\,n^{x_{k+1}})(\forall\log n)^1(\forall\,n^{y})\mathsf{coNTS}[n^{x_{k+1}}]`$, with $`y=c^2x_k^2/\sum_i x_i`$ and $`x_{k+1}=cy`$, into $`(\exists\,n^{x_{k+1}})(\forall\,n^{x_{k+1}})\mathsf{coNTS}[n^{x_{k+1}}]`$, in which the two universal blocks have become one (the lines are printed with most input constraints omitted; the treatment of the omitted constraints, under two readings, is given below, after Table 1).

- **Further sound inclusions** (not printed as items of Lemma 6.2). The argument for (3)/(4) converts the kernel alone, whatever the type of the innermost block, so it also gives the in-place flip of a matching kernel, $`Q\,(\exists\, n^{g})^{o}\,\mathsf{NTS}[n^{a}]\subseteq Q\,(\exists\, n^{g})^{o}\,\mathsf{coNTS}[n^{c\max(a,o)}]`$ and its dual, and, with no block, the quantifier-free flip $`\mathsf{NTS}[n^a]\subseteq\mathsf{coNTS}[n^{c\max(a,1)}]`$ and its dual.

### 2.3 Proofs and normal form

A *proof* (from $`A_0`$ to $`A_N`$) is a sequence of lines $`A_0,\dots,A_N`$, $`N\ge1`$, each obtained from the previous one by one rule. Following \[W13, Definition 6.4\], a proof is in *normal form* if its first line is $`\mathsf{NTS}[n^a]`$, its last line is $`\mathsf{coNTS}[n^{a'}]`$ with $`a'\le a`$, and no other line is quantifier-free. \[W13, Lemma 6.5\] shows that, for $`c\ge1`$, a normal-form proof with at least two lines contradicts $`H_c`$ (Lemma 6.3 covers $`a'<a`$, a separate argument covers $`a'=a`$). \[W13, Theorem 6.6\] states that a proof between simple complementary classes can be converted into a normal-form proof; its proof is omitted there (“analogous to that of Theorem 4.4”).

### 2.4 The formalisation

A Lean line is a triple $`(\mathit{bl},k,a)`$: the block list $`\mathit{bl}`$, stored innermost first, of blocks $`\langle q,g,o\rangle`$ ($`q=\mathtt{true}`$ for $`\exists`$); the kernel type $`k`$ ($`\mathtt{true}`$ for $`\mathsf{NTS}`$); and the kernel exponent $`a\in\mathbb R`$ (`TW.WLine`, `TW.Blk`, `TW.pin`, `TW.compl`). There are four rule relations.

- $`\texttt{TW.WStepE}\,c`$ (*exact merging rules*) has the exact output values of Lemmas 6.1 and 6.2, the side conditions $`b\ge1`$, $`a\ge1`$, $`x\ge0`$ of Lemma 6.1, and merges a new block into an innermost block of the same type.

- $`\texttt{TW.WStep}\,c`$ is its relaxation: the same four rule shapes, but every output exponent is only bounded below by the exact value (so weakening is built in), and the only side condition is $`x\ge0`$.

- $`\texttt{TW.WStepXE}\,c`$ (*exact extended rules*) is `WStepE` together with the exact values of five further rules: a speedup that opens new blocks next to an innermost block of the same type without merging (`speedSame`), the matching-kernel flip (`flipM`), the quantifier-free flip (`flipQ`), and the identity of \[W13, §2\] applied to any two adjacent blocks of a line, $`(Q\,n^a)^a(Q\,n^b)^b\mapsto(Q\,n^{\max(a,b)})^b`$ (`combine`) and back (`split`).

- $`\texttt{TW.WStepX}\,c`$ (*extended rules*) is the relaxation of `WStepXE`: a speedup may open new blocks whatever the innermost block is, a pop may leave a kernel that is matching or opposite to the new innermost block (so lines need not alternate), a flip applies to any kernel under a block, `flipQ` flips a quantifier-free kernel, `combine` replaces two adjacent blocks $`(Q\,n^{g_1})^{o_1}(Q\,n^{g_2})^{o_2}`$ of the same type, anywhere in the line, by one block $`(Q\,n^{g})^{o}`$ with $`g\ge\max(g_1,g_2)`$ and $`o\ge o_2`$ (the outer constraint $`o_1`$ is dropped without condition), and `split` replaces a block $`(Q\,n^{g})^{o}`$ by two blocks $`(Q\,n^{g_1})^{o_1}(Q\,n^{g_2})^{o_2}`$ with $`o_2\ge o`$ and $`g_1,g_2,o_1`$ arbitrary; both may also raise the kernel exponent.

Lean proves $`\texttt{WStepE}\subseteq\texttt{WStep}\subseteq\texttt{WStepX}`$ and $`\texttt{WStepXE}\subseteq\texttt{WStepX}`$ (`TW.wstepE_wstep`, `TW.wstep_wstepX`, `TW.wstepXE_wstepX`). The impossibility theorem is proved for `WStepX`, and hence holds for the other three; the construction uses only `WStepE`. Table 1 compares the rules. In it, $`k`$ is the kernel type, $`\bar k`$ the other type, $`Q_k`$ the quantifier matching $`k`$ ($`\exists`$ for $`\mathsf{NTS}`$), $`u=\langle q,g,o\rangle`$ the innermost block and $`\mathit{rest}`$ the blocks outside it.

| Rule of \[W13\] | Lean constructors | Effect and cost in the exact system (in `WStep`, `WStepX`: each output only $`\ge`$ this) |
|:---|:---|:---|
| Lemma 6.1, block list empty or innermost block not of type $`Q_k`$ | `WStepE.speedNew`, `WStep.speedNew`, `WStepX.speed` | opens $`(Q_k\,n^{x})^{\max(b,x)}(\bar Q_k\,\log n)^{b}`$ with $`b=\mathrm{pin}(\mathit{bl})`$; kernel $`a-x`$; requires $`b\ge1`$, $`a\ge1`$, $`x\ge0`$ |
| Lemma 6.1 with merging (\[W13, §2, eq. (14)\]) | `speedMerge` (all four) | $`u=\langle Q_k,g,o\rangle`$ becomes $`(Q_k\,n^{\max(g,x)})^{\max(o,x)}`$, then $`(\bar Q_k\,\log n)^{o}`$ is opened; kernel $`a-x`$; requires $`o\ge1`$, $`a\ge1`$, $`x\ge0`$ |
| Lemma 6.2(1),(2) (pop) | `pop` (all four), $`q`$ matches $`k`$ | removes $`u`$; kernel type $`\bar k`$, exponent $`c\max(g,a,o,\mathrm{pin}(\mathit{rest}))`$, with $`\mathrm{pin}(\emptyset)=1`$ |
| Lemma 6.2(3),(4) (flip) | `WStepE.flip`, `WStep.flip`, `WStepX.flip`; $`q`$ opposite to $`k`$ | keeps blocks; kernel type $`\bar k`$, exponent $`c\max(a,o)`$ |
| Lemma 6.1 opening a block of type $`Q_k`$ next to $`u=\langle Q_k,g,o\rangle`$, not merged | `WStepXE.speedSame`, `WStepX.speed` | covered by the extended system: keeps $`u`$, opens $`(Q_k\,n^{x})^{\max(o,x)}(\bar Q_k\,\log n)^{o}`$; kernel $`a-x`$; requires $`o\ge1`$, $`a\ge1`$, $`x\ge0`$. Later pops may leave an opposite kernel |
| not printed: matching-kernel flip $`Q\,(Q_k\,n^{g})^{o}\,K_k[n^a]\subseteq Q\,(Q_k\,n^{g})^{o}\,K_{\bar k}[n^{c\max(a,o)}]`$ | `WStepXE.flipM`, `WStepX.flip`; $`q`$ matches $`k`$ | covered by the extended system: keeps blocks; kernel type $`\bar k`$, exponent $`c\max(a,o)`$ |
| not printed: quantifier-free flip $`\mathsf{NTS}[n^a]\subseteq\mathsf{coNTS}[n^{c\max(a,1)}]`$ and dual | `WStepXE.flipQ`, `WStepX.flipQ` | covered by the extended system: kernel type $`\bar k`$, exponent $`c\max(a,1)`$ |
| §2 identity, combining two adjacent blocks of the same type | `WStepXE.combine`, `WStepX.combine` | anywhere in the line: $`(Q\,n^a)^a(Q\,n^b)^b`$ becomes $`(Q\,n^{\max(a,b)})^b`$; kernel unchanged. In `WStepX`: $`(Q\,n^{g_1})^{o_1}(Q\,n^{g_2})^{o_2}`$ becomes any $`(Q\,n^{g})^{o}`$ with $`g\ge\max(g_1,g_2)`$, $`o\ge o_2`$ |
| §2 identity read from right to left (splitting) | `WStepXE.split`, `WStepX.split` | anywhere in the line: $`(Q\,n^{\max(a,b)})^b`$ becomes $`(Q\,n^a)^a(Q\,n^b)^b`$. In `WStepX`: $`(Q\,n^{g})^{o}`$ becomes $`(Q\,n^{g_1})^{o_1}(Q\,n^{g_2})^{o_2}`$ with $`o_2\ge o`$ |

*Table 1.* The rules of \[W13, §6\] and their Lean counterparts. The $`\log n`$ blocks are represented with guess exponent $`0`$. The last five rows are in the extended systems `WStepXE`, `WStepX` only.

**Merging versus not merging.**

\[W13, §2\] says that adjacent blocks of the same type can be combined, and its displayed speedups merge (eq. (14)). \[W13, Definition 4.1\], the DTS analogue to which §6 refers, requires adjacent blocks of a line to have different quantifiers ($`Q_i\ne Q_{i+1}`$). These support the merging convention of `WStepE`. On the other hand Lemma 6.1 is stated for any prefix, and the proof of Theorem 6.7 on p. A:27 of \[W13\] displays a line with adjacent universal blocks $`(\forall\log n)^1(\forall\,n^{c^2x_k^2/\sum_i x_i})`$, which a later step combines. We do not decide between the readings. The extended system contains all of them: it can merge at the speedup (`speedMerge`), keep the blocks apart (`speed`), and combine two adjacent blocks of the same type at any later point, anywhere in the line (`combine`); the p. A:27 step is inside the system under either reading of its omitted input constraints, and the identity of \[W13, §2\] itself is one `WStepXE` step (`TW.w13_combine` checks the instance $`(\exists\,n)^1(\exists\,n)^1\mathsf{NTS}[n]\subseteq(\exists\,n)^1\mathsf{NTS}[n]`$). The converse, splitting one block into two, is included as well (`split`), although we found no step of \[W13\] that uses it. On the p. A:27 step: if each omitted input constraint is read as the default $`\max(g,1)`$ of its own block, the step is one `WStepX` step (`TW.a27_combine`, for $`c\ge1`$, $`y\ge0`$). If instead the omitted constraints are read positionally, as \[W13, §2\] indexes them, the constraint after the outer $`\exists`$ block is $`1`$ before the step and $`x_{k+1}`$ after it; then a single `WStepX` step does not suffice when $`x_{k+1}>1`$, and the step is three `WStepX` steps: split the outer $`\exists`$ block, recombine it with constraint $`x_{k+1}`$, and combine the two $`\forall`$ blocks (`TW.a27_combine_indexed`, for $`1\le y\le x_{k+1}`$). Both readings are covered by the impossibility theorem.

**Where the formalisation is more permissive.**

Each of the following only makes the impossibility theorem stronger. `WStepX` has no side conditions $`a\ge1`$, $`b\ge1`$, no lower bound on kernel exponents, and no bound $`x\le a-1`$ (the DTS analogue Lemma 3.3 of \[W13\] has one; Lemma 6.1 as printed has none); parameters are arbitrary reals; outputs may be weakened; lines need not alternate; and it contains the five rules in the last five rows of Table 1. Its `combine` drops the outer input constraint $`o_1`$ whatever its value (the identity of \[W13, §2\] has $`o_1=g_1\le\max(g_1,g_2)`$), and its `split` leaves $`g_1`$, $`g_2`$ and $`o_1`$ free. A `split` followed by a `combine` raises the input constraint of any block and sets its guess exponent to any value, so arbitrary weakening of a line with at least one block is derivable (not of a quantifier-free line: every step that ends at a quantifier-free line multiplies an exponent by $`c`$); guess exponents play no role in the impossibility proof.

**Where it is exact.**

The construction of Section 8 uses only `WStepE`, and every speedup in it has $`b=1`$, $`a\ge1`$ and in fact $`a-x\ge1`$ (Section 8).

**Soundness scope.**

The exact rules, as Lean states them, accept parameters for which a line has no complexity meaning; for example a speedup with $`a=1`$ and $`x=3`$ gives the kernel exponent $`-2`$. We attribute soundness of a step only to the published simulations (\[W13, Theorem 3.1 and Lemmas 6.1, 6.2\], for the two flips not printed in Lemma 6.2 the same simulation argument, and for combining and splitting the identity of \[W13, §2\] in the form printed there) in their range of applicability. The relaxed `combine` and `split` of `WStepX` go beyond that identity (for example when the dropped constraint $`o_1`$ exceeds both $`g`$ and $`o`$), and are included only because they enlarge the set of formal proofs. Allowing arbitrary real parameters likewise only enlarges the set of formal proofs, so it can only strengthen the impossibility theorems.

Likewise, \[W13, Lemma 6.5\] (a normal-form proof contradicts $`H_c`$) concerns proofs in the published calculus, and we appeal to it only for those. Its proof does not apply directly to the extended system: at $`c=1`$, `flipQ` alone gives the two-line normal-form “proof” $`\mathsf{NTS}[n]\subseteq\mathsf{coNTS}[n]`$ with $`a=a'=1`$, and the argument of \[W13\] for $`a'=a`$, which passes through an intermediate class with a positive quantifier guess, does not cover it. (The implication itself still holds for $`c\ge1`$, indirectly: by Theorems 2 and 4, an extended normal-form proof at $`c`$ forces $`c^3<4`$, and then a normal-form proof in the exact rules exists.) This does not affect our results: the impossibility theorems only exclude proofs, and the existence direction uses only the exact rules `WStepE` and constructs its own normal-form proofs for every $`1\le c<\sqrt[3]{4}`$. These stay in range: every speedup in them has $`b=1`$, $`a\ge1`$ and $`a-x\ge1`$.

## 3. Statements

**Definition 1** (`TW.LineLE`). For lines $`B,A`$ write $`B\le A`$ if $`B`$ and $`A`$ have the same number of blocks, the same quantifier in each block and the same kernel type, and every guess exponent, every input constraint and the kernel exponent of $`B`$ is at most the corresponding value of $`A`$.

**Theorem 2** (`TW.no_proofX`, `TW.no_nfX`). *Let $`c\in\mathbb R`$ with $`c^3\ge4`$.*

1.  *For every line $`A`$ and every $`N\ge1`$ there is no `WStepX` $`c`$-path of length $`N`$ from $`A`$ to a line $`B`$ with $`B\le\neg A`$; in particular none to $`\neg A`$, and none in `WStepXE`, `WStep` or `WStepE`.*

2.  *There is no normal-form proof in `WStepX` $`c`$, hence none in the three subsystems.*

The statements for the subsystems are the Lean corollaries `TW.no_proofXE`, `TW.no_literal_proof`, `TW.no_literal_proofE` and `TW.no_nf`.

**Theorem 3** (`TW.normal_form_gen`; instances `TW.normal_form`, `TW.normal_formE`, `TW.normal_formX`). *Let $`c\in\mathbb R`$ and let $`R`$ be `WStep` $`c`$, `WStepE` $`c`$ or `WStepX` $`c`$ (more generally, any relation contained in `WStepX` $`c`$ and closed under complement). If there is an $`R`$-path of length $`N\ge1`$ from a line $`A`$ to $`\neg A`$, then there is a normal-form proof in $`R`$.*

**Theorem 4** (`TDL.nf_exists`, `TDL.threshold_literal`). *Let $`c\ge1`$. There is a normal-form proof in `WStepE` $`c`$ if and only if $`c^3<4`$.*

Theorem 4 ($`\Leftarrow`$) is the result of \[DvMW11\] (Theorem 6.7 of \[W13\]), re-proved in Lean following the inductive argument printed in \[W13, §6.3\]. Lean’s normal-form predicate does not require $`a'\ge1`$ (needed by \[W13, Lemma 6.3\]); the proofs constructed have $`a'=c^2\ell`$ with $`\ell\ge1`$. The Lean version of Theorem 3 does not include the length bound of \[W13, Theorem 6.6\].

The proof of Theorem 2 has four steps: reduce to normal form (Section 4); handle end lines below the complement by replay (Section 5); map a normal-form proof into a reduced homogeneous calculus (Section 6); show the reduced calculus has no refutation (Section 7).

## 4. Reduction to normal form

Fix $`c`$ and a relation $`R\subseteq\texttt{WStepX}\,c`$ closed under complement. `WStep`, `WStepE` and `WStepX` are closed under complement (`TW.wstep_compl`, `TW.wstepE_compl`, `TW.wstepX_compl`), since every rule is stated symmetrically in $`\exists/\forall`$ and $`\mathsf{NTS}/\mathsf{coNTS}`$. The *outermost quantifier* of a non-quantifier-free line is the quantifier of its block 1.

**Lemma 5** (`TW.step_nil_nil`). *A step between two quantifier-free lines is a quantifier-free flip: it swaps the kernel type and its exponent $`e`$ satisfies $`e\ge c\max(a,1)`$.*

*Proof.* From a quantifier-free line only the speedup with an empty block list and `flipQ` apply, and the speedup opens two blocks. ◻

**Lemma 6** (`TW.outer_step`, `TW.stretch_outer`). *If $`L\to L'`$ is a step and neither $`L`$ nor $`L'`$ is quantifier-free, then $`L`$ and $`L'`$ have the same outermost quantifier. Hence the outermost quantifier is constant along any stretch of non-quantifier-free lines.*

*Proof.* A speedup on a nonempty block list adds blocks inside, or merges into the innermost block keeping its quantifier; a pop removes the innermost block, and since $`L'`$ is not quantifier-free, block 1 survives; a flip changes no block; `combine` and `split` replace blocks by blocks of the same quantifier, so the quantifier of block 1 is unchanged even when they act on it. ◻

**Lemma 7** (`TW.seg_types`). *Let $`M_0,\dots,M_n`$ ($`n\ge1`$) be a path whose end lines are quantifier-free and whose interior lines are not. Then the kernel type of $`M_n`$ is the opposite of that of $`M_0`$.*

*Proof.* If $`n=1`$ this is Lemma 5. Otherwise the first step is a speedup from an empty block list, so the outermost quantifier of $`M_1`$ matches the kernel type of $`M_0`$. By Lemma 6 this quantifier is unchanged up to $`M_{n-1}`$. The last step produces an empty block list from a nonempty one, so it is a pop of block 1, whose quantifier matches the kernel of $`M_{n-1}`$; the pop flips the kernel type. ◻

**Lemma 8** (`TW.qf_up`, `TW.qf_strict`). *Suppose there is no normal-form proof in $`R`$. Then for every $`R`$-path $`M_0,\dots,M_n`$ ($`n\ge1`$) whose two end lines are quantifier-free, the kernel exponent of $`M_n`$ is strictly larger than that of $`M_0`$.*

*Proof.* First let the path have no quantifier-free interior line (a *segment*). If $`M_0`$ has kernel $`\mathsf{NTS}`$, then $`M_n`$ has kernel $`\mathsf{coNTS}`$ by Lemma 7, and if the exponent did not increase the path would be a normal-form proof. If $`M_0`$ has kernel $`\mathsf{coNTS}`$, apply the same argument to the complemented path $`\neg M_0,\dots,\neg M_n`$, which is an $`R`$-path with the same exponents. So every segment strictly increases the exponent. A general path splits at its first quantifier-free interior line into a segment and a shorter path; conclude by strong induction on $`n`$. ◻

**Lemma 9** (`TW.exists_qf`). *Every $`R`$-path from $`A`$ to a line whose outermost quantifier is that of $`\neg A`$ (in particular to $`\neg A`$, or to any $`B\le\neg A`$) contains a quantifier-free line.*

*Proof.* Otherwise, by Lemma 6, the end line has the outermost quantifier of $`A`$; but complementation swaps it. ◻

**Lemma 10** (`TW.splice`). *Let $`L_0,\dots,L_N`$ be an $`R`$-path with $`L_N=\neg L_0`$, and $`0\le i\le N`$. Then there is an $`R`$-path of length $`N`$ from $`L_i`$ to $`\neg L_i`$.*

*Proof.* Concatenate the path with its complement $`\neg L_0=L_N,\neg L_1,\dots,\neg L_N=L_0`$ (an $`R`$-path by closure under complement), and take the window of length $`N`$ starting at position $`i`$. ◻

*Proof of Theorem 3.* Suppose there is no normal-form proof in $`R`$. By Lemma 9 some $`L_i`$ is quantifier-free; by Lemma 10 there is an $`R`$-path of length $`N\ge1`$ from $`L_i`$ to $`\neg L_i`$. Both ends are quantifier-free and have the same kernel exponent, contradicting Lemma 8. ◻

This argument needs no parity argument and no case split, unlike the proof of \[W13, Theorem 4.4\] that Theorem 6.6 refers to.

## 5. End lines below the complement

**Lemma 11** (replay; `TW.replay`, `TW.replay_path`). *Let $`c\ge0`$. If $`A\to A'`$ is a `WStepX` $`c`$ step and $`B\le A`$, then there is a line $`B'\le A'`$ with a `WStepX` $`c`$ step $`B\to B'`$. Consequently a `WStepX` $`c`$-path $`A_0,\dots,A_n`$ and a line $`B_0\le A_0`$ give a `WStepX` $`c`$-path $`B_0,\dots,B_n`$ with $`B_j\le A_j`$ for all $`j`$.*

*Proof.* Apply the same rule to $`B`$ with the same parameter $`x`$ and the same new values (new blocks, new kernel exponent) as in $`A'`$; the blocks of $`B`$ that the rule does not touch are kept. Whether a rule applies depends only on the quantifiers and kernel types, which $`B`$ shares with $`A`$. Every lower bound in `WStepX` is a nondecreasing function of the input values (for the costs $`c\max(\dots)`$ this uses $`c\ge0`$), so the bounds for $`B`$ are at most those for $`A`$, which the new values satisfy. The untouched blocks of $`B`$ are below those of $`A`$, and the new values are equal. ◻

**Lemma 12** (`TW.splice_le`). *Let $`c\ge0`$, let $`L_0,\dots,L_N`$ be a `WStepX` $`c`$-path with $`L_N\le\neg L_0`$, and $`0\le i\le N`$. Then there is a `WStepX` $`c`$-path of length $`N`$ from $`L_i`$ to a line $`S_N\le\neg L_i`$.*

*Proof.* The complemented prefix $`\neg L_0,\dots,\neg L_i`$ is a `WStepX` $`c`$-path. Replay it from $`L_N\le\neg L_0`$ (Lemma 11) to get $`L_N=B_0,\dots,B_i`$ with $`B_i\le\neg L_i`$, and take $`L_i,\dots,L_N=B_0,\dots,B_i`$. ◻

*Proof of Theorem 2.* $`c^3\ge4`$ implies $`c>1`$ (`TW.pos_of_cube`, `TW.one_lt_of_cube`). Part 2: a normal-form proof with one step is a quantifier-free flip (Lemma 5), whose exponent $`e\ge c\max(a,1)>a`$ contradicts $`e\le a`$. A normal-form proof with $`n\ge2`$ steps gives a refutation in the reduced calculus by Lemma 15, which Theorem 16 excludes. Part 1: suppose $`L_0,\dots,L_N`$ is a `WStepX` $`c`$-path with $`L_N\le\neg L_0`$. By Part 2 and Lemma 8 (with $`R=\texttt{WStepX}\,c`$), the exponent strictly increases between any two quantifier-free lines of a path. By Lemma 9 some $`L_i`$ is quantifier-free, and by Lemma 12 there is a path of length $`N`$ from $`L_i`$ to some $`S_N\le\neg L_i`$. Since $`\neg L_i`$ is quantifier-free, so is $`S_N`$, and its exponent is at most that of $`L_i`$: a contradiction. The corollaries follow from $`\texttt{WStepE}\subseteq\texttt{WStep}\subseteq\texttt{WStepX}`$, $`\texttt{WStepXE}\subseteq\texttt{WStepX}`$, and $`\neg A\le\neg A`$. ◻

The replay argument uses the relaxed rules: in `WStepE` and `WStepXE` outputs are exact, so a smaller line does not reach the same new values. Theorem 2(1) covers the exact systems because they are contained in `WStepX`.

## 6. The reduced calculus

The limit argument runs on a homogeneous relaxation, in the style of \[BW15\], adapted to two kernel types (`TL.TLine`, `TL.TStep`).

**Definition 13** (reduced lines and rules). A *reduced line* is $`(s_1,\dots,s_m;\,t;\,a)`$: a list of reals (input constraints, outermost first), a flag $`t\in\{\mathrm{match},\mathrm{opp}\}`$ and a real $`a`$. Its *depth* is $`m`$, and $`\mathrm{top}(s)=s_m`$ ($`\mathrm{top}(\emptyset)=0`$). Write $`s\cdot b`$ for the list $`s`$ with $`b`$ appended. The rules of $`\texttt{TStep}\,c`$ are:

- `init`: $`(\emptyset;\mathrm{match};a)\vdash(0;\mathrm{match};a)`$ (a virtual block of constraint $`0`$ stands for the input);

- `speedM`: $`(s\cdot b;\mathrm{match};a)\vdash(s\cdot b_1\cdot b_2;\mathrm{opp};a_2)`$ with $`0\le x\le a`$, $`b_1\ge\max(x,b)`$, $`b_2\ge b`$, $`a_2\ge a-x`$;

- `speedO`: $`(s\cdot b;t;a)\vdash(s\cdot b\cdot b_1\cdot b_2;\mathrm{opp};a_2)`$ for either flag $`t`$, with the same conditions;

- `flip`: $`(s\cdot b;t;a)\vdash(s\cdot b;\bar t;e)`$ with $`e\ge c\max(b,a)`$, in both directions;

- `pop`: $`(s\cdot b;\mathrm{match};a)\vdash(s;t';e)`$ for either flag $`t'`$, with $`e\ge c\max(\mathrm{top}(s),b,a)`$;

- `popIn`: $`(s\cdot b;\mathrm{match};a)\vdash(s\cdot b';\mathrm{opp};e)`$ with $`b'\ge0`$ and $`e\ge c\max(b',b,a)`$;

- `weak`: increase any entries and $`a`$, keeping depth and flag.

$`\texttt{TRefutes}\,c\,n\,L`$ says: $`L_0,\dots,L_n`$ is a $`\texttt{TStep}\,c`$-path with $`n\ge2`$, $`L_0`$ has depth $`0`$ and exponent $`a_0>0`$, $`L_n`$ has depth $`0`$ and exponent $`\le a_0`$, and no interior line has depth $`0`$. The flags of $`L_0`$ and $`L_n`$ are not constrained, so the Lean statement of Theorem 16 is slightly stronger than one with fixed end flags.

A *run* of a literal line is a maximal sequence of adjacent blocks of the same type. The *encoding* `TW.enc` maps a literal line to the list with one entry per run (outermost first), namely $`\max(o,0)`$ for the input constraint $`o`$ of the innermost block of the run (`TW.rr`); the flag “matching” ($`\mathrm{match}`$ for a quantifier-free line); and $`\max(a,0)`$. Guess exponents, and the input constraints of blocks that are not innermost in their run, are dropped. So two blocks of the same type that are adjacent count as one reduced block, which is what makes combining and splitting harmless; the price is `popIn`, which is a pop of the innermost block of a run of length at least two: the run survives, its entry becomes the constraint $`b'`$ of the next block, and the kernel no longer matches.

**Lemma 14** (simulation; `TW.sim`, `TW.sim0`). *Let $`c\ge0`$. A `WStepX` $`c`$ step $`L\to L'`$ from a line with a nonempty block list is one `TStep` $`c`$ step from $`\mathrm{enc}(L)`$ to $`\mathrm{enc}(L')`$. A `WStepX` $`c`$ step from a quantifier-free line $`L`$ to a line $`L'`$ that is not quantifier-free is `init` followed by one `TStep` $`c`$ step to $`\mathrm{enc}(L')`$. Alternation is not needed.*

*Proof.* Each reduced rule only bounds outputs from below by expressions monotone in the inputs, and the literal rules give at least these bounds. A speedup that opens new blocks after an innermost block $`u`$ of the other type becomes `speedO`; if $`u`$ has the type of the new outer block, the new block joins the run of $`u`$ and the step becomes `speedM` with $`b=\max(o_u,0)`$ and $`b_1=\max(o_1,0)\ge\max(x,b)`$; from the empty list it becomes `init` then `speedM` with $`b=0`$ (the literal constraints $`\max(1,x)`$ and $`1`$ dominate $`\max(x,0)`$ and $`0`$); `speedMerge` acts on a matching kernel and becomes `speedM` with $`b=\max(o,0)`$. A literal pop costs $`c\max(g,a,o,\mathrm{pin}(\mathit{rest}))`$. If the next block has the other type, or there is none, it removes a whole run and becomes a reduced pop, with $`\max(\mathrm{pin}(\mathit{rest}),0)\ge\mathrm{top}`$ (and $`\mathrm{pin}(\emptyset)=1\ge0=\mathrm{top}(\emptyset)`$); otherwise it becomes `popIn` with $`b'=\max(\mathrm{pin}(\mathit{rest}),0)`$. A literal flip of either kernel becomes a reduced flip. `combine` and `split` keep the runs and their order (the blocks involved have one type); they change only the entry of the run they act in, and only if they act at its innermost block, where the new innermost constraint is at least the old one. They are `weak` steps (`TW.rr_drop`, `TW.rr_mono`, `TW.weak_f2`). If $`x>a`$, the reduced step uses $`x'=\min(x,\max(a,0))`$, and clamping the kernel at $`0`$ keeps the inequalities (`TW.clamp_sub`, `TW.cmax_le`). ◻

**Lemma 15** (`TW.nf_trefutes`). *Let $`c>0`$. A normal-form `WStepX` $`c`$ proof with $`n\ge2`$ steps gives a $`\texttt{TRefutes}\,c\,(n+1)`$ instance.*

*Proof.* Encode the lines and insert `init` after the first. The last literal step reaches a quantifier-free line from a line that is not, so it pops block 1, at cost at least $`c\cdot\mathrm{pin}(\emptyset)=c>0`$ (`TW.pop_pos`), so $`a\ge a'\ge c>0`$. ◻

Two facts about `TStep` are used below. For $`c\ge0`$, nonnegativity of all entries and the exponent is preserved from the start line (`TL.tstep_nonneg`). On nonnegative lines, a $`\texttt{TStep}\,c`$ step is a $`\texttt{TStep}\,c_0`$ step for every $`c_0\le c`$, since every cost is $`c`$ times a nonnegative quantity (`TL.tstep_restrict`). So for the limit theorem we may replace $`c`$ by $`\min(c,2)`$ and assume $`\sqrt[3]{4}\le c\le2`$.

## 7. The limit theorem

**Theorem 16** (`TL.no_trefutation`). *If $`c^3\ge4`$ then $`\texttt{TRefutes}\,c\,n\,L`$ fails for all $`n`$ and $`L`$.*

It follows from a quantitative bound on genuine excursions.

**Theorem 17** (return bound; `TL.return_bound`). *Let $`c^3\ge4`$ and let $`L_0,\dots,L_n`$ be a $`\texttt{TStep}\,c`$-path with $`n\ge2`$, where $`L_0`$ has depth $`0`$ and exponent $`a_0\ge0`$, every interior line has positive depth, and $`L_n`$ has depth $`0`$. Then the exponent of $`L_n`$ is at least $`(\min(c,2)^2/2)\,a_0\ge 2^{1/3}a_0`$.*

The hypotheses are needed: a single `weak` step at depth $`0`$ is a path from $`(\emptyset;t;a_0)`$ to $`(\emptyset;t;a_0)`$. Since $`\min(c,2)^3\ge4`$, $`\min(c,2)^2\ge 4^{2/3}=2\cdot2^{1/3}`$. For $`a_0>0`$ the bound exceeds $`a_0`$, which gives Theorem 16.

### 7.1 The potential

Let $`\sqrt[3]{4}\le c\le2`$, $`\gamma=c/2`$ and $`\kappa=5/2`$. For reals $`b,a`$ define
``` math
\Psi(b,a)=\min\bigl(\max(b,a),\ \max(\gamma a,\kappa b)\bigr)\qquad(\texttt{TL.Ps}).
```
The potential of a reduced line with $`\mathrm{top}=b`$ and exponent $`a`$ is $`\Psi(b,a)`$ if it is matching and $`\Psi(b,c\,\Psi(b,a))`$ if it is opposite (`TL.pot`). For an opposite line, a flip to matching costs $`e\ge c\max(b,a)\ge c\Psi(b,a)`$, so $`\Psi(b,c\Psi(b,a))`$ is a lower bound for the potential after the flip; it is not in general equal to it. For example at $`b=0`$, $`a=1`$, $`c=\sqrt[3]{4}`$ the defined value is $`\Psi(0,c^2/2)=c^3/4=1`$, while the flip gives the matching line $`(0;\mathrm{match};c)`$ of potential $`c^2/2>1`$.

**Lemma 18** (`TL.ps_mono`, `ps_le_max`, `ps_ge_g`, `ps_ge_min`, `ps_ge_b`, `ps_nonneg`). *For $`b,a\ge0`$ and $`0\le c\le2`$ where needed: $`\Psi`$ is monotone in both arguments; $`\Psi(b,a)\le\max(b,a)`$; $`\Psi(b,a)\ge\gamma a`$; $`\Psi(b,a)\ge\min(a,\kappa b)`$; $`\Psi(b,a)\ge b`$ if $`a\le b`$; $`\Psi(b,a)\ge0`$.*

**Lemma 19** (`TL.ps_le_cps`, `TL.ps_le_pot`, `TL.pot_le_opp`). *Let $`0\le c\le 2`$ and $`c^2\ge2`$, and let $`L`$ be a nonnegative reduced line with $`\mathrm{top}=b`$ and exponent $`a`$. Then $`a\le c\Psi(b,a)`$, and $`\Psi(b,a)\le\mathrm{pot}(L)\le\Psi(b,c\Psi(b,a))`$, whichever its flag.*

*Proof.* $`c\Psi(b,a)\ge c\gamma a=(c^2/2)a\ge a`$; the rest is monotonicity of $`\Psi`$. ◻

**Lemma 20** (`TL.cfacts`). *For $`\sqrt[3]{4}\le c\le 2`$: $`c\ge3/2`$, $`c^2\ge5/2`$, $`c-c^2/5\ge1`$, $`c^4/4\ge c`$, and $`c^3/4\ge1`$.*

The constant $`\kappa=5/2`$ is chosen just below $`(\sqrt[3]{4})^2\approx2.5198`$.

### 7.2 The key inequality

**Lemma 21** (key inequality; `TL.key`). *Let $`\sqrt[3]{4}\le c\le2`$, $`b\ge0`$, $`0\le x\le a`$, $`T\ge\max(x,b)`$, $`D=a-x`$, $`P=\Psi(b,D)`$, $`W=\Psi(b,cP)`$ and $`E\ge c\max(T,W)`$. Then $`\Psi(b,a)\le\Psi(T,E)`$.*

Reading: a matching line with top $`b`$ and exponent $`a`$ is sped up by $`x`$; the merged configuration block ends with constraint $`T`$; the inner part has potential at least $`W`$ when it returns, and popping the index block costs $`E`$. The potential does not drop.

*Proof.* Write $`h=\Psi(b,a)`$, so $`h\le\max(b,a)`$ and $`h\le\max(\gamma a,\kappa b)`$; in particular $`h\le\gamma a`$ or $`h\le\kappa b`$. Since $`\Psi(T,E)=\min(\max(T,E),\max(\gamma E,\kappa T))`$, it suffices to show (A) $`E\ge h`$ and (B) $`\max(\gamma E,\kappa T)\ge h`$. We use $`E\ge cT\ge cx`$, $`E\ge cW`$, and, from Lemma 18, $`P\ge\gamma D`$, $`W\ge\gamma cP\ge(c^3/4)D\ge D`$, $`P\ge\min(D,\kappa b)`$ and $`W\ge\min(cP,\kappa b)`$.

\(A\) If $`h\le cT`$ we are done, so assume $`cT<h`$; then $`cb<h`$.

- *Case $`D\le b`$.* Then $`P\ge b`$ and $`W\ge\min(cb,\kappa b)=cb`$, so $`E\ge c^2b`$. If $`h\le c^2 b`$ we are done. Otherwise $`h>c^2b\ge\kappa b`$, so $`h\le\gamma a`$, and $`c^2b<\gamma a=ca/2`$ gives $`cb<a/2`$. Since $`x\ge a-b`$, we get $`E\ge cx\ge ca-cb>ca-a/2\ge ca/2\ge h`$, using $`c\ge1`$.

- *Case $`D>b`$ and $`h\le\gamma a`$.* From $`E\ge cW\ge cD`$ and $`E\ge cx`$ we get $`2E\ge c(D+x)=ca`$, so $`E\ge\gamma a\ge h`$.

- *Case $`D>b`$ and $`h\le\kappa b`$.* If $`W\ge\kappa b`$ then $`E\ge c\kappa b\ge\kappa b\ge h`$. Otherwise $`W\ge cP`$. If $`P\ge D`$ then $`E\ge c^2D\ge\kappa D>\kappa b\ge h`$. If $`P\ge\kappa b`$ then $`E\ge c^2\kappa b\ge h`$.

\(B\) If $`\kappa T\ge h`$ we are done, so assume $`\kappa T<h`$. Then $`\kappa x<h`$ and $`\kappa b<h`$, so $`h\le\gamma a`$, and $`\kappa x<\gamma a`$ gives $`x<(\gamma/\kappa)a=(c/5)a`$. Hence
``` math
E\ge cW\ge c\cdot\tfrac{c^3}{4}D=\tfrac{c^4}{4}D\ge cD=c(a-x)\ge\bigl(c-\tfrac{c^2}{5}\bigr)a\ge a,
```
using Lemma 20 and $`a\ge0`$ (which follows from $`0\le\kappa b<h\le\gamma a`$). So $`\gamma E\ge\gamma a\ge h`$. ◻

**Remark 22** (tightness). At $`c^3=4`$, $`b=0`$, $`x=a/2`$, $`T=a/2`$, $`E=c\max(T,W)`$: $`P=ca/4`$, $`W=c^3a/8=a/2`$, $`E=ca/2`$ and $`\Psi(a/2,ca/2)=ca/2=\Psi(0,a)`$, so case (A) is an equality. This is one stage of the \[DvMW11\] recursion: speed up by half, use the previous stage twice, pop. Correspondingly, the fixed-point equation $`s=1+s^2/c^3`$ of \[W13, Claim 2\] has a real solution if and only if $`c^3\ge4`$.

### 7.3 Segments and excursions

Fix $`\sqrt[3]{4}\le c\le 2`$ and a $`\texttt{TStep}\,c`$-path $`L_0,L_1,\dots`$. Depth changes by $`+1`$ under `speedM`, by $`+2`$ under `speedO`, by $`-1`$ under `pop`, and not at all under `flip`, `popIn` and `weak` (`TL.tstep_len`, `TL.tstep_pop`).

**Lemma 23** (`TL.entry_mono`). *If every line $`L_i`$ with $`p\le i<q`$ has depth at least $`k+2`$, then entry $`k`$ (0-indexed) of $`L_q`$ is at least entry $`k`$ of $`L_p`$.*

*Proof.* A step from a line of depth $`\ge k+2`$ changes only entries at positions $`\ge k+1`$ (`popIn` changes only the last entry), except `weak`, which increases entries. ◻

**Lemma 24** (segment lemma; `TL.segment`). *Let $`L_p,\dots,L_{p+\ell}`$ be nonnegative lines (all entries and exponents $`\ge0`$), all of depth $`\ge k+1`$, and let $`L_p`$ and $`L_{p+\ell}`$ have depth exactly $`k+1`$. Then $`\mathrm{pot}(L_p)\le\mathrm{pot}(L_{p+\ell})`$.*

**Lemma 25** (excursion lemma; `TL.excursion`). *Assume Lemma 24 for all stretches shorter than $`q-p`$. Let $`L_p,\dots,L_{q-1}`$ be nonnegative lines, $`L_p`$ of depth $`k+1`$, $`L_i`$ of depth $`\ge k+1`$ for $`p\le i<q`$, and $`L_q`$ of depth $`k`$. Then the exponent of $`L_q`$ is at least $`c\max(\mathrm{top}(L_q),\mathrm{pot}(L_p))`$.*

*Proof.* Depth drops only by `pop`, so $`L_{q-1}=(s\cdot b;\mathrm{match};a)`$ has depth $`k+1`$ and $`L_q=(s;t';e)`$ with $`e\ge c\max(\mathrm{top}(s),b,a)`$. By Lemma 24 on $`L_p,\dots,L_{q-1}`$, $`\mathrm{pot}(L_p)\le\mathrm{pot}(L_{q-1})=\Psi(b,a)\le\max(b,a)`$. ◻

*Proof of Lemma 24.* Strong induction on $`\ell`$; for $`\ell=0`$ there is nothing to show. Let $`b=\mathrm{top}(L_p)`$ and $`a`$ its exponent. Split on the first step $`L_p\to L_{p+1}`$. `init` and `pop` cannot occur (depth $`\ge1`$, and a pop would reach depth $`k`$); `popIn` keeps the depth.

- `weak`, `flip`: $`L_{p+1}`$ has depth $`k+1`$, and by induction it suffices to show $`\mathrm{pot}(L_p)\le\mathrm{pot}(L_{p+1})`$. For `weak` this is monotonicity of $`\Psi`$. For a flip from matching to opposite with new exponent $`e\ge c\max(b,a)\ge ca`$: $`c\Psi(b,e)\ge c\gamma e\ge(c^3/2)a\ge a`$, so $`\Psi(b,c\Psi(b,e))\ge\Psi(b,a)`$. For a flip from opposite to matching: $`e\ge c\max(b,a)\ge c\Psi(b,a)`$, so $`\Psi(b,e)\ge\Psi(b,c\Psi(b,a))`$.

- `popIn`: $`L_{p+1}=(s\cdot b';\mathrm{opp};e)`$ has depth $`k+1`$, with $`e\ge c\max(b,a)=:cm`$. As for the flip, $`\Psi(b',e)\ge\gamma e`$ and $`\Psi(b',c\Psi(b',e))\ge\gamma c\Psi(b',e)\ge (c^3/4)e\ge(c^4/4)m\ge m\ge\Psi(b,a)`$, whatever $`b'`$ is, so $`\mathrm{pot}(L_p)\le\mathrm{pot}(L_{p+1})`$ and induction finishes.

- `speedM`: $`L_p=(s\cdot b;\mathrm{match};a)`$, $`L_{p+1}=(s\cdot b_1\cdot b_2;\mathrm{opp};a_2)`$. Let $`L_m`$ be the first line after $`p`$ of depth $`\le k+1`$; it has depth exactly $`k+1`$ and $`m\le p+\ell`$. By monotonicity, $`\mathrm{pot}(L_{p+1})=\Psi(b_2,c\Psi(b_2,a_2))\ge\Psi(b,c\Psi(b,a-x))=W`$. By Lemma 25 (at level $`k+1`$), $`L_m`$ has exponent $`E\ge c\max(T,W)`$, where $`T=\mathrm{top}(L_m)`$; by Lemma 23, $`T\ge b_1\ge\max(x,b)`$. Lemma 21 and Lemma 19 give $`\mathrm{pot}(L_p)=\Psi(b,a)\le\Psi(T,E)\le\mathrm{pot}(L_m)`$, and the induction hypothesis on $`L_m,\dots,L_{p+\ell}`$ finishes.

- `speedO`: $`L_p=(s\cdot b;t;a)`$ with either flag, $`L_{p+1}=(s\cdot b\cdot b_1\cdot b_2;\mathrm{opp};a_2)`$. Let $`m_1`$ be the first index after $`p`$ with depth $`\le k+2`$ and $`m_0`$ the first index after $`m_1`$ with depth $`\le k+1`$. As in the previous case (excursion at level $`k+2`$), $`\Psi(b,a)\le\mathrm{pot}(L_{m_1})`$ by Lemmas 21 and 19 applied to the virtual matching line $`(b,a)`$. By Lemma 25 at level $`k+1`$, $`L_{m_0}`$ has exponent $`\ge c\,\mathrm{pot}(L_{m_1})\ge c\Psi(b,a)`$, and by Lemma 23 its top is $`\ge b`$. So $`\mathrm{pot}(L_{m_0})\ge\Psi(b,c\Psi(b,a))\ge\mathrm{pot}(L_p)`$ by Lemma 19, and induction finishes.

 ◻

*Proof of Theorem 17.* Replace $`c`$ by $`\min(c,2)`$ (Section 6); all lines are nonnegative. The first step must be `init` (the other rules need depth $`\ge1`$, and `weak` would give a quantifier-free interior line, since $`n\ge2`$), so $`L_1=(0;\mathrm{match};a_0)`$ with $`\mathrm{pot}(L_1)=\Psi(0,a_0)\ge\gamma a_0`$. The rest is one excursion from depth 1 to depth 0, so by Lemma 25 the final exponent is at least $`c\gamma a_0=(c^2/2)a_0`$. ◻

## 8. The construction below $`\sqrt[3]{4}`$

We follow the inductive argument of \[W13, §6.3\] (Claims 1 and 2), using only the exact rules `WStepE`. Fix $`c\ge1`$. For a kernel type $`k`$ write $`Q_k`$ for the matching quantifier and $`\bar Q_k`$, $`\bar k`$ for the opposite ones. All derivations below pass only through lines that are not quantifier-free (`TDL.DNW`).

**Definition 26** (`TDL.MacE`, `TDL.InnerE`). $`\mathrm{Mac}(s,R)`$ holds if for every scale $`\ell\ge R`$ and every kernel type $`k`$ the following hold, where in each case $`w,g,\kappa`$ are some reals (depending on the data) with $`1\le w\le\ell`$, $`g\le w`$, $`\kappa\le\ell`$:

1.  for every block list $`P`$ with $`\mathrm{pin}(P)=1`$ whose innermost block (if any) is not of type $`Q_k`$, the line $`P\,K_k[n^{s\ell}]`$ derives $`P\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,n^{g})^{w}\,K_{\bar k}[n^{\kappa}]`$;

2.  for every $`g_0\le\ell`$ and every $`\mathit{rest}`$, the line $`\mathit{rest}\,(Q_k\,n^{g_0})^{1}\,K_k[n^{s\ell}]`$ derives $`\mathit{rest}\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,n^{g})^{w}\,K_{\bar k}[n^{\kappa}]`$.

$`\mathrm{Inner}(s,R)`$ holds if for every $`\ell\ge R`$, every $`P`$ and $`k`$, the line $`P\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,\log n)^{1}\,K_k[n^{s\ell-\ell}]`$ derives $`P\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,n^{g})^{w}\,K_{\bar k}[n^{\kappa}]`$ for some $`w,g,\kappa`$ as above.

**Lemma 27** (`TDL.macE_of_inner`). *If $`R\ge1`$, $`s\ge1`$ and $`\mathrm{Inner}(s,R)`$, then $`\mathrm{Mac}(s,R)`$.*

*Proof.* Apply the speedup with $`x=\ell`$ to the kernel exponent $`s\ell\ge1`$, with $`b=\mathrm{pin}(P)=1`$ (case 1, `speedNew`) or $`b=1`$ from the block $`(Q_k\,n^{g_0})^1`$ (case 2, `speedMerge`, where $`\max(g_0,\ell)=\ell`$). Both give $`(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,\log n)^{1}\,K_k[n^{s\ell-\ell}]`$; then use $`\mathrm{Inner}(s,R)`$. ◻

**Lemma 28** (base, W13’s stage 2; `TDL.innerE_base`). *If $`R\ge c`$ then $`\mathrm{Inner}(1+1/c,R)`$.*

*Proof.* The kernel exponent is $`\ell/c\ge1`$, and the kernel is opposite to the $`\log n`$ block. Flip (Lemma 6.2(3)/(4)) at cost $`c\max(\ell/c,1)=\ell`$; take $`w=1`$, $`g=0`$, $`\kappa=\ell`$. ◻

**Lemma 29** (stage step; `TDL.innerE_step`). *If $`R\ge1`$, $`s\ge1`$ and $`\mathrm{Mac}(s,R)`$, then $`\mathrm{Inner}(1+s^2/c^3,\,c^3R)`$.*

*Proof.* Let $`\ell\ge c^3R`$, $`\mu=s\ell/c^3`$ and $`\nu=\ell/c`$; then $`\mu,\nu\ge R\ge1`$, $`\nu\le\ell`$, and the kernel exponent is $`(1+s^2/c^3)\ell-\ell=s\mu`$. Write $`C=P\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,\log n)^{1}`$; $`\mathrm{pin}(C)=1`$ and its innermost block is not of type $`Q_k`$.

1.  $`\mathrm{Mac}(s,R)`$, case 1, at scale $`\mu`$: $`C\,K_k[n^{s\mu}]`$ derives $`C\,(Q_k\,n^{\mu})^{\mu}(\bar Q_k\,n^{g_1})^{w_1}K_{\bar k}[n^{\kappa_1}]`$.

2.  Pop the $`\bar Q_k`$ block: cost $`c\max(g_1,\kappa_1,w_1,\mu)=c\mu`$, giving $`C\,(Q_k\,n^{\mu})^{\mu}K_k[n^{c\mu}]`$.

3.  Pop the $`Q_k`$ block: cost $`c\max(\mu,c\mu,\mu,1)=c^2\mu=s\nu`$, giving $`C\,K_{\bar k}[n^{s\nu}]`$. Now the innermost block $`(\bar Q_k\,\log n)^1`$ matches the kernel.

4.  $`\mathrm{Mac}(s,R)`$, case 2 (kernel type $`\bar k`$, $`g_0=0`$), at scale $`\nu`$: derive $`P\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,n^{\nu})^{\nu}(Q_k\,n^{g_2})^{w_2}K_k[n^{\kappa_2}]`$.

5.  Pop the $`Q_k`$ block: cost $`c\max(g_2,\kappa_2,w_2,\nu)=c\nu=\ell`$, giving $`P\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,n^{\nu})^{\nu}K_{\bar k}[n^{\ell}]`$.

Take $`w=g=\nu`$ and $`\kappa=\ell`$. No weakening is needed: the final $`\bar Q_k`$ block keeps its exact exponent $`\nu`$. ◻

Let $`s_0=1+1/c`$ and $`s_{j+1}=1+s_j^2/c^3`$ (`TDL.sq`; these are the ratios $`s_k`$ of \[W13, Claim 2\], shifted to start at the $`s_2`$ of \[W13\]). Induction gives $`\mathrm{Mac}(s_j,\,c(c^3)^j)`$ for all $`j`$ (`TDL.macE_all`). Since
``` math
s_{j+1}-s_j=\frac{(s_j-c^3/2)^2}{c^3}+1-\frac{c^3}{4}\ge1-\frac{c^3}{4},
```
we have $`s_j\ge1+j(1-c^3/4)`$ (`TDL.sq_growth`).

*Proof of Theorem 4.* ($`\Rightarrow`$) A normal-form proof in `WStepE` is one in `WStepX`, excluded for $`c^3\ge4`$ by Theorem 2. ($`\Leftarrow`$) If $`c^3<4`$, pick $`j`$ with $`s_j\ge c^2`$ and let $`\ell=c(c^3)^j\ge1`$. By $`\mathrm{Mac}(s_j,\ell)`$, case 1 with $`P`$ empty and $`k=\mathsf{NTS}`$, the line $`\mathsf{NTS}[n^{s_j\ell}]`$ derives $`(\exists\,n^{\ell})^{\ell}(\forall\,n^{g})^{w}\mathsf{coNTS}[n^{\kappa}]`$. Pop the $`\forall`$ block at cost $`c\ell`$ and then the $`\exists`$ block at cost $`c\max(\ell,c\ell,\ell,1)=c^2\ell\le s_j\ell`$, reaching $`\mathsf{coNTS}[n^{c^2\ell}]`$. ◻

**Side conditions.**

Every speedup in this construction has $`b=1`$ and kernel exponent $`s\ell\ge1`$, and leaves a kernel exponent $`\ge1`$: in the base case $`\ell/c\ge1`$, and in the stage step $`s\mu\ge\mu\ge1`$. These facts are established inside the Lean proofs (`innerE_base`, `innerE_step`), although they are not part of the statement of `nf_exists`. So every speedup also satisfies the bound $`x\le a-1`$ of \[W13, Lemma 3.3\]. That every other line also has kernel exponent $`\ge1`$ is not stated in Lean and is not needed. For the depth of the recursion it suffices to choose $`j>c^2/(1-c^3/4)`$, and the number of lines roughly doubles with each stage, so the proofs become very long as $`c\to\sqrt[3]{4}`$.

The reduced calculus has the same threshold (`TD.dvmw`, `TD.threshold`): for $`c\ge1`$, $`\texttt{TRefutes}\,c`$ instances exist if and only if $`c^3<4`$.

## 9. What is and is not verified

**(a) Kernel-checked.**

Lean 4.31 with Mathlib (pinned revision in the repository). The library builds with no `sorry`, no `admit`, no `native_decide` and no new axioms; `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for every headline theorem. Checked are: Theorems 2, 3, 4, 16 and 17; Lemmas 11, 14 and 15; the key inequality and the segment lemma; and non-vacuity: the five-line example of \[W13, §6\] is a normal-form proof under the exact rules at $`c=5/4`$ (`TW.w5_nf`), a proof $`A\subseteq\neg A`$ with $`a'=a`$ exists at $`c=5/4`$ (`TW.wq_proof`), the identity of \[W13, §2\] is a step of `WStepXE` (`TW.w13_combine`), the combining step on p. A:27 is one `WStepX` step if omitted input constraints are read as block-local defaults (`TW.a27_combine`) and three `WStepX` steps if they are read positionally (`TW.a27_combine_indexed`), and a five-step reduced refutation exists at $`c=13/10`$ (`TL.tlv_refutes`).

**(b) Not machine-checked.**

- *That the formal rules cover the calculus of \[W13\].* This is a modelling claim. Table 1 compares the rules with \[W13, §2 and §6\]. \[W13\] fixes the notion of alternation-trading proof in §6 only by analogy with §4 (“analogous” rules, normal form and Theorem 6.6), so Conjecture 6.8 itself is informal; our theorem concerns the formal rule sets. The extended system `WStepX` removes the dependence on whether same-type blocks are merged at a speedup, kept apart, or combined (or split) later anywhere in a line, whether lines alternate, and whether the matching-kernel and quantifier-free flips count as rules. The reading points that remain are these.

  1.  *$`n^{o(1)}`$ terms.* Lemma 6.1 is stated with space $`n^s`$: guess $`x+s`$ and superscripts $`\max\{b,x+s\}`$ and $`\max\{b,s\}`$. The formalisation sets $`s=0`$, following the convention stated after \[W13, Definition 4.1\] that polylogarithmic and $`n^{o(1)}`$ factors do not affect the exponents of these proofs. Since our impossibility already holds at $`c=\sqrt[3]{4}`$, the conjecture’s range $`c>\sqrt[3]{4}`$ leaves room for such vanishing terms; we do not make this precise.

  2.  *Outer input.* We take $`b=1`$ for the block outside the outermost one (the input has length $`n`$).

  3.  *Dual speedup.* We read the speedup for a $`\mathsf{coNTS}`$ kernel (which Lemma 6.1 does not state separately) as the complement of the $`\mathsf{NTS}`$ rule, as used in \[W13, eq. (18)\].

- *Soundness of the calculus*, i.e. \[W13, Theorem 3.1 and Lemmas 6.1--6.5\], the identity of \[W13, §2\], and the simulation argument for the two flips not printed in Lemma 6.2. These are published or standard results, in the range of parameters discussed under “Soundness scope” in Section 2; we do not formalise complexity classes. Theorem 4 ($`\Leftarrow`$) is a lower bound for TAUTOLOGY only through \[W13, Lemma 6.5\], applied to proofs in `WStepE`, i.e. in the published calculus; Lemma 6.5 is not claimed for the extended system (see “Soundness scope”).

**(c) Rule variants and end lines.**

Three variants that a literal reading of \[W13\] permits are rules of `WStepX`: the speedup that does not merge a new block into an adjacent block of the same type (with the resulting non-alternating lines and pops that leave an opposite kernel), the in-place flip of a matching kernel, and the quantifier-free flip. So are combining two adjacent blocks of the same type as a step of its own, anywhere in a line and also when the start line already has such blocks, and the converse splitting. Theorem 2 covers all of them. Theorem 2(1) also covers proofs that end at any line $`B\le\neg A`$, not only at $`\neg A`$; \[W13, Theorem 6.6\] is itself stated for complementary classes.

**(d) The published listing and table.**

The 11-line proof printed in \[W13, §6.2\] gives one exponent per quantifier block, in the position of the guess exponent of \[W13\]’s notation $`(Q\,n^{a})^{b}`$; the input constraints are not printed. The listing is ambiguous as printed. With $`c=1.419`$, the kernel exponents determine the speedup parameters, and the script `scripts/w13_listing.py` (exact rational arithmetic) recomputes every kernel exponent under two readings:

- if the printed exponent is the guess exponent (a $`\log n`$ block shown as $`n^1`$), every printed kernel exponent follows from the rules with the $`b`$ term of Lemma 6.2(1),(2), and also without it. The value $`2.378351877`$ of the $`\forall`$ block in lines 6–8 is then a guess exponent above the value $`1.676076023`$ given by Lemma 6.1, which the LP form allows; it does not affect any cost (the pop at line 9 costs $`c\max(2.378\ldots,2.378\ldots,\dots)=3.3749`$ either way);

- if the printed exponent is the input constraint, the step from line 7 to line 8 matches only without the $`b`$ term (with it, the pop would cost $`3.3749`$ instead of the printed $`2.3784`$).

So the listing alone does not decide whether the $`b`$ term is present. The table of \[W13, §6.2\] does: the script `scripts/w13_lp.py` solves the LP of \[W13, §6.1\] exactly for every valid annotation (an exact simplex over the rationals, bisection on $`c`$) and gives, with the $`b`$ term, best exponents $`1.3802`$ for 8 lines and $`1.4196`$ for 11 lines, attained by the optimal annotations listed in \[W13\], which agree with the tabulated $`1.380`$ and $`1.419`$; for 14 lines (bisection to three digits) the four annotations listed there are exactly those whose computed interval is the best one, $`[1.4326,1.4336]`$ (tabulated: $`1.433`$); bisection does not show that their exact optima coincide. Deciding feasibility exactly at single values of $`c`$ (option `--at`) narrows this: all four are feasible at $`c=1.43308`$, and none of the 55 valid 14-line annotations is feasible at $`c=1.43310`$. For 5 lines it gives $`1.3247`$, the real root of $`c^3=c+1`$, which agrees with the text of \[W13, p. A:27\] (``$`c^3\ge 1+c`$ implies $`c\ge1.324`$’’), against the tabulated $`1.323`$. Without the $`b`$ term the 5-, 8- and 11-line values are $`1.4655`$, $`1.5701`$ and $`1.6663`$; the last exceeds $`\sqrt[3]{4}`$. At 14 lines without it, four annotations are feasible at $`c=1.69261`$ and none at $`c=1.69263`$. We therefore read the calculus as including the $`b`$ term, as Lemma 6.2 states; our theorems include it.

**(e) Scope.**

The result limits the formalised proof calculus. Rules outside `WStepX`—for example other speedup or slowdown variants, or non-relativizing ingredients—are not covered. Nothing here bears on lower bounds for TAUTOLOGY proved by other methods.

## 10. Relation to earlier work

\[W13, Theorem 6.9\] (no proof for $`c\ge\varphi`$) is proved by deleting a pattern $`1,0,0`$ from a minimal annotation. Our potential adds the cap $`\max(b,a)`$ and the $`\kappa b`$ term, and treats two line types (matching and opposite). For SAT versus $`\mathsf{DTS}`$, Buss and Williams \[BW15\] showed that alternation-trading proofs stop at $`2\cos(\pi/7)\approx1.8019`$, the exponent reached by earlier alternation-trading proofs of Williams; their proof uses an invariant on achievable pairs. Here a scalar potential on two line types and a first-return induction play that role. Buss’s survey \[B13\] reviews these results and lists the optimality of $`\sqrt[3]{4}`$ as open.

## Licence

This text is licensed under CC BY 4.0. The Lean code is licensed under the Apache License 2.0.

## References

- **[B13]** S. Buss. Alternation trading proofs and their limitations. In K. Chatterjee and J. Sgall, editors, *Mathematical Foundations of Computer Science 2013 (MFCS 2013)*, volume 8087 of *Lecture Notes in Computer Science*, pages 1–7. Springer, 2013. [doi:10.1007/978-3-642-40313-2_1](https://doi.org/10.1007/978-3-642-40313-2_1).
- **[BW15]** S. R. Buss and R. Williams. Limits on alternation trading proofs for time–space lower bounds. *Computational Complexity*, 24(3):533–600, 2015. [doi:10.1007/s00037-015-0104-9](https://doi.org/10.1007/s00037-015-0104-9). Preliminary version in CCC 2012, pages 181–191.
- **[DvMW11]** S. Diehl, D. van Melkebeek, and R. Williams. An improved time-space lower bound for tautologies. *Journal of Combinatorial Optimization*, 22(3):325–338, 2011. [doi:10.1007/s10878-009-9286-x](https://doi.org/10.1007/s10878-009-9286-x). Preliminary version in COCOON 2009, volume 5609 of *Lecture Notes in Computer Science*, pages 429–438.
- **[FvM00]** L. Fortnow and D. van Melkebeek. Time-space tradeoffs for nondeterministic computation. In *Proceedings of the 15th Annual IEEE Conference on Computational Complexity (CCC 2000)*, pages 2–13, 2000. [doi:10.1109/CCC.2000.856730](https://doi.org/10.1109/CCC.2000.856730).
- **[W13]** R. Williams. Alternation-trading proofs, linear programming, and lower bounds. *ACM Transactions on Computation Theory*, 5(2):Article 6, 1–49, 2013. [doi:10.1145/2493246.2493249](https://doi.org/10.1145/2493246.2493249). Preliminary version in STACS 2010. Page and equation numbers and quotations in this paper refer to the author copy, <https://people.csail.mit.edu/rrw/automated-lbs.pdf>.
