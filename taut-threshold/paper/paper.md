# The alternation-trading calculus for TAUTOLOGY versus NTS stops exactly at ∛4: a kernel-checked proof

**PastaPastaPasta** · November 2026

*Markdown rendering of `paper.tex`, which is the reference version.*

## Abstract

Williams \[W13, §6\] set up a calculus of alternation-trading proofs for showing that TAUTOLOGY has no nondeterministic algorithm running in time $`n^c`$ and space $`n^{o(1)}`$. Diehl, van Melkebeek and Williams \[DvMW11\] gave proofs in this calculus for every $`c<\sqrt[3]{4}\approx 1.5874`$. Williams conjectured that no proof in the calculus works for any $`c>\sqrt[3]{4}`$ (Conjecture 6.8 of \[W13\]) and proved that none works for $`c\ge\varphi\approx 1.618`$ (Theorem 6.9).

We prove Conjecture 6.8 for a formalisation, in Lean 4 with Mathlib, of the calculus of \[W13, §6\] (Lemmas 6.1 and 6.2 in the line format of \[W13, §2\]). We prove slightly more: for every $`c`$ with $`c^3\ge 4`$, including $`c=\sqrt[3]{4}`$, no sequence of rule applications takes any line to its complement, and no normal-form proof exists. Together with a Lean re-proof of the \[DvMW11\] construction, this shows that for $`c\ge 1`$ the formalised calculus has a normal-form proof if and only if $`c^3<4`$. The impossibility proof uses a potential function with two line types and a first-return induction on proofs.

*What is kernel-checked:* both directions of this threshold, for the formal calculus, including the reduction of arbitrary proofs to normal form (the analogue of \[W13, Theorem 6.6\], whose proof \[W13\] omits). *What is not machine-checked:* that the formal rules coincide with the published calculus (a modelling claim, which we compare rule by rule on paper in Table 1), and soundness of the calculus itself (which is published, not formalised). Conjecture 6.8 refers to “alternation-trading proofs” in the sense of \[W13\], whose rules are fixed only informally there; our theorem is about the formalised rule set. The result is a limit on one proof calculus. It says nothing about lower bounds for TAUTOLOGY proved by other methods.

## 1. Introduction

**Background.**

Fortnow and van Melkebeek \[FvM00\] showed that TAUTOLOGY cannot be solved in time $`n^{\sqrt2-o(1)}`$ by a nondeterministic algorithm using $`n^{o(1)}`$ space. Williams \[W13\] cast proofs of this kind (“alternation-trading proofs”) as sequences of rule applications whose exponents can be optimised by linear programming, and used computer search to find better proofs. Generalising the proofs found, Diehl, van Melkebeek and Williams \[DvMW11\] obtained the exponent $`\sqrt[3]{4}`$; Williams presents the argument as Theorem 6.7 of \[W13\]. Exhaustive search over short proofs led to Conjecture 6.8 of \[W13\]:

> There is no alternation trading proof that $`\mathsf{coNTIME}[n]\not\subseteq\mathsf{NTS}[n^c]`$, for any $`c>\sqrt[3]{4}`$.

\[W13\] proves the weaker limit $`c<\varphi`$ (Theorem 6.9). For the analogous problem of SAT versus deterministic time and $`n^{o(1)}`$ space, Buss and Williams \[BW15\] proved that the calculus stops at $`2\cos(\pi/7)`$. Buss’s 2013 survey \[B13\] states, after recalling the $`\sqrt[3]{4}`$ bound, that extending the methods of \[BW15\] to show that $`\sqrt[3]{4}`$ is optimal for alternation-trading proofs “has not been attempted yet and so it remains an open problem”.

**Results.**

We work with a formalisation of the calculus of \[W13, §6\], described in Section 2. Result numbers of the form $`x.y`$ (Lemma 6.1, Theorem 6.6, …) always refer to \[W13\]; our own results are numbered $`1,2,3,\dots`$ All statements below are Lean theorems; the names are those of the accompanying Lean library (namespace `PastaMath.TautThreshold`).

- **Impossibility** (Theorem 1; `TW.no_literal_proof`, `TW.no_literal_proofE`, `TW.no_nf`). Let $`c`$ be real with $`c^3\ge4`$. For every line $`A`$ (any number of quantifier blocks, any real parameters) and every $`N\ge1`$, there is no sequence of $`N`$ rule applications from $`A`$ to its complement $`\neg A`$. There is no normal-form proof.

- **Normal form** (Theorem 2; `TW.normal_form`, `TW.normal_formE`). For every $`c`$, a proof of $`A\subseteq\neg A`$ with at least two lines yields a normal-form proof in the same calculus.

- **Threshold** (Theorem 3; `TDL.nf_exists`, `TDL.threshold_literal`). For $`c\ge1`$, a normal-form proof using the exact rules exists if and only if $`c^3<4`$.

So Conjecture 6.8 holds for the formalised calculus, and also at $`c=\sqrt[3]{4}`$ itself. Section 8 lists exactly what is kernel-checked and what rests on paper arguments.

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
  and dually $`Q\,\mathsf{coNTS}[n^a]\subseteq Q\,(\forall\, n^{x})^{\max(b,x)}(\exists\,\log n)^{b}\,\mathsf{coNTS}[n^{a-x}]`$. If the innermost block of $`Q`$ already has the new first quantifier, the two blocks merge \[W13, §2\]; for example, if $`Q=Q'(\exists\, n^{g})^{o}`$ then the result is $`Q'(\exists\, n^{\max(g,x)})^{\max(o,x)}(\forall\,\log n)^{o}\,\mathsf{NTS}[n^{a-x}]`$, as in \[W13, eq. (14)\].

- **Slowdown** (Lemma 6.2, under $`H_c`$).

  1.  $`Q\,(\exists\, n^{g})^{o}\,\mathsf{NTS}[n^{a}]\subseteq Q\,\mathsf{coNTS}[n^{c\max(g,a,o,b)}]`$;

  2.  $`Q\,(\forall\, n^{g})^{o}\,\mathsf{coNTS}[n^{a}]\subseteq Q\,\mathsf{NTS}[n^{c\max(g,a,o,b)}]`$;

  3.  $`Q\,(\exists\, n^{g})^{o}\,\mathsf{coNTS}[n^{a}]\subseteq Q\,(\exists\, n^{g})^{o}\,\mathsf{NTS}[n^{c\max(a,o)}]`$;

  4.  $`Q\,(\forall\, n^{g})^{o}\,\mathsf{NTS}[n^{a}]\subseteq Q\,(\forall\, n^{g})^{o}\,\mathsf{coNTS}[n^{c\max(a,o)}]`$.

  Rules (1)/(2) remove (“pop”) the innermost block over a matching kernel. Rules (3)/(4) flip an opposite kernel.

### 2.3 Proofs and normal form

A *proof* (from $`A_0`$ to $`A_N`$) is a sequence of lines $`A_0,\dots,A_N`$, $`N\ge1`$, each obtained from the previous one by one rule. Following \[W13, Definition 6.4\], a proof is in *normal form* if its first line is $`\mathsf{NTS}[n^a]`$, its last line is $`\mathsf{coNTS}[n^{a'}]`$ with $`a'\le a`$, and no other line is quantifier-free. \[W13, Lemma 6.5\] shows that, for $`c\ge1`$, a normal-form proof with at least two lines contradicts $`H_c`$ (Lemma 6.3 covers $`a'<a`$, a separate argument covers $`a'=a`$). \[W13, Theorem 6.6\] states that a proof between simple complementary classes can be converted into a normal-form proof; its proof is omitted there (“analogous to that of Theorem 4.4”).

### 2.4 The formalisation

A Lean line is a triple $`(\mathit{bl},k,a)`$: the block list $`\mathit{bl}`$, stored innermost first, of blocks $`\langle q,g,o\rangle`$ ($`q=\mathtt{true}`$ for $`\exists`$); the kernel type $`k`$ ($`\mathtt{true}`$ for $`\mathsf{NTS}`$); and the kernel exponent $`a\in\mathbb R`$ (`TW.WLine`, `TW.Blk`, `TW.pin`, `TW.compl`). There are two rule relations.

- $`\texttt{TW.WStepE}\,c`$ has the exact output values of Lemmas 6.1 and 6.2 and the side conditions $`b\ge1`$, $`a\ge1`$, $`x\ge0`$ of Lemma 6.1.

- $`\texttt{TW.WStep}\,c`$ is its relaxation: the same four rule shapes, but every output exponent is only bounded below by the exact value (so weakening is built in), and the only side condition is $`x\ge0`$. Lean proves $`\texttt{WStepE}\subseteq\texttt{WStep}`$ (`TW.wstepE_wstep`).

The impossibility theorems are proved for `WStep`, and hence hold for `WStepE`; the construction uses only `WStepE`. Table 1 compares the rules. In it, $`k`$ is the kernel type, $`\bar k`$ the other type, $`Q_k`$ the quantifier matching $`k`$ ($`\exists`$ for $`\mathsf{NTS}`$), $`u=\langle q,g,o\rangle`$ the innermost block and $`\mathit{rest}`$ the blocks outside it.

| Rule of \[W13\] | Lean constructor | Effect and cost in `WStepE` (in `WStep`: each output only $`\ge`$ this) |
|:---|:---|:---|
| Lemma 6.1, block list empty or innermost block not of type $`Q_k`$ | `speedNew` | opens $`(Q_k\,n^{x})^{\max(b,x)}(\bar Q_k\,\log n)^{b}`$ with $`b=\mathrm{pin}(\mathit{bl})`$; kernel $`a-x`$; requires $`b\ge1`$, $`a\ge1`$, $`x\ge0`$ |
| Lemma 6.1 with merging (\[W13, §2, eq. (14)\]) | `speedMerge` | $`u=\langle Q_k,g,o\rangle`$ becomes $`(Q_k\,n^{\max(g,x)})^{\max(o,x)}`$, then $`(\bar Q_k\,\log n)^{o}`$ is opened; kernel $`a-x`$; requires $`o\ge1`$, $`a\ge1`$, $`x\ge0`$ |
| Lemma 6.2(1),(2) (pop) | `pop`, $`q`$ matches $`k`$ | removes $`u`$; kernel type $`\bar k`$, exponent $`c\max(g,a,o,\mathrm{pin}(\mathit{rest}))`$, with $`\mathrm{pin}(\emptyset)=1`$ |
| Lemma 6.2(3),(4) (flip) | `flip`, $`q`$ opposite to $`k`$ | keeps blocks; kernel type $`\bar k`$, exponent $`c\max(a,o)`$ |
| not a rule: $`\mathsf{NTS}[n^a]\subseteq\mathsf{coNTS}[n^{c\max(a,1)}]`$ (quantifier-free flip) | none | sound under $`H_c`$; omitted; harmless by Proposition 25 |
| not a rule: speedup that opens a new block of the same type as the innermost one without merging | none | sound; not covered (Remark 26) |

*Table 1. The rules of \[W13, §6\] and their Lean counterparts. The $`\log n`$ blocks are represented with guess exponent $`0`$.*

**Where the formalisation is more permissive.**

Each of the following only makes the impossibility theorem stronger. `WStep` has no side conditions $`a\ge1`$, $`b\ge1`$, no lower bound on kernel exponents, and no bound $`x\le a-1`$ (the DTS analogue Lemma 3.3 of \[W13\] has one; Lemma 6.1 as printed has none); parameters are arbitrary reals; outputs may be weakened; the start line of Theorem 1 need not alternate. The constructor `speedNew` does forbid opening a block of the same type as the innermost block without merging, so a non-alternating line can only come from the start line.

**Where it is exact.**

The construction of Section 7 uses only `WStepE`, and every speedup in it has $`b=1`$, $`a\ge1`$ and in fact $`a-x\ge1`$ (Section 7).

## 3. Statements

**Theorem 1** (`TW.no_literal_proof`, `TW.no_literal_proofE`, `TW.no_nf`). *Let $`c\in\mathbb R`$ with $`c^3\ge4`$.*

1.  *For every line $`A`$ and every $`N\ge1`$ there is no `WStep` $`c`$-path of length $`N`$ from $`A`$ to $`\neg A`$; hence none in `WStepE` $`c`$.*

2.  *There is no normal-form proof in `WStep` $`c`$.*

**Theorem 2** (`TW.normal_form`, `TW.normal_formE`; generic form `TW.normal_form_gen`). *Let $`c\in\mathbb R`$ and let $`R`$ be `WStep` $`c`$ or `WStepE` $`c`$ (more generally, any relation contained in `WStep` $`c`$ and closed under complement). If there is an $`R`$-path of length $`N\ge1`$ from a line $`A`$ to $`\neg A`$, then there is a normal-form proof in $`R`$.*

**Theorem 3** (`TDL.nf_exists`, `TDL.threshold_literal`). *Let $`c\ge1`$. There is a normal-form proof in `WStepE` $`c`$ if and only if $`c^3<4`$.*

Theorem 3 ($`\Leftarrow`$) is the result of \[DvMW11\] (Theorem 6.7 of \[W13\]), re-proved in Lean following the inductive argument printed in \[W13, §6.3\]. Lean’s normal-form predicate does not require $`a'\ge1`$ (needed by \[W13, Lemma 6.3\]); the proofs constructed have $`a'=c^2\ell`$ with $`\ell\ge1`$. The Lean version of Theorem 2 does not include the length bound of \[W13, Theorem 6.6\].

The proof of Theorem 1 has three steps: reduce to normal form (Section 4); map a normal-form proof into a reduced homogeneous calculus (Section 5); show the reduced calculus has no refutation (Section 6).

## 4. Reduction to normal form

Fix $`c`$ and a relation $`R\subseteq\texttt{WStep}\,c`$ closed under complement. `WStep` and `WStepE` are closed under complement (`TW.wstep_compl`, `TW.wstepE_compl`), since every rule is stated symmetrically in $`\exists/\forall`$ and $`\mathsf{NTS}/\mathsf{coNTS}`$. The *outermost quantifier* of a non-quantifier-free line is the quantifier of its block 1.

**Lemma 4** (`TW.step_from_nil`). *A step from a quantifier-free line leads to a line that is not quantifier-free.*

*Proof.* Only the speedup with an empty block list applies to a quantifier-free line, and it opens two blocks. ◻

**Lemma 5** (`TW.outer_step`, `TW.stretch_outer`). *If $`L\to L'`$ is a step and neither $`L`$ nor $`L'`$ is quantifier-free, then $`L`$ and $`L'`$ have the same outermost quantifier. Hence the outermost quantifier is constant along any stretch of non-quantifier-free lines.*

*Proof.* Every rule acts at the innermost block. A speedup on a nonempty block list adds blocks inside, or merges into the innermost block keeping its quantifier; a pop removes the innermost block, and since $`L'`$ is not quantifier-free, block 1 survives; a flip changes no block. ◻

**Lemma 6** (`TW.seg_types`). *Let $`M_0,\dots,M_n`$ ($`n\ge1`$) be a path whose end lines are quantifier-free and whose interior lines are not. Then the kernel type of $`M_n`$ is the opposite of that of $`M_0`$.*

*Proof.* By Lemma 4, $`n\ge2`$. The first step is a speedup from an empty block list, so the outermost quantifier of $`M_1`$ matches the kernel type of $`M_0`$. By Lemma 5 this quantifier is unchanged up to $`M_{n-1}`$. The last step produces an empty block list, so it is a pop of block 1, whose quantifier matches the kernel of $`M_{n-1}`$; the pop flips the kernel type. ◻

**Lemma 7** (`TW.qf_up`). *Suppose there is no normal-form proof in $`R`$. Then for every $`R`$-path $`M_0,\dots,M_n`$ ($`n\ge1`$) whose two end lines are quantifier-free, the kernel exponent of $`M_n`$ is strictly larger than that of $`M_0`$.*

*Proof.* First let the path have no quantifier-free interior line (a *segment*). If $`M_0`$ has kernel $`\mathsf{NTS}`$, then $`M_n`$ has kernel $`\mathsf{coNTS}`$ by Lemma 6, and if the exponent did not increase the path would be a normal-form proof. If $`M_0`$ has kernel $`\mathsf{coNTS}`$, apply the same argument to the complemented path $`\neg M_0,\dots,\neg M_n`$, which is an $`R`$-path with the same exponents. So every segment strictly increases the exponent. A general path splits at its first quantifier-free interior line into a segment and a shorter path; conclude by strong induction on $`n`$. ◻

**Lemma 8** (`TW.exists_qf`). *Every $`R`$-path from $`A`$ to $`\neg A`$ contains a quantifier-free line.*

*Proof.* Otherwise, by Lemma 5, $`A`$ and $`\neg A`$ have the same outermost quantifier; but complementation swaps it. ◻

**Lemma 9** (`TW.splice`). *Let $`L_0,\dots,L_N`$ be an $`R`$-path with $`L_N=\neg L_0`$, and $`0\le i\le N`$. Then there is an $`R`$-path of length $`N`$ from $`L_i`$ to $`\neg L_i`$.*

*Proof.* Concatenate the path with its complement $`\neg L_0=L_N,\neg L_1,\dots,\neg L_N=L_0`$ (an $`R`$-path by closure under complement), and take the window of length $`N`$ starting at position $`i`$. ◻

*Proof of Theorem 2.* Suppose there is no normal-form proof in $`R`$. By Lemma 8 some $`L_i`$ is quantifier-free; by Lemma 9 there is an $`R`$-path of length $`N\ge1`$ from $`L_i`$ to $`\neg L_i`$. Both ends are quantifier-free and have the same kernel exponent, contradicting Lemma 7. ◻

This argument needs no parity argument and no case split, unlike the proof of \[W13, Theorem 4.4\] that Theorem 6.6 refers to.

## 5. The reduced calculus

The limit argument runs on a homogeneous relaxation, in the style of \[BW15\], adapted to two kernel types (`TL.TLine`, `TL.TStep`).

**Definition 10** (reduced lines and rules). A *reduced line* is $`(s_1,\dots,s_m;\,t;\,a)`$: a list of reals (input constraints, outermost first), a flag $`t\in\{\mathrm{match},\mathrm{opp}\}`$ and a real $`a`$. Its *depth* is $`m`$, and $`\mathrm{top}(s)=s_m`$ ($`\mathrm{top}(\emptyset)=0`$). Write $`s\cdot b`$ for the list $`s`$ with $`b`$ appended. The rules of $`\texttt{TStep}\,c`$ are:

- `init`: $`(\emptyset;\mathrm{match};a)\vdash(0;\mathrm{match};a)`$ (a virtual block of constraint $`0`$ stands for the input);

- `speedM`: $`(s\cdot b;\mathrm{match};a)\vdash(s\cdot b_1\cdot b_2;\mathrm{opp};a_2)`$ with $`0\le x\le a`$, $`b_1\ge\max(x,b)`$, $`b_2\ge b`$, $`a_2\ge a-x`$;

- `speedO`: $`(s\cdot b;\mathrm{opp};a)\vdash(s\cdot b\cdot b_1\cdot b_2;\mathrm{opp};a_2)`$ with the same conditions;

- `flip`: $`(s\cdot b;t;a)\vdash(s\cdot b;\bar t;e)`$ with $`e\ge c\max(b,a)`$, in both directions;

- `pop`: $`(s\cdot b;\mathrm{match};a)\vdash(s;\mathrm{match};e)`$ with $`e\ge c\max(\mathrm{top}(s),b,a)`$;

- `weak`: increase any entries and $`a`$, keeping depth and flag.

$`\texttt{TRefutes}\,c\,n\,L`$ says: $`L_0,\dots,L_n`$ is a $`\texttt{TStep}\,c`$-path with $`n\ge2`$, $`L_0=(\emptyset;\mathrm{match};a_0)`$ with $`a_0>0`$, $`L_n`$ has depth $`0`$ and exponent $`\le a_0`$, and no interior line has depth $`0`$.

The *encoding* `TW.enc` maps a literal line to the list of its input constraints (outermost first), the flag “matching” ($`\mathrm{match}`$ for a quantifier-free line), and $`\max(a,0)`$. Guess exponents are dropped.

**Lemma 11** (simulation; `TW.sim`, `TW.sim0`). *Let $`c\ge0`$. A `WStep` $`c`$ step $`L\to L'`$ from a line with an alternating, nonempty block list is one `TStep` $`c`$ step from $`\mathrm{enc}(L)`$ to $`\mathrm{enc}(L')`$. A `WStep` $`c`$ step from a quantifier-free line $`L`$ is `init` followed by one `TStep` $`c`$ step to $`\mathrm{enc}(L')`$.*

*Proof.* Each reduced rule only bounds outputs from below by expressions monotone in the inputs, and the literal rules give at least these bounds. A `speedNew` on a nonempty list acts on an opposite kernel and becomes `speedO`; from the empty list it becomes `init` then `speedM` with $`b=0`$ (the literal constraints $`\max(1,x)`$ and $`1`$ dominate $`\max(x,0)`$ and $`0`$); `speedMerge` acts on a matching kernel and becomes `speedM` with $`b=o`$. A literal pop costs $`c\max(g,a,o,\mathrm{pin}(\mathit{rest}))\ge c\max(\mathrm{top},o,a)`$, using $`\mathrm{pin}(\emptyset)=1\ge0=\mathrm{top}(\emptyset)`$. After a pop the new innermost block has the other quantifier, by alternation, and the kernel type has flipped, so the result is again matching; this is the only use of alternation. A literal flip becomes a reduced flip. If $`x>a`$, the reduced step uses $`x'=\min(x,\max(a,0))`$, and clamping the kernel at $`0`$ keeps the inequalities (`TW.clamp_sub`, `TW.cmax_le`). ◻

Rules preserve alternation (`TW.alt_step`), so along a path from a quantifier-free line every block list alternates (`TW.path_alt`).

**Lemma 12** (`TW.nf_trefutes`). *Let $`c>0`$. A normal-form `WStep` $`c`$ proof with $`n`$ steps gives a $`\texttt{TRefutes}\,c\,(n+1)`$ instance.*

*Proof.* Encode the lines and insert `init` after the first. By Lemma 4, $`n\ge2`$. The last literal step pops block 1, at cost at least $`c\cdot\mathrm{pin}(\emptyset)=c>0`$ (`TW.pop_pos`), so $`a\ge a'\ge c>0`$. ◻

Two facts about `TStep` are used below. For $`c\ge0`$, nonnegativity of all entries and the exponent is preserved from the start line (`TL.tstep_nonneg`). On nonnegative lines, a $`\texttt{TStep}\,c`$ step is a $`\texttt{TStep}\,c_0`$ step for every $`c_0\le c`$, since every cost is $`c`$ times a nonnegative quantity (`TL.tstep_restrict`). So for the limit theorem we may replace $`c`$ by $`\min(c,2)`$ and assume $`\sqrt[3]{4}\le c\le2`$.

## 6. The limit theorem

**Theorem 13** (`TL.no_trefutation`). *If $`c^3\ge4`$ then $`\texttt{TRefutes}\,c\,n\,L`$ fails for all $`n`$ and $`L`$.*

The proof shows more: the final exponent of a path from $`(\emptyset;\mathrm{match};a_0)`$ back to depth $`0`$ is at least $`(\min(c,2)^2/2)\,a_0\ge 2^{1/3}a_0`$. This bound appears inside the proof; it is not stated as a separate Lean theorem.

### 6.1 The potential

Let $`\sqrt[3]{4}\le c\le2`$, $`\gamma=c/2`$ and $`\kappa=5/2`$. For reals $`b,a`$ define
``` math
\Psi(b,a)=\min\bigl(\max(b,a),\ \max(\gamma a,\kappa b)\bigr)\qquad(\texttt{TL.Ps}).
```
The potential of a reduced line with $`\mathrm{top}=b`$ and exponent $`a`$ is $`\Psi(b,a)`$ if it is matching and $`\Psi(b,c\,\Psi(b,a))`$ if it is opposite (`TL.pot`). The second value is the potential the line would have after flipping its kernel to matching at cost $`c`$.

**Lemma 14** (`TL.ps_mono`, `ps_le_max`, `ps_ge_g`, `ps_ge_min`, `ps_ge_b`, `ps_nonneg`). *For $`b,a\ge0`$ and $`0\le c\le2`$ where needed: $`\Psi`$ is monotone in both arguments; $`\Psi(b,a)\le\max(b,a)`$; $`\Psi(b,a)\ge\gamma a`$; $`\Psi(b,a)\ge\min(a,\kappa b)`$; $`\Psi(b,a)\ge b`$ if $`a\le b`$; $`\Psi(b,a)\ge0`$.*

**Lemma 15** (`TL.cfacts`). *For $`\sqrt[3]{4}\le c\le 2`$: $`c\ge3/2`$, $`c^2\ge5/2`$, $`c-c^2/5\ge1`$, $`c^4/4\ge c`$, and $`c^3/4\ge1`$.*

The constant $`\kappa=5/2`$ is chosen just below $`(\sqrt[3]{4})^2\approx2.5198`$.

### 6.2 The key inequality

**Lemma 16** (key inequality; `TL.key`). *Let $`\sqrt[3]{4}\le c\le2`$, $`b\ge0`$, $`0\le x\le a`$, $`T\ge\max(x,b)`$, $`D=a-x`$, $`P=\Psi(b,D)`$, $`W=\Psi(b,cP)`$ and $`E\ge c\max(T,W)`$. Then $`\Psi(b,a)\le\Psi(T,E)`$.*

Reading: a matching line with top $`b`$ and exponent $`a`$ is sped up by $`x`$; the merged configuration block ends with constraint $`T`$; the inner part has potential at least $`W`$ when it returns, and popping the index block costs $`E`$. The potential does not drop.

*Proof.* Write $`h=\Psi(b,a)`$, so $`h\le\max(b,a)`$ and $`h\le\max(\gamma a,\kappa b)`$; in particular $`h\le\gamma a`$ or $`h\le\kappa b`$. Since $`\Psi(T,E)=\min(\max(T,E),\max(\gamma E,\kappa T))`$, it suffices to show (A) $`E\ge h`$ and (B) $`\max(\gamma E,\kappa T)\ge h`$. We use $`E\ge cT\ge cx`$, $`E\ge cW`$, and, from Lemma 14, $`P\ge\gamma D`$, $`W\ge\gamma cP\ge(c^3/4)D\ge D`$, $`P\ge\min(D,\kappa b)`$ and $`W\ge\min(cP,\kappa b)`$.

\(A\) If $`h\le cT`$ we are done, so assume $`cT<h`$; then $`cb<h`$.

- *Case $`D\le b`$.* Then $`P\ge b`$ and $`W\ge\min(cb,\kappa b)=cb`$, so $`E\ge c^2b`$. If $`h\le c^2 b`$ we are done. Otherwise $`h>c^2b\ge\kappa b`$, so $`h\le\gamma a`$, and $`c^2b<\gamma a=ca/2`$ gives $`cb<a/2`$. Since $`x\ge a-b`$, we get $`E\ge cx\ge ca-cb>ca-a/2\ge ca/2\ge h`$, using $`c\ge1`$.

- *Case $`D>b`$ and $`h\le\gamma a`$.* From $`E\ge cW\ge cD`$ and $`E\ge cx`$ we get $`2E\ge c(D+x)=ca`$, so $`E\ge\gamma a\ge h`$.

- *Case $`D>b`$ and $`h\le\kappa b`$.* If $`W\ge\kappa b`$ then $`E\ge c\kappa b\ge\kappa b\ge h`$. Otherwise $`W\ge cP`$. If $`P\ge D`$ then $`E\ge c^2D\ge\kappa D>\kappa b\ge h`$. If $`P\ge\kappa b`$ then $`E\ge c^2\kappa b\ge h`$.

\(B\) If $`\kappa T\ge h`$ we are done, so assume $`\kappa T<h`$. Then $`\kappa x<h`$ and $`\kappa b<h`$, so $`h\le\gamma a`$, and $`\kappa x<\gamma a`$ gives $`x<(\gamma/\kappa)a=(c/5)a`$. Hence
``` math
E\ge cW\ge c\cdot\tfrac{c^3}{4}D=\tfrac{c^4}{4}D\ge cD=c(a-x)\ge\bigl(c-\tfrac{c^2}{5}\bigr)a\ge a,
```
using Lemma 15 and $`a\ge0`$ (which follows from $`0\le\kappa b<h\le\gamma a`$). So $`\gamma E\ge\gamma a\ge h`$. ◻

**Remark 17** (tightness). At $`c^3=4`$, $`b=0`$, $`x=a/2`$, $`T=a/2`$, $`E=c\max(T,W)`$: $`P=ca/4`$, $`W=c^3a/8=a/2`$, $`E=ca/2`$ and $`\Psi(a/2,ca/2)=ca/2=\Psi(0,a)`$, so case (A) is an equality. This is one stage of the \[DvMW11\] recursion: speed up by half, use the previous stage twice, pop. Correspondingly, the fixed-point equation $`s=1+s^2/c^3`$ of \[W13, Claim 2\] has a real solution if and only if $`c^3\ge4`$.

### 6.3 Segments and excursions

Fix $`\sqrt[3]{4}\le c\le 2`$ and a $`\texttt{TStep}\,c`$-path $`L_0,L_1,\dots`$ of nonnegative lines. Depth changes by $`+1`$ under `speedM`, by $`+2`$ under `speedO`, by $`-1`$ under `pop`, and not at all under `flip` and `weak` (`TL.tstep_len`, `TL.tstep_pop`).

**Lemma 18** (`TL.entry_mono`). *If every line $`L_i`$ with $`p\le i<q`$ has depth at least $`k+2`$, then entry $`k`$ (0-indexed) of $`L_q`$ is at least entry $`k`$ of $`L_p`$.*

*Proof.* A step from a line of depth $`\ge k+2`$ changes only entries at positions $`\ge k+1`$, except `weak`, which increases entries. ◻

**Lemma 19** (segment lemma; `TL.segment`). *Let $`L_p,\dots,L_{p+\ell}`$ all have depth $`\ge k+1`$, and let $`L_p`$ and $`L_{p+\ell}`$ have depth exactly $`k+1`$. Then $`\mathrm{pot}(L_p)\le\mathrm{pot}(L_{p+\ell})`$.*

**Lemma 20** (excursion lemma; `TL.excursion`). *Assume Lemma 19 for all stretches shorter than $`q-p`$. Let $`L_p`$ have depth $`k+1`$, $`L_i`$ have depth $`\ge k+1`$ for $`p\le i<q`$, and $`L_q`$ have depth $`k`$. Then $`L_q`$ is matching and its exponent is at least $`c\max(\mathrm{top}(L_q),\mathrm{pot}(L_p))`$.*

*Proof.* Depth drops only by `pop`, so $`L_{q-1}=(s\cdot b;\mathrm{match};a)`$ has depth $`k+1`$ and $`L_q=(s;\mathrm{match};e)`$ with $`e\ge c\max(\mathrm{top}(s),b,a)`$. By Lemma 19 on $`L_p,\dots,L_{q-1}`$, $`\mathrm{pot}(L_p)\le\mathrm{pot}(L_{q-1})=\Psi(b,a)\le\max(b,a)`$. ◻

*Proof of Lemma 19.* Strong induction on $`\ell`$; for $`\ell=0`$ there is nothing to show. Let $`b=\mathrm{top}(L_p)`$ and $`a`$ its exponent. Split on the first step $`L_p\to L_{p+1}`$. `init` and `pop` cannot occur (depth $`\ge1`$, and a pop would reach depth $`k`$).

- `weak`, `flip`: $`L_{p+1}`$ has depth $`k+1`$, and by induction it suffices to show $`\mathrm{pot}(L_p)\le\mathrm{pot}(L_{p+1})`$. For `weak` this is monotonicity of $`\Psi`$. For a flip from matching to opposite with new exponent $`e\ge c\max(b,a)\ge ca`$: $`c\Psi(b,e)\ge c\gamma e\ge(c^3/2)a\ge a`$, so $`\Psi(b,c\Psi(b,e))\ge\Psi(b,a)`$. For a flip from opposite to matching: $`e\ge c\max(b,a)\ge c\Psi(b,a)`$, so $`\Psi(b,e)\ge\Psi(b,c\Psi(b,a))`$.

- `speedM`: $`L_p=(s\cdot b;\mathrm{match};a)`$, $`L_{p+1}=(s\cdot b_1\cdot b_2;\mathrm{opp};a_2)`$. Let $`L_m`$ be the first line after $`p`$ of depth $`\le k+1`$; it has depth exactly $`k+1`$ and $`m\le p+\ell`$. By monotonicity, $`\mathrm{pot}(L_{p+1})=\Psi(b_2,c\Psi(b_2,a_2))\ge\Psi(b,c\Psi(b,a-x))=W`$. By Lemma 20 (at level $`k+1`$), $`L_m`$ is matching with exponent $`E\ge c\max(T,W)`$, where $`T=\mathrm{top}(L_m)`$; by Lemma 18, $`T\ge b_1\ge\max(x,b)`$. Lemma 16 gives $`\mathrm{pot}(L_p)=\Psi(b,a)\le\Psi(T,E)=\mathrm{pot}(L_m)`$, and the induction hypothesis on $`L_m,\dots,L_{p+\ell}`$ finishes.

- `speedO`: $`L_p=(s\cdot b;\mathrm{opp};a)`$, $`L_{p+1}=(s\cdot b\cdot b_1\cdot b_2;\mathrm{opp};a_2)`$. Let $`m_1`$ be the first index after $`p`$ with depth $`\le k+2`$ and $`m_0`$ the first index after $`m_1`$ with depth $`\le k+1`$. As in the previous case (excursion at level $`k+2`$), $`L_{m_1}`$ is matching and $`\Psi(b,a)\le\mathrm{pot}(L_{m_1})`$ by Lemma 16 applied to the virtual matching line $`(b,a)`$. By Lemma 20 at level $`k+1`$, $`L_{m_0}`$ is matching with exponent $`\ge c\,\mathrm{pot}(L_{m_1})\ge c\Psi(b,a)`$, and by Lemma 18 its top is $`\ge b`$. So $`\mathrm{pot}(L_{m_0})\ge\Psi(b,c\Psi(b,a))=\mathrm{pot}(L_p)`$, and induction finishes.

 ◻

*Proof of Theorem 13.* Replace $`c`$ by $`\min(c,2)`$ (Section 5). The first step of a refutation must be `init` (the other rules need depth $`\ge1`$, and `weak` would give a quantifier-free interior line), so $`L_1=(0;\mathrm{match};a_0)`$ with $`\mathrm{pot}(L_1)=\Psi(0,a_0)\ge\gamma a_0`$. The rest is one excursion from depth 1 to depth 0, so by Lemma 20 the final exponent is at least $`c\gamma a_0=(c^2/2)a_0\ge(5/4)a_0>a_0`$, using $`c^2\ge5/2`$ and $`a_0>0`$. ◻

*Proof of Theorem 1.* $`c^3\ge4`$ implies $`c>0`$ (`TW.pos_of_cube`). Part 2: a normal-form proof gives a refutation by Lemma 12, which Theorem 13 excludes. Part 1: by Theorem 2 a path from $`A`$ to $`\neg A`$ yields a normal-form proof, excluded by Part 2 (`TW.literal_trefutes`). ◻

## 7. The construction below $`\sqrt[3]{4}`$

We follow the inductive argument of \[W13, §6.3\] (Claims 1 and 2), using only the exact rules `WStepE`. Fix $`c\ge1`$. For a kernel type $`k`$ write $`Q_k`$ for the matching quantifier and $`\bar Q_k`$, $`\bar k`$ for the opposite ones. All derivations below pass only through lines that are not quantifier-free (`TDL.DNW`).

**Definition 21** (`TDL.MacE`, `TDL.InnerE`). $`\mathrm{Mac}(s,R)`$ holds if for every scale $`\ell\ge R`$ and every kernel type $`k`$ the following hold, where in each case $`w,g,\kappa`$ are some reals (depending on the data) with $`1\le w\le\ell`$, $`g\le w`$, $`\kappa\le\ell`$:

1.  for every block list $`P`$ with $`\mathrm{pin}(P)=1`$ whose innermost block (if any) is not of type $`Q_k`$, the line $`P\,K_k[n^{s\ell}]`$ derives $`P\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,n^{g})^{w}\,K_{\bar k}[n^{\kappa}]`$;

2.  for every $`g_0\le\ell`$ and every $`\mathit{rest}`$, the line $`\mathit{rest}\,(Q_k\,n^{g_0})^{1}\,K_k[n^{s\ell}]`$ derives $`\mathit{rest}\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,n^{g})^{w}\,K_{\bar k}[n^{\kappa}]`$.

$`\mathrm{Inner}(s,R)`$ holds if for every $`\ell\ge R`$, every $`P`$ and $`k`$, the line $`P\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,\log n)^{1}\,K_k[n^{s\ell-\ell}]`$ derives $`P\,(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,n^{g})^{w}\,K_{\bar k}[n^{\kappa}]`$ for some $`w,g,\kappa`$ as above.

**Lemma 22** (`TDL.macE_of_inner`). *If $`R\ge1`$, $`s\ge1`$ and $`\mathrm{Inner}(s,R)`$, then $`\mathrm{Mac}(s,R)`$.*

*Proof.* Apply the speedup with $`x=\ell`$ to the kernel exponent $`s\ell\ge1`$, with $`b=\mathrm{pin}(P)=1`$ (case 1, `speedNew`) or $`b=1`$ from the block $`(Q_k\,n^{g_0})^1`$ (case 2, `speedMerge`, where $`\max(g_0,\ell)=\ell`$). Both give $`(Q_k\,n^{\ell})^{\ell}(\bar Q_k\,\log n)^{1}\,K_k[n^{s\ell-\ell}]`$; then use $`\mathrm{Inner}(s,R)`$. ◻

**Lemma 23** (base, W13’s stage 2; `TDL.innerE_base`). *If $`R\ge c`$ then $`\mathrm{Inner}(1+1/c,R)`$.*

*Proof.* The kernel exponent is $`\ell/c\ge1`$, and the kernel is opposite to the $`\log n`$ block. Flip (Lemma 6.2(3)/(4)) at cost $`c\max(\ell/c,1)=\ell`$; take $`w=1`$, $`g=0`$, $`\kappa=\ell`$. ◻

**Lemma 24** (stage step; `TDL.innerE_step`). *If $`R\ge1`$, $`s\ge1`$ and $`\mathrm{Mac}(s,R)`$, then $`\mathrm{Inner}(1+s^2/c^3,\,c^3R)`$.*

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

*Proof of Theorem 3.* ($`\Rightarrow`$) A normal-form proof in `WStepE` is one in `WStep`, excluded for $`c^3\ge4`$ by Theorem 1. ($`\Leftarrow`$) If $`c^3<4`$, pick $`j`$ with $`s_j\ge c^2`$ and let $`\ell=c(c^3)^j\ge1`$. By $`\mathrm{Mac}(s_j,\ell)`$, case 1 with $`P`$ empty and $`k=\mathsf{NTS}`$, the line $`\mathsf{NTS}[n^{s_j\ell}]`$ derives $`(\exists\,n^{\ell})^{\ell}(\forall\,n^{g})^{w}\mathsf{coNTS}[n^{\kappa}]`$. Pop the $`\forall`$ block at cost $`c\ell`$ and then the $`\exists`$ block at cost $`c\max(\ell,c\ell,\ell,1)=c^2\ell\le s_j\ell`$, reaching $`\mathsf{coNTS}[n^{c^2\ell}]`$. ◻

**Side conditions.**

Every speedup in this construction has $`b=1`$ and kernel exponent $`s\ell\ge1`$, and leaves a kernel exponent $`\ge1`$: in the base case $`\ell/c\ge1`$, and in the stage step $`s\mu\ge\mu\ge1`$. These facts are established inside the Lean proofs (`innerE_base`, `innerE_step`), although they are not part of the statement of `nf_exists`. So every speedup also satisfies the bound $`x\le a-1`$ of \[W13, Lemma 3.3\]. That every other line also has kernel exponent $`\ge1`$ is not stated in Lean and is not needed. The depth $`j`$ needed grows like $`c^2/(1-c^3/4)`$ and the number of lines roughly doubles with each stage, so the proofs become very long as $`c\to\sqrt[3]{4}`$.

The reduced calculus has the same threshold (`TD.dvmw`, `TD.threshold`): for $`c\ge1`$, $`\texttt{TRefutes}\,c`$ instances exist if and only if $`c^3<4`$.

## 8. What is and is not verified

**(a) Kernel-checked.**

Lean 4.31 with Mathlib (pinned revision in the repository). The library builds with no `sorry`, no `admit`, no `native_decide` and no new axioms; `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for every headline theorem. Checked are: Theorems 1, 2, 3 and 13; Lemmas 11 and 12; the key inequality and the segment lemma; and non-vacuity: the five-line example of \[W13, §6\] is a normal-form proof under the exact rules at $`c=5/4`$ (`TW.w5_nf`), a proof $`A\subseteq\neg A`$ with $`a'=a`$ exists at $`c=5/4`$ (`TW.wq_proof`), and a five-step reduced refutation exists at $`c=13/10`$ (`TL.tlv_refutes`).

**(b) Not machine-checked.**

- *That `WStepE` is the calculus of \[W13\].* This is a modelling claim. Table 1 compares it rule by rule with \[W13, §2 and §6\]. \[W13\] fixes the notion of alternation-trading proof in §6 only by analogy with §4 (“analogous” rules, normal form and Theorem 6.6), so Conjecture 6.8 itself is informal; our theorem concerns the formal rule set. Two points of reading: we take $`b=1`$ for the block outside the outermost one (the input has length $`n`$), and we read the dual speedup for $`\mathsf{coNTS}`$ (which Lemma 6.1 does not state separately) as the complement of the $`\mathsf{NTS}`$ rule, as used in \[W13, eq. (18)\].

- *Soundness of the calculus*, i.e. \[W13, Theorem 3.1 and Lemmas 6.1–6.5\]. These are published results; we do not formalise complexity classes. Theorem 3 ($`\Leftarrow`$) is a lower bound for TAUTOLOGY only through \[W13, Lemma 6.5\].

**(c) The quantifier-free flip.**

Under $`H_c`$ the inclusion $`\mathsf{NTS}[n^a]\subseteq\mathsf{coNTS}[n^{c\max(a,1)}]`$ is sound. It is not a rule of \[W13\]: every item of Lemma 6.2 has an explicit innermost block, and the corresponding DTS rule of \[W13, Definition 4.1\] is stated for $`k>0`$. We omit it. It cannot help:

**Proposition 25** (paper argument, not formalised). *Let $`c^3\ge4`$ and let $`R'`$ be `WStep` $`c`$ together with the steps $`F`$: $`(\emptyset,k,a)\to(\emptyset,\bar k,e)`$ with $`e\ge c\max(a,1)`$. Then there is no $`R'`$-path of length $`\ge1`$ from any line $`A`$ to $`\neg A`$.*

*Proof.* For $`c>1`$ an $`F`$ step strictly increases the exponent: if $`a\ge1`$ then $`e\ge ca>a`$, and if $`a<1`$ then $`e\ge c>1>a`$. Repeat the proof of Theorem 2 for $`R'`$. Lemma 8 still holds, since $`F`$ acts only on quantifier-free lines. Lemma 9 still holds, since $`F`$ is closed under complement. For Lemma 7, split a path between quantifier-free lines at its quantifier-free lines: each piece is either a single $`F`$ step, which strictly increases the exponent, or a `WStep` segment, which strictly increases it because otherwise it or its complement would be a normal-form proof, excluded by Theorem 1. So the exponent strictly increases from $`Q`$ to $`\neg Q`$, a contradiction. ◻

This could be formalised by generalising `normal_form_gen` to allow extra steps on quantifier-free lines that strictly increase the exponent; we have not done so.

**Remark 26** (non-merged same-type blocks). Lemma 6.2(1) is stated for an arbitrary prefix. If a speedup were allowed to open a new $`\exists`$ block directly inside an $`\exists`$ block instead of merging, a later pop would remove only the inner block, at a cost that omits the outer guess exponent. This is sound, but outside `WStep` and arguably outside \[W13\]’s calculus, whose lines alternate (\[W13, Definition 4.1\]; adjacent blocks of the same type “are combined”, §2; Theorem 6.6 speaks of simple classes). A bounded numerical search (not part of this repository) found no gain from this move for proofs of up to 17 lines. That is evidence only; no theorem here covers it.

**Remark 27** (proofs ending below the complement). Theorem 1(1) excludes reaching exactly $`\neg A`$. Reaching a line $`B`$ that is componentwise below $`\neg A`$ also leads to a normal-form proof, because `WStep` is monotone in its inputs; this is a paper argument only. \[W13, Theorem 6.6\] is itself stated for complementary classes.

**(d) The published 11-line example.**

The 11-line proof printed in \[W13, §6.2\] gives one exponent per block. Line 6 prints the $`\forall`$ block as $`(\forall\,n^{2.378})`$. By Lemma 6.1 (merging the speedup into this block) the value at that position is $`\max(1,x)`$ with $`x=2.857-1.181=1.676`$. If the printed $`2.378`$ is read as the input constraint of that block, the slowdown producing line 8 would cost $`c\max(\dots,2.378)\approx3.37`$ instead of the printed $`2.378`$; that is, the printed listing would omit the term $`b`$ of Lemma 6.2(1)/(2). With $`1.676`$, every printed value follows from the rules including that term. The table values of \[W13, §6.2\] include the term: an LP reimplementation (not part of this repository) reproduces the tabulated exponents $`1.380`$ (8 lines) and $`1.419`$ (11 lines) with the $`b`$ term and gives larger values without it. We therefore read line 6 as a misprint, and the calculus as including the $`b`$ term, as Lemma 6.2 states.

**(e) Scope.**

The result limits one proof calculus. Rules outside the formalised set—for example other speedup or slowdown variants, or non-relativizing ingredients—are not covered. Nothing here bears on lower bounds for TAUTOLOGY proved by other methods.

## 9. Relation to earlier work

\[W13, Theorem 6.9\] (no proof for $`c\ge\varphi`$) is proved by deleting a pattern $`1,0,0`$ from a minimal annotation. Our potential adds the cap $`\max(b,a)`$ and the $`\kappa b`$ term, and treats two line types (matching and opposite). For SAT versus $`\mathsf{DTS}`$, Buss and Williams \[BW15\] showed that alternation-trading proofs stop at $`2\cos(\pi/7)\approx1.8019`$, the exponent reached by earlier alternation-trading proofs of Williams; their proof uses an invariant on achievable pairs. Here a scalar potential on two line types and a first-return induction play that role. Buss’s survey \[B13\] reviews these results and lists the optimality of $`\sqrt[3]{4}`$ as open.

## Licence

This text is licensed under CC BY 4.0. The Lean code is licensed under the Apache License 2.0.

## References

- **[B13]** S. Buss. Alternation trading proofs and their limitations. In K. Chatterjee and J. Sgall, editors, *Mathematical Foundations of Computer Science 2013 (MFCS 2013)*, volume 8087 of *Lecture Notes in Computer Science*, pages 1–7. Springer, 2013. [doi:10.1007/978-3-642-40313-2_1](https://doi.org/10.1007/978-3-642-40313-2_1).
- **[BW15]** S. R. Buss and R. Williams. Limits on alternation trading proofs for time–space lower bounds. *Computational Complexity*, 24(3):533–600, 2015. [doi:10.1007/s00037-015-0104-9](https://doi.org/10.1007/s00037-015-0104-9). Preliminary version in CCC 2012, pages 181–191.
- **[DvMW11]** S. Diehl, D. van Melkebeek, and R. Williams. An improved time-space lower bound for tautologies. *Journal of Combinatorial Optimization*, 22(3):325–338, 2011. [doi:10.1007/s10878-009-9286-x](https://doi.org/10.1007/s10878-009-9286-x). Preliminary version in COCOON 2009, pages 429–438.
- **[FvM00]** L. Fortnow and D. van Melkebeek. Time-space tradeoffs for nondeterministic computation. In *Proceedings of the 15th Annual IEEE Conference on Computational Complexity (CCC 2000)*, pages 2–13, 2000. [doi:10.1109/CCC.2000.856730](https://doi.org/10.1109/CCC.2000.856730).
- **[W13]** R. Williams. Alternation-trading proofs, linear programming, and lower bounds. *ACM Transactions on Computation Theory*, 5(2):Article 6, 1–49, 2013. [doi:10.1145/2493246.2493249](https://doi.org/10.1145/2493246.2493249). Preliminary version in STACS 2010.
