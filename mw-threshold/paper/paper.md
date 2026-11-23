# The Mudigonda–Williams calculus for ∃·BPTIME versus BPTS stops exactly at the golden ratio: a kernel-checked threshold

**PastaPastaPasta** · November 2026

*Markdown rendering of `paper.tex`, which is the reference version.*

## Abstract

Mudigonda and Williams \[MW21\] define a calculus of alternation-trading proofs for showing that problems verifiable by Merlin–Arthur protocols in linear time cannot be solved by randomized algorithms running in time $`n^c`$ and space $`n^{o(1)}`$. Their Theorem 5.3 proves, by a proof in this calculus, that $`\exists\cdot\mathsf{BPTIME}[n]\not\subseteq\mathsf{BPTS}[n^c]`$ for every $`c<r_1\approx1.4656`$, the largest root of $`x^3-x^2-1`$.

We determine the exact threshold of a Lean 4 formalisation of this calculus. For every real $`c\ge1`$, a refutation exists if and only if $`c(c-1)<1`$, that is, if and only if $`c<\varphi=(1+\sqrt5)/2\approx1.6180`$. The construction for $`c<\varphi`$ repeats one move of \[MW21\]: a randomized speedup applied under the outer quantifier block that the first randomized speedup leaves behind. The source paper makes this move itself in the proof of a later theorem, its quantum result (Theorem 5.4). The impossibility for $`c\ge\varphi`$ is a potential-function argument on a relaxed calculus. The relaxed calculus also contains the unmerged orientation of the randomized speedup, speedups at the end points of their parameter range, and weakening of exponents.

*What is kernel-checked:* the threshold of the *formal* calculus, in both directions, including a 15-step refutation at $`c=1.467>r_1`$. *What is not machine-checked:* that the formal rules coincide with the rules of \[MW21\] (a modelling claim, which we compare rule by rule on paper in Table 1), and the soundness of the lemmas of \[MW21\], on which the published bound $`1.4656`$ depends in the same way. This includes its hierarchy and contradiction lemma (Lemma 5.2), whose proof \[MW21\] only sketch. Conditional on exactly the lemmas that \[MW21, Theorem 5.3\] uses, the formal result gives $`\exists\cdot\mathsf{BPTIME}[n]\not\subseteq\mathsf{BPTS}[n^c]`$, hence $`\mathsf{MATIME}[n]\not\subseteq\mathsf{BPTS}[n^c]`$, for every $`c<\varphi`$. The threshold is a limit on one proof calculus. It says nothing about lower bounds proved by other methods.

## 1. Introduction

**Background.**

Alternation-trading proofs \[W13\] derive a contradiction from a hypothesis such as “SAT has an algorithm running in time $`n^c`$ and space $`n^{o(1)}`$” by alternately applying *speedup* rules, which add quantifiers to a class and reduce its running time, and *slowdown* rules, which use the hypothesis to remove a quantifier at the cost of a factor $`c`$ in the exponent. Fortnow and van Melkebeek obtained the exponent $`\varphi`$ for SAT against deterministic algorithms in this way \[FvM00, FLvMV05\]; Williams later reached $`2\cos(\pi/7)\approx1.8019`$, and Buss and Williams \[BW15\] proved that $`2\cos(\pi/7)`$ is the limit of alternation-trading proofs with those rules.

Mudigonda and Williams \[MW21\] extend the method to randomized and quantum verifiers. For randomized algorithms, the hypothesis is $`H_c`$: $`\exists\cdot\mathsf{BPTIME}[n]\subseteq\mathsf{BPTS}[n^c]`$, where $`\mathsf{BPTS}[t]`$ is two-sided-error randomized time $`t^{1+o(1)}`$ with space $`n^{o(1)}`$ (the ITCS version uses $`O(\log n)`$ space; nothing below depends on the difference). Their speedups are the Diehl–van Melkebeek randomized speedup \[DvM06\] (their Theorem 2.10 and Corollary 2.11) and the usual deterministic speedup (Corollary 2.8). The slowdown is their Lemma 5.1, and their Lemma 5.2 turns a proof $`\mathsf{BPTS}[n^d]\subseteq\dots\subseteq\mathsf{BPTS}[n^{d'}]`$ with $`d'<d`$ into a contradiction. Their Theorem 5.3 gives $`\exists\cdot\mathsf{BPTIME}[n]\not\subseteq\mathsf{BPTS}[n^c]`$ for $`c<r_1\approx1.4656`$, the largest root of $`x^3-x^2-1`$, and hence $`\mathsf{MATIME}[n]\not\subseteq\mathsf{BPTS}[n^c]`$ (part of their Main Theorem 3). The previous bound was $`\sqrt2`$ \[DvM06, Die07\]. \[MW21\] make no optimality claim for $`r_1`$; their optimality result (Appendix A) concerns their Main Theorem 1, for deterministic verifiers.

Result numbers of the form $`x.y`$ (Theorem 2.10, Lemma 5.2, …) refer to the arXiv version of \[MW21\].[^1] Our own results are numbered $`1,2,3,\dots`$ All theorems below are Lean theorems; names refer to the accompanying Lean library (namespace `PastaMath.MWThreshold`).

**Results.**

- **Threshold** (Theorem 2; `MWG.threshold_phi`, `MWG.threshold_goldenRatio`). For $`c\ge1`$, the formal calculus `MWL.Step` (Section 2) has a refutation if and only if $`c(c-1)<1`$, i.e. $`c<\varphi`$.

- **Construction** (Theorem 3; `MWG.refutes_of_lt_phi`). For $`1\le c<\varphi`$ a refutation exists in the exact rules. A refutation with 15 steps at $`c=1.467>r_1`$ is checked separately (`MWG.mw15_ok`, `MWG.mw21_root_lt`; Section 4.1).

- **Limit** (Theorem 4; `MW.no_mrefutation`, `MW.no_urefutation`, `MW.no_wrefutation`, `MWL.no_lit_refutation`). For $`c\ge\varphi`$ there is no refutation, strict or not, in a relaxed calculus that contains the exact rules, the unmerged orientation of the randomized speedup, and weakening. Every quantifier-free line reached from $`\mathsf{BPTS}[n^{a_0}]`$ has exponent at least $`c\,a_0`$.

Conditional on the lemmas of \[MW21\] listed in Section 7, this gives $`\exists\cdot\mathsf{BPTIME}[n]\not\subseteq\mathsf{BPTS}[n^c]`$ for every $`c<\varphi`$ (Corollary 11).

**Where the improvement comes from.**

The proof of \[MW21, Theorem 5.3\] uses one randomized speedup (Theorem 2.10), then $`k-1`$ deterministic speedups and $`k+2`$ slowdowns. The first randomized speedup leaves an outer block $`(\exists\,n^0)^1`$. Before the last slowdown removes it, the line is $`(\exists\,n^0)^1\mathsf{BPTS}[n^{e}]`$, and the randomized speedup Corollary 2.11 applies to it again; its own leading $`n^0`$ block is absorbed into $`(\exists\,n^0)^1`$ (the footnote to Corollary 2.11). Repeating the inner pattern under this block contracts the exponent by a factor $`\rho<1`$ whenever $`c(c-1)<1`$ (for a long enough pattern), and the factor $`c`$ for removing the block is paid only once. Using the pattern once needs $`c\cdot c(c-1)<1`$ in the limit, which is $`c^3-c^2-1<0`$. \[MW21\] repeat a pattern under a persistent outer block in the proof of their Theorem 5.4 (for $`\exists\cdot\mathsf{BQTIME}`$, with Grover search in place of the classical speedups); the construction here is the same move in the classical setting.

**Novelty.**

We are not aware of a prior statement of this improvement, or of a determination of the threshold of this calculus. Our search was not exhaustive.

**AI assistance.**

The proofs and the Lean formalisation were produced with Anthropic’s Claude models under the author’s direction. The kernel-checked Lean proofs are the primary evidence for the theorems about the formal calculus; this text explains them and states what they do and do not establish.

## 2. The calculus

### 2.1 Lines

A *line* is an alternating complexity class
``` math
(Q_1\,n^{a_1})^{b_1}\,(Q_2\,n^{a_2})^{b_2}\cdots(Q_k\,n^{a_k})^{b_k}\;K[n^{d}]
```
\[MW21, Definition 2.5\]: in stage $`i`$ the machine receives a string of length $`n^{a_i}`$ from quantifier $`Q_i\in\{\exists,\forall\}`$ and passes $`n^{b_i}`$ bits to the next stage; the verifier $`K\in\{\mathsf{TS},\mathsf{BPTS}\}`$ runs in time $`n^{d}`$; all $`n^{o(1)}`$ factors are suppressed. We call $`a_i`$ the *guess exponent* and $`b_i`$ the *output exponent* (or superscript) of block $`i`$, and set $`b_0=1`$ (the input has length $`n`$). A block written $`(Q\,x\log n)^b`$ or $`(Q\,n^0)^b`$ has guess exponent $`0`$. For a block list $`P`$ let $`\mathrm{pin}(P)`$ be the output exponent of its innermost block, with $`\mathrm{pin}(\emptyset)=1`$. Every line of a proof is *orderly*, $`a_i\le b_i`$ \[MW21, Lemma 2.17\].

### 2.2 Rules

Fix $`c`$. The rules are those of \[MW21, Definition 2.14\] that can occur in a proof from a $`\mathsf{BPTS}`$ line, with the slowdown of \[MW21, Lemma 5.1\] (the generic slowdown of Definition 2.13 with $`\alpha=1`$). In each rule $`P`$ is the rest of the block list and $`(Q\,n^{a})^{b}`$ the innermost block.

1.  **(R3)** **Randomized speedup on a quantifier-free line** (rule 3, Theorem 2.10). For $`0<x<d`$:
    ``` math
    \mathsf{BPTS}[n^d]\subseteq(\exists\,n^0)^1(\forall\,n^x)^{\max(x,1)}(\exists\,x\log n)^1\,\mathsf{TS}[n^{d-x}].
    ```

2.  **(R4)** **Randomized speedup under a block** (rule 4, Corollary 2.11). For $`0<x<d`$:
    ``` math
    P\,(Q\,n^{a})^{b}\,\mathsf{BPTS}[n^d]\subseteq P\,(Q\,n^{a})^{b}(\neg Q\,n^{x})^{\max(b,x)}(Q\,x\log n)^{b}\,\mathsf{TS}[n^{d-x}].
    ```
    Corollary 2.11 prints the new quantifiers as $`Q_{k+1},Q_{k+2}`$. By its footnote, the leading $`n^0`$ quantifier of Theorem 2.10 “is absorbed into the previous quantifier”, which forces $`Q_{k+1}=\neg Q`$ and $`Q_{k+2}=Q`$.

3.  **(R2)** **Deterministic speedup** (rule 2, Corollary 2.8). For $`0<x<d`$:
    ``` math
    P\,(Q\,n^{a})^{b}\,\mathsf{TS}[n^d]\subseteq P\,(Q\,n^{\max(a,x)})^{\max(b,x)}(\neg Q\,x\log n)^{b}\,\mathsf{TS}[n^{d-x}].
    ```

4.  **(S)** **Slowdown** (rule 5, Lemma 5.1, under $`H_c`$). For a kernel $`K\in\{\mathsf{TS},\mathsf{BPTS}\}`$ (a $`\mathsf{TS}`$ kernel is a $`\mathsf{BPTS}`$ kernel):
    ``` math
    P\,(Q\,n^{a})^{b}\,K[n^d]\subseteq P\,\mathsf{BPTS}[n^{c\max(d,\,b,\,a,\,\mathrm{pin}(P))}].
    ```

Rule 1 (Lemma 2.7 on a quantifier-free $`\mathsf{TS}`$ line) never applies: the start line is $`\mathsf{BPTS}`$, a $`\mathsf{TS}`$ kernel is produced only by a speedup, and every slowdown produces a $`\mathsf{BPTS}`$ kernel. For the same reason a deterministic speedup is applied only to a line produced by a speedup (randomized or deterministic), never directly after a slowdown, and a randomized speedup only to a line produced by a slowdown or to the start line.

**Definition 1** (refutation; `MWL.Refutes`). A *refutation* at $`c`$ is a sequence of $`N\ge1`$ rule applications from $`\mathsf{BPTS}[n^{a_0}]`$, $`a_0>0`$, to a quantifier-free line $`\mathsf{BPTS}[n^{a'}]`$ with $`a'<a_0`$.

Intermediate lines are unrestricted. The first step is necessarily (R3), so a refutation has at least two inclusions, as Lemma 5.2 requires. Lemma 5.2 as printed says “$`d<d'`$”; Definition 2.14 says $`d'\le d`$, and the proof of Lemma 5.2 uses $`d'<d`$. We read the condition as strict; the limit theorem holds for the non-strict version as well.

### 2.3 The formalisation

A Lean line is a triple $`(\mathit{bl},k,a)`$: the block list $`\mathit{bl}`$, stored innermost first, of blocks $`\langle q,g,o\rangle`$ ($`q=\mathtt{true}`$ for $`\exists`$, $`g`$ the guess exponent, $`o`$ the output exponent); the kernel type $`k`$ ($`\mathtt{true}`$ for $`\mathsf{BPTS}`$); and the kernel exponent $`a\in\mathbb R`$ (`MWL.Line`, `MWL.Blk`, `MWL.pin`). The relation `MWL.Step` $`c`$ has one constructor per rule, with the exact output values and side conditions above; `MWL.Refutes` is Definition 1. Table 1 compares them with \[MW21\].

| [MW21] | Lean | Effect, cost and side conditions in `MWL.Step` ($`u=\langle q,g,o\rangle`$ innermost block, $`\mathit{rest}`$ the blocks outside it) |
|:---|:---|:---|
| Def. 2.14 rule 3, Theorem 2.10 | `rspeed0` | $`([],\mathsf{BPTS},a)\mapsto([\langle\exists,0,1\rangle,\langle\forall,x,\max(x,1)\rangle,\langle\exists,0,1\rangle],\mathsf{TS},a-x)`$ (innermost first); requires $`0<x<a`$ |
| Def. 2.14 rule 4, Corollary 2.11 (merged, footnote 6) | `rspeed` | $`(u::\mathit{rest},\mathsf{BPTS},a)\mapsto(\langle q,0,o\rangle::\langle\neg q,x,\max(o,x)\rangle::u::\mathit{rest},\mathsf{TS},a-x)`$; $`u`$ unchanged; requires $`0<x<a`$ |
| Def. 2.14 rule 2, Corollary 2.8 | `dspeed` | $`(u::\mathit{rest},\mathsf{TS},a)\mapsto(\langle\neg q,0,o\rangle::\langle q,\max(g,x),\max(o,x)\rangle::\mathit{rest},\mathsf{TS},a-x)`$; requires $`0<x<a`$ |
| Def. 2.14 rule 5, Lemma 5.1 ($`\alpha=1`$) | `slow` | $`(u::\mathit{rest},k,a)\mapsto(\mathit{rest},\mathsf{BPTS},c\max(a,o,g,\mathrm{pin}(\mathit{rest})))`$ for either kernel; $`\mathrm{pin}([])=1`$ |
| Lemma 5.2, Def. 2.14 | `Refutes` | $`N\ge1`$ steps from $`([],\mathsf{BPTS},a_0)`$, $`a_0>0`$, to $`([],\mathsf{BPTS},a')`$ with $`a'<a_0`$ |
| Theorem 2.10 under a block, leading $`n^0`$ block not absorbed | `StepU.rspeedU` | $`(u::\mathit{rest},\mathsf{BPTS},a)\mapsto(\langle\neg q,0,o\rangle::\langle q,x,\max(o,x)\rangle::\langle\neg q,0,o\rangle::u::\mathit{rest},\mathsf{TS},a-x)`$; requires $`0<x<a`$ |
| trivial inclusions (weakening) | `StepW.weaken` | same quantifiers and block count; any guess exponent, output exponent or the kernel exponent raised (guess $`\le`$ output); a $`\mathsf{TS}`$ kernel may become $`\mathsf{BPTS}`$ |

*Table 1: The rules of \[MW21\] used in proofs from a $`\mathsf{BPTS}`$ line, and their Lean counterparts. Constructor names are those of `MWL.Step`, `MWL.StepU` and `MWL.StepW`. Rows below the middle line are not rules of \[MW21\]; they are covered by the limit theorem only (Section 6).*

**Reading points.**

The following choices are ours; each is either forced by the text of \[MW21\] or affects only the limit side, where it is covered anyway (Section 6).

1.  *Rule 3’s last block.* \[MW21\] do not print the output exponent of the $`(\exists\,x\log n)`$ block of rule 3. We use $`1`$, the value $`b_k`$ that Corollary 2.11 gives for $`k=0`$ (the input). The relaxed calculus allows any value.

2.  *Orientation of rule 4.* We use the merged orientation prescribed by the footnote to Corollary 2.11. The construction uses only it; the limit also covers the other one.

3.  *Theorem 2.10’s orientation.* Theorem 2.10 is printed as $`\mathsf{BPTS}\subseteq(\forall\,n^0)^1(\exists\,n^x)(\forall\,x\log n)\mathsf{TS}`$, rule 3 of Definition 2.14 as $`(\exists\,n^0)^1(\forall\,n^x)(\exists\,x\log n)\mathsf{TS}`$; they are equivalent because $`\mathsf{BPTS}`$ is closed under complement.

4.  *Slowdown of a $`\mathsf{TS}`$ kernel.* Lemma 5.1 is stated for $`\mathsf{BPTS}`$ kernels; rule 5 of Definition 2.14 is stated for $`(\mathsf{BP})\mathsf{TS}`$ kernels, and \[MW21, Theorem 5.3\] applies it to a $`\mathsf{TS}`$ kernel. We use $`\mathsf{TS}\subseteq\mathsf{BPTS}`$.

5.  *Strictness* (Definition 1).

6.  *Lower-order terms.* As in \[MW21\], $`n^{o(1)}`$ factors are suppressed and do not appear in the exponents.

## 3. Statements

**Theorem 2** (`MWG.threshold_phi`, `MWG.threshold_goldenRatio`). For every real $`c\ge1`$:
``` math
\bigl(\exists N,M:\ \texttt{MWL.Refutes}\ c\ N\ M\bigr)\iff c(c-1)<1\iff c<\tfrac{1+\sqrt5}{2}.
```

**Theorem 3** (`MWG.refutes_of_lt_phi`). If $`c\ge1`$ and $`c(c-1)<1`$, there is a refutation at $`c`$ in `MWL.Step`.

**Theorem 4** (`MW.qf_ge`, `MW.no_mrefutation`, `MWL.no_lit_refutation`; `MW.no_urefutation`, `MW.no_wrefutation`, `MWL.no_litU_refutation`, `MWL.no_litW_refutation`). Let $`c>0`$ with $`c^2\ge c+1`$. In the relaxed calculus of Section 5, every quantifier-free line $`\mathsf{BPTS}[n^{a'}]`$ reached from $`\mathsf{BPTS}[n^{a_0}]`$, $`a_0\ge0`$, by at least one rule step (and any number of weakening steps) has $`a'\ge c\,a_0`$. Hence there is no refutation, strict or non-strict, in `MWL.Step`, in its extension `MWL.StepU` by the unmerged orientation of rule 4, or in its further extension `MWL.StepW` by weakening.

Theorem 2 is Theorems 3 and 4 together; $`c(c-1)<1`$ is equivalent to $`c<\varphi`$ for $`c\ge1`$. The same equivalence holds with `StepU` and with `StepW` in place of `Step` (`MWG.threshold_phi_U`, `MWG.threshold_phi_W`; for `StepW` the refutation is non-strict and must contain at least one rule step, since a weakening alone gives $`\mathsf{BPTS}[n^{a_0}]\subseteq\mathsf{BPTS}[n^{a_0}]`$).

## 4. The construction for $`c<\varphi`$

Fix $`c\ge1`$. Let $`\sigma_0=1`$ and $`\sigma_{i+1}=\sigma_i+c^i`$, so $`\sigma_j=1+\sum_{i<j}c^i`$ and $`(c-1)\sigma_j=c^j+c-2`$ (`MWG.sig`, `MWG.sig_closed`). Write $`\top=(\exists\,n^0)^1`$ for the outer block that (R3) creates (`MWG.top`).

**Lemma 5** (inner phase; `MWG.inner`). Let $`j\ge0`$, $`t\ge1`$, and let $`R`$ be a block list with $`\mathrm{pin}(R)\le c^jt`$. Then the line $`R\,(q\,\log n)^1\,\mathsf{TS}[n^{\sigma_jt}]`$ derives $`R\,\mathsf{BPTS}[n^{v}]`$ for some $`0\le v\le c^{j+1}t`$, using $`j`$ deterministic speedups and $`j+1`$ slowdowns.

*Proof.* Induction on $`j`$. For $`j=0`$ the kernel is $`t`$; one slowdown costs $`c\max(t,1,0,\mathrm{pin}(R))\le ct`$, since $`t\ge1`$ and $`\mathrm{pin}(R)\le t`$. For $`j+1`$ the kernel is $`\sigma_{j+1}t=\sigma_jt+c^jt`$. Apply (R2) with $`x=c^jt`$, which satisfies $`1\le x<\sigma_{j+1}t`$: the block $`(q\,\log n)^1`$ becomes $`(q\,n^{x})^{x}`$ (as $`\max(0,x)=x=\max(1,x)`$), a new block $`(\neg q\,\log n)^1`$ is opened, and the kernel becomes $`\sigma_jt`$. By induction with $`R'=R\,(q\,n^x)^x`$, $`\mathrm{pin}(R')=c^jt`$, we reach $`R\,(q\,n^x)^x\,\mathsf{BPTS}[n^{v}]`$ with $`v\le c^{j+1}t`$. A slowdown costs $`c\max(v,x,x,\mathrm{pin}(R))\le c\cdot c^{j+1}t`$, because $`x=c^jt\le c^{j+1}t`$ and $`\mathrm{pin}(R)\le c^{j+1}t`$. ∎

All the floors $`\max(\cdot,1)`$ in the rules are resolved by $`t\ge1`$: every speedup parameter is at least $`t\ge1`$, and every kernel exponent in the derivation is at least $`t`$.

**Lemma 6** (the macro $`M(j+1)`$; `MWG.mac`). Let $`j\ge0`$, $`T\ge1`$ and $`e=\sigma_{j+1}T`$. Both $`\mathsf{BPTS}[n^{e}]`$ and $`\top\,\mathsf{BPTS}[n^{e}]`$ derive $`\top\,\mathsf{BPTS}[n^{e'}]`$ for some $`0\le e'\le c^{j+2}T=\rho_{j+1}\,e`$, where
``` math
\rho_{j+1}=\frac{c^{j+2}}{\sigma_{j+1}}=\frac{c^{j+2}(c-1)}{c^{j+1}+c-2}\quad(c\neq1).
```
The derivation (the *macro* $`M(j+1)`$) is one randomized speedup with $`x=c^jT`$, then the deterministic speedups $`x=c^{j-1}T,\dots,cT,T`$, then $`j+2`$ slowdowns.

*Proof.* From $`\mathsf{BPTS}[n^e]`$ apply (R3), from $`\top\,\mathsf{BPTS}[n^e]`$ apply (R4) under $`\top`$ (its new $`n^0`$ block is absorbed into $`\top`$), with $`x=c^jT\in[1,e)`$. Both give $`\top\,(\forall\,n^{x})^{x}(\exists\,\log n)^1\,\mathsf{TS}[n^{\sigma_jT}]`$. Lemma 5 with $`R=\top\,(\forall\,n^x)^x`$, $`\mathrm{pin}(R)=c^jT`$, reaches $`\top\,(\forall\,n^x)^x\,\mathsf{BPTS}[n^v]`$ with $`v\le c^{j+1}T`$, and the last slowdown costs $`c\max(v,x,x,1)\le c^{j+2}T`$, because $`1\le x\le c^{j+1}T`$. ∎

The kernel after all speedups of the macro is exactly $`T`$, and the slowdowns cost at most $`cT,c^2T,\dots,c^{j+2}T`$ in turn.

**Example: $`c=3/2`$.**

Here $`\sigma_2=1+1+\tfrac32=\tfrac72`$ and $`\rho_2=(3/2)^3/(7/2)=27/28`$. For $`e\ge7/2`$, $`T=2e/7`$ and the macro $`M(2)`$ is
``` math
\begin{aligned}
\top\,\mathsf{BPTS}[n^{e}]
&\subseteq\top\,(\forall\,n^{3e/7})^{3e/7}(\exists\,\log n)^1\,\mathsf{TS}[n^{4e/7}] &&\text{Cor. 2.11, }x=3e/7\\
&\subseteq\top\,(\forall\,n^{3e/7})^{3e/7}(\exists\,n^{2e/7})^{2e/7}(\forall\,\log n)^1\,\mathsf{TS}[n^{2e/7}] &&\text{Cor. 2.8, }x=2e/7\\
&\subseteq\top\,(\forall\,n^{3e/7})^{3e/7}(\exists\,n^{2e/7})^{2e/7}\,\mathsf{BPTS}[n^{3e/7}] &&\text{Lemma 5.1: }\tfrac32\max(\tfrac{2e}7,1,0,\tfrac{2e}7)\\
&\subseteq\top\,(\forall\,n^{3e/7})^{3e/7}\,\mathsf{BPTS}[n^{9e/14}] &&\text{Lemma 5.1: }\tfrac32\max(\tfrac{3e}7,\tfrac{2e}7,\tfrac{2e}7,\tfrac{3e}7)\\
&\subseteq\top\,\mathsf{BPTS}[n^{27e/28}] &&\text{Lemma 5.1: }\tfrac32\max(\tfrac{9e}{14},\tfrac{3e}7,\tfrac{3e}7,1).
\end{aligned}
```
Each application multiplies the kernel exponent by exactly $`27/28`$ (the script `scripts/mw_check.py macro` checks this exactly). Twelve applications from $`a_0=25/4`$ (the first one creates $`\top`$ by (R3)) and the final slowdown give a 61-step refutation, ending at $`\mathsf{BPTS}[n^{6.0595\ldots}]`$.

**Lemma 7** (`MWG.exists_contracting`, via Bernoulli’s inequality `MWG.bernoulli`). If $`c\ge1`$ and $`c(c-1)<1`$, then $`\rho_{j+1}<1`$, i.e. $`c^{j+2}<\sigma_{j+1}`$, for some $`j`$.

*Proof.* For $`c=1`$ take $`j=0`$: $`\rho_1=1/2`$. For $`c>1`$, using $`(c-1)\sigma_{N+1}=c^{N+1}+c-2`$, the claim $`c^{N+2}<\sigma_{N+1}`$ is equivalent to $`c^{N+1}(1+c-c^2)>2-c`$. Here $`1+c-c^2>0`$, and $`c^{N+1}\ge1+(N+1)(c-1)`$ grows without bound. ∎

As $`j\to\infty`$, $`\rho_{j+1}\to c(c-1)`$; so the macros contract for some length exactly when $`c(c-1)<1`$. The shortest contracting macro at $`c`$ is $`M(1)`$ (with $`\rho_1=c^2/2`$) for $`c<\sqrt2`$, $`M(2)`$ (with $`\rho_2=c^3/(c+2)`$) for $`c`$ below the real root $`1.5213\ldots`$ of $`c^3=c+2`$, and longer macros closer to $`\varphi`$. Iterating $`M(1)`$ recovers the earlier bound $`\sqrt2`$.

*Proof of Theorem 3.* Take $`j`$ from Lemma 7, write $`\sigma=\sigma_{j+1}`$ and $`\rho=\rho_{j+1}<1`$, and choose $`m`$ with $`c\rho^{m+1}<1`$. Start from $`a_0=c\sigma+1`$. One macro from $`\mathsf{BPTS}[n^{a_0}]`$ (with $`T=a_0/\sigma\ge1`$) reaches $`\top\,\mathsf{BPTS}[n^{e_1}]`$ with $`e_1\le\rho a_0`$. Repeat the macro under $`\top`$ while the kernel $`e`$ satisfies $`e\ge\sigma`$ (so $`T=e/\sigma\ge1`$), at most $`m`$ times; each round multiplies the kernel by at most $`\rho`$, so afterwards $`e'\le\max(\rho^{m}e_1,\sigma)\le\max(\rho^{m+1}a_0,\sigma)`$ (`MWG.iter`). The final slowdown removes $`\top`$ at cost $`c\max(e',1,0,1)\le c\max(\rho^{m+1}a_0,\sigma)<a_0`$, since $`c\rho^{m+1}<1`$ and $`c\sigma<a_0`$. ∎

**Side conditions.**

Every speedup parameter in the construction is at least $`1`$ and below the current kernel exponent, every kernel exponent is at least $`1`$, and every line is orderly and alternates. The outer block $`\top`$ is never popped until the last step. Its guess exponent enters only the final slowdown; the slowdowns that remove the block directly inside $`\top`$ use its output exponent $`1`$.

**Relation to the proof of \[MW21, Theorem 5.3\].**

The annotation $`1^k0^{k+2}`$ of \[MW21, Theorem 5.3\] is the macro $`M(k)`$ used once from $`\mathsf{BPTS}[n^d]`$, followed by the final slowdown. It is a refutation when $`c^{k+2}<\sigma_k`$, i.e. $`c\rho_k<1`$, and in the limit $`k\to\infty`$ this is $`c^2(c-1)<1`$, i.e. $`c<r_1`$. The parameters printed in \[MW21\] differ from these (Section 8). The proof of \[MW21, Theorem 5.3\] never applies Corollary 2.11. The construction above applies it every time it repeats the macro under $`\top`$; the first use is the eighth line of the 15-step proof below.

### 4.1 A 15-step refutation at $`c=1.467`$

The sequence $`M(3)\,M(3)`$ followed by the final slowdown is a refutation at $`c=1467/1000`$ from $`a_0=10^4`$ (`MWG.mw15_ok`, checked by kernel evaluation of the executable checker `MWL.checkQ`, whose soundness is `MWL.checkQ_sound`). Every real root of $`x^3-x^2-1`$ is below $`1.467`$ (`MWG.mw21_root_lt`), so this proof works at an exponent where \[MW21, Theorem 5.3\] does not apply. The speedup parameters are not those of the general construction; they were chosen for this sequence, and any parameters satisfying the side conditions may be used. Exponents are rounded to two decimals; the checks are exact. Lines are outermost first.

``` math
\begin{aligned}
 0\quad&\mathsf{BPTS}[n^{10000}]\\
 1\quad&\subseteq(\exists\,n^0)^1(\forall\,n^{3830})^{3830}(\exists\,\log n)^1\,\mathsf{TS}[n^{6170}] &&\text{Thm 2.10, }x=3830\\
 2\quad&\subseteq\cdots(\forall\,n^{3830})^{3830}(\exists\,n^{2610.76})^{2610.76}(\forall\,\log n)^1\,\mathsf{TS}[n^{3559.24}] &&\text{Cor. 2.8, }x=206250/79\\
 3\quad&\subseteq\cdots(\exists\,n^{2610.76})^{2610.76}(\forall\,n^{1779.66})^{1779.66}(\exists\,\log n)^1\,\mathsf{TS}[n^{1779.58}] &&\text{Cor. 2.8, }x=105000/59\\
 4\quad&\subseteq(\exists\,n^0)^1(\forall\,n^{3830})^{3830}(\exists\,n^{2610.76})^{2610.76}(\forall\,n^{1779.66})^{1779.66}\,\mathsf{BPTS}[n^{2610.76}] &&\text{Lemma 5.1}\\
 5\quad&\subseteq(\exists\,n^0)^1(\forall\,n^{3830})^{3830}(\exists\,n^{2610.76})^{2610.76}\,\mathsf{BPTS}[n^{3829.99}] &&\text{Lemma 5.1}\\
 6\quad&\subseteq(\exists\,n^0)^1(\forall\,n^{3830})^{3830}\,\mathsf{BPTS}[n^{5618.61}] &&\text{Lemma 5.1}\\
 7\quad&\subseteq(\exists\,n^0)^1\,\mathsf{BPTS}[n^{8242.50}] &&\text{Lemma 5.1}\\
 8\quad&\subseteq(\exists\,n^0)^1(\forall\,n^{3156.82})^{3156.82}(\exists\,\log n)^1\,\mathsf{TS}[n^{5085.68}] &&\text{Cor. 2.11, }x=1550000/491\\
 9\quad&\subseteq\cdots(\forall\,n^{3156.82})^{3156.82}(\exists\,n^{2151.90})^{2151.90}(\forall\,\log n)^1\,\mathsf{TS}[n^{2933.78}] &&\text{Cor. 2.8, }x=170000/79\\
10\quad&\subseteq\cdots(\exists\,n^{2151.90})^{2151.90}(\forall\,n^{1466.85})^{1466.85}(\exists\,\log n)^1\,\mathsf{TS}[n^{1466.92}] &&\text{Cor. 2.8, }x=1040000/709\\
11\quad&\subseteq(\exists\,n^0)^1(\forall\,n^{3156.82})^{3156.82}(\exists\,n^{2151.90})^{2151.90}(\forall\,n^{1466.85})^{1466.85}\,\mathsf{BPTS}[n^{2151.98}] &&\text{Lemma 5.1}\\
12\quad&\subseteq(\exists\,n^0)^1(\forall\,n^{3156.82})^{3156.82}(\exists\,n^{2151.90})^{2151.90}\,\mathsf{BPTS}[n^{3156.95}] &&\text{Lemma 5.1}\\
13\quad&\subseteq(\exists\,n^0)^1(\forall\,n^{3156.82})^{3156.82}\,\mathsf{BPTS}[n^{4631.25}] &&\text{Lemma 5.1}\\
14\quad&\subseteq(\exists\,n^0)^1\,\mathsf{BPTS}[n^{6794.04}] &&\text{Lemma 5.1}\\
15\quad&\subseteq\mathsf{BPTS}[n^{9966.86}] &&\text{Lemma 5.1}
\end{aligned}
```

In lines 2, 3, 9 and 10, “$`\cdots`$” stands for the blocks of the previous line outside the ones shown. At line 8 the leading $`n^0`$ block of Theorem 2.10 is absorbed into $`(\exists\,n^0)^1`$, as the footnote to Corollary 2.11 prescribes; line 8 is the first use of rule 4. The final exponent is exactly $`27410261545753261542320966055909/2750140100000000000000000000\approx9966.86<10^4`$, so Lemma 5.2 applies.

A longer certificate at $`c=8/5`$ (2687 steps: $`M(8)`$ repeated 158 times, then the final slowdown) is also kernel-checked (`MWL.mwcert_ok`). The general theorem makes it redundant.

## 5. The limit for $`c\ge\varphi`$

### 5.1 The relaxed calculus

A *relaxed line* (`MW.MLine`) is $`(s_1,\dots,s_m;\,k;\,a)`$: the output exponents of the blocks (outermost first; Lean stores them innermost first), a kernel type $`k\in\{\mathsf{TS},\mathsf{BPTS}\}`$ and a kernel exponent $`a`$. Quantifiers and guess exponents are dropped. The input exponent in front of the first block is $`0`$ (instead of $`1`$). The rules of `MW.MStep` $`c`$ only bound their outputs from below, and every speedup allows $`0\le x\le a`$. Write $`s\cdot b`$ for the list $`s`$ with $`b`$ appended (innermost), and $`\mathrm{pin}'(s)`$ for the last entry of $`s`$ ($`0`$ if $`s`$ is empty).

- `rspeed0`: $`(\emptyset;k;a)\vdash(b_1,b_2,b_3;\mathsf{TS};a_2)`$ for either $`k`$, with $`b_1\ge0`$, $`b_2\ge\max(x,0)`$, $`b_3\ge0`$, $`a_2\ge a-x`$.

- `rspeed`: $`(s\cdot b;k;a)\vdash(s\cdot b\cdot b_2\cdot b_3;\mathsf{TS};a_2)`$ for either $`k`$, with $`b_2\ge\max(b,x)`$, $`b_3\ge b`$, $`a_2\ge a-x`$.

- `dspeed`: $`(s\cdot b;\mathsf{TS};a)\vdash(s\cdot t_2\cdot b_3;\mathsf{TS};a_2)`$ with $`t_2\ge\max(b,x)`$, $`b_3\ge b`$, $`a_2\ge a-x`$.

- `slow`: $`(s\cdot b;k;a)\vdash(s;\mathsf{BPTS};e)`$ with $`e\ge c\max(\mathrm{pin}'(s),b,a)`$.

`MW.UStep` adds `rspeedU`: $`(s\cdot b;k;a)\vdash(s\cdot b\cdot b_1\cdot b_2\cdot b_3;\mathsf{TS};a_2)`$ with $`b_1\ge0`$, $`b_2\ge\max(b,x)`$, $`b_3\ge b`$, $`a_2\ge a-x`$ (Theorem 2.10 under a block without absorbing its leading $`n^0`$ block). `MW.StepW` adds weakening (`MW.Weaker`): $`(s;k;a)\vdash(s';k';a')`$ with $`s'`$ of the same length as $`s`$ and $`s'_i\ge s_i`$, $`a'\ge a`$, and $`k'=k`$ or $`k'=\mathsf{BPTS}`$.

**Lemma 8** (`MWL.lit_m`, `MWL.lit_u`, `MWL.lit_w`). Let $`c\ge0`$. The encoding that keeps the output exponents and the kernel maps every `MWL.Step` step between orderly lines with nonnegative exponents to an `MW.MStep` step, every `MWL.StepU` step to a `MW.UStep` step and every `MWL.StepW` step to a `MW.StepW` step, and preserves these invariants.

*Proof.* Each relaxed rule has the literal outputs as admissible values. For the slowdown, the literal cost $`c\max(a,o,g,\mathrm{pin}(\mathit{rest}))`$ dominates $`c\max(\mathrm{pin}'(\mathit{rest}),o,a)`$ because $`\mathrm{pin}(\emptyset)=1\ge0=\mathrm{pin}'(\emptyset)`$. Guess exponents can be dropped because they satisfy $`g\le o`$ on every line. ∎

### 5.2 The potential

Let $`c>0`$ with $`c^2\ge c+1`$, and $`g=1/(c^2-1)`$. Then (`MW.facts_of_phi`)
``` math
c\ge1,\qquad 0\le g\le1,\qquad 1+g\le c,\qquad 1+g=c^2g.
```
The third is equivalent to $`(c-1)(c^2-1)\ge1`$, i.e. $`c(c^2-c-1)\ge0`$, i.e. $`c^2\ge c+1`$; the fourth is an identity. Only the third condition constrains $`c`$: with this choice of $`g`$ the condition $`1+g\le c^2g`$, which the randomized speedup needs, holds with equality for every $`c>1`$. For a relaxed line define (`MW.pot`, `MW.up`, `MW.Φ`)
``` math
\begin{aligned}
\mathrm{pot}(b,\mathsf{BPTS},a)&=\max(b,a), & \mathrm{pot}(b,\mathsf{TS},a)&=\max(b,\,g a),\\
U(\emptyset;y)&=c\max(0,y), & U(s\cdot b';y)&=U(s;\,c\max(b',y)),\\
\Phi(\emptyset;k;a)&=a, & \Phi(s\cdot b;k;a)&=U(s;\mathrm{pot}(b,k,a)).
\end{aligned}
```
So $`\Phi(s_1,\dots,s_m;k;a)=c\max(0,c\max(s_1,\dots c\max(s_{m-1},\mathrm{pot}(s_m,k,a))\cdots))`$: the innermost block contributes a line value, and each outer block contributes the cost of a slowdown through it. $`U`$ is monotone in $`y`$ and in every entry of the list for $`c\ge0`$ (`MW.up_mono`, `MW.up_mono_list`), and $`\mathrm{pot}`$ is monotone in $`b`$ and $`a`$ for $`g\ge0`$ (`MW.pot_mono`). For $`a\ge0`$ and $`g\le1`$, $`\mathrm{pot}(b,k,a)\le\max(b,a)`$ (`MW.pot_le`).

**Lemma 9** (balance; `MW.bal`, `MW.key_d`, `MW.key_r`). For $`0\le x\le a`$ let $`\mu=\max(x,\,g(a-x))`$. Then $`(1+g)\mu\ge g a`$; hence $`g a\le c\mu`$ and $`a\le c^2\mu`$.

*Proof.* $`(1+g)\mu=\mu+g\mu\ge g(a-x)+gx=ga`$. Then $`ga\le(1+g)\mu\le c\mu`$; and $`(1+g)a=c^2ga\le c^2(1+g)\mu`$, so $`a\le c^2\mu`$. ∎

**Lemma 10** (the potential never decreases; `MW.phi_step`, `MW.phi_ustep`, `MW.phi_mono`). Let $`c^2\ge c+1`$, and let $`L\vdash L'`$ be a `MW.StepW` step from a line with nonnegative entries. Then $`\Phi(L)\le\Phi(L')`$.

*Proof.* In each case the outer blocks $`s`$ are unchanged, so by monotonicity of $`U`$ it suffices to compare the values passed to $`U(s;\cdot)`$.

- `dspeed` from $`(s\cdot b;\mathsf{TS};a)`$: we need $`\max(b,ga)\le c\max(t_2,b_3,ga_2)`$. Now $`b\le cb\le ct_2`$, and $`ga\le c\mu\le c\max(t_2,ga_2)`$ by Lemma 9, since $`t_2\ge x`$ and $`a_2\ge a-x`$.

- `rspeed` from $`(s\cdot b;k;a)`$: since $`\mathrm{pot}(b,k,a)\le\max(b,a)`$, we need
  ``` math
  \max(b,a)\le c\max\bigl(b,\ c\max(b_2,b_3,ga_2)\bigr).
  ```
  Now $`b\le cb`$, and $`a\le c^2\mu\le c\cdot c\max(b_2,ga_2)`$ by Lemma 9.

- `rspeedU`: the same with one more lift $`c\max(b_1,\cdot)`$ inserted, which only increases the value because $`c\ge1`$.

- `slow` from $`(s\cdot b'\cdot b;k;a)`$ to $`(s\cdot b';\mathsf{BPTS};e)`$: before the step the value is $`c\max(b',\mathrm{pot}(b,k,a))\le c\max(b',b,a)\le e`$, and after it the value is $`\mathrm{pot}(b',\mathsf{BPTS},e)=\max(b',e)\ge e`$. If $`s\cdot b'`$ is empty, $`\Phi(L)=c\max(0,\mathrm{pot}(b,k,a))\le c\max(0,b,a)\le e=\Phi(L')`$.

- `rspeed0` from a quantifier-free line: $`\Phi(L')\ge c\cdot c\cdot c\mu\ge c\,a=c\,\Phi(L)\ge\Phi(L)`$ (`MW.first_step`).

- weakening: monotonicity of $`U`$ and $`\mathrm{pot}`$, together with $`\mathrm{pot}(b,\mathsf{TS},a)\le\mathrm{pot}(b,\mathsf{BPTS},a)`$ for $`a\ge0`$, $`g\le1`$.

∎

*Proof of Theorem 4.* Nonnegativity of all entries is preserved (`MW.nn_step`, `MW.nn_stepw`). A path from $`\mathsf{BPTS}[n^{a_0}]`$ stays at quantifier-free lines, with exponent at least $`a_0`$, while it uses only weakenings (`MW.ustep_nil_ne`: a rule step from a quantifier-free line opens blocks). Its first rule step is therefore `rspeed0` from a quantifier-free line of exponent $`a\ge a_0`$, and gives $`\Phi\ge c\,a\ge c\,a_0`$ (`MW.first_step`). By Lemma 10, $`\Phi`$ never decreases afterwards, and on the final quantifier-free line $`\Phi`$ is its exponent $`a'`$. So $`a'\ge ca_0>a_0`$ when $`a_0>0`$, since $`c>1`$ (`MW.qf_ge`, `MW.qf_ge_u`, `MW.qf_ge_w`). The literal statements follow by Lemma 8. ∎

**Tightness.**

At $`c=\varphi`$, $`g=1/(\varphi^2-1)=1/\varphi`$ and $`1+g=\varphi=c`$, so the inequality for `dspeed` is an equality when $`x=g(a-x)`$, and the one for `rspeed` is then an equality as well. The macros of Section 4 approach this balance as their length grows: in $`M(j+1)`$ consecutive speedup parameters have ratio $`c`$, and at $`c=\varphi`$ the ratio $`x/(a-x)`$ of each deterministic speedup tends to $`g=1/\varphi`$. We note, as a heuristic and not as something the Lean proofs show, that a deterministic speedup can follow only a speedup in this calculus (every slowdown leaves a $`\mathsf{BPTS}`$ kernel), which is why the threshold is $`\varphi`$ and not the larger $`2\cos(\pi/7)`$ of the deterministic calculus \[BW15\].

## 6. What the relaxed calculus covers

Every relaxation below makes more steps possible, so the limit theorem covers it.

1.  *Unmerged randomized speedup.* Theorem 2.10 applied under a block $`(Q\,n^a)^b`$ whose leading $`n^0`$ block is not absorbed: `rspeedU`. Since quantifiers are not tracked, this covers the leading block of either type; the literal `MWL.StepU.rspeedU` formalises the alternating case $`(Q\,n^a)^b(\neg Q\,n^0)^b(Q\,n^x)^{\max(b,x)}(\neg Q\,\log n)^b`$.

2.  *Rule 4 with any quantifiers*, i.e. the printed Corollary 2.11 with $`Q_{k+1},Q_{k+2}`$ read as arbitrary, and *rule 4 on a $`\mathsf{TS}`$ kernel* (through $`\mathsf{TS}\subseteq\mathsf{BPTS}`$): `rspeed` for either kernel type.

3.  *Lemma 2.7 with $`Q=\neg Q_k`$ under a block*, the deterministic speedup that opens a new block of the opposite type, which \[MW21\] set aside after Corollary 2.8 by \[W13, Lemma 3.2\]: it has the shape of `rspeed` on a $`\mathsf{TS}`$ kernel.

4.  *Speedup parameters at the end points* $`x=0`$ and $`x=a`$, any output exponents above the exact values, and any output exponent of rule 3’s blocks.

5.  *Input exponent $`0`$* instead of $`1`$ in front of the first block.

6.  *Weakening*: raising any exponent of an existing line, and $`\mathsf{TS}[n^a]\subseteq\mathsf{BPTS}[n^a]`$ (`MW.StepW`; Lemma 10 proves that $`\Phi`$ is monotone under it). The proof of \[MW21, Theorem 5.3\] uses such steps.

7.  *Non-strict refutations*, $`a'\le a_0`$, as in the wording of Definition 2.14.

Two things are outside both the formalisation and, as far as we can see, the source’s notion of proof:

- *Combining two adjacent blocks of the same type* as a separate step. Under the rules of \[MW21\] lines always alternate; non-alternating lines arise only from the same-type variant of item 1. Applied immediately, combining turns that variant into the merged rule 4; combining at a later time is not formalised, and $`\Phi`$ is not monotone under it.

- *Contradictions other than $`\mathsf{BPTS}[n^d]\subseteq\dots\subseteq\mathsf{BPTS}[n^{d'}]`$*, for example a line with quantifiers contained in a smaller line of the same shape via an alternating hierarchy theorem. Definition 2.14 and Lemma 5.2 of \[MW21\] use only the $`\mathsf{BPTS}\to\mathsf{BPTS}`$ form (Definition 2.14 also lists $`\mathsf{TS}\to\mathsf{TS}`$, which cannot occur in a proof whose slowdowns all produce $`\mathsf{BPTS}`$ kernels). Since $`\Phi`$ is homogeneous of degree 1 and never decreases, a path from a line $`L`$ to $`\lambda L`$ with $`\lambda<1`$ is impossible for $`c\ge\varphi`$; this is a paper argument, not checked in Lean, and the case of a target line that is smaller only in some coordinates is not analysed.

Rules at positions other than the innermost block are not rules of \[MW21\] and are not included.

## 7. Consequence for lower bounds

The proof of \[MW21, Theorem 5.3\] uses: Theorem 2.10 (quoted from \[DvM06\], with a proof sketch), Corollaries 2.8 and 2.11, Lemma 5.1, and Lemma 5.2.

**Corollary 11** (conditional). Assume that these lemmas of \[MW21\] hold as stated, and that each step of `MWL.Step` is an instance of them (the modelling claim of Section 2). Then $`\exists\cdot\mathsf{BPTIME}[n]\not\subseteq\mathsf{BPTS}[n^c]`$ for every $`c<\varphi`$, and hence $`\mathsf{MATIME}[n]\not\subseteq\mathsf{BPTS}[n^c]`$.

*Argument (not machine-checked).* For $`1\le c<\varphi`$ Theorem 3 gives a refutation; for $`c<1`$ use the refutation at $`c=1`$, since $`H_c`$ implies $`H_1`$. Read as a chain of inclusions under $`H_c`$, each step is an instance of Theorem 2.10/Corollary 2.11, Corollary 2.8 or Lemma 5.1, and Lemma 5.2 turns the chain into a contradiction. Three points specific to the construction: (i) Corollary 2.11 is applied repeatedly under the outer block $`(\exists\,n^0)^1`$, each time absorbing a new $`n^{o(1)}`$-bit guess into it; the number of applications is a constant for fixed $`c`$, so the block stays of size $`n^{o(1)}`$. \[MW21\] iterate under the same kind of block in the proof of their Theorem 5.4. (ii) The proof of Lemma 5.2 replaces the guess exponent $`0`$ of the first block by a small $`\varepsilon>0`$; in the construction that exponent enters only the final slowdown, whose cost $`c\max(e',1,\varepsilon,1)`$ is unchanged for $`\varepsilon<1`$. (iii) Lemma 5.2’s proof sets $`x'=x-(d-d')/2`$, which must be positive; if the refutation ends far below $`d`$ (as the 8/5 certificate does), first weaken the last line to $`\mathsf{BPTS}[n^{d''}]`$ with $`\max(d',d-2x)<d''<d`$ (Section 8). ∎

By $`\mathsf{MATIME}[t]\subseteq\mathsf{QCMATIME}[t]`$, which \[MW21, §1.3\] state, the same conditional bound holds for $`\mathsf{QCMATIME}[n]`$; \[MW21, Main Theorem 3\] gives $`1.5`$ for that class against $`\mathsf{BPTS}`$.

The published bound $`r_1`$ depends on Theorem 2.10 and Lemma 5.2 in the same way as Corollary 11. Lemma 5.2 rests on “a fine-grained version of the alternating time hierarchy theorem (proved by direct diagonalization)” for $`n^{o(1)}`$-space verifiers and quantifier blocks of $`n^0`$ and $`x\log n`$ type, which \[MW21\] do not prove in detail; the ITCS version defers the proof of Lemma 5.2 to the full version. If Lemma 5.2 needed further hypotheses, both bounds would have to be re-examined.

## 8. Two points in the source paper

We report two points in \[MW21\] that we checked against the arXiv text. Neither affects the statements of \[MW21\] or the results here.

**The parameters in the proof of Theorem 5.3.**

The proof sets $`x_1=d/c^3`$ and $`x_i=(c(1-\varepsilon))^{1-i}x_1`$ with $`\varepsilon=1/k`$. With these values the displayed chain does not hold as written. Consecutive parameters have ratio $`x_{i-1}/x_i=c(1-\varepsilon)<c`$. The chain removes the block of guess $`x_i`$ from a kernel $`cx_i`$ and then uses $`\mathsf{BPTS}[n^{c^2x_i}]\subseteq\mathsf{BPTS}[n^{cx_{i-1}}]`$; together these need $`cx_i\le x_{i-1}`$, which fails. Moreover, if $`c^2(c-1)<1`$ (the range of the theorem), then $`\sum_ix_i>d`$ for all large $`k`$, so the kernel exponent $`d-\sum_ix_i`$ of the first line is negative. With $`x_i=c^{k-i}T`$ and $`d=\sigma_kT`$ (the macro $`M(k)`$ of Lemma 6) the chain holds and gives exactly the stated condition in the limit. The script `scripts/mw_check.py thm53` checks both claims exactly: with the printed parameters, $`cx_i\le x_{i-1}`$ fails for every $`k`$ tried and the kernel is negative for $`c\in\{1.40,1.44,1.46\}`$ and $`k\ge5`$; with the corrected ones, the best ratio of final to initial exponent over $`k\le60`$ is $`0.998`$ at $`c=1.465`$ and $`1.0015`$ at $`c=1.466`$.

**The case $`x'\le0`$ in the proof of Lemma 5.2.**

The proof of Lemma 5.2 applies a speedup with parameter $`x'=x-(d-d')/2`$, where $`x`$ is the parameter of the first speedup. If $`d-d'\ge2x`$, then $`x'\le0`$ and the speedup is not defined. Weakening the end line first, $`\mathsf{BPTS}[n^{d'}]\subseteq\mathsf{BPTS}[n^{d''}]`$ with $`\max(d',d-2x)<d''<d`$, avoids this.

## 9. What is and is not verified

**(a) Kernel-checked.**

Lean 4.31 with Mathlib (pinned revision in the repository). The library builds with no `sorry`, no `admit`, no `native_decide` and no new axioms; `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for every headline theorem. The two concrete certificates are checked with `decide +kernel`, which adds no axiom. Checked are: the threshold of the *formal* calculus in both directions (Theorems 2, 3, 4, including the variants with the unmerged randomized speedup and with weakening); the simulation of the literal rules in the relaxed calculus (Lemma 8); monotonicity of the potential (Lemma 10); soundness of the executable checker; the 15-step refutation at $`c=1.467`$ and the bound $`r_1<1.467`$; and the 2687-step refutation at $`c=8/5`$.

**(b) Not machine-checked.**

- *That the formal rules coincide with the rules of \[MW21\].* This is a modelling claim, compared rule by rule in Table 1, with the reading points listed after it. The construction uses only `MWL.Step`, whose rules are the exact rules with equal or stricter side conditions. The limit side is proved for a relaxation (Section 6).

- *Soundness of the lemmas of \[MW21\]*: Theorem 2.10 (labelled a sketch there, quoting \[DvM06\]), Corollaries 2.8 and 2.11, Lemma 5.1 and Lemma 5.2. The published bound $`r_1`$ depends on them in the same way; in particular Lemma 5.2 is only sketched (Section 7). We do not formalise complexity classes.

- *Corollary 11* and the points (i)–(iii) in its argument.

- The paper arguments marked as such in Section 6 (contradictions of other forms) and the heuristic remark after the limit proof.

- The scripts in `scripts/` use exact rational arithmetic and are independent of the Lean code, but they are not part of the kernel-checked results.

**(c) Scope.**

The result is a limit on one proof calculus, the one of \[MW21, Definition 2.14 and §5\], with the variants listed in Section 6. Other speedup or slowdown rules (for instance Grover search, as in \[MW21, §4\]), other contradiction forms, and other proof methods are not covered. Nothing here bears on lower bounds for $`\exists\cdot\mathsf{BPTIME}`$ or $`\mathsf{MATIME}`$ proved by other methods.

## 10. Relation to earlier work

For SAT against deterministic $`n^{o(1)}`$-space algorithms, Fortnow and van Melkebeek \[FvM00, FLvMV05\] obtained $`\varphi`$; Williams later reached $`2\cos(\pi/7)`$, which Buss and Williams \[BW15\] proved optimal for alternation-trading proofs with those rules. For $`\mathsf{MATIME}`$ against randomized $`n^{o(1)}`$-space algorithms, Diehl and van Melkebeek \[DvM06\] and Diehl \[Die07\] obtained $`\sqrt2`$, and Mudigonda and Williams \[MW21\] obtained $`r_1\approx1.4656`$. Iterating the macro $`M(1)`$ reproduces $`\sqrt2`$, using $`M(k)`$ once reproduces $`r_1`$ as $`k\to\infty`$, and iterating $`M(k)`$ gives every $`c<\varphi`$; $`\varphi`$ is the exact threshold of the calculus.

## Licence

This text is licensed under CC BY 4.0. The Lean code and the scripts are licensed under the Apache License 2.0.

## References

- \[BW15\] S. R. Buss and R. Williams. Limits on alternation trading proofs for time–space lower bounds. *Computational Complexity*, 24(3):533–600, 2015. [doi:10.1007/s00037-015-0104-9](https://doi.org/10.1007/s00037-015-0104-9).
- \[Die07\] S. Diehl. Lower bounds for swapping Arthur and Merlin. In *Approximation, Randomization, and Combinatorial Optimization (APPROX-RANDOM 2007)*, *Lecture Notes in Computer Science*, pages 449–463. Springer, 2007.
- \[DvM06\] S. Diehl and D. van Melkebeek. Time-space lower bounds for the polynomial-time hierarchy on randomized machines. *SIAM Journal on Computing*, 36(3):563–594, 2006. [doi:10.1137/050642228](https://doi.org/10.1137/050642228).
- \[FLvMV05\] L. Fortnow, R. Lipton, D. van Melkebeek, and A. Viglas. Time-space lower bounds for satisfiability. *Journal of the ACM*, 52(6):835–865, 2005. [doi:10.1145/1101821.1101822](https://doi.org/10.1145/1101821.1101822).
- \[FvM00\] L. Fortnow and D. van Melkebeek. Time-space tradeoffs for nondeterministic computation. In *Proceedings of the 15th Annual IEEE Conference on Computational Complexity (CCC 2000)*, pages 2–13, 2000. [doi:10.1109/CCC.2000.856730](https://doi.org/10.1109/CCC.2000.856730).
- \[MW21\] A. S. Mudigonda and R. R. Williams. Time-space lower bounds for simulating proof systems with quantum and randomized verifiers. In *12th Innovations in Theoretical Computer Science Conference (ITCS 2021)*, volume 185 of *LIPIcs*, pages 50:1–50:20, 2021. [doi:10.4230/LIPIcs.ITCS.2021.50](https://doi.org/10.4230/LIPIcs.ITCS.2021.50). Full version: [arXiv:2012.00330](https://arxiv.org/abs/2012.00330) (v2, January 2021), whose numbering we use.
- \[W13\] R. Williams. Alternation-trading proofs, linear programming, and lower bounds. *ACM Transactions on Computation Theory*, 5(2):Article 6, 1–49, 2013. [doi:10.1145/2493246.2493249](https://doi.org/10.1145/2493246.2493249).

[^1]: In the ITCS version: Definition 2.14 is Definition 12, Lemma 2.7 is Lemma 4, Corollary 2.8 is Corollary 5, Theorem 2.10 is Theorem 7, Corollary 2.11 is Corollary 8, Lemma 2.17 is Lemma 15, Lemmas 5.1 and 5.2 are Lemmas 33 and 34, Theorems 5.3 and 5.4 are Theorems 35 and 36.
