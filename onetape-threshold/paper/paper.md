# Williams's alternation-trading calculus for SAT on d-dimensional one-tape machines, as formalised: the optimality conjecture fails, and the threshold lies in a short interval

**PastaPastaPasta** · November 2026

*Markdown rendering of `paper.tex`, which is the reference version.*

## Abstract

Williams \[W13, §7\] sets up a calculus of alternation-trading proofs for lower bounds against machines with random-access input, $`n^{o(1)}`$ bits of random-access storage and one $`d`$-dimensional sequential work tape. His Theorem 7.5 proves that SAT is not solvable in time $`n^c`$ on such machines for every $`c<r_d`$, where $`r_d`$ is a root of a quintic ($`r_1\approx1.30094`$, $`r_2\approx1.18879`$, $`r_3\approx1.13728`$). He conjectures that $`r_d`$ is optimal for alternation-trading proofs, and proves (in a sketch, Theorem 7.9) that no proof in the calculus reaches $`c\ge1+1/(d+1)`$.

We study a Lean 4 formalisation of this calculus. For $`d=1,2,3`$ it has normal-form proofs at $`c=1.30921174`$, $`1.1915968`$ and $`1.1386523`$, all above $`r_d`$, so the conjecture fails for the formalised calculus. These proofs also satisfy a stricter reading of the speedup lemma (kernel time at least the input length, and space at most time, on every line). Conversely, for every $`c\ge1.3094`$, $`1.192`$ and $`1.1392`$ respectively there is no normal-form proof from any starting exponent $`a_0>0`$, strict or not, even in a relaxed calculus that contains every move of Williams’s calculus as we read it, and also when the sound inclusion $`\mathsf{DTIME}_d[t]\subseteq\mathsf{DTISP}[t,t]`$ is added (Williams’s Lemma 3.4, in the forms that follow from the hypothesis, is Lemma 7.2 followed by this inclusion). So the threshold of the formalised calculus lies in $`[1.30921174,\,1.3094]`$, $`[1.1915968,\,1.192]`$ and $`[1.1386523,\,1.1392]`$. Two reading choices matter for these ceilings (Section 2.4). First, we give the new $`\log n`$ block of Lemma 3.3 inside a prefix the output superscript $`\max(b,e)`$ that the proof of Lemma 3.3 gives there, while three displays in Williams’s sketch of Theorem 7.9 show a smaller one ($`1`$, or $`\max\{b,1\}`$). The ceilings are proved for our reading only; under the displayed one we prove only the ceiling $`c^2\ge1+1/d`$ for strict normal-form proofs (for $`d\ge1`$). The proofs at the three lower values exist under both readings: the staircase proofs are kernel-checked also in the calculus in which that superscript is exactly $`1`$. Second, the output of Lemma 7.2 is always a $`\mathsf{DTIME}_d`$ class, while one slowdown in the prose proof of Williams’s Theorem 7.5 keeps a $`\mathsf{DTISP}`$ kernel whose space is below its time; we know no derivation of that line from the hypothesis, and the ceilings do not cover it. The constructions are shared-subproof certificates checked by a verified checker; the impossibility results are multi-level potential functions whose Lemma 7.1 condition is checked for all words at once by a finite abstraction. The exact threshold is open. A recursion read off from the best proofs found has a boundary between refuting and stopping that we estimate numerically as $`c^{*}_{\mathrm{stair}}(1)\approx1.3092117446776`$; that this is the threshold of the calculus is a conjecture, supported by numerics only.

*What is kernel-checked:* the existence of the proofs at the three lower values (for the staircase proofs also when the new $`\log n`$ block has output exactly $`1`$), the absence of proofs from any $`a_0>0`$ at and above the three upper values (also with the inclusion added), and the simpler ceiling $`c^2\ge1+1/d`$ for strict normal-form proofs (for $`d\ge1`$ also with the inclusion and with any superscript of the new $`\log n`$ block), all for the formal calculus. *What is not:* that the formal rules are Williams’s (a modelling claim, compared rule by rule in Table 2 with the reading choices listed in Section 2.4), and the soundness of Williams’s lemmas. The complexity consequence, $`\mathsf{SAT}\notin\mathsf{DTIME}_d[n^c]`$ for every $`c<1.30921174`$, $`1.1915968`$, $`1.1386523`$, holds exactly as far as Williams’s Lemmas 7.1, 7.2, 7.3, his Lemma 3.3 used inside a prefix, and Theorem 3.1 do. These are the results his Theorem 7.5 rests on, and they are not formalised here. All statements concern one proof calculus.

## 1. Introduction

**Background.**

Alternation-trading proofs derive a contradiction from a hypothesis such as $`H_c`$: $`\mathsf{NTIME}[n]\subseteq\mathsf{DTIME}_d[n^c]`$ by alternately applying *speedup* rules, which add quantifier blocks to a class and reduce its running time, and *slowdown* rules, which use the hypothesis to remove a block at the cost of a factor $`c`$ in the exponent, until a time hierarchy is contradicted. Williams \[W13\] formalises such proofs for three settings and studies them by linear programming. Its §7 treats the “hybrid” model: $`\mathsf{DTIME}_d[t]`$ is the class of languages recognised in time $`O(t)`$ by a machine with a read-only random-access input tape, $`n^{o(1)}`$ bits of read-write random-access storage, and one $`d`$-dimensional read-write tape with sequential access \[W13, p. A:29\]. The speedups are Lemma 7.1 (from $`\mathsf{DTIME}_d`$ to $`\mathsf{DTISP}`$, by guessing crossing sequences) and the $`\mathsf{DTISP}`$ speedup Lemma 3.3; the slowdown is Lemma 7.2.

Theorem 7.5 of \[W13\] gives $`\mathsf{SAT}\notin\mathsf{DTIME}_d[n^c]`$ for $`c<r_d`$, where $`r_d\ge1`$ is a root of
``` math
p_d(x)=(2d+1)(d+1)^2x^5-2(d+1)(2d+1)x^4-d^2x^3+2(d+1)x^2-((2d+1)(d+1)^2+1)x+d(d+1).
```
Numerically $`r_1=1.3009428844`$, $`r_2=1.1887894930`$, $`r_3=1.1372807069`$ (script `staircase.py roots`). After the proof, \[W13, p. A:35\] writes: “We again conjecture that the above lower bound is optimal for alternation-trading proofs”, and Theorem 7.9 (stated on p. A:35, proof sketch on pp. A:36–A:38) says that no alternation-trading proof gives $`c\ge1+1/(d+1)`$. The long version \[Wfull\] treats $`d=1`$ and says “we feel safe in conjecturing that our above theorem is optimal for alternation-trading proofs”.

Page and result numbers refer to the TOCT author copy of \[W13\]. Our own results are numbered $`1,2,3,\dots`$ Every theorem below is a statement about the formal calculus, proved by the Lean theorems named with it; names refer to the accompanying Lean library (namespace `PastaMath.OneTapeThreshold`). The conditional complexity consequence, Corollary 15, is a paper argument.

**Results.**

- **Proofs above $`r_d`$** (Theorem 2; `conjecture_fails`, `HStair.stairD{1,2,3}_snf`). The formal calculus `HY.Step` has strict normal-form proofs at $`c=1.30921174`$ ($`d=1`$), $`1.1915968`$ ($`d=2`$) and $`1.1386523`$ ($`d=3`$). Each has kernel time $`\ge`$ input superscript and space $`\le`$ time on every line. Every real root of $`p_d`$ is below the respective $`c`$. The same certificates give such proofs in the variant in which the new $`\log n`$ block of Lemma 3.3 has output exactly $`1`$ (`conjecture_fails_one`). A 39-line proof at $`c=1.30095>r_1`$ is checked separately (Theorem 3).

- **Ceilings** (Theorem 4; `HLM.ceiling_d{1,2,3}`, `HLM.ceilingX_d{1,2,3}`). For every real $`c\ge1.3094`$, $`1.192`$, $`1.1392`$ respectively there is no normal-form proof from any starting exponent $`a_0>0`$, strict or non-strict, in `HY.Step` or in the relaxed calculus `HL.RStep` of Section 5.1, and none when the inclusion $`\mathsf{DTIME}_d[t]\subseteq\mathsf{DTISP}[t,t]`$ is added to either. This is for our reading of the output superscript of the new $`\log n`$ block of Lemma 3.3 (item 3 of Section 2.4); for the smaller superscript displayed in Williams’s sketch of Theorem 7.9 these ceilings are not established.

- **A closed-form ceiling** (Theorem 5; `HL.no_nf`, `HL.no_drop_W`). For every real $`d>0`$ and $`c\ge1`$ with $`c^2\ge1+1/d`$ there is no strict normal-form proof. For $`d\ge1`$ this also holds with the inclusion added and with any output superscript $`\ge0`$ for the new $`\log n`$ block of Lemma 3.3, so it holds under the displayed reading too; there it excludes $`a'<a_0`$, not a path with $`a'=a_0`$. Since $`\sqrt{1+1/d}<1+1/(d+1)`$ for $`d\ge1`$, this improves the bound of \[W13, Theorem 7.9\] for the formal calculus for every $`d\ge1`$.

- **The threshold** (Corollary 6; `threshold_bounds`). The supremum $`c^*_d`$ of the $`c`$ with a strict normal-form proof satisfies $`c^*_1\in[1.30921174,1.3094]`$, $`c^*_2\in[1.1915968,1.192]`$, $`c^*_3\in[1.1386523,1.1392]`$. The exact values are open (Section 7).

| $`d`$ | $`r_d`$ | proof at | no proof for $`c\ge`$ | $`\sqrt{1+1/d}`$ | $`1+\frac1{d+1}`$ | $`c^{*}_{\mathrm{stair}}(d)`$ |
|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| 1 | 1.3009429 | 1.30921174 | 1.3094 | 1.4142 | 1.5 | 1.30921174468 |
| 2 | 1.1887895 | 1.1915968 | 1.192 | 1.2247 | 1.3333 | 1.19159683545 |
| 3 | 1.1372807 | 1.1386523 | 1.1392 | 1.1547 | 1.25 | 1.13865239000 |

*Table 1: Exponents for the formal calculus. Column 2 is the exponent of \[W13, Theorem 7.5\]; columns 3 and 4 are Theorems 2 and 4 (column 4: no normal-form proof from any starting exponent $`a_0>0`$, for our reading of the $`\log n`$ superscript), column 5 is Theorem 5 (strict normal-form proofs; all kernel-checked); column 6 is \[W13, Theorem 7.9\]; the last column is a numerical estimate of the boundary of the staircase recursion, conjectured to be the threshold (Section 7; not proved). Columns 2 and 7 come from `scripts/staircase.py`.*

**Where the improvement comes from.**

The proofs of \[W13, Theorem 7.5\] have annotations $`[1\,(1\,1\,0)^k\,0\,(1\,1\,0)^\ell\,0]`$ (1 a speedup, 0 a slowdown): under an outer $`\exists`$ block they make one excursion to a $`\forall`$ level, where simple rounds run (the inner pattern of Lemma 7.7 and Corollary 7.8 of \[W13\]), return to the $`\exists`$ level for further simple rounds, and remove the $`\exists`$ block. The 39-line proof of Section 4.1 makes a second excursion under the same $`\exists`$ block: the first new block of the second excursion merges into the $`\exists`$ block, so it costs no alternation. Its annotation has three occurrences of $`0\,0`$; \[W13, §7.2\] reports that a heuristic search for annotations with three occurrences found none better. Iterating the idea gives proofs whose level structure is a staircase (Section 4.4). Every step of every proof is an application of Lemma 7.1, Lemma 3.3 or Lemma 7.2 of the kinds that occur in the 25-line proof printed in \[W13, §7.2\]: Lemma 7.1 opening the first block on the first line (`convNew` from the empty prefix) and merged into an existing block afterwards (`convMerge`), Lemma 3.3 merged into the innermost block inside a prefix (`speedMerge`), and Lemma 7.2 under a prefix with input superscript at least 1 and, on the last line, under the empty prefix. This is a fact about how the proofs are built (the 39-line tag list, and the soundness proofs of the DAG checkers, use only these four constructors), not part of the statements of Theorems 2 and 3, which assert the existence of `HY.Step` proofs. The proofs are much longer: at most $`7.62\cdot10^{21}`$ lines when unfolded ($`d=1`$), a constant independent of $`n`$.

**Scope.**

All results concern one proof calculus. The complexity reading needs the soundness of Williams’s lemmas, which we do not formalise (Section 8); it rests on the same lemmas as \[W13, Theorem 7.5\]. The ceilings say nothing about lower bounds proved by other means.

**Novelty.**

We are not aware of an improvement of the exponents $`r_d`$ after \[W13\], of a resolution of its §7 conjecture, or of a limit for this calculus below $`1+1/(d+1)`$. Our search was not exhaustive.

**AI assistance.**

The proofs, the formalisation and the scripts were produced with Anthropic’s Claude models under the author’s direction. The kernel-checked Lean proofs are the primary evidence for the theorems about the formal calculus; this text explains them and states what they do and do not establish.

## 2. The calculus as formalised

### 2.1 Lines

A *line* is a class $`(Q_1\,n^{g_1})^{o_1}\cdots(Q_m\,n^{g_m})^{o_m}\,K`$ with $`Q_i\in\{\exists,\forall\}`$ and kernel $`K=\mathsf{DTIME}_d[n^a]`$ or $`K=\mathsf{DTISP}[n^a,n^e]`$ \[W13, §2, §7.1\]. Here $`g_i`$ is the guess exponent of block $`i`$ (with $`0`$ standing for a $`\log n`$ block) and $`o_i`$ is its output superscript: block $`i`$ passes $`n^{o_i+o(1)}`$ bits to the next stage (Williams’s $`b_{i+1}`$). The *input superscript* of the kernel, $`b=\mathrm{pin}`$, is $`o_m`$, or $`1`$ if $`m=0`$. In Lean (`HY.Line`) a line is a block list, innermost block first, and a kernel `T a` or `S a e`; `HY.pin` is the input superscript and `HY.Alt` says adjacent blocks have different quantifiers. Exponents are real numbers.

### 2.2 Rules

Table 2 lists Williams’s rules and their formal versions. In each rule $`b`$ is the input superscript of the line it is applied to, and $`c`$ the exponent of the hypothesis $`H_c`$.

| Williams | statement as formalised (exact outputs) | `HY.Step` | `HL.RStep` |
|:---|:---|:---|:---|
| Lemma 7.1 (p. A:29) | $`Q^b\mathsf{DTIME}_d[n^a]\subseteq{}`$ $`Q^b(Q'\,n^{a-s})^{\max(a-s,b)}\mathsf{DTISP}[n^a,n^{ds}]`$, $`0<s\le a`$, $`b\ge1`$; $`Q'`$ is merged into the innermost block when it has the same type (§2, p. A:5), giving guess $`\max(g,a-s)`$ and output $`\max(a-s,o)`$ | `convMerge`; `convNew` (new block of the other type, or the first block) | `convM`, `convN` |
| Lemma 3.3 (p. A:6) inside a prefix, Speedup Rule 1 (p. A:9) | $`(Q\,n^g)^o\mathsf{DTISP}[n^a,n^e]\subseteq{}`$ $`(Q\,n^{\max(g,x+e)})^{\max(o,x+e)}`$ $`(\bar Q\log n)^{\max(o,e)}`$ $`\mathsf{DTISP}[n^{a-x},n^e]`$, $`a\ge1`$, $`0\le e\le a-x`$, $`0\le x\le a-1`$, $`o\ge1`$ (the superscript $`\max(o,e)`$: item 3 of Section 2.4) | `speedMerge` | `speedM` |
| Speedup Rule 2 (p. A:9; unnecessary by p. A:31) | two new blocks $`(Q\,n^{x+e})^{\max(b,x+e)}(\bar Q\log n)^{\max(b,e)}`$, $`Q`$ opposite to the innermost block, same side conditions | `speedNew` | `speedN` |
| Lemma 7.2 (p. A:30) | $`Q^{b_k}(Q'\,n^{a_k})^{b_{k+1}}K[n^{a_{k+1}}]\subseteq{}`$ $`Q^{b_k}\mathsf{DTIME}_d[n^{c\max(b_k,b_{k+1},a_k,a_{k+1})}]`$ for $`K=\mathsf{DTIME}_d`$ or $`\mathsf{DTISP}`$; $`b_k,b_{k+1},a_{k+1}\ge1`$, $`a_k\ge0`$ | `slow` | `slow` |
| Normal form (p. A:31), Lemma 7.3, Thm. 7.4 | $`\mathsf{DTIME}_d[n^a]\subseteq\cdots\subseteq{}`$ $`\mathsf{DTIME}_d[n^{a'}]`$ | `HY.NF` (strict, $`1\le a'<a`$) | Thm. 4(2) |

*Table 2: Williams’s rules \[W13\] and the formal rules. `HY.Step` is defined in `Calculus.lean`, `HL.RStep` in `Relaxed.lean` (Section 5.1).*

Precisely, `HY.Step c d` has the constructors

- `convMerge u rest a s`: from $`(u::\mathit{rest},\ \texttt{T}\,a)`$ with $`0<s\le a`$, $`1\le u.o`$, to $`(\langle u.q,\max(u.g,a-s),\max(a-s,u.o)\rangle::\mathit{rest},\ \texttt{S}\,a\,(ds))`$;

- `convNew bl q a s`: if the innermost block of $`\mathit{bl}`$ (if any) has quantifier $`\ne q`$, $`0<s\le a`$ and $`1\le\mathrm{pin}(\mathit{bl})`$, from $`(\mathit{bl},\texttt{T}\,a)`$ to $`(\langle q,a-s,\max(a-s,\mathrm{pin}\,\mathit{bl})\rangle::\mathit{bl},\ \texttt{S}\,a\,(ds))`$;

- `speedMerge u rest a e x`: if $`1\le a`$, $`0\le e\le a-x`$, $`0\le x\le a-1`$ and $`1\le u.o`$, from $`(u::\mathit{rest},\texttt{S}\,a\,e)`$ to $`(\langle\overline{u.q},0,\max(u.o,e)\rangle::\langle u.q,\max(u.g,x+e),\max(u.o,x+e)\rangle::\mathit{rest},\ \texttt{S}\,(a-x)\,e)`$;

- `speedNew bl q a e x`: if the innermost block of $`\mathit{bl}`$ (if any) has quantifier $`\ne q`$, the same conditions on $`a,e,x`$ hold and $`1\le\mathrm{pin}\,\mathit{bl}`$, from $`(\mathit{bl},\texttt{S}\,a\,e)`$ to $`(\langle\bar q,0,\max(\mathrm{pin}\,\mathit{bl},e)\rangle::\langle q,x+e,\max(\mathrm{pin}\,\mathit{bl},x+e)\rangle::\mathit{bl},\ \texttt{S}\,(a-x)\,e)`$;

- `slow u rest k`: if $`1\le\mathrm{pin}\,\mathit{rest}`$, $`1\le u.o`$, $`1\le\mathrm{time}(k)`$ and $`0\le u.g`$, from $`(u::\mathit{rest},k)`$ to $`(\mathit{rest},\ \texttt{T}\,(c\max(\mathrm{pin}\,\mathit{rest},u.o,u.g,\mathrm{time}(k))))`$.

### 2.3 Normal form

**Definition 1** (`HY.NF c d M n`). A *strict normal-form proof* at $`c`$ in dimension $`d`$ is a list of lines $`M_0,\dots,M_n`$ with $`n\ge1`$, each obtained from the previous one by a `HY.Step c d`, such that $`M_0=\mathsf{DTIME}_d[n^a]`$ and $`M_n=\mathsf{DTIME}_d[n^{a'}]`$ have no blocks, no line strictly between them has an empty block list, $`1\le a'<a`$, and every line alternates.

\[W13, p. A:31\] defines normal-form proofs by their first and last lines, $`\mathsf{DTIME}_d[n^a]`$ and $`\mathsf{DTIME}_d[n^{a'}]`$ with $`a'\le a`$; the condition that no other line is quantifier-free is the analogue of \[W13, Definition 4.2(b)\]. Lemma 7.3 gives a contradiction from such a proof when $`a>a'\ge1`$, and Theorem 7.4 (proof sketched as “closely follows” Theorems 4.4 and 6.6) turns any alternation-trading proof $`A_1\subseteq A_2`$ between complementary simple classes into a normal-form proof. Our constructions are strict ($`a'<a`$). Our ceilings exclude $`a'\le a`$, and do not need the condition on intermediate lines (Theorem 4).

### 2.4 Modelling and reading choices

The following choices are ours or are readings of \[W13\] on which a reader may differ.

1.  *$`n^{o(1)}`$ and polylogarithmic factors are dropped*; a line records exponents only, and a $`\log n`$ block has guess exponent $`0`$. This is the convention of \[W13, §4, p. A:9\] (“Polylogarithmic and $`n^{o(1)}`$ factors do not affect any of the elements in these proofs”).

2.  *Merging.* When the new block of Lemma 7.1, or the first new block of Lemma 3.3, has the same quantifier as the innermost block, the two are combined by \[W13, §2\]: $`(\exists n^a)^a(\exists n^b)^b=(\exists n^{\max(a,b)})^b`$, so the guess exponent is the maximum and the output superscript is the new block’s. Williams’s proofs do this throughout; the sketch of Theorem 7.9 says “the first 1 in a run …does not add a new quantifier if the class already has quantifiers” (p. A:37). A new block of the opposite type is `convNew`; `HY.Step` has no unmerged same-type block (the relaxed calculus does not track quantifiers, so it covers that case).

3.  *Lemma 3.3 inside a prefix.* Lemma 3.3 is stated for a quantifier-free $`\mathsf{DTISP}`$ class with outputs $`\max\{1,x+e\}`$ and $`\max\{1,e\}`$; inside a prefix whose kernel has input superscript $`b`$ we use $`\max\{b,x+e\}`$ and $`\max\{b,e\}`$, as Speedup Rule 1 of \[W13, Definition 4.1\] does for $`\mathsf{DTS}`$. Williams’s printed 25-line proof replays under this reading, but equally under the smaller one below, so it does not support ours over it (Section 2.5). The side conditions are those printed in Lemma 3.3: $`a\ge1`$, $`0\le e\le a-x`$, $`0\le x\le a-1`$. We call this the *literal* reading. Since the kernel reads an input of length $`n^{b}`$, one may also require that its time stays at least its input length, i.e. kernel time $`\ge\mathrm{pin}`$ after every step; we call this, together with space $`\le`$ time on every $`\mathsf{DTISP}`$ line (item 5), the *strict* reading. Theorem 2 holds under both.

    *Conflicting displays.* Three displays in the sketch of Theorem 7.9 give the new $`\log n`$ block a smaller output superscript. In the derivation for the annotation $`[1,1,0,0]`$ (p. A:36) and in Case 2 (p. A:38) it is $`(\forall n^0)^1`$. In Case 1 (p. A:37), from a line $`Q^b(Q_1n^{a'})^{b'}\mathsf{DTISP}[n^a,n^e]`$, it is $`(Q_2n^0)^{\max\{b,1\}}`$ and then $`(Q_3n^0)^{\max\{b,1\}}`$, below our $`\max(b',e)`$ whenever $`e>b'`$ (as after Lemma 7.1 with large $`s`$; in our proofs $`b\le b'`$). For example, with $`d=1`$, start $`\mathsf{DTIME}_1[n^4]`$, Lemma 7.1 with $`s=1`$ and Lemma 3.3 with $`x=1`$: after Lemma 7.1 the line is $`(\exists n^3)^3\mathsf{DTISP}[n^4,n^1]`$; the displays of pp. A:36 and A:38 give the new block the output $`1`$, while `HY.Step` gives $`\max(3,1)=3`$ and `HL.RStep` requires at least $`3`$. The proof of Theorem 7.5 (p. A:34) also displays $`(\forall\log n)^1`$ and $`(\exists\log n)^1`$; there the enclosing block has output $`1`$ and $`e=d(a-1)`$, and the assumption $`1-d(a-1)\ge0`$ made a few lines later gives $`\max(b,e)=1`$, so that display agrees with ours. We formalise $`\max(b,e)`$ because (i) the proof of Lemma 3.3 gives it inside a prefix: the new kernel simulates the old one between two guessed configurations, so it still reads the old kernel’s input of $`n^{b}`$ bits, and each stage passes on only the bits its superscript allows (p. A:29), together with the two configurations of $`n^{e}`$ bits; (ii) it is the output of Speedup Rule 1 of Definition 4.1 ($`b_{k+1}`$, for $`\mathsf{DTS}`$ kernels), which applies here by p. A:31; and (iii) no displayed exponent depends on the choice: in the first two displays the $`\log n`$ block is removed by Lemma 7.2 on the next line, whose maximum contains the output of the block outside it, which is $`\ge\max(b,e)`$; in Case 1 the same holds for $`Q_3`$, and $`Q_2`$ is first merged into by a second Lemma 3.3 step whose term $`y+e\ge e`$ is in the displayed superscript (once $`b`$ is identified with $`b'`$, as the display of $`Q_1`$’s output $`\max\{b,x+e\}`$ there does). We know of no derivation of the smaller superscript from Williams’s lemmas. Under the displayed reading:

    - the existence results stand as proofs of lower bounds: every step of our proofs uses the larger superscript, which Lemma 3.3 supports, and since raising an output superscript can only enlarge a class, the line with the smaller superscript is contained in ours. A derivation that writes $`\max(b,e)`$ is not literally a derivation in a calculus whose exact output is $`1`$; for the staircase proofs this is closed in Lean: the soundness proofs of both DAG checkers hold for every output $`\ell(o,e)`$ of the new $`\log n`$ block with $`1\le\ell(o,e)\le\max(o,e)`$, so the same certificate checks give strict normal-form proofs, with kernel time $`\ge`$ input superscript and space $`\le`$ time on every line, in the calculus `HY.StepO (fun _ _ => 1)` in which that output is exactly $`1`$ (Theorem 2, `conjecture_fails_one`). For the 39-line proof only a script check is done: it replays with output exactly $`1`$, with every side condition and the strict reading, and with the same kernels and final exponent (`replay39.py --log-one`). The output $`\max\{b,1\}`$ of Case 1 depends on the superscript of an outer block and is not of the form $`\ell(o,e)`$; a calculus with that exact output is not checked;

    - the closed-form ceiling holds for strict normal-form proofs (Theorem 5(2), `HL.no_drop_W`, for $`d\ge1`$): the one-level potential does not depend on the new block’s superscript. It gives $`a_0\le a'`$, so a path with $`a'=a_0`$ is not excluded;

    - the ceilings of Theorem 4 are *not* established. The multi-level potentials use that superscript (the term $`\theta_p\mathrm{Ad}(w)\max(b,e)`$ of $`V_{p::w}`$ in Section 5.3), and a smaller superscript lets the levels opened inside the new block close more cheaply. We do not know whether proofs at or above $`1.3094`$, $`1.192`$, $`1.1392`$ exist under that reading.

4.  *Speedup Rule 2* (two new blocks) is included as `speedNew`, and Lemma 7.1 may open a block of the opposite type anywhere (`convNew`). \[W13, p. A:31\] says Rule 2 can be shown unnecessary. None of our proofs uses either move except `convNew` on the first line; the ceilings allow both.

5.  *Lemma 7.2.* TOCT states it “for $`a_i,b_i\ge1`$, and all $`e\ge0`$”. We allow guess exponent $`a_k\ge0`$, because Williams’s proofs slow down $`\log n`$ blocks (e.g. lines 3–4 of the 25-line proof). This changes no value, since $`b_{k+1}\ge1`$ is in the same maximum. The long version \[Wfull, Lemma 5.2\] requires $`e\le a_{k+1}`$ for a $`\mathsf{DTISP}`$ kernel; `HY.Step` does not, and the strict-reading proofs satisfy it on every line.

6.  *The output of Lemma 7.2 is always $`\mathsf{DTIME}_d`$.* The sketch of Theorem 7.9 says “After a slowdown, the deterministic portion of a class is $`\mathsf{DTIME}_d`$” (p. A:36). The prose proof of Theorem 7.5 writes $`(\exists n^{x+d(a-1)})(\forall n)\mathsf{DTISP}[n^c,n^{d/(d+1)}]`$ after a slowdown (p. A:34), and its next step uses this line as time $`n^c`$; we read it as $`\mathsf{DTIME}_d[n^c]`$. Literally, that line keeps a $`\mathsf{DTISP}`$ kernel with space $`n^{d/(d+1)}`$ below its time $`n^c`$. It would follow from Lemma 3.4 with $`e=d/(d+1)<c`$, which needs $`\mathsf{NTIME}[n]\subseteq\mathsf{DTISP}[n^c,n^{d/(d+1)}]`$, and we know no derivation of that from $`H_c`$ (item 7). It is not the inclusion $`\mathsf{DTIME}_d[t]\subseteq\mathsf{DTISP}[t,t]`$, it is not covered by `HL.Widen` (which needs space at least the time $`c`$), and `HL.RStep` has no slowdown to a $`\mathsf{DTISP}`$ kernel. So the ceilings of Theorems 4 and 5 assume this reading: a slowdown that keeps a $`\mathsf{DTISP}`$ kernel with space below its time is outside what they cover. For Theorem 7.5 the choice is immaterial, since its next step uses only the time.

7.  *Lemma 3.4 for $`\mathsf{DTISP}`$ kernels.* \[W13, p. A:31\] lists “Slowdown via Lemma 3.4 when $`C`$ is a DTISP class” among the rules. Lemma 3.4 assumes $`\mathsf{NTIME}[n]\subseteq\mathsf{DTISP}[n^{c'},n^e]`$ (Williams writes $`c`$ for $`c'`$). From $`H_c`$ this follows for every $`c'\ge c`$ and $`e\ge c`$, the best case being $`c'=e=c`$, since $`\mathsf{DTIME}_d[t]\subseteq\mathsf{DTISP}[t,t]`$ (a machine running $`t`$ steps visits at most $`t`$ cells); for $`e<c`$ it follows by no argument we know. `HY.Step` takes the slowdown of a $`\mathsf{DTISP}`$ kernel to be the second inclusion of Lemma 7.2, as Williams’s proofs do. Lemma 3.4 with $`c'\ge c`$ and $`e\ge c`$ gives the line of Lemma 7.2 followed by a weakened inclusion $`\mathsf{DTIME}_d[n^t]\subseteq\mathsf{DTISP}[n^{t_2},n^{e_2}]`$ with $`t_2,e_2\ge t`$ (time $`c'm`$ and space $`em`$, both at least the time $`cm`$ of Lemma 7.2, $`m`$ its maximum); with $`c'=e=c`$ it is Lemma 7.2 followed by $`\mathsf{DTIME}_d[t]\subseteq\mathsf{DTISP}[t,t]`$. These inclusions are not rules of `HY.Step`, but the ceilings cover them: Theorem 4(4) the weakened ones (`HL.Widen`), Theorem 4(5) and Theorem 5(2) the exact one (Section 6).

8.  *Normal form*: strict for the constructions, $`a'\le a`$ for the ceilings (Definition 1 and the remark after it).

9.  *No weakening rule* in `HY.Step`: every output is the exact one. The relaxed calculus bounds outputs only from below.

10. *Starting exponent and length.* The starting exponent $`a`$ is free, as in Williams’s linear programs, and so is the length of the proof. Our certificates start at large exponents (about $`1.4\cdot10^{17}`$ for $`d=1`$; Section 4.4), which keeps every $`\ge1`$ floor slack except two: the first conversion (`convNew` from the empty prefix) and the final slowdown use the input superscript $`1`$ of the empty prefix, so their conditions $`1\le\mathrm{pin}`$ hold with equality. They unfold to very long proofs. Lemma 7.3 and Theorem 7.4 put no bound on either.

### 2.5 Calibration

The script `w13_25line.py` replays the 25-line proof printed in \[W13, §7.2\] (pp. A:32–A:33) under the rules of `HY.Step`, at $`c=1.297844`$ (the value implied by its lines 9 and 10). It infers each rule from the shape of the next line and its parameter from the printed numbers, carries the output superscripts itself (they are not printed), and compares every printed number: the kernel exponents (time, and space on $`\mathsf{DTISP}`$ lines) directly, and the guess exponent of every block as $`\max(\text{guess},1)`$, since the display prints every guess below 1 as $`n^1`$ (the $`\log n`$ blocks, and the first block, whose computed guess is $`0.999997582`$). Output superscripts are not compared, since none is printed. Every step is a rule of the formal calculus with its side conditions, and every printed number is reproduced to within $`1.1\cdot10^{-8}`$ (largest deviation $`1.02\cdot10^{-8}`$ for kernel exponents, $`5.6\cdot10^{-9}`$ for guesses; the printed numbers have 9–10 significant digits). So the annotation is legal under our reading and the replay reproduces the printed kernel exponents and block guesses.

The replay does not support our reading of the $`\log n`$ superscript over the smaller one. Run with output exactly $`1`$ for the new $`\log n`$ block, it passes the same checks with the same deviations. Nor does it reproduce the implicit superscripts under Williams’s default: an omitted superscript is $`\max\{a_i,1\}`$ for a block of guess exponent $`a_i`$ (§2, p. A:5), which on the usual block-wise reading is $`1`$ for a $`\log n`$ block, whereas our replay gives the $`\log n`$ blocks of lines 13, 16, 19 and 22 (e.g. the final $`(\forall n^{1.})`$ of line 13) the output $`\approx1.04010891`$, inherited from the enclosing existential block. The next step removes each of them by Lemma 7.2, whose maximum contains that block’s output, so the difference does not reach any printed number. These are the only carried superscripts that differ from the default by more than $`10^{-7}`$. Read with the default, the display thus gives these blocks the smaller superscript, which is further evidence that Williams uses the smaller output (item 3 of Section 2.4).

This is a replay of Williams’s rounded display, not a verified proof: from the printed start $`1.751958454`$ at $`c=1.297844`$ the computed last line is $`1.7519584642`$, about $`1.0\cdot10^{-8}`$ *above* the first, so the normal-form condition $`a'<a`$ fails at that $`c`$. What the calibration shows is that the formal rules reproduce each printed step to the printed precision.

## 3. Statements

**Theorem 2** (Proofs above $`r_d`$; `conjecture_fails`, `HStair.stairD{1,2,3}_nf` and `_snf`). For $`(d,c)=(1,\,130921174/10^8)`$, $`(2,\,11915968/10^7)`$ and $`(3,\,11386523/10^7)`$ there is a strict normal-form proof `HY.NF c d M n` in which every line $`M_i`$ has kernel time $`\ge\mathrm{pin}`$ and, if its kernel is $`\mathsf{DTISP}[n^a,n^e]`$, $`e\le a`$. Every real root of $`p_d`$ is below $`c`$ (`HY.pd1_root_lt`, `pd2_root_lt`, `pd3_root_lt`: below $`1.301`$, $`1.1888`$, $`1.1373`$). The same holds with `HY.NFO (fun _ _ => 1) c d M n` in place of `HY.NF c d M n`, i.e. in the calculus `HY.StepO (fun _ _ => 1)` in which the new $`\log n`$ block of Lemma 3.3 has output exactly $`1`$ (`conjecture_fails_one`, `HStair.stairD{1,2,3}_snf1`).

**Theorem 3** (A 39-line proof; `HY.cert39_spec`). At $`c=26019/20000=1.30095`$ and $`d=1`$ there is a strict normal-form proof `HY.NF c 1 M 38`, i.e. 39 lines $`M_0,\dots,M_{38}`$, each obtained from the previous one by a `HY.Step`, with $`M_0=\mathsf{DTIME}_1[n^{100000}]`$ and kernel time $`\ge\mathrm{pin}`$ on every line $`M_i`$, $`i\le38`$. Every real root of $`p_1`$ is below $`1.30095`$.

**Theorem 4** (Ceilings; `HLM.ceiling_d1`, `HLM.ceiling_d2`, `HLM.ceiling_d3`). Let $`(d,c_0)=(1,6547/5000)`$, $`(2,149/125)`$ or $`(3,712/625)`$, i.e. $`c_0=1.3094`$, $`1.192`$, $`1.1392`$. For every real $`c\ge c_0`$:

1.  there is no strict normal-form proof `HY.NF c d M n`;

2.  there is no relaxed path `HL.RPath c d M n` with $`n\ge1`$ from $`([\,],\texttt{T}\,a_0)`$, $`a_0>0`$, to $`([\,],\texttt{T}\,a')`$ with $`a'\le a_0`$;

3.  every `HY.Step c d` path of length $`n\ge1`$ from $`([\,],\texttt{T}\,a_0)`$, $`a_0>0`$, to $`([\,],\texttt{T}\,a')`$ has $`a_0<a'`$;

4.  (`HLM.ceilingX_d1`, `_d2`, `_d3`) there is no path `HL.RPathX c d M n` of `HL.RStep c d` and `HL.Widen` steps with $`n\ge1`$ from $`([\,],\texttt{T}\,a_0)`$, $`a_0>0`$, to $`([\,],\texttt{T}\,a')`$ with $`a'\le a_0`$;

5.  every path of `HY.Step c d` and `HY.Incl` steps of length $`n\ge1`$ from $`([\,],\texttt{T}\,a_0)`$, $`a_0>0`$, to $`([\,],\texttt{T}\,a')`$ has $`a_0<a'`$.

Here `HY.Incl` is the inclusion $`\mathsf{DTIME}_d[n^a]\subseteq\mathsf{DTISP}[n^a,n^a]`$ under any prefix, from $`(\mathit{bl},\texttt{T}\,a)`$ to $`(\mathit{bl},\texttt{S}\,a\,a)`$, and `HL.Widen` its relaxed form, from $`(\mathit{bl},\texttt{T}\,a)`$ to $`(\mathit{bl},\texttt{S}\,a_2\,e_2)`$ with $`a\le a_2`$ and $`a\le e_2`$ (Section 6). Parts (2)–(5) put no condition on the intermediate lines (they may be quantifier-free or non-alternating). In (2) and (4) the condition $`a_0>0`$ is needed: with $`s=0`$ the relaxed rules admit $`([\,],\texttt{T}\,0)\to([0],\texttt{S}\,0\,0)\to([\,],\texttt{T}\,0)`$ at every $`c`$. All five parts are for the reading $`\max(b,e)`$ of the output superscript of the new $`\log n`$ block of Lemma 3.3 (item 3 of Section 2.4).

**Theorem 5** (A closed-form ceiling; `HL.no_nf`, `HL.no_drop_W`). Let $`c\ge1`$ and $`c^2\ge1+1/d`$.

1.  For real $`d>0`$ there is no strict normal-form proof `HY.NF c d M n`.

2.  For real $`d\ge1`$, along every path $`M_0,\dots,M_n`$ of `HY.Step c d`, `HY.Incl` and `HY.SpeedLog` steps from $`([\,],\texttt{T}\,a_0)`$, $`a_0\ge0`$, to $`([\,],\texttt{T}\,a')`$, $`a_0\le a'`$.

`HY.SpeedLog` is Lemma 3.3 inside a prefix with the side conditions of `speedMerge` and `speedNew` but an arbitrary output superscript $`\ell\ge0`$ for the new $`\log n`$ block (for example $`1`$, as displayed in the sketch of Theorem 7.9). So part (2) excludes strict normal-form proofs ($`a'<a_0`$) that also use these moves; it does not exclude a path with $`a'=a_0`$.

**Corollary 6** (`threshold_bounds`). Let $`c^*_d=\sup\{c:\exists M\,n,\ \texttt{HY.NF c d M n}\}`$. Then $`1.30921174\le c^*_1\le1.3094`$, $`1.1915968\le c^*_2\le1.192`$ and $`1.1386523\le c^*_3\le1.1392`$.

`threshold_bounds` states the existence at the lower values and the non-existence for every $`c`$ at or above the upper values; the bounds on the supremum follow. We do not prove that the set of $`c`$ with a proof is an interval (the exact rules have equalities and $`\ge1`$ floors, so monotonicity in $`c`$ is not immediate); for the complexity reading this does not matter, since $`\mathsf{NTIME}[n]\not\subseteq\mathsf{DTIME}_d[n^{c}]`$ implies the same for every smaller exponent.

## 4. The constructions

### 4.1 A 39-line proof at $`c=1.30095`$

The tag list `HY.cert39` (word `11101101101100111011011001101101101100`) is checked by the executable checker `HY.nfCheck`, whose soundness theorem `HY.nfCheck_sound` turns acceptance into an `HY.NF` proof over $`\mathbb R`$; the extra condition time $`\ge`$ input is `HY.timeCheck`. Both run by `decide +kernel`. The proof, with exponents divided by 1000 (so $`a_0=10^5`$ is shown as $`100`$; the certificate is exact), as printed by `replay39.py`, an independent transcription of Williams’s rules:

     0       DTIME_1[n^100.000]
     1 L7.1  (E n^56.454)^56.454 DTISP[n^100.000, n^43.546]
     2 L3.3  (E n^56.454)^56.454 (A log)^56.454 DTISP[n^87.091, n^43.546]
     3 L3.3  (E n^56.454)^56.454 (A n^58.466)^58.466 (E log)^56.454 DTISP[n^72.171, n^43.546]
     4 L7.2  (E n^56.454)^56.454 (A n^58.466)^58.466 DTIME_1[n^93.891]
     5-13    three rounds L7.1, L3.3, L7.2 at the A level: 93.891 -> 92.172 -> 87.699 -> 76.061
    14 L7.2  (E n^56.454)^56.454 DTIME_1[n^98.952]
    15 L7.1  (E n^56.454)^56.454 DTISP[n^98.952, n^42.498]
    16 L3.3  (E n^59.082)^59.082 (A log)^56.454 DTISP[n^82.368, n^42.498]
    17 L3.3  (E n^59.082)^59.082 (A n^56.454)^56.454 (E log)^56.454 DTISP[n^68.412, n^42.498]
    18 L7.2  (E n^59.082)^59.082 (A n^56.454)^56.454 DTIME_1[n^89.000]
    19-24   two rounds at the A level: 89.000 -> 84.681 -> 73.444
    25 L7.2  (E n^59.082)^59.082 DTIME_1[n^95.547]
    26-37   four rounds at the E level: 95.547 -> 94.880 -> 93.142 -> 88.623 -> 76.862
    38 L7.2  DTIME_1[n^99.994]                                  99.994 < 100

Lines 0–14 are the first part of Williams’s pattern: the $`\exists`$ block, an excursion to a $`\forall`$ level with three simple rounds there (lines 5–13), and the return to the $`\exists`$ level (line 14). Lines 15–25 make a second excursion under the same $`\exists`$ block: the Lemma 3.3 guess of line 16 merges into that block and raises it from $`56.454`$ to $`59.082`$, at no cost in alternations. This second excursion is what the annotation family of \[W13, Theorem 7.5\] does not contain. Lines 26–37 are simple rounds under the raised $`\exists`$ block, and line 38 is the final slowdown. The final exponent is $`99994.12966\ldots<10^5`$. On lines 12, 23 and 36 the kernel time exceeds the input superscript by less than $`10^{-6}`$ (the smallest gap is about $`4.63\cdot10^{-20}`$, on line 12).

### 4.2 Level claims

Proofs at $`c`$ close to the threshold are far too long to list, so they are checked as directed acyclic graphs of reusable sub-derivations. A sub-derivation is stated as a claim about a whole family of lines, at every scale (`Dag.lean`, namespace `HD`):

**Definition 7** (`HD.SC`, `HD.TC`). Call a block list *good* (`HD.Good`) if it alternates and every block has $`1\le o`$ and $`0\le g\le o`$. `HD.Der` is a `HY.Step` derivation whose lines after the first have nonempty, alternating block lists. The *S-claim* `SC`$`(c,d,B_0,\kappa,\varepsilon,V)`$ says: for every scale $`B\ge B_0`$ and every line $`(u::\mathit{rest},\mathsf{DTISP}[n^a,n^e])`$ with good blocks, $`u.o\le B`$, $`1\le a\le\kappa B`$ and $`0\le e\le\varepsilon B`$, there are $`a'`$ with $`1\le a'\le c\max(\mathrm{pin}\,\mathit{rest},VB)`$, a `Der` derivation from that line to some line $`L_p`$, and one `HY.Step` from $`L_p`$ to $`(\mathit{rest},\mathsf{DTIME}_d[n^{a'}])`$. The *T-claim* `TC`$`(c,d,B_0,\alpha,V)`$ says the same for lines $`(u::\mathit{rest},\mathsf{DTIME}_d[n^a])`$ with $`1\le a\le\alpha B`$.

A claim is about the level of the innermost block: it says that the level can be closed, removing that block, at cost $`c\max(\mathrm{pin}\,\mathit{rest},VB)`$. Because claims are downward closed (they speak about every good line whose top, time and space are at most the planned ones) and hold at every scale $`B\ge B_0`$, one claim can be used at every call site. Claims are combined by three lemmas, all proved in Lean for the exact rules:

- `HD.SC_pop`, `HD.TC_pop`: closing the level at once (one Lemma 7.2 step) proves $`\texttt{SC}(\dots,\max(1,\kappa))`$ and $`\texttt{TC}(\dots,\max(1,\alpha))`$, for $`c\ge1`$ and $`B_0\ge0`$.

- `HD.TC_of_SC` (Lemma 7.1, merged): for $`B_0\ge0`$, $`d>0`$, $`\kappa\ge1`$, $`\varepsilon>0`$ and $`d(\kappa-1)\le\varepsilon`$, an S-claim $`\texttt{SC}(B_0,\kappa,\varepsilon,\Omega)`$ gives $`\texttt{TC}(B_0,\alpha,\Omega\alpha/\kappa)`$ for every $`\alpha\ge\kappa`$. The T-level is rescaled to top at most $`\beta=\alpha B/\kappa`$ by Lemma 7.1 with $`s=\min(a,\varepsilon\beta/d)`$ if $`a\le\beta`$ and $`s=a-\beta`$ otherwise.

- `HD.SC_speed` (Lemma 3.3, merged): for $`c\ge1`$ and $`B_0\ge0`$, from an inner S-claim $`\texttt{SC}(B_0,\kappa',\varepsilon,W)`$ and an outer T-claim $`\texttt{TC}(B_0,\alpha,V_T)`$, with $`1\le u`$, $`\varepsilon\le u`$, $`\kappa'=\kappa+\varepsilon-u`$, $`\varepsilon\le\kappa'`$, $`0\le\varepsilon\le1`$, $`1\le\kappa'B_0`$, $`c\max(u,W)\le\alpha u`$ and $`1\le uV_T`$, follows $`\texttt{SC}(B_0,\kappa,\varepsilon,uV_T)`$. The derivation applies one Lemma 3.3 step, after which the innermost block’s top $`\max(u.o,x+e)`$ is at most $`uB`$ (it can be smaller when the speedup is clipped, below), then the inner claim for the new $`\log n`$ level at scale $`B`$, then the outer claim for the raised level at scale $`uB`$.

When the actual line is below the planned one, `SC_speed` clips the speedup to $`x=\min((u-\varepsilon)B,\ a-\max(e,1))`$, and closes the level at once if $`e>a`$. Every side condition of the exact rules, including the $`\ge1`$ floors, is discharged; no weakening rule is used. Finally `HD.nf_of_SC`: for $`c\ge1`$, $`B_0\ge0`$, $`d\ge0`$, $`\kappa>1`$, $`d(\kappa-1)\le\varepsilon`$, $`V\ge1`$ and $`cV<\kappa`$, an S-claim $`\texttt{SC}(B_0,\kappa,\varepsilon,V)`$ gives an `HY.NF` proof: from $`\mathsf{DTIME}_d[n^{\kappa\beta}]`$, $`\beta=\max(B_0,1)`$, apply Lemma 7.1 (`convNew`) with $`s=\kappa\beta-\beta`$, then the claim; the final line has exponent at most $`cV\beta<\kappa\beta`$.

### 4.3 The checker and its soundness

`HD.dagCheck c d M SH nodes root` is an executable function over $`\mathbb Q`$, with a grid $`M`$ and values in units of $`2^{-\mathit{SH}}`$. A node (`HD.Node`) claims an S-claim at $`\kappa=t/M`$, $`\varepsilon=d(t-M)/M`$ (the space Lemma 7.1 leaves when it rescales a kernel $`\kappa B`$ to top $`B`$) with value $`V=\varphi\kappa`$, $`\varphi=\mathit{phi}/2^{\mathit{SH}}`$. Its `steps` list a chain of Lemma 3.3 steps: for each, the new top $`u=k_u/M`$, the closing of the outer T-level after the inner level (`r = 0`: Lemma 7.2 at once, value $`\max(1,\alpha)`$; otherwise the table entry of index $`r-1`$, an earlier node, which needs its $`\kappa_{r-1}\le\alpha`$ and gives value $`\varphi_{r-1}\alpha`$; function `tval`), and a claimed value $`w/2^{\mathit{SH}}`$. `chain` walks the chain: each step needs $`M\le k_u`$ and $`d(t-M)\le k_u\le j`$, and moves the kernel position from $`j`$ to $`j+d(t-M)-k_u`$ (which must be $`\ge1`$); the innermost level is closed at the recorded final position $`p`$ with value $`\max(1,p/M)`$, and every claimed value must satisfy $`1\le u\,v\le w/2^{\mathit{SH}}`$ with $`v`$ the closing value of the outer T-level at $`\alpha=c\max(1,W/u)`$, $`W`$ the value of the rest of the chain. `procNodes` checks the nodes in order ($`M<t`$, $`d(t-M)\le M`$, chain value$`/\kappa\le\varphi`$, $`\varphi\kappa\ge1`$) and records the proved claims (invariant `TabOK`). `dagCheck` also requires $`1\le c`$, $`1\le d`$, $`1\le M`$ and $`c\varphi_{\mathrm{root}}<1`$.

**Theorem 8** (`HD.dagCheck_sound`). If `HD.dagCheck c d M SH nodes root = true` then there is a strict normal-form proof `HY.NF c d Mp n` (with $`c`$ and $`d`$ cast to $`\mathbb R`$).

The proof composes `tval_sound`, `chain_sound` and `procNodes_sound`, which interpret each check by the lemmas of Section 4.2 at scale $`B_0=M`$, and ends with `nf_of_SC`. So the normal-form proof starts at $`a_0=\kappa_{\mathrm{root}}M=t_{\mathrm{root}}`$.

**Other outputs of the new $`\log n`$ block.**

The claims, the lemmas of Section 4.2 and the soundness proof are stated for the calculus `HY.StepO `$`\ell`$` c d` (`Calculus.lean`), which is `HY.Step` except that the new $`\log n`$ block of Lemma 3.3 gets the output $`\ell(u.o,e)`$ (resp. $`\ell(\mathrm{pin}\,\mathit{bl},e)`$), for any function $`\ell`$ with $`1\le\ell(o,e)\le\max(o,e)`$ whenever $`o\ge1`$ and $`e\ge0`$ (`HY.LogOK`). The proofs use only that this output is at least $`1`$ and at most $`\max(u.o,e)`$, which is at most the scale $`B`$ (as $`u.o\le B`$ and $`e\le\varepsilon B\le B`$) and, for the strict reading, at most the new kernel time. `HD.dagCheck_soundO` gives `HY.NFO `$`\ell`$` c d Mp n` for every such $`\ell`$; $`\ell=\max`$ is `HY.Step` (`HY.nf_of_nfO_max`, giving Theorem 8), and $`\ell=1`$ is the calculus with output exactly $`1`$ (`HD.dagCheck_sound1`). The checker itself does not depend on $`\ell`$, so the same acceptance proves both.

**The strict reading**

(`DagStrict.lean`, namespace `HDS`). The same claims and checker with: `HDS.Der` requires kernel time $`\ge\mathrm{pin}`$ and `SpOK` (space $`\le`$ time on a $`\mathsf{DTISP}`$ kernel) on every line after the first; claims assume $`u.o\le a`$ (and, for S-claims, $`e\le a`$) on their first line and guarantee $`\mathrm{pin}\,\mathit{rest}\le a'`$; a speedup is clipped at $`x\le a-\max(e,u.o,1)`$; chain positions must stay $`\ge M`$ ($`\kappa'\ge1`$); Lemma 7.1 picks $`s\le a/d`$. Accordingly `HDS.TC_of_SC` needs $`d\ge1`$ (instead of $`d>0`$) and $`\varepsilon\le1`$ besides the other hypotheses of `HD.TC_of_SC`; `HDS.SC_speed` needs $`1\le\kappa'`$; and `HDS.nf_of_SC` needs $`\varepsilon\le1`$. The checker discharges these: `dagCheck` requires $`d\ge1`$, a node has $`\varepsilon=d(t-M)/M\le1`$ by $`d(t-M)\le M`$, and `HDS.chain` keeps every position $`\ge M`$. `HDS.dagCheck_sound` gives an `HY.NF` proof with kernel time $`\ge\mathrm{pin}`$ and `SpOK` on every line, and `HDS.dagCheck_soundO`, `HDS.dagCheck_sound1` the same for `HY.StepO `$`\ell`$.

### 4.4 The staircase certificates

The three certificates of Theorem 2 (`StairD1.lean`, `StairD2.lean`, `StairD3.lean`) are node lists produced by an untrusted generator (`scripts/stair_cert.py`) from the level structure of Section 7. Each list is checked twice by `decide +kernel`, by `HD.dagCheck` (`stairD{d}_ok`) and by `HDS.dagCheck` (`stairD{d}_sok`); `stairD{d}_snf1` applies `HDS.dagCheck_sound1` to the second check. Lean checks that the node lists are proofs; it does not check that they are the proofs the recursion describes.

| $`d`$ | $`c`$ | grid $`M`$ | units | nodes | speedup steps | root $`c\varphi`$ | unfolded lines |
|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| 1 | $`130921174/10^8`$ | $`2^{56}`$ | $`2^{-120}`$ | 552 | 3915 | 0.99916308 | $`\le7.62\cdot10^{21}`$ |
| 2 | $`11915968/10^7`$ | $`2^{50}`$ | $`2^{-110}`$ | 286 | 1846 | 0.99940456 | $`\le2.47\cdot10^{17}`$ |
| 3 | $`11386523/10^7`$ | $`2^{50}`$ | $`2^{-110}`$ | 212 | 1255 | 0.99961709 | $`\le1.10\cdot10^{15}`$ |

*Table 3: The staircase certificates (`scripts/dag_check.py`, which re-implements both checkers in exact rationals on the Lean data). Root ratios are rounded. “Unfolded lines” bounds from above the number of lines of the derivation that the soundness proof builds (it counts them as if no level were closed early). The proofs start at $`a_0=t_{\mathrm{root}}\approx1.41\cdot10^{17}`$, $`1.68\cdot10^{15}`$, $`1.50\cdot10^{15}`$.*

The structure of the certificates (as built by the generator). In a node’s chain the first step is the outermost one, so its T-level is closed last. Level 0 is a climb of nodes, each one Lemma 3.3 step with $`u\approx1`$ (top kept) whose inner level is closed at once and whose T-level is closed by the previous node (the first node closes it at once). These are Williams’s simple rounds, which contract the kernel below the repelling fixed point $`\alpha_1=c(1+d)/(c(1+d)-1)`$. Level $`h+1`$ starts with a *fresh* node, whose chain closes its T-levels, from the outermost in, with the top node (the *kink*) of level $`h`$, again with that kink, and then with the kinks of levels $`h-1,\dots,0`$. It continues with a *climb*, each node of which closes its outermost T-level with the previous node and the others with the kinks of levels $`h,\dots,0`$. The construction stops at the first kink with $`c\varphi<1`$; that node is the root.

## 5. The ceilings

### 5.1 The relaxed calculus

The ceilings are proved for a relaxation `HL.RStep c d` (`Relaxed.lean`). A relaxed line keeps only the output superscripts of its blocks (innermost first) and the kernel; quantifiers and guess exponents are dropped, the input superscript of the empty prefix is $`0`$, and every output is bounded only from below:

- `convM`: $`(b::r,\texttt{T}\,a)\to(b_1::r,\texttt{S}\,a_2\,e)`$ with $`0\le s\le a`$, $`\max(b,a-s)\le b_1`$, $`a\le a_2`$, $`ds\le e`$; `convN`: $`(bl,\texttt{T}\,a)\to(g::bl,\texttt{S}\,a_2\,e)`$ with $`\max(\mathrm{pin}\,bl,a-s)\le g`$ and the same other conditions;

- `speedM`: $`(b::r,\texttt{S}\,a\,e)\to(L::b'::r,\texttt{S}\,a_2\,e_2)`$ with $`0\le x`$, $`e\le a-x`$, $`\max(b,x+e)\le b'`$, $`\max(b,e)\le L`$, $`a-x\le a_2`$, $`e\le e_2`$; `speedN`: the same with two new blocks $`g_2::g_1::bl`$;

- `slow`: $`(b::r,k)\to(r,\texttt{T}\,a')`$ with $`c\max(\mathrm{pin}\,r,b,\mathrm{time}(k))\le a'`$.

**Lemma 9** (`HL.sim`). For $`c\ge0`$, every `HY.Step c d L L'` gives `HL.RStep c d (enc L) (enc L')`, where `enc` keeps the output superscripts and the kernel.

The relaxation drops the side conditions $`a\ge1`$, $`e\ge0`$, $`x\le a-1`$, $`s>0`$, the conditions on quantifiers, all $`\ge1`$ floors and the guess exponent in the slowdown maximum; since the relaxed slowdown only bounds its output from below, dropping a term only weakens its condition.

### 5.2 A one-level potential: the ceiling $`c^2\ge1+1/d`$

Theorem 5 has a short proof that shows the method. Put $`A=\max(1+1/d,c)`$ and $`g=1/A`$. On a level whose innermost block has superscript $`b`$, let
``` math
\psi_T(b,a)=\min\bigl(\max(b,a),\ c\max(b,ga)\bigr),\qquad \psi_S(b,a,e)=\min\bigl(\max(b,a),\ c\max(b,e)\bigr)
```
for kernels $`\mathsf{DTIME}_d[n^a]`$ and $`\mathsf{DTISP}[n^a,n^e]`$. The potential $`\Phi`$ of a line (`HL.Phi`) lifts the innermost value $`y`$ through each outer block of superscript $`b'`$ by $`y\mapsto\psi_T(b',c\max(b',y))`$, and finally by $`y\mapsto c\max(0,y)`$; a quantifier-free line $`\mathsf{DTIME}_d[n^a]`$ has potential $`a`$. Intuitively $`\psi`$ is a lower bound for what the level can still reach: an S-level can at best end at $`c\max(\text{top},\text{space})`$, a T-level with kernel $`a`$ at best at $`c\max(\text{top},a/A)`$. The facts used (`HL.Facts`) are $`1\le c`$, $`0\le g`$, $`cg\le1`$, $`c^2g\ge1`$, $`0\le d`$ and $`g\le d(1-g)`$, i.e. $`c\le A\le c^2`$ and $`A\ge1+1/d`$; with $`c^2\ge1+1/d`$ they hold.

**Lemma 10** (`HL.phi_step`). Under `HL.Facts c d g`, an `RStep c d` from a line with nonnegative entries does not lower $`\Phi`$.

*Proof sketch.* Each constructor reduces to a local inequality; the lift is monotone (`up_mono`). *Lemma 7.1* (`conv_ineq`): $`\psi_T(b,a)\le\psi_S(\max(b,a-s),a,ds)`$ for $`0\le s\le a`$, because $`ga\le\max(a-s,ds)`$: if $`s\le(1-g)a`$ then $`a-s\ge ga`$, and otherwise $`ds>d(1-g)a\ge ga`$. *Lemma 3.3* (`speed_ineq`): for $`0\le b\le b'`$, $`e\le b'`$ and every real $`Y`$, $`\psi_S(b,a,e)\le\psi_T(b',c\max(b',Y))`$, where $`b'\ge\max(b,x+e)`$ is the new top of the level and $`Y`$ the value of the new inner level. Indeed $`\psi_S(b,a,e)\le c\max(b,e)\le cb'`$, and both arguments of the min in $`\psi_T(b',c\max(b',Y))`$ are $`\ge cb'`$. The inequality does not use the output superscript of the new $`\log n`$ block, which is why the one-level ceiling also holds under the displayed reading of item 3 of Section 2.4 (`HL.phi_loose`). *Opening a block* (`push_ineq`, for `convN` and `speedN` under a prefix): $`y\le\psi_T(b,c\max(b,y))`$ for $`y\ge b`$, by $`c^2g\ge1`$. *Lemma 7.2*: $`\psi\le\max(\text{top},\text{time})`$ (`pot_le`), so the new exponent bounds the lifted value. *First step* (`first_ineq`): from $`\mathsf{DTIME}_d[n^{a}]`$ the potential becomes at least $`c\,\psi_T(0,a)=c\min(a,cga)\ge a`$. ∎

So along every relaxed path from $`\mathsf{DTIME}_d[n^{a_0}]`$, $`a_0\ge0`$, every later quantifier-free line $`\mathsf{DTIME}_d[n^{a'}]`$ has $`a'\ge a_0`$ (`HL.qf_ge`), and with Lemma 9 no strict normal-form proof exists (`HL.no_nf`). The facts hold with $`g=1/A`$ whenever $`d>0`$, $`c\ge1`$ and $`c^2\ge1+1/d`$ (`HL.facts_of`). For $`d\ge1`$ the same conclusion holds along paths that also use `HL.Loose` and `HL.Widen` steps (`HL.qf_ge_W`, Section 6), which gives Theorem 5(2). The bound $`\sqrt{1+1/d}`$ is the previous best exponent $`\sqrt{(d+2)/(d+1)}`$ recalled in \[W13, p. A:3\] (for $`d=1`$ the van Melkebeek–Raz bound $`\sqrt{3/2}`$, p. A:31) with $`d`$ shifted by one.

### 5.3 Multi-level potentials

The one-level potential ignores that a T-level can be closed more cheaply by running further subproofs under it. The multi-level potential (`Potential.lean`, namespace `HLM`) has a finite list of levels $`(P_j,\theta_j)`$ together with level 0, $`(0,\theta_0)`$; put $`\kappa_p=\max(c,P_p)`$. Then
``` math
\begin{aligned}
\psi_T(b,a)&=\min\bigl(\max(b,a),\ \max(cb,\ \mathrm{Tm}(b,a))\bigr),\qquad \mathrm{Tm}(b,a)=\min_j\max(P_jb,\ \theta_ja/c),\\
\psi_S(b,a,e)&=\inf_w\max\bigl(0,V_w(b,a,e)\bigr),
\end{aligned}
```
where $`w`$ ranges over words (lists of levels, outermost first), $`V_{[\,]}(b,a,e)=\max(b,a)`$ and
``` math
V_{p::w}(b,a,e)=\max\Bigl(\kappa_pb,\ \theta_p\,\mathrm{Ad}(w)\max(b,e),\ \frac{a+|p::w|\,e}{D(p::w)}\Bigr),
```
with $`\mathrm{Ad}([\,])=1`$, $`\mathrm{Ad}(p::w)=\max(\kappa_p,\theta_p\mathrm{Ad}(w))`$, $`D([\,])=1`$, $`D(p::w)=1/\kappa_p+D(w)/\theta_p`$. A word stands for a chain of Lemma 3.3 steps whose T-levels are closed by the listed levels; $`V_w`$ is an explicit lower bound for the cost of that chain. The one-level potential of Section 5.2 has a cruder $`\psi_S`$; with only level 0 and $`\theta_0=c^2/A`$ the T-parts agree.

`HLM.Base`: $`1\le c`$, $`0\le d`$, and $`1\le\theta_p\le c`$, $`P_p\ge0`$ for every level. `HLM.Hyp` adds, for every nonempty word $`w`$, the condition `ConvOK` for its state $`(\mathrm{Ad}\,w,\mathrm{AL}\,w,D\,w,|w|)`$, where $`\mathrm{AL}([\,])=0`$, $`\mathrm{AL}(p::w)=\theta_p\mathrm{Ad}(w)`$, and $`\texttt{ConvOK}(A,L,D,m)`$ says $`\mathrm{Tm}(b,a)\le\max(Ab,\ Q\,a)`$ for all $`b,a\ge0`$, with
``` math
Q=\max\Bigl(\frac{ALd}{A+Ld},\ \frac{A(1+md)}{AD+md}\Bigr).
```

**Lemma 11** (`HLM.phi_step`). Under `HLM.Hyp`$`(c,d,\theta_0,\mathit{lv})`$, an `HL.RStep c d` from a line with nonnegative entries does not lower $`\Phi`$.

*Proof sketch.* *Lemma 3.3* needs only `Base`. Prepending a letter absorbs one speedup (`V_succ`): for $`b,x\ge0`$,
``` math
V_{p::w}(b,a,e)\le\max\bigl(\kappa_p\max(b,x+e),\ \theta_pV_w(\max(b,e),a-x,e)\bigr).
```
The first two terms of $`V_{p::w}`$ are bounded directly ($`V_w(L,\cdot)\ge\mathrm{Ad}(w)L`$), and the third by a weighted average with weights $`1/\kappa_p`$ and $`D(w)/\theta_p`$: $`a+(m+1)e=(x+e)+(a-x+me)`$ (`U_succ`). The lift satisfies $`\psi_T(b',c\max(b',W))\ge\min_p\max(\kappa_pb',\theta_pW)`$ (`le_psT_lift`); together they give `speed_ineq`. *Lemma 7.1* (`conv_word`, `conv_ineq`): for a nonempty word, $`V_w(\max(b,a-s),a,ds)\ge\max(\mathrm{Ad}\cdot\max(b,a-s),\ \mathrm{AL}\cdot ds,\ (a+|w|ds)/D)`$, and two weighted averages over $`s`$ (`cross`) give $`\ge\max(\mathrm{Ad}\,b,\ Q\,a)`$, which dominates $`\psi_T(b,a)`$ by `ConvOK` and $`\mathrm{Ad}\ge c`$. The empty word is $`\max(b,a)\ge\psi_T`$. *Opening a block* (`push_ineq`) uses $`\theta\ge1`$; *Lemma 7.2* and the *first step* (`first_ineq`, using $`\mathrm{Tm}(0,a)\ge a/c`$) are as before. ∎

Consequences: `HLM.qf_ge` ($`a_0\le a'`$ along relaxed paths from $`\mathsf{DTIME}_d[n^{a_0}]`$, $`a_0\ge0`$), `HLM.no_nf`, and, when every $`\theta`$ (level 0 included) exceeds $`1`$ and $`c>1`$, `HLM.qf_gt` and `HLM.no_nf_le`: the first step raises the potential strictly (`first_strict`), so $`a_0<a'`$ along every path of length $`\ge1`$ from $`a_0>0`$, which excludes non-strict normal forms.

**All larger $`c`$.**

The relaxed calculus is monotone in $`c`$ (`HLM.rstep_mono`): an `RStep` at $`c`$ from a line with nonnegative entries is one at every $`c_0\le c`$, because only `slow` depends on $`c`$ and its lower bound only weakens. So a potential valid at $`c_0`$ excludes proofs at every $`c\ge c_0`$ (`rge_of`, `rgt_of`, `no_nf_of`, `no_nf_le_of`). For the exact calculus we neither claim nor use it; it enters only through `HL.sim`.

### 5.4 Checking the Lemma 7.1 condition for all words

`Hyp` quantifies over infinitely many words. `AbsCheck.lean` reduces it to a finite check. Prepending a letter $`p`$ maps a state $`(A,L,D,m)`$ to $`(\max(\kappa_p,\theta_pA),\ \theta_pA,\ 1/\kappa_p+D/\theta_p,\ m+1)`$. This map is monotone for the order “$`A`$, $`L`$, $`m`$ larger and $`D`$ smaller” (`Dom`, `dom_prep`), and `ConvOK` transfers along that order (`convOK_mono`; monotonicity of $`Q`$ in $`m`$ uses $`AD\ge1`$, which holds for every real word, `AdDw_ge_one`). A state is *done* once $`\theta_0/c\le ALd/(A+Ld)`$: then `ConvOK` holds (`convOK_done`) and stays true under prepending. The executable `absCheck`$`(c,d,\theta_0,\mathit{lv},S)`$ accepts when $`1\le c`$, $`0\le d`$, every level has $`1\le\theta\le c`$ and $`P\ge0`$, every state of the list $`S`$ has $`A>0`$, $`L\ge0`$, $`D>0`$ and an interval certificate for `ConvOK` (`ivOK`: breakpoints in the ratio $`a/b`$, starting at $`0`$, with one level per piece whose term is below $`\max(Ab,Qa)`$ on that piece), and $`S`$ together with the empty word’s state $`(1,0,1,0)`$ is closed under prepending each letter up to done states and domination: every successor that is not done dominates some state of $`S`$ (it has $`A`$, $`L`$, $`m`$ at least and $`D`$ at most those of that state), so `ConvOK` transfers from that state to the successor.

**Theorem 12** (`HLM.absCheck_sound`). If `absCheck`$`(c,d,\theta_0,\mathit{lv},S)={}`$`true` then `HLM.Hyp` holds for the data cast to $`\mathbb R`$.

The proof is an induction over the real word (prepending), so word length is unbounded.

**The three ceilings**

(`Ceiling.lean`). In each case $`\theta_0=c_0^2-c_0/(d+1)`$; the further levels have $`P_{j+1}=\theta_jP_j`$ with $`P_1=c_0\theta_0`$, and $`\theta_j`$ slightly above $`1`$, found by an untrusted search. Only their acceptance matters.

<div class="center">

| $`d`$ | $`c_0`$ | abstract states | levels $`(P_j,\theta_j)`$, $`j\ge1`$ ($`P_j`$ rounded) |
|:--:|:--:|:--:|:---|
| 1 | $`6547/5000`$ | 105 | $`(1.38774,1.027)`$, $`(1.42521,1.017)`$, $`(1.44944,1.014)`$ |
| 2 | $`149/125`$ | 50 | $`(1.22005,1.011)`$, $`(1.23347,1.008)`$ |
| 3 | $`712/625`$ | 19 | $`(1.15398,1.0055)`$ |

</div>

Each list is accepted by `decide +kernel` (`absD{d}_ok`); every $`\theta`$ exceeds $`1`$ (`thD{d}_gt`); and `ceiling_d{d}` combines `no_nf_of`, `no_nf_le_of` and `rgt_of` into parts (1)–(3) of Theorem 4; `ceilingX_d{d}` (`Variants.lean`) gives parts (4) and (5) from `rgt_of` and `HL.rpath_of_rpathX` (Section 6). The script `abs_check.py` re-implements `absCheck` in exact rationals on the Lean data; it accepts all three, and rejects each when $`c_0`$ is lowered by $`10^{-4}`$ (with $`\theta_0`$ recomputed) or when the last abstract state is removed.

## 6. What the relaxed calculus covers

Lemma 9 embeds `HY.Step`. Beyond it, `HL.RStep` contains:

- weakening of every output, time and space exponent (all are bounded only from below);

- Lemma 7.1 with $`s=0`$, and Lemma 3.3 without $`a\ge1`$, $`x\le a-1`$ and $`e\ge0`$;

- Speedup Rule 2 and Lemma 7.1 opening a block anywhere (`speedN`, `convN`), and since quantifiers are not tracked, new blocks of either type, merged or not;

- Lemma 3.3 on a quantifier-free $`\mathsf{DTISP}`$ kernel (Speedup Rule 0, `speedN` with $`\mathit{bl}=[\,]`$), which arises only through the inclusion below;

- no $`\ge1`$ floors, input superscript $`0`$ for the empty prefix, and the slowdown without the guess exponent;

- paths whose intermediate lines are quantifier-free or do not alternate (Theorem 4(2), (3)).

Combining adjacent same-type blocks after the fact is covered too (a paper argument): all rules act on the innermost block and never change outer blocks, so a same-type adjacency arises only when a block is created, and “create unmerged, then combine” gives the merged rule’s result (the combined block’s output is the inner one’s). Creating an unmerged same-type block, or splitting a block into two of the same type, is not itself a Williams move: the lines of his proofs alternate ($`Q_i\ne Q_{i+1}`$ in \[W13, Definition 4.1\], and the simple classes of §7 have the same form). `HY.Step` has no such move; `HL.RStep` contains the unmerged creation only because it does not track quantifiers.

**The inclusion $`\mathsf{DTIME}_d[t]\subseteq\mathsf{DTISP}[t,t]`$**

(`HY.Incl`; relaxed form `HL.Widen`, with weakening). It is sound (a $`d`$-dimensional tape machine running $`t`$ steps visits at most $`t`$ cells), but it is not among Williams’s rules (p. A:31 lists Lemma 3.3 or 7.1 for speedups and Lemma 3.4 or 7.2 for slowdowns). The forms of Lemma 3.4 that follow from $`H_c`$, with time exponent $`c'\ge c`$ and space exponent $`e\ge c`$ (the best being $`c'=e=c`$; item 7 of Section 2.4), give the line of Lemma 7.2 followed by a `Widen` step: time $`c'm`$ and space $`em`$, both at least the time $`cm`$ that Lemma 7.2 gives. The exact inclusion is the case $`c'=e=c`$. For $`d=1`$ inside a prefix it is the case $`s=a`$ of `convM`; in general it is outside `RStep`. It adds nothing to the relaxed calculus, by a short argument checked in Lean (`Variants.lean`). After the inclusion the kernel is $`\mathsf{DTISP}[n^{a_2},n^{e_2}]`$ with $`a_2,e_2\ge a`$ (for the exact inclusion $`a_2=e_2=a`$, so Lemma 3.3 is then possible only with $`x=0`$). `HL.widen_dec`: for $`c\ge0`$ and $`d\ge1`$, a `Widen` step from $`(\mathit{bl},\texttt{T}\,a)`$, $`a\ge0`$, followed by any `RStep` from the $`\mathsf{DTISP}`$ line can be replaced by Lemma 7.1 with $`s=a/d`$ (`convM`, or `convN` when the next step is `speedN`) followed by an `RStep` to the same line. Lemma 7.1 creates or raises a block with output $`\max(b,a-a/d)`$, $`b`$ the previous output of the innermost block (or $`\mathrm{pin}\,\mathit{bl}`$ when `convN` creates the block), and gives space $`ds=a\le e_2`$; the next move absorbs that output. The part $`b`$ is absorbed by the original step’s own lower bounds $`\ge b`$ (resp. $`\ge\mathrm{pin}\,\mathit{bl}`$), and the part $`a-a/d\le a`$ as follows: Lemma 3.3 gives the outer of its blocks an output $`\ge x+e_2\ge a`$ and the new $`\log n`$ block an output $`\ge e_2\ge a`$, and Lemma 7.2 has $`a_2\ge a`$ in its maximum.

`HL.path_unwiden` then removes the `Widen` steps from a path. Precisely: let a relation $`R`$ preserve nonnegativity of all entries and satisfy the conclusion of `widen_dec` (for $`a\ge0`$); then every path of $`R`$ and `Widen` steps from a line with nonnegative entries to a line with a $`\mathsf{DTIME}_d`$ kernel can be replaced by an $`R`$-path of the same length with the same two endpoints. For `RStep c d` this needs $`c\ge0`$ and $`d\ge1`$ (`HL.rpath_of_rpathX`). So what transfers are statements determined by the length of a path and its two endpoints: Theorem 4(4) from part (2), (5) from it with `HL.sim`, and, with `HL.Loose` steps as well, `HL.qf_ge_W` and Theorem 5(2). Statements about the intermediate lines need not transfer: from $`([\,],\texttt{T}\,1)`$ a `Widen` step reaches $`([\,],\texttt{S}\,1\,1)`$ and lowers the one-level potential from $`\Phi([\,],\texttt{T}\,1)=1`$ to $`\Phi([\,],\texttt{S}\,1\,1)=0`$. This is also why the argument goes through the rewriting rather than the potential: the rewritten path never passes through the line after the inclusion.

**Lemma 3.3 with a smaller superscript for the new $`\log n`$ block**

(`HY.SpeedLog`; relaxed form `HL.Loose`, any superscript $`\ge0`$). This is the displayed reading of item 3 of Section 2.4. The one-level potential covers it (`HL.phi_loose`, used in Theorem 5(2)), because its Lemma 3.3 inequality `HL.speed_ineq` holds for every value of the new inner level. The multi-level potentials of Theorem 4 do not.

Not covered:

- Lemma 3.3 with the smaller $`\log n`$ superscript, by the ceilings of Theorem 4.

- A slowdown that keeps a $`\mathsf{DTISP}`$ kernel with space below its time, as in the line of p. A:34 discussed in item 6 of Section 2.4, by any of the ceilings.

- Other sound moves that are not rules of the calculus, e.g. $`\mathsf{DTISP}[t,s]\subseteq\mathsf{DTIME}_d[t\cdot s^{1/d}]`$ (laying out the space as a $`d`$-cube), other speedup or slowdown lemmas, and contradictions other than a normal-form proof. Extending the ceilings to arbitrary alternation-trading proofs between complementary classes uses \[W13, Theorem 7.4\], whose proof is only sketched there.

## 7. The threshold

### 7.1 What is proved

By Corollary 6, $`c^*_1\in[1.30921174,1.3094]`$ (width $`1.8826\cdot10^{-4}`$), $`c^*_2\in[1.1915968,1.192]`$ ($`4.032\cdot10^{-4}`$), $`c^*_3\in[1.1386523,1.1392]`$ ($`5.477\cdot10^{-4}`$). The exact values are open.

### 7.2 The staircase recursion (numerics, not proved)

Fix a level with top $`B`$ and normalise $`B=1`$. Numerical optimisation over the reduced system of level values (not a search over all proofs) suggests that the least achievable closing value $`F(\alpha)`$ of a T-level with kernel $`\alpha`$ is a staircase of constant pieces: level 0 is Williams’s simple-round basin, with value $`\Psi_0=c`$ up to the kink $`r_0=\alpha_1=c(1+d)/(c(1+d)-1)`$, and each further level $`h`$ has a value $`\Psi_h`$ on a branch ending at a kink $`r_h`$, with ratio $`g_h=\Psi_h/r_h`$. A point of a branch is reached by one Lemma 3.3 step with $`u=1`$ into a lower point of the same branch, then one step into each lower kink; a new level starts with the fresh chain of Section 4.4. This leads to the recursion (`staircase.py`): $`S_{-1}=1`$, $`S_0=S_{-1}/(cg_0)+1/\Psi_0`$, and for $`h\ge0`$, with $`n_h=1+(h+2)d`$,
``` math
\Psi_{h+1}=c\,g_h\Psi_h,\qquad r_{h+1}=\max\Bigl(\frac{n_h}{n_h-S_h/c},\ \frac{cg_h+n_h+(r_h/c)S_{h-1}}{n_h}\Bigr),\qquad g_{h+1}=\frac{\Psi_{h+1}}{r_{h+1}},
```
$`S_{h+1}=S_h/(cg_{h+1})+1/\Psi_{h+1}`$. The first term of $`r_{h+1}`$ is the kink of the branch, the second the end of the fresh chain’s kernel budget. Level $`h+1`$ exists iff $`n_h>S_h/c`$, $`r_{h+1}\le1+1/d`$ and $`r_{h+1}>c\Psi_h`$ (equivalently $`g_{h+1}<g_h`$). The recursion *refutes* at $`c`$ if some existing level has $`cg_h<1`$, and *stops* if the staircase ends with $`cg_h>1`$ throughout. At $`c=1.3092`$, $`d=1`$, it gives $`r_h=1.61789`$, $`1.76931`$, $`1.83631`$, $`1.87385`$, $`1.89816`$, $`1.91635`$, $`1.93374`$ and $`cg_h=1.0594`$, $`1.0263`$, $`1.0148`$, $`1.0093`$, $`1.0056`$, $`1.0016`$, $`0.9941`$, so it refutes at level 6. The generator of Section 4.4 builds certificates from exactly this structure, and they check; that is the only machine-checked link between the recursion and the calculus.

**Definition 13**. $`c^{*}_{\mathrm{stair}}(d)`$ is the supremum of the $`c\in[1+1/(4d),\,1+1/d]`$ at which the recursion refutes. (It refutes at the lower end and stops at the upper end, certified by `staircase.py threshold`, which evaluates the recursion on outward-rounded decimal enclosures of the exact endpoints $`1+1/(4d)`$ and $`1+1/d`$.)

`staircase.py threshold` bisects in decimal interval arithmetic with directed rounding, starting from the upper decimal end of the enclosure of $`1+1/(4d)`$ and the lower decimal end of the enclosure of $`1+1/d`$ (where the verdicts are certified by the enclosures), and certifies the verdict at both ends of the final bracket, which are exact decimals: refute at the lower end, stop at the upper end. Two certified opposite verdicts $`10^{-60}`$ apart locate a point where the verdict changes; they are digits of the supremum, and the bisection converges to it, only if the verdict is monotone in $`c`$ (refute below a single boundary, stop above it). We observe this but have not proved it, so the values below are numerical estimates of $`c^{*}_{\mathrm{stair}}(d)`$:
``` math
\begin{aligned}
c^{*}_{\mathrm{stair}}(1)&=1.3092117446776010510221902603497164170365731409176335370894\ldots\\
c^{*}_{\mathrm{stair}}(2)&=1.19159683545302011311694956315014944535226780478297581606997\ldots\\
c^{*}_{\mathrm{stair}}(3)&=1.13865239000087119328135666360349492168754860133162470872070\ldots
\end{aligned}
```
(the digits shared by both ends of the final bracket; 116–149 levels are needed at the bracket ends, and at the lower end the first term of $`r_{h+1}`$ is the maximum at every level $`h+1\ge1`$). The $`d=1`$ certificate of Theorem 2 is about $`4.68\cdot10^{-9}`$ below this estimate of $`c^{*}_{\mathrm{stair}}(1)`$. Numerically, the orbit is of saddle type near the boundary: below it $`cg_h`$ eventually drops below $`1`$; above it $`g_h`$ eventually increases and the staircase stops. We see no reason for $`c^{*}_{\mathrm{stair}}`$ to be algebraic and did not search for a closed form.

Let $`c_h`$ be the point of $`[1+1/(4d),\,1+1/d]`$ found by bisection (in floating point; `staircase.py appear`) at which the predicate “the recursion reaches level $`h`$, or refutes before reaching it” changes from true to false. The predicate is not “level $`h`$ exists”: a refutation stops the recursion, and for instance at $`d=1`$, $`c=5/4`$ level 0 already refutes, while continuing past it would give a level-2 candidate $`r_2=42375/13639>2`$ that fails the existence test. Just below each $`c_h`$ listed here the recursion reaches level $`h`$ without refuting (checked at $`c_h-2\cdot10^{-6}`$), so there the two agree. For $`d=1`$ the estimates are $`c_1,\dots,c_6\approx1.330278`$, $`1.311714`$, $`1.309609`$, $`1.309287`$, $`1.309228`$, $`1.309215`$; they decrease and approach the estimate of $`c^{*}_{\mathrm{stair}}(1)`$, but neither the monotonicity nor the convergence is proved. The first value, $`c_1=1.330277691377`$, $`1.199453639736`$, $`1.142696215782`$ for $`d=1,2,3`$, coincides to the 12 printed digits with the real root in $`[1.1,2]`$ of $`8c^3-2c^2-13c+2`$, $`36c^3-9c^2-46c+6`$ and $`96c^3-20c^2-113c+12`$ respectively (`staircase.py roots`); we have no proof of this identity. Heuristically, a potential with levels $`0,\dots,h`$ (the level values of the staircase) should be valid as long as level $`h+1`$ does not exist, i.e. for $`c\ge c_{h+1}`$. The checked ceilings are consistent with this and lag a little behind: the four-level ceiling for $`d=1`$ is $`1.3094`$, above $`c_4\approx1.309287`$; the three-level ceiling for $`d=2`$ is $`1.192`$, above $`c_3\approx1.191768`$; the two-level ceiling for $`d=3`$ is $`1.1392`$, above $`c_2\approx1.139159`$.

**Conjecture 14**. $`c^*_d=c^{*}_{\mathrm{stair}}(d)`$ for $`d=1,2,3`$.

*Evidence*: the certificates built from the recursion check at $`c`$ about $`4.68\cdot10^{-9}`$, $`3.55\cdot10^{-8}`$ and $`9.00\cdot10^{-8}`$ below the estimates of $`c^{*}_{\mathrm{stair}}(1)`$, $`c^{*}_{\mathrm{stair}}(2)`$ and $`c^{*}_{\mathrm{stair}}(3)`$; and the ceilings, which mirror the levels of the staircase, come down toward it as levels are added ($`\sqrt2`$ with one level, $`1.3094`$ with four, for $`d=1`$). *Caveats*: the recursion is read off from the best proofs found by numerical optimisation, not derived as a theorem; the digits of $`c^{*}_{\mathrm{stair}}`$ are estimates (the verdict’s monotonicity in $`c`$ is not proved); we have not proved that a refuting verdict always yields a proof, or that the shapes of the best proofs found are the shapes of all best proofs; and the ceilings are equally consistent with any value of $`c^*_d`$ in the interval of Corollary 6. The conjecture should be treated as open.

## 8. Consequence for lower bounds

**Corollary 15** (conditional; paper argument). Assume the following results of \[W13\] for the hybrid model with a $`d`$-dimensional tape: Lemma 7.1 (for both quantifiers), Lemma 3.3 applied inside a prefix in the form of Speedup Rule 1 (with output superscript $`\max(b,e)`$ for the new $`\log n`$ block, as its proof gives; item 3 of Section 2.4), Lemma 7.2 (also for $`\log n`$ blocks), Lemma 7.3, the combining of same-type blocks of §2, and Theorem 3.1 with Corollary 3.2. Then $`\mathsf{NTIME}[n]\not\subseteq\mathsf{DTIME}_d[n^{c}]`$ for $`c=1.30921174`$, $`1.1915968`$, $`1.1386523`$ ($`d=1,2,3`$), and hence $`\mathsf{SAT}\notin\mathsf{DTIME}_d[n^{c}]`$ for every $`c<1.30921174`$, $`1.1915968`$, $`1.1386523`$ respectively. In particular $`\mathsf{SAT}\notin\mathsf{DTIME}_1[n^{1.3092}]`$, $`\mathsf{SAT}\notin\mathsf{DTIME}_2[n^{1.1915}]`$ and $`\mathsf{SAT}\notin\mathsf{DTIME}_3[n^{1.1386}]`$.

*Argument.* Under $`H_c`$, each line of a normal-form proof of Theorem 2 is contained in the next by the named lemma (Table 2, with the readings of Section 2.4), so $`\mathsf{DTIME}_d[n^{a}]\subseteq\mathsf{DTIME}_d[n^{a'}]`$ with $`a>a'\ge1`$, contradicting Lemma 7.3. The proof has a fixed finite length, so the $`n^{o(1)}`$ losses of its steps compose to $`n^{o(1)}`$, and $`a-a'`$ is a fixed positive constant. Hence $`\mathsf{NTIME}[n]\not\subseteq\mathsf{DTIME}_d[n^c]`$, which implies the same for every smaller exponent, and Corollary 3.2 of \[W13\] transfers it to SAT up to a polylogarithmic factor. ∎

This is exactly the dependence of \[W13, Theorem 7.5\]. Lemma 7.1 is proved in \[W13\] as a sketch, for $`d=1`$ (the universal case in one sentence) with a further sketch for $`d\ge2`$ (pp. A:29–A:30); Lemma 7.2’s proof “directly follows that of earlier, similar results” (p. A:31); Lemma 7.3 is “analogous” to Lemmas 4.3 and 6.3. The strict-reading proofs also satisfy the condition $`e\le a_{k+1}`$ of \[Wfull, Lemma 5.2\] and kernel time $`\ge`$ input length on every line. Our proofs use the lemmas only in configurations that occur in Williams’s printed proofs, but many more times (constant in $`n`$, though astronomically large). The normal-form theorem, Theorem 7.4, is not needed for the corollary, because the proofs are already in normal form; it is needed to read the ceilings as statements about all alternation-trading proofs.

## 9. What is and is not verified

**(a) Kernel-checked.**

Lean 4.31.0 with Mathlib (pinned revision). The library builds with no `sorry`, no `admit`, no `native_decide` and no new axioms; `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for every headline theorem (`Axioms.lean` in `PastaMath/OneTapeThreshold/`). The certificates are checked with `decide +kernel`, which adds no axiom. Checked are: Theorems 2, 3, 4, 5 and Corollary 6 for the formal calculus; the soundness of the three checkers (`HY.nfCheck_sound`, `HD.dagCheck_sound`, `HDS.dagCheck_sound`; the DAG checkers also for every output $`\ell`$ of the new $`\log n`$ block with $`1\le\ell\le\max(o,e)`$, `HD.dagCheck_soundO`, `HDS.dagCheck_soundO`, which gives the staircase proofs in the calculus with output exactly $`1`$, `conjecture_fails_one`) and of the abstraction (`HLM.absCheck_sound`); the simulation `HL.sim`; the removal of the inclusion $`\mathsf{DTIME}_d[t]\subseteq\mathsf{DTISP}[t,t]`$ from relaxed paths (`HL.widen_dec`, `HL.path_unwiden`); the monotonicity of the potentials along relaxed steps and of the relaxed calculus in $`c`$; and the root bounds for $`p_d`$.

**(b) Not machine-checked.**

- *That the formal rules are Williams’s.* This is a modelling claim, compared rule by rule in Table 2, with the reading choices of Section 2.4 and the calibration of Section 2.5. The constructions use only `HY.Step` (and its variant `HY.StepO (fun _ _ => 1)` for `conjecture_fails_one`); the ceilings are proved for the relaxation of Section 5.1 (extended by the inclusion), with the gaps listed in Section 6, and for the reading $`\max(b,e)`$ of the output superscript of the new $`\log n`$ block of Lemma 3.3. Under the smaller superscript displayed in the sketch of Theorem 7.9 only the closed-form ceiling is proved, for strict normal-form proofs (item 3 of Section 2.4); the existence of the staircase proofs is proved there too, that of the 39-line proof is only replayed by a script. The ceilings also assume that Lemma 7.2 outputs a $`\mathsf{DTIME}_d`$ kernel (item 6).

- *Soundness of Williams’s lemmas* (Section 8) and Corollary 15. We do not formalise complexity classes.

- *The staircase recursion, $`c^{*}_{\mathrm{stair}}`$ and Conjecture 14* (Section 7.2): numerics. The 58–59-digit values are numerical estimates: the recursion’s verdicts at the two ends of the final bracket are certified by interval arithmetic, but reading the shared digits as digits of $`c^{*}_{\mathrm{stair}}`$ assumes that the verdict is monotone in $`c`$, which is not proved; and they are statements about the recursion, not about the calculus.

- *The generators* (`stair_cert.py` and the search for the potential parameters) are untrusted; only acceptance of their output by the Lean checkers matters.

- The scripts in `scripts/` use exact rational arithmetic, except `staircase.py` (floating point, and decimal interval arithmetic with outward rounding for the threshold) and the bisections for displayed roots; `replay39.py` and `w13_25line.py` are written from Williams’s text, `dag_check.py` and `abs_check.py` from the Lean definitions. None is part of the kernel-checked results.

**(c) Scope.**

The results are about one proof calculus, the one of \[W13, §7\] as formalised, with the variants of Section 6. They say nothing about lower bounds for SAT on these machines proved by other methods.

## 10. Relation to earlier work

For $`d=1`$, \[W13, p. A:31\] recalls that Kannan proved $`\mathsf{NTIME}[n]\not\subseteq\mathsf{DTIME}_1[n^{\sqrt[4]{3/2}}]`$, and that the argument with Lemmas 7.1 and 3.3 gives $`\sqrt{3/2}`$, “the SAT lower bound proved by Van Melkebeek and Raz” \[vMR05\]; for general $`d`$ the previous bound was $`\sqrt{(d+2)/(d+1)}`$ (p. A:3). Williams \[W13\] obtained $`r_d`$ (Theorem 7.5) and the limit $`1+1/(d+1)`$ for the calculus (Theorem 7.9). Theorem 2 improves $`r_d`$ to $`1.30921174`$, $`1.1915968`$, $`1.1386523`$, conditionally on the same lemmas, and for the formal calculus Theorem 4 lowers the limit to $`1.3094`$, $`1.192`$, $`1.1392`$ (for our reading of the $`\log n`$ superscript), and Theorem 5 lowers it, for strict normal-form proofs, to $`\sqrt{1+1/d}`$ for every real $`d\ge1`$, in particular every integer dimension, the setting of Williams’s theorem. The formal ceiling $`c^2\ge1+1/d`$ holds for every real $`d>0`$, but it improves on $`1+1/(d+1)`$ only for larger $`d`$: at $`d=1/2`$, $`\sqrt3>5/3`$. For the $`\mathsf{DTS}`$ setting of \[W13, §4\], Buss and Williams \[BW15\] proved that $`2\cos(\pi/7)`$ is optimal for alternation-trading proofs.

## Licence

This text is licensed under CC BY 4.0. The Lean code and the scripts are licensed under the Apache License 2.0.

## References

- \[BW15\] S. R. Buss and R. Williams. Limits on alternation trading proofs for time–space lower bounds. *Computational Complexity*, 24(3):533–600, 2015. [doi:10.1007/s00037-015-0104-9](https://doi.org/10.1007/s00037-015-0104-9).
- \[vMR05\] D. van Melkebeek and R. Raz. A time lower bound for satisfiability. *Theoretical Computer Science*, 348(2–3):311–320, 2005.
- \[Wfull\] R. R. Williams. Automated proofs of time lower bounds. Long version of \[W13\], Carnegie Mellon University, <https://www.cs.cmu.edu/~ryanw/automated-lbs-full.pdf>. Its §5 treats the hybrid model with $`d=1`$; we cite its Lemma 5.2 and the end of §5.
- \[W13\] R. Williams. Alternation-trading proofs, linear programming, and lower bounds. *ACM Transactions on Computation Theory*, 5(2):Article 6, 1–49, 2013. [doi:10.1145/2493246.2493249](https://doi.org/10.1145/2493246.2493249). Author copy: <https://people.csail.mit.edu/rrw/automated-lbs.pdf>, whose page numbers (A:1–A:40) we use.
