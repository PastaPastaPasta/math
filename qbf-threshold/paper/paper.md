# The alternation-trading calculus for QBF_k versus DTS stops at Williams's exponent: a kernel-checked limit

**PastaPastaPasta** · November 2026

*Markdown rendering of `paper.tex`, which is the reference version.*

## Abstract

Williams \[W13, Section 5\] applies alternation-trading proofs to show that for every integer $`k\ge1`$, $`\mathsf{QBF}_k\notin\mathsf{DTS}[n^c]`$ whenever $`c>k`$ satisfies $`c^3/k-c^2-2c+k<0`$ (Theorem 5.1). For $`k=1`$ ($`\mathsf{SAT}`$ versus $`\mathsf{DTS}[n^c]`$), the unique root in $`(1,2)`$ is $`r_1=2\cos(\pi/7)\approx1.801938`$, which Buss and Williams \[BW15\] proved is the exact limit of the alternation-trading calculus. For general $`k\ge2`$, Williams’s exponents are $`c_2\approx2.903212`$, $`c_3\approx3.942820`$, $`c_4\approx4.962389`$, and so on, and no upper limit for the $`k`$-block calculus was established.

We prove in Lean 4 that for every integer $`k\ge1`$, a formalisation `QStep` of the $`\mathsf{QBF}_k`$ alternation-trading calculus has no refutation for any $`c>k`$ with $`c^3/k-c^2-2c+k\ge0`$ (that is, $`c\ge c_k`$), and strictly above $`c_k`$ excludes even non-strict refutations ($`a'\le a_0`$ from $`a_0>0`$ in at least one step). The proof constructs a $`k`$-parametric grouping potential over partitions of the quantifier stack into consecutive pop groups of size $`1,\dots,k`$; at $`k=1`$ it recovers the Buss–Williams bound $`2\cos(\pi/7)`$ directly. On the lower side, we provide a rational transcription `checkL` of Williams’s literal rules, prove its soundness into `QStep`, and kernel-check explicit refutation certificates at $`c=7/4`$ ($`k=1`$), $`c=289/100`$ ($`k=2`$), $`c=393/100`$ ($`k=3`$), and $`c=989/200`$ ($`k=4`$), bracketing the formal thresholds in $`[1.75, c_1]`$, $`[2.89, c_2]`$, $`[3.93, c_3]`$, and $`[4.945, c_4]`$.

*What is kernel-checked:* the upper limit $`c\ge c_k`$ for all $`k\ge1`$ (and non-strict exclusion for $`c>c_k`$), the equality $`c_1=2\cos(\pi/7)`$, the soundness of the literal checker `checkL` into `QStep`, and the four literal refutation certificates. *What is not machine-checked:* that the formal rules coincide with Williams’s brief prose description in \[W13, Section 5\] (a modelling claim set out in Section 2), Williams’s own parametric family achieving every $`c<c_k`$, and the complexity-theoretic simulation lemmas underlying \[W13\]. The limit applies only to this formal calculus.

## 1. Introduction

**Background.**

In \[W13\], Williams formalised alternation-trading proofs for deterministic time–space lower bounds of the form $`\mathsf{SAT}\notin\mathsf{DTS}[n^c]`$ (time $`n^{c+o(1)}`$, space $`n^{o(1)}`$) and extended them in Section 5 to quantified Boolean formulas with $`k`$ alternating quantifier blocks ($`\mathsf{QBF}_k`$). Theorem 5.1 of \[W13\] establishes $`\mathsf{QBF}_k\notin\mathsf{DTS}[n^c]`$ for every $`c<c_k`$, where $`c_k`$ is the unique root in $`(k,k+1)`$ of
``` math
p_k(c) := \frac{c^3}{k} - c^2 - 2c + k = 0.
```
Table 1 lists the roots $`c_k`$ and our kernel-checked certificate values for $`k=1,2,3,4`$. In the CMU full version of \[W13\] (end of Section 3), Williams remarked empirically that automated search did not find a better lower bound than $`c_k`$, though Section 5 of \[W13\] states no formal optimality theorem or conjecture. For $`k=1`$, Buss and Williams \[BW15\] proved that $`c_1=2\cos(\pi/7)`$ is indeed the exact limit of the calculus.

| $`k`$ | Williams root $`c_k`$ | $`q_k = k/c_k`$ | Certified $`c`$ | Lines | Final $`a'/a_0`$ | Lean certificate |
|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| 1 | $`1.801938`$ | $`0.554958`$ | $`7/4 = 1.75`$ | 140 | $`0.801670`$ | `qcert1_ok` |
| 2 | $`2.903212`$ | $`0.688892`$ | $`289/100 = 2.89`$ | 324 | $`0.970106`$ | `qcert2_ok` |
| 3 | $`3.942820`$ | $`0.760877`$ | $`393/100 = 3.93`$ | 432 | $`0.983568`$ | `qcert3_ok` |
| 4 | $`4.962389`$ | $`0.806063`$ | $`989/200 = 4.945`$ | 540 | $`0.969004`$ | `qcert4_ok` |

*Table 1: Williams’s $`\mathsf{QBF}_k`$ exponents $`c_k`$ (roots of $`c^3/k-c^2-2c+k=0`$ in $`(k,k+1)`$) and our kernel-checked literal certificates.*

**Results.**

We determine the upper limit of the formal $`\mathsf{QBF}_k`$ alternation-trading calculus for every $`k\ge1`$ in Lean 4:

1.  For every integer $`k\ge1`$ and every real $`c>k`$ with $`c^3/k-c^2-2c+k\ge0`$, no path in the relaxed calculus `QStep` from $`\mathsf{DTS}[n^{a_0}]`$ ($`a_0\ge0`$) back to a quantifier-free line $`\mathsf{DTS}[n^{a'}]`$ achieves $`a'<a_0`$ (`qbf_no_refutation`, `qbf_no_refutation_reach`, `not_refutes`).

2.  When $`c^3/k-c^2-2c+k>0`$, even non-strict refutations ($`a'\le a_0`$ from $`a_0>0`$ in at least one step) are impossible (`qbf_no_refutation_strict`).

3.  At $`k=1`$, the unique threshold parameter satisfies $`c=2\cos(\pi/7)`$ (`par_one_eq_r7`), recovering the Buss–Williams bound for $`\mathsf{SAT}`$ versus $`\mathsf{DTS}`$ (`sat_no_refutation`).

4.  For $`k=1,2,3,4`$, literal refutations checked by `checkL` (tracking guesses, input floor $`1`$, and $`x\le a-1`$) verify the lower endpoints $`c=7/4, 289/100, 393/100, 989/200`$ via `decide +kernel`, with soundness proved into `QStep` (`checkL_sound`, `interval_k1`–`interval_k4`).

**AI assistance.**

The proofs and Lean formalisation were produced with AI assistance under the author’s direction. The kernel-checked Lean proofs in `PastaMath/QbfThreshold/` are the primary evidence for the theorems about the formal calculus.

## 2. The calculus

### 2.1 Transcription from Williams (TOCT 2013, Section 5)

Williams \[W13, Section 5\] describes the $`\mathsf{QBF}_k`$ calculus in one sentence: only the Slowdown Rule differs from the $`\mathsf{SAT}`$ calculus (Definition 4.1 of \[W13\]), because its application removes up to $`k`$ quantifier blocks instead of just one.

A literal line is an alternating class
``` math
(Q_1\,n^{a_1})^{b_2}(Q_2\,n^{a_2})^{b_3}\cdots(Q_m\,n^{a_m})^{b_{m+1}}\;\mathsf{DTS}[n^{a_{m+1}}]
```
with input superscript $`b_1=1`$. Speedup Rules 0 and 1 are unchanged from \[W13, Definition 4.1\] (Rule 2 is two applications of Rule 1 with $`x=0`$ and $`x`$, giving the same line): for $`0\le x\le a-1`$,

- if $`m=0`$, $`\mathsf{DTS}[n^a]`$ goes to $`(Q\,n^x)^{\max(x,1)}(Q'\,n^0)^1\mathsf{DTS}[n^{a-x}]`$;

- if $`m>0`$, the innermost block $`(Q_m\,n^{a_m})^{b_{m+1}}`$ becomes $`(Q_m\,n^{\max(a_m,x)})^{\max(x,b_{m+1})}(Q'\,n^0)^{b_{m+1}}`$ and the kernel becomes $`a-x`$.

The $`\mathsf{QBF}_k`$ slowdown removes $`j`$ innermost blocks ($`1\le j\le\min(k,m)`$) and replaces the kernel by
``` math
c\cdot\max\{a_{m+1},\; b_{m-j+1},\; a_i, b_{i+1} \text{ for } m-j+1\le i\le m\},
```
where $`b_{m-j+1}`$ is the superscript in front of the outermost removed block (the input length of the removed $`\Sigma_j`$/$`\Pi_j`$ subcomputation). This is the literal checker `stepL` and `checkL` in `CertDefs.lean`, which uses exact rational arithmetic and requires normal form (no intermediate quantifier-free lines).

### 2.2 The relaxed calculus `QStep`

For the upper limit, we drop guess exponents (which never exceed their after-superscripts in legal literal lines), replace the input floor $`1`$ by $`0`$, allow $`0\le x\le a`$, and allow every output exponent to be raised arbitrarily (weakening). A line in `Calculus.lean` is a pair `QLine` $`= \mathrm{List}\;\mathbb{R} \times \mathbb{R}`$ storing the stack of after-superscripts *innermost first* together with the kernel exponent $`a`$. Write $`\operatorname{front}([]):=0`$, $`\operatorname{front}(b::l):=b`$, and $`\operatorname{lmax}(l):=\max(\{0\}\cup l)`$.

**Definition 1** (Relaxed step `QStep`). Fix $`c\in\mathbb{R}`$ and $`k\in\mathbb{N}`$. A step `QStep c k` is either:

1.  **Speedup** (`QStep.speed`): from $`(\mathrm{st},a)`$ with $`0\le x\le a`$, move to $`(b_2::b_1::\mathrm{st.tail},\; a_2)`$ whenever $`\max(x,\operatorname{front}(\mathrm{st}))\le b_1`$, $`\operatorname{front}(\mathrm{st})\le b_2`$, and $`a-x\le a_2`$.

2.  **Slowdown** (`QStep.pop`): from $`(\mathrm{rem}\mathbin{++}\mathrm{rest},\; a)`$ with $`1\le |\mathrm{rem}|\le k`$, move to $`(\mathrm{rest},\; e)`$ whenever $`c\cdot\max(a,\;\operatorname{lmax}(\mathrm{rem}),\;\operatorname{front}(\mathrm{rest}))\le e`$.

Note that when $`\mathrm{st}=[]`$, $`\mathrm{st.tail}=[]`$ and $`\operatorname{front}(\mathrm{st})=0`$, so `QStep.speed` creates two blocks $`(b_2, b_1)`$ with $`x\le b_1`$ and $`0\le b_2`$ in a single step, matching Speedup Rule 0.

**Proposition 2** (Soundness of the literal checker; `checkL_sound`). If $`c\in\mathbb{Q}_{\ge0}`$ and `checkL c k a0 ops = true`, then there exists $`a'\in\mathbb{R}`$ with $`0\le a_0`$, $`a'<a_0`$, and a `QStep c k` path from $`([],a_0)`$ to $`([],a')`$.

## 3. Threshold parameterisation and grouping potential

### 3.1 The threshold parameters `Par`

Fix $`k\ge1`$. Set $`q:=k/c`$. The equation $`p_k(c)=0`$ is equivalent to the pair of identities
``` math
q\cdot c = k, \qquad c - k = q(2-q), \qquad 0 < q < 1
```
stored in the Lean structure `Par`. Indeed, substituting $`c=k+q(2-q)`$ into $`q c = k`$ yields $`k(1-q)=q^2(2-q)`$, whose right-hand side minus left-hand side is $`-k<0`$ at $`q=0`$ and $`1>0`$ at $`q=1`$.

**Lemma 3** (Existence and monotonicity; `exists_par`, `ge_of_poly`, `par_one_eq_r7`). For every integer $`k\ge1`$ there exists $`P:\texttt{Par}`$ with $`P.k=k`$, satisfying $`p_k(P.c)=0`$ and $`k<P.c\le k+1`$. Every $`c>k`$ with $`p_k(c)\ge0`$ satisfies $`P.c\le c`$. When $`k=1`$, $`P.c=2\cos(\pi/7)`$.

### 3.2 The grouping potential

Fix $`P:\texttt{Par}`$ with $`k=P.k`$, $`c=P.c`$, $`q=P.q`$. Define the two auxiliary functions (`Lam`, `Lf`):
``` math
\Lambda(s,e) := \min\!\bigl(e,\;\max(q(s+e),\; cs)\bigr), \qquad
L_r(s,e) := \max\!\left(s,\;\frac{\Lambda(s,e)}{r+1}\right) \quad (r\in\mathbb{N}).
```
A *valid grouping* $`g=[h_1,\dots,h_t]`$ of a stack $`\mathrm{st}`$ (`Valid k g st`) partitions $`\mathrm{st}`$ from innermost to outermost into consecutive blocks of lengths $`1\le h_i\le k`$. Its value `val P st g a` is defined recursively by $`\texttt{val}(\mathrm{st}, [], a) = a`$ and
``` math
\begin{aligned}
&\;\texttt{val}(\mathrm{st}, h::g, a) := \\
&\quad \texttt{val}\!\Bigl(\mathrm{st.drop}\;h,\; g,\; c\cdot\max\bigl(\operatorname{lmax}((\mathrm{st.take}\;h).\mathrm{tail}),\; \operatorname{front}(\mathrm{st.drop}\;h),\; L_{k-h}(\operatorname{front}(\mathrm{st}), a)\bigr)\Bigr).
\end{aligned}
```
Intuitively, a valid grouping anticipates how the remaining blocks on the stack will eventually be popped in groups of size at most $`k`$; a group of size $`h<k`$ still has $`r=k-h`$ spare slots that can absorb future speedups before the group is popped, reducing the effective kernel by the factor $`1/(r+1)`$ inside $`L_r`$.

**Lemma 4** (Core inequalities; `key`, `lf_S`, `lf_E`, `top_eq`). For all $`s,x,D,K\ge0`$:

1.  (`key`) If $`K\ge c\cdot\max(\max(x,s),\;\Lambda(s,D)/k)`$, then $`\Lambda(s, x+D)\le \Lambda(\max(x,s), K)`$.

2.  (`lf_S`) For every $`r\in\mathbb{N}`$, if $`K\ge c\cdot\max(\max(x,s),\;L_{k-1}(s,D))`$, then $`L_r(s,x+D)\le L_r(\max(x,s),K)`$.

3.  (`lf_E`) For every $`r\ge1`$, $`L_r(s,x+D)\le \max(\max(x,s),\; L_{r-1}(s,D))`$.

4.  (`top_eq`) For every $`a\ge0`$, $`c\cdot L_{k-1}(0, a) = a`$.

**Theorem 5** (Step monotonicity; `step_pot`). Let $`L,L':\texttt{QLine}`$ with $`L`$ nonnegative (`NN L`) and `QStep P.c P.k L L'`. For every valid grouping $`g'`$ of $`L'.1`$, there exists a valid grouping $`g`$ of $`L.1`$ such that
``` math
\texttt{val}(P, L.1, g, L.2) \le \texttt{val}(P, L'.1, g', L'.2).
```

*Proof idea.* For a slowdown popping $`j\in\{1,\dots,k\}`$ blocks from $`L.1=\mathrm{rem}\mathbin{++}\mathrm{rest}`$, prepend $`j`$ to $`g'`$: the outermost values match because $`L_{k-j}(\operatorname{front}(\mathrm{rem}),a)\le\max(\operatorname{front}(\mathrm{rem}),a)\le\max(a,\operatorname{lmax}(\mathrm{rem}),\operatorname{front}(\mathrm{rest}))`$. For a speedup pushing a new block onto a nonempty stack, inspect the innermost group size $`h`$ of $`g'`$: if $`h=1`$, the new block forms its own group and Lemma 4(`lf_S`) applies; if $`h\ge2`$, removing the new block shrinks the group to size $`h-1`$ and Lemma 4(`lf_E`) applies. When $`L.1=[]`$, the new stack has length $`2`$, and `top_eq` collapses the two possible groupings ($`[1,1]`$ or $`[2]`$ when $`k\ge2`$) directly to $`a`$. ∎

## 4. Main theorems

By induction along a path using Theorem 5 and monotonicity of `QStep` in $`c`$ (`qstep_restrict`), starting from $`L_0=([],a_0)`$ and ending at $`L_n=([],a')`$ (where the unique valid grouping is $`[]`$, with value $`a'`$), we obtain $`a_0\le a'`$.

**Theorem 6** (Upper limit for all $`k\ge1`$; `qbf_no_refutation`, `qbf_no_refutation_strict`). Let $`k\ge1`$ be an integer and let $`c\in\mathbb{R}`$ with $`c>k`$.

1.  If $`c^3/k - c^2 - 2c + k \ge 0`$, then every `QStep c k` path from $`([],a_0)`$ ($`a_0\ge0`$) to $`([],a')`$ satisfies $`a_0\le a'`$.

2.  If $`c^3/k - c^2 - 2c + k > 0`$, then every nonempty `QStep c k` path ($`n\ge1`$) from $`([],a_0)`$ ($`a_0>0`$) to $`([],a')`$ satisfies $`a_0 < a'`$.

For $`k=1,2,3,4`$, `Cert.lean` encodes four literal refutations from Williams’s recursive word family, verified in the Lean kernel with `decide +kernel` (`qcert1_ok`–`qcert4_ok`). Combining Proposition 2, downward monotonicity in $`c`$ (`refutes_mono`), and Theorem 6 gives the bracketed intervals in `Summary.lean`:

**Theorem 7** (Certified threshold intervals; `interval_k1`–`interval_k4`, `cert_below`). Define `Refutes c k` to hold when there exist $`0\le a_0`$ and $`a'<a_0`$ with a `QStep c k` path from $`([],a_0)`$ to $`([],a')`$. Then:

- $`k=1`$: `Refutes c 1` holds for $`0\le c\le 7/4`$ and fails for $`c\ge 2\cos(\pi/7)`$;

- $`k=2`$: `Refutes c 2` holds for $`0\le c\le 289/100`$ and fails for $`c>2`$ with $`c^3/2-c^2-2c+2\ge0`$;

- $`k=3`$: `Refutes c 3` holds for $`0\le c\le 393/100`$ and fails for $`c>3`$ with $`c^3/3-c^2-2c+3\ge0`$;

- $`k=4`$: `Refutes c 4` holds for $`0\le c\le 989/200`$ and fails for $`c>4`$ with $`c^3/4-c^2-2c+4\ge0`$.

## 5. Scope and limitations

- **Modelling claim.** Williams \[W13, Section 5\] states the $`\mathsf{QBF}_k`$ slowdown only briefly in prose. Our literal checker `checkL` generalizes \[W13, Definition 4.1\] directly, retaining the in-front superscript $`b_{m-j+1}`$ (as in Williams’s Table I LP for $`k=1`$). Dropping guess exponents and input floors in `QStep` only enlarges the set of proofs, so the impossibility theorem covers any tighter literal reading.

- **Lower side for general $`k`$.** Williams’s Theorem 5.1 gives a paper construction achieving every $`c<c_k`$ for all $`k\ge1`$; we kernel-check four explicit rational instances ($`k=1,2,3,4`$) rather than formalising the general parametric family.

- **What is outside the formalisation.** Soundness of the complexity-theoretic speedup and slowdown lemmas, rules beyond Speedup Rules 0–2 and $`k`$-block Slowdown, and lower bounds obtained outside this calculus are not formalised.

## References

- \[BW15\] S. Buss and R. Williams, *Limits on alternation-trading proofs for time-space lower bounds*, Computational Complexity **24** (2015), 533–600.
- \[W13\] R. Williams, *Alternation-trading proofs, linear programming, and lower bounds*, ACM Transactions on Computation Theory **5** (2013), no. 2, Article 6 (and CMU full version).
