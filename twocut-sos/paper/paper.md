# Two-cut rank, partial-transpose rank, and sum-of-squares complexity of biquadratic forms

**PastaPastaPasta** · November 2026

*Markdown rendering of `paper.tex`, which is the reference version.*

## Abstract

We study the *two-cut rank* $`\operatorname{TC}_\mathbb{K}(M) := \min\{\operatorname{rank} A + \operatorname{rank} W : M = A + W^\Gamma\}`$ of an $`rs \times rs`$ matrix $`M`$ under the partial transpose $`(\cdot)^\Gamma`$, and its relation to the *partial-transpose rank* $`\operatorname{PT\text{-}rank}_\mathbb{K}(M)`$ of Rossman and Zhu [RZ25], the bilinear product complexity $`\operatorname{Prod}_\mathbb{K}(Q_M)`$, and the sum-of-squares complexity $`\operatorname{SoS}_\mathbb{K}(Q_M)`$ of the associated biquadratic form $`Q_M(x, y) = \sum M_{(a,b),(c,d)} x_a x_c y_b y_d`$. All theorems in this paper are unconditional and kernel-checked end-to-end in Lean 4 with Mathlib (library `PastaMath.TwoCutSoS`).

1. **Exact dictionary and refutation of Rossman–Zhu §3.2.** Over every field $`\mathbb{K}`$, $`\operatorname{PT\text{-}rank}_\mathbb{K}(M) = \operatorname{TC}_\mathbb{K}(M)`$ and $`\operatorname{Prod}_\mathbb{K}(Q_M) \le \operatorname{TC}_\mathbb{K}(M)`$. When $`\operatorname{char}\mathbb{K} \neq 2`$ and $`M`$ is fully symmetric, $`\operatorname{TC}_\mathbb{K}(M) \le 2\operatorname{SoS}_\mathbb{K}(Q_M)`$ and $`\operatorname{TC}_\mathbb{K}(M) \le 4\operatorname{Prod}_\mathbb{K}(Q_M)`$. When $`\operatorname{char}\mathbb{K} \neq 2`$ and $`\sqrt{-1} \in \mathbb{K}`$ (for arbitrary $`M`$), $`\operatorname{SoS}_\mathbb{K}(Q_M) \le 2\operatorname{Prod}_\mathbb{K}(Q_M) \le 2\operatorname{TC}_\mathbb{K}(M) = 2\operatorname{PT\text{-}rank}_\mathbb{K}(M)`$. We exhibit explicit matrices ($`M_1, M_3 \in M_4(\mathbb{K})`$ and $`M_2 \in M_{16}(\mathbb{K})`$) refuting the printed statements of [RZ25, Lemma 3.13] ($`\operatorname{SoS}(Q_M) \le \operatorname{PT\text{-}rank}(M)`$) and both inequalities of [RZ25, Proposition 3.16] ($`\operatorname{SoS}(Q_M) - 1 \le \operatorname{PT\text{-}rank}(M) \le 2^{d-1}\operatorname{SoS}(Q_M)`$) at $`d = 2`$ over every field of characteristic $`\neq 2`$, and show that the repaired factor $`2`$ in $`\operatorname{SoS}_\mathbb{K}(Q_M) \le 2\operatorname{PT\text{-}rank}_\mathbb{K}(M)`$ is tight for general $`M`$. Whether $`\operatorname{SoS}_\mathbb{K}(Q_M) \le \operatorname{PT\text{-}rank}_\mathbb{K}(M)`$ holds for *fully symmetric* $`M`$ over algebraically closed fields remains open.
2. **Characteristic-free crossing bounds.** For the identity matrix $`I_{rs}`$ (corresponding to the Hurwitz biquadratic form $`X_{r,s} = (\sum_{i=1}^r x_i^2)(\sum_{j=1}^s y_j^2)`$), over *every* field $`\mathbb{K}`$ including $`\operatorname{char}\mathbb{K} = 2`$: $`\operatorname{TC}_\mathbb{K}(r,s) \ge \max(r,s)`$; $`\operatorname{TC}_\mathbb{K}(r,s) \ge \max(r,s) + 1`$ whenever $`r,s \ge 3`$; $`\operatorname{TC}_\mathbb{K}(2,s) = 2\lceil s/2\rceil`$; $`\operatorname{TC}_\mathbb{K}(r,s) \le 1 + rs - \binom{\min(r,s)+1}{2}`$; and hence $`\operatorname{TC}_\mathbb{K}(3,3) = 4`$.
3. **Explicit exact and border witnesses.** Over every field $`\mathbb{K}`$, explicit $`\pm 1`$ decompositions give $`\operatorname{TC}_\mathbb{K}(4,5) \le 8`$, $`\operatorname{TC}_\mathbb{K}(4,6) \le 8`$, and $`\operatorname{TC}_\mathbb{K}(8,8) \le 16`$, and a pole-order-2 border decomposition gives $`\underline{\operatorname{TC}}_{\mathbb{K},2}(4,4) \le 6`$. Over $`\operatorname{char}\mathbb{K} \neq 2`$, $`n`$ anticommuting involutions in $`M_d(\mathbb{K})`$ yield $`\operatorname{TC}_\mathbb{K}(d,n) \le 2d`$; over every field $`\mathbb{K}`$, a pole-order-$`k`$ border two-cut decomposition of $`I_{rs}`$ of ranks $`a + b`$ yields $`\operatorname{TC}_\mathbb{K}(r,s) \le (k+1)(a+b)`$.
4. **Word-span tensor powers of reflection-type decompositions.** For any reflection-type decomposition ($`\operatorname{spec} M = \{0^{D-n}, \lambda^n\}`$, $`\operatorname{spec} M^\Gamma = \{1^{D-n}, (1-\lambda)^n\}`$, $`D = rs`$, $`p = n/D`$, $`\lambda = 1/(2p)`$), word-span decompositions of $`K`$-th tensor powers reduce to a weighted uncertainty problem for the $`p`$-biased reflection operator $`T_{-1} = E_1(p)^{\otimes K}`$ in $`L^2(\mu_p)`$. When $`\lambda = a/b`$ with a prime $`\ell \mid (a-b)`$ and $`\ell \nmid a`$, we prove a *Valuation Theorem*: for every $`K`$, no $`\mathbb{Z}_{(\ell)}`$-linear word combination beats the Bayes error $`\sum_T \min(\mu_p(T), \mu_{1-p}(T))`$, attained exactly by the layer grouping. Finally, via tensorising Farkas-certificate packings—parametric at $`K = 1, 2`$ together with a kernel-checked 22-certificate rational packing of exact value $`57/256`$ at $`K = 4, p = 1/4`$—we prove that for every shape $`r,s \ge 2`$ and every reflection-type decomposition over $`\mathbb{R}`$, no word-span tensor power achieves asymptotic rate $`\le \sqrt{1+q^2}`$ ($`q = \log\min(r,s)/\log\max(r,s)`$).

*What is kernel-checked:* every theorem and counterexample stated above, with zero `sorry`, zero `native_decide`, and only the standard axioms `[propext, Classical.choice, Quot.sound]`. *What is not machine-checked:* the Kronecker-product simultaneous-diagonalisation bridge identifying the matrix rank of a $`K`$-th word-span tensor power with $`D^K \varphi_K(p; h)`$ is proved on paper; furthermore, the word-span no-go theorem applies to word-span decompositions of reflection-type diagonalisable bases over $`\mathbb{R}`$ and does not rule out general (non-word-span) decompositions, non-reflection spectra, non-diagonalisable bases, or border families.

## 1. Introduction

**Background.** For a biquadratic form $`Q(x,y)`$ in variables $`x = (x_1,\dots,x_r)`$ and $`y = (y_1,\dots,y_s)`$ over a field $`\mathbb{K}`$, its *sum-of-squares (SoS) complexity* $`\operatorname{SoS}_\mathbb{K}(Q)`$ is the minimum $`c`$ such that $`Q(x,y) = \sum_{k=1}^c L_k(x,y)^2`$ with each $`L_k`$ bilinear, and its *bilinear product complexity* $`\operatorname{Prod}_\mathbb{K}(Q)`$ is the minimum $`c`$ such that $`Q(x,y) = \sum_{k=1}^c U_k(x,y) V_k(x,y)`$ with $`U_k, V_k`$ bilinear. Hrubeš, Wigderson and Yehudayoff [HWY11] proved that a superlinear lower bound $`\operatorname{SoS}_\mathbb{C}(Q) = n^{1+\Omega(1)}`$ for an explicit biquadratic form implies exponential lower bounds for non-commutative arithmetic circuits. Rossman and Zhu [RZ25] extended this connection to $`d`$-multiquadratic forms and $`\mathrm{VNC}^1 \neq \mathrm{VNP}`$, introducing the *partial-transpose rank* $`\operatorname{PT\text{-}rank}_\mathbb{K}(M)`$ of the coefficient matrix $`M`$ representing $`Q`$.

For the canonical Hurwitz form $`X_{r,s}(x,y) = (\sum_{i=1}^r x_i^2)(\sum_{j=1}^s y_j^2)`$ (represented by $`M = I_{rs}`$), classical Hurwitz–Radon composition gives $`\operatorname{SoS}_\mathbb{R}(X_{r,s}) = r`$ only for Hurwitz–Radon pairs, while over $`\mathbb{C}`$ the asymptotic exponent $`\lim_{N\to\infty} \log_N \operatorname{SoS}_\mathbb{C}(X_{N,N}) \le \sqrt{2}`$ was recently established by Siemaszko [Sie26] (we make no priority claim on that square exponent). A natural programme for understanding both lower bounds and rectangular exponents $`\tau(q)`$ (where $`r = N`$, $`s = N^q`$, $`0 < q \le 1`$, and the square-derived benchmark is $`\sqrt{1+q^2}`$) is to work directly with the matrix *two-cut rank*

```math
\operatorname{TC}_\mathbb{K}(M) := \min\bigl\{\operatorname{rank} A + \operatorname{rank} W : A, W \in \mathbb{K}^{(r\times s)\times(r\times s)},\; M = A + W^\Gamma\bigr\},
```

where $`(W^\Gamma)_{(a,b),(c,d)} := W_{(a,d),(c,b)}`$ is the partial transpose on the second index.

**Overview of results.** All theorem names in code font refer to the Lean 4 library `PastaMath.TwoCutSoS`; Section 6 gives the complete theorem-to-Lean index.

- **Section 2 (Dictionary and Rossman–Zhu §3.2).** We prove $`\operatorname{PT\text{-}rank}_\mathbb{K}(M) = \operatorname{TC}_\mathbb{K}(M)`$ (`hasPTRank_iff_hasTwoCut`) and $`\operatorname{Prod}_\mathbb{K}(Q_M) \le \operatorname{TC}_\mathbb{K}(M)`$ (`prod_of_twoCut`) over every field $`\mathbb{K}`$; $`\operatorname{TC}_\mathbb{K}(M) \le 2\operatorname{SoS}_\mathbb{K}(Q_M)`$ and $`\operatorname{TC}_\mathbb{K}(M) \le 4\operatorname{Prod}_\mathbb{K}(Q_M)`$ for fully symmetric $`M`$ when $`\operatorname{char}\mathbb{K} \neq 2`$ (`twoCut_of_sos`, `twoCut_of_prod`); and $`\operatorname{SoS}_\mathbb{K}(Q_M) \le 2\operatorname{Prod}_\mathbb{K}(Q_M) \le 2\operatorname{TC}_\mathbb{K}(M) = 2\operatorname{PT\text{-}rank}_\mathbb{K}(M)`$ when $`\operatorname{char}\mathbb{K} \neq 2`$ and $`\sqrt{-1} \in \mathbb{K}`$ (`sos_of_prod`, `sos_of_twoCut`, `sos_of_ptRank`). We then construct three explicit matrices ($`M_1, M_3 \in M_4(\mathbb{K})`$ and $`M_2 \in M_{16}(\mathbb{K})`$) refuting the printed statements of [RZ25, Lemma 3.13] and both sides of [RZ25, Proposition 3.16] at $`d = 2`$ over every field of characteristic $`\neq 2`$ (`rz_lemma313_counterexample`, `rz_prop316_left_counterexample`, `rz_prop316_right_counterexample`), showing that the factor $`2`$ in $`\operatorname{SoS}_\mathbb{K}(Q_M) \le 2\operatorname{PT\text{-}rank}_\mathbb{K}(M)`$ is sharp in general.
- **Section 3 (Characteristic-free crossing bounds).** Over *every* field $`\mathbb{K}`$ (including $`\operatorname{char}\mathbb{K} = 2`$), we prove $`\operatorname{TC}_\mathbb{K}(r,s) \ge \max(r,s)`$ (`twoCut_ge_max`), $`\operatorname{TC}_\mathbb{K}(r,s) \ge \max(r,s) + 1`$ for all $`r,s \ge 3`$ (`twoCut_gt_max_of_ge_three`), the exact formula $`\operatorname{TC}_\mathbb{K}(2,s) = 2\lceil s/2\rceil`$ (`twoCut_two_iff`), the transpose upper bound $`\operatorname{TC}_\mathbb{K}(r,s) \le 1 + rs - \binom{\min(r,s)+1}{2}`$ (`transpose_twoCut`), and $`\operatorname{TC}_\mathbb{K}(3,3) = 4`$ (`twoCut_three_three_iff`).
- **Section 4 (Explicit exact and border witnesses).** We formalise the self-dual Clifford bound $`\operatorname{TC}_\mathbb{K}(d,n) \le 2d`$ (`clifford_twoCut`), border-to-exact conversion $`\operatorname{TC}_\mathbb{K}(r,s) \le (k+1)(a+b)`$ (`exact_of_border_coeffs`), explicit $`\pm 1`$ integer schemes proving $`\operatorname{TC}_\mathbb{K}(4,5) \le 8`$, $`\operatorname{TC}_\mathbb{K}(4,6) \le 8`$, and $`\operatorname{TC}_\mathbb{K}(8,8) \le 16`$ over every field (`tc45_twoCut`, `tc46_twoCut`, `tc88_twoCut`), and an explicit pole-order-2 border decomposition proving $`\underline{\operatorname{TC}}_{\mathbb{K},2}(4,4) \le 6`$ over every field (`border44_identity_field`).
- **Section 5 (Word-span tensor powers of reflection-type decompositions).** A major class of exact two-cut decompositions—including Hurwitz $`[2,2,2]`$, $`[4,4,4]`$, $`[8,8,8]`$, all Clifford self-dual decompositions, the $`(2,2)`$ transpose point, and the $`(4,6)`$ scheme—have *reflection-type* spectra $`\operatorname{spec} M = \{0^{D-n}, \lambda^n\}`$ and $`\operatorname{spec} M^\Gamma = \{1^{D-n}, (1-\lambda)^n\}`$. We prove that word-span decompositions of their $`K`$-th tensor powers are governed by the $`p`$-biased reflection operator $`T_{-1}`$ in $`L^2(\mu_p)`$ (`reflOp_involutive`, `reflOp_selfadjoint`, `wordPoly_eval_B`), prove the Valuation Theorem (`valuation_theorem`, `layer_grouping_le`), develop tensorising Farkas-certificate packings (`CertPacking.lower_bound`, `CertPacking.asymptotic_bound`), verify a 22-certificate rational packing of value $`57/256`$ at $`K = 4, p = 1/4`$ (`packing_K4_quarter_value`), and prove that no reflection-type word-span tensor power beats the rate $`\sqrt{1+q^2}`$ for any shape $`r,s \ge 2`$ (`reflection_wordSpan_nogo`).

**AI assistance.** The proofs and the Lean formalisation were produced with AI coding agents under the author's direction. The kernel-checked Lean proofs are the primary evidence for every theorem stated below; this text explains them and states their exact scope.

## 2. Definitions, dictionary, and Rossman–Zhu §3.2

### 2.1 Matrix partial transpose and biquadratic forms

Let $`\mathbb{K}`$ be a field and $`r, s \ge 1`$. Matrices in $`M_{rs}(\mathbb{K})`$ are indexed by pairs $`(a,b) \in [r]\times[s]`$. The *partial transpose* $`M^\Gamma`$ is defined by $`(M^\Gamma)_{(a,b),(c,d)} := M_{(a,d),(c,b)}`$. It is a $`\mathbb{K}`$-linear involution with $`(M^\Gamma)^\Gamma = M`$, $`I^\Gamma = I`$, and $`\operatorname{tr}(M^\Gamma) = \operatorname{tr}(M)`$ (`ptr_ptr`, `ptr_one`, `trace_ptr`). A matrix $`M`$ is *fully symmetric* (`IsFullySym`) if $`M^\top = M`$ and $`M^\Gamma = M`$.

The associated biquadratic form is $`Q_M(x, y) := \sum_{a,c,b,d} M_{(a,b),(c,d)} x_a x_c y_b y_d`$. Two matrices $`M, N`$ define the same biquadratic form if and only if they have the same four-way symmetrisation

```math
(\operatorname{sym}_4 M)_{(a,b),(c,d)} := M_{(a,b),(c,d)} + M_{(c,b),(a,d)} + M_{(a,d),(c,b)} + M_{(c,d),(a,b)}
```

(`sameBiquad_iff_qf`). Notice that $`\operatorname{sym}_4(M^\Gamma) = \operatorname{sym}_4(M)`$.

**Definition 1.** For $`M \in M_{rs}(\mathbb{K})`$ and $`c \in \mathbb{N}`$:
1. *Two-cut rank* (`HasTwoCut`): $`\operatorname{TC}_\mathbb{K}(M) \le c`$ if $`M = A + W^\Gamma`$ with $`\operatorname{rank} A + \operatorname{rank} W \le c`$. Write $`\operatorname{TC}_\mathbb{K}(r,s) := \operatorname{TC}_\mathbb{K}(I_{rs})`$.
2. *Partial-transpose rank* (`HasPTRank`, following [RZ25, §3.2] for $`d=2`$): $`B`$ is *PT-basic* (`IsPTBasic`) if $`\operatorname{rank} B = 1`$ or $`\operatorname{rank}(B^\Gamma) = 1`$; $`\operatorname{PT\text{-}rank}_\mathbb{K}(M) \le c`$ if $`M = \sum_{i=1}^m B_i`$ with $`m \le c`$ and each $`B_i`$ PT-basic.
3. *Bilinear product complexity* (`HasProdFormula`): $`\operatorname{Prod}_\mathbb{K}(Q_M) \le c`$ if $`\operatorname{sym}_4 M = \operatorname{sym}_4(\sum_{k=1}^c u_k v_k^\top)`$.
4. *Sum-of-squares complexity* (`HasSoSFormula`): $`\operatorname{SoS}_\mathbb{K}(Q_M) \le c`$ if $`\operatorname{sym}_4 M = \operatorname{sym}_4(\sum_{k=1}^c \ell_k \ell_k^\top)`$.

### 2.2 The exact dictionary

**Theorem 1 (Dictionary; `Dictionary.lean`).** Let $`\mathbb{K}`$ be any field and $`M \in M_{rs}(\mathbb{K})`$.
1. (`hasPTRank_iff_hasTwoCut`) $`\operatorname{PT\text{-}rank}_\mathbb{K}(M) \le c \iff \operatorname{TC}_\mathbb{K}(M) \le c`$.
2. (`prod_of_twoCut`) $`\operatorname{TC}_\mathbb{K}(M) \le c \implies \operatorname{Prod}_\mathbb{K}(Q_M) \le c`$.
3. (`twoCut_of_sos`, [RZ25, Lemma 3.15] for $`d=2`$) If $`\operatorname{char}\mathbb{K} \neq 2`$ and $`M`$ is fully symmetric, then $`\operatorname{SoS}_\mathbb{K}(Q_M) \le c \implies \operatorname{TC}_\mathbb{K}(M) \le 2c`$.
4. (`twoCut_of_prod`) If $`\operatorname{char}\mathbb{K} \neq 2`$ and $`M`$ is fully symmetric, then $`\operatorname{Prod}_\mathbb{K}(Q_M) \le c \implies \operatorname{TC}_\mathbb{K}(M) \le 4c`$.
5. (`sos_of_prod`, `sos_of_twoCut`, `sos_of_ptRank`) If $`\operatorname{char}\mathbb{K} \neq 2`$ and $`\sqrt{-1} \in \mathbb{K}`$, then for every $`M`$, $`\operatorname{Prod}_\mathbb{K}(Q_M) \le c \implies \operatorname{SoS}_\mathbb{K}(Q_M) \le 2c`$ and $`\operatorname{PT\text{-}rank}_\mathbb{K}(M) \le c \implies \operatorname{SoS}_\mathbb{K}(Q_M) \le 2c`$.

Note that the factor $`2`$ in (3) cannot be removed even for fully symmetric $`M = I_{16}`$: Euler's four-square identity gives $`\operatorname{SoS}_\mathbb{K}(X_{4,4}) \le 4`$, whereas Theorem 3(2) proves $`\operatorname{TC}_\mathbb{K}(4,4) \ge 5 > 4`$.

### 2.3 Refutation of Rossman–Zhu Lemma 3.13 and Proposition 3.16

In [RZ25, §3.2], Lemma 3.13 ($`\operatorname{SoS}(Q_M) \le \operatorname{PT\text{-}rank}(M)`$) and Proposition 3.16 ($`\operatorname{SoS}(Q_M) - 1 \le \operatorname{PT\text{-}rank}(M) \le 2^{d-1}\operatorname{SoS}(Q_M)`$) are printed without a full-symmetry hypothesis on $`M`$.

**Theorem 2 (Counterexamples; `RossmanZhu.lean`).** Let $`\mathbb{K}`$ be any field of characteristic $`\neq 2`$.
1. (`rz_lemma313_counterexample`, `rzM1_hasSoS_two`) $`M_1 := E_{(0,0),(0,1)} \in M_4(\mathbb{K})`$ ($`Q_{M_1} = x_0^2 y_0 y_1`$) has $`\operatorname{PT\text{-}rank}_\mathbb{K}(M_1) = 1`$ and $`\operatorname{SoS}_\mathbb{K}(Q_{M_1}) > 1`$ ($`= 2`$ when $`\sqrt{-1} \in \mathbb{K}`$), refuting [RZ25, Lemma 3.13].
2. (`rz_prop316_left_counterexample`, `rzM2_hasSoS_four`) $`M_2 := E_{(0,0),(0,1)} + E_{(1,2),(1,3)} \in M_{16}(\mathbb{K})`$ ($`Q_{M_2} = x_0^2 y_0 y_1 + x_1^2 y_2 y_3`$) has $`\operatorname{PT\text{-}rank}_\mathbb{K}(M_2) \le 2`$ and $`\operatorname{SoS}_\mathbb{K}(Q_{M_2}) > 3`$ ($`= 4`$ when $`\sqrt{-1} \in \mathbb{K}`$), refuting the left inequality of [RZ25, Proposition 3.16].
3. (`rz_prop316_right_counterexample`) $`M_3 := E_{(0,0),(0,1)} - E_{(0,1),(0,0)} \in M_4(\mathbb{K})`$ has $`\operatorname{SoS}_\mathbb{K}(Q_{M_3}) = 0`$ and $`\operatorname{PT\text{-}rank}_\mathbb{K}(M_3) \ge 1`$, refuting the right inequality of [RZ25, Proposition 3.16].

In particular, the repaired factor $`2`$ in $`\operatorname{SoS}_\mathbb{K}(Q_M) \le 2\operatorname{PT\text{-}rank}_\mathbb{K}(M)`$ is tight for general $`M`$. Whether $`\operatorname{SoS}_\mathbb{C}(Q_M) \le \operatorname{PT\text{-}rank}_\mathbb{C}(M)`$ holds for *fully symmetric* $`M`$ remains open.

## 3. Characteristic-free crossing bounds

**Theorem 3 (Crossing bounds and exact values; `LowerBounds.lean`).** Over *every* field $`\mathbb{K}`$ (arbitrary characteristic, including $`\operatorname{char}\mathbb{K} = 2`$):
1. (`twoCut_ge_max`) $`\operatorname{TC}_\mathbb{K}(r,s) \ge \max(r,s)`$ for all $`r, s \ge 1`$.
2. (`twoCut_gt_max_of_ge_three`) $`\operatorname{TC}_\mathbb{K}(r,s) \ge \max(r,s) + 1`$ for all $`r, s \ge 3`$.
3. (`twoCut_two_iff`) $`\operatorname{TC}_\mathbb{K}(2,s) = 2\lceil s/2\rceil`$ for all $`s \ge 1`$.
4. (`transpose_twoCut`) $`\operatorname{TC}_\mathbb{K}(r,s) \le 1 + rs - \frac{m(m+1)}{2}`$ where $`m = \min(r,s)`$.
5. (`twoCut_three_three_iff`) $`\operatorname{TC}_\mathbb{K}(3,3) = 4`$.

The proof of (2) contracts $`I_{rs} = A + W^\Gamma`$ along rank-1 slices $`(x, \varphi)`$ with $`\varphi^\top x = 1`$ to derive block biorthogonality $`V_k^\top U_i = \delta_{k,i} I_a`$ (giving $`ra \le s`$), and constructs an injective linear map $`\Psi : \ker(W) \to \mathbb{K}^{\{(k,i): k \le i\} \times [a]}`$ via symmetry of $`M(k,i,t) = (U_k^\top v_i)_t`$, using no trace and no division by $`2`$. This gives $`2(r-1)s \le (r^2 + r - 2)a`$, contradicting $`ra \le s`$ for $`r \ge 3`$.

## 4. Explicit exact and border constructions

**Theorem 4 (Witnesses; `Witnesses.lean`).** Let $`\mathbb{K}`$ be a field.
1. (`clifford_twoCut`) If $`\operatorname{char}\mathbb{K} \neq 2`$ and $`\gamma_1,\dots,\gamma_n \in M_d(\mathbb{K})`$ satisfy $`\gamma_i \gamma_j + \gamma_j \gamma_i = 2\delta_{ij} I_d`$, then $`\operatorname{TC}_\mathbb{K}(d,n) \le 2d`$.
2. (`exact_of_border_coeffs`) Over *every* field $`\mathbb{K}`$, a pole-order-$`k`$ formal Laurent border two-cut decomposition of $`I_{rs}`$ of ranks $`a + b`$ yields $`\operatorname{TC}_\mathbb{K}(r,s) \le (k+1)(a+b)`$.
3. (`tc45_twoCut`, `tc46_twoCut`, `tc88_twoCut`) Over *every* field $`\mathbb{K}`$: $`\operatorname{TC}_\mathbb{K}(4,5) \le 8`$, $`\operatorname{TC}_\mathbb{K}(4,6) \le 8`$, and $`\operatorname{TC}_\mathbb{K}(8,8) \le 16`$.
4. (`border44_identity_field`) Over *every* field $`\mathbb{K}`$, $`I_{16}`$ has an explicit integer pole-order-2 border two-cut decomposition of ranks $`3 + 3`$ ($`\underline{\operatorname{TC}}_{\mathbb{K},2}(4,4) \le 6`$): the $`\varepsilon^{-2}`$ and $`\varepsilon^{-1}`$ coefficients vanish and the $`\varepsilon^0`$ coefficient equals $`I_{16}`$.

| $`(r, s)`$ | Lower | Upper | $`\underline{\operatorname{TC}}_2`$ | Lean witnesses |
|---|---|---|---|---|
| $`(2, s)`$ | $`2\lceil s/2\rceil`$ | $`2\lceil s/2\rceil`$ | — | `twoCut_two_iff` |
| $`(3, 3)`$ | 4 | 4 | — | `twoCut_three_three_iff` |
| $`(4, 4)`$ | 5 | 7 | $`\le 6`$ | `twoCut_gt_max_of_ge_three`, `transpose_twoCut`, `border44_identity_field` |
| $`(4, 5)`$ | 6 | 8 | — | `twoCut_gt_max_of_ge_three`, `tc45_twoCut` |
| $`(4, 6)`$ | 7 | 8 | — | `twoCut_gt_max_of_ge_three`, `tc46_twoCut` |
| $`(8, 8)`$ | 9 | 16 | — | `twoCut_gt_max_of_ge_three`, `tc88_twoCut` |

## 5. Reflection-type word-span tensor powers

A matrix $`M \in M_{rs}(\mathbb{R})`$ ($`D = rs`$) has *reflection-type spectrum* with multiplicity $`0 < n < D`$ and eigenvalue $`\lambda`$ if $`M \sim \operatorname{diag}(0^{D-n}, \lambda^n)`$ and $`M^\Gamma \sim \operatorname{diag}(1^{D-n}, (1-\lambda)^n)`$. Put $`p = n/D`$.

**Proposition 5 (`ReflectionPowers.lean`).**
1. (`reflection_lam_eq`) $`\operatorname{tr} M = \operatorname{tr}(M^\Gamma)`$ forces $`2\lambda n = D`$, i.e. $`\lambda = 1/(2p)`$.
2. (`reflection_slice_constraint`) Both $`M`$ and $`\frac{\lambda}{2\lambda-1}(I - \lambda^{-1}M)`$ give two-cut decompositions of $`I_{rs}`$, forcing $`\max(r,s) \le 2\min(n, D-n)`$, i.e. $`\min(p, 1-p) \ge \frac{1}{2\min(r,s)}`$.
3. (`reflOp_involutive`, `reflOp_selfadjoint`, `reflOp_const_one`, `wordPoly_eval_B`) With $`E_1(p) = \begin{pmatrix} 1-2p & 2p \\ 2-2p & 2p-1 \end{pmatrix}`$ and $`T_{-1} = E_1(p)^{\otimes K}`$, $`T_{-1}`$ is an involution, is self-adjoint in $`L^2(\mu_p)`$, and fixes $`\mathbf{1}`$. Every multilinear word polynomial $`F`$ satisfies $`F(1 - \lambda b) = (T_{-1} h)(b)`$ where $`h(a) = F(\lambda a)`$, giving normalised cost $`\varphi_K(p; h) := \mu_p(\operatorname{supp} h) + \mu_p(\operatorname{supp}(\mathbf{1} - T_{-1} h))`$.

**Theorem 6 (Valuation Theorem; `valuation_theorem`, `layer_grouping_le`).** Let $`\lambda = a/b \in \mathbb{Q}`$ ($`a, b \in \mathbb{Z}\setminus\{0\}`$) with $`p = b/(2a) \in [0,1]`$, and suppose a prime $`\ell \mid (a - b)`$ with $`\ell \nmid a`$. Then for every $`K \ge 1`$ and every word-span polynomial with $`\ell`$-integral coefficients $`c_w \in \mathbb{Z}_{(\ell)}`$ (including every $`0/1`$ grouping and every integer combination),

```math
\varphi_K(p; h) \ge \sum_{T \in \{0,1\}^K} \min\bigl(\mu_p(T),\, \mu_{1-p}(T)\bigr).
```

For $`0 < p \le 1/2`$, the layer grouping $`c_w = \mathbf{1}_{2|w| \ge K}`$ attains equality at every $`K \ge 1`$.

**Lemma 7 (Tensorising certificate packings; `CertPacking.lower_bound`, `CertPacking.asymptotic_bound`).** A certificate $`y : \{0,1\}^K \to \mathbb{R}`$ with $`\sum_b y(b) \neq 0`$ and $`y_A = (E_1^\top)^{\otimes K} y`$ meets $`\operatorname{supp}(h) \cup \operatorname{supp}(\mathbf{1} - T_{-1} h)`$ for every $`h`$. Fractional packings of certificates bounded by $`\mu_p`$ on both sides lower-bound $`\varphi_K(p; h)`$ and multiply under tensor product.

We verify four packings: a trivial $`K=1`$ packing (`packing_K1_trivial`, value $`\min(p, 1-p)`$), a parametric $`K=1`$ packing on $`[1/3, 2/3]`$ (`packing_K1_mid`, value $`2/3`$), a parametric $`K=2`$ packing on $`(0, 1/2]`$ (`packing_K2`, value $`\min(2p-p^2, (1-p)^2)`$), and a kernel-checked 22-certificate rational packing at $`K = 4, p = 1/4`$ (`packing_K4_quarter`, exact value $`57/256`$).

**Theorem 8 (Reflection-type word-span no-go theorem; `reflection_wordSpan_nogo`).** Let $`r, s \ge 2`$, $`D = rs`$, and $`0 < n < D`$ satisfy $`\max(r,s) \le 2\min(n, D-n)`$. Put $`p = n/D`$. Then there exist $`c > 0`$ and $`g > 0`$ with $`\log(D g) > \sqrt{(\log r)^2 + (\log s)^2}`$ such that for every $`K \ge 1`$ and every $`h : \{0,1\}^K \to \mathbb{R}`$,

```math
c \cdot (D g)^K \le D^K \varphi_K(p; h).
```

In particular, no reflection-type decomposition yields word-span tensor powers with asymptotic rate $`\le \sqrt{1 + q^2}`$ ($`q = \log\min(r,s)/\log\max(r,s)`$).

## 6. Formalisation and verification

The Lean 4 formalisation resides in `PastaMath/TwoCutSoS/` (Lean 4.31.0, Mathlib revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`). Every headline theorem is audited by `PastaMath/TwoCutSoS/Axioms.lean` and depends exclusively on `[propext, Classical.choice, Quot.sound]`.

| Paper result | Lean module | Headline Lean theorems |
|---|---|---|
| Theorem 1 (Dictionary) | `Dictionary.lean` | `hasPTRank_iff_hasTwoCut`, `prod_of_twoCut`, `twoCut_of_sos`, `twoCut_of_prod`, `sos_of_prod`, `sos_of_twoCut`, `sos_of_ptRank` |
| Theorem 2 (RZ §3.2) | `RossmanZhu.lean` | `rz_lemma313_counterexample`, `rzM1_hasSoS_two`, `rz_prop316_left_counterexample`, `rzM2_hasSoS_four`, `rz_prop316_right_counterexample` |
| Theorem 3 (Crossing) | `LowerBounds.lean` | `twoCut_ge_max`, `twoCut_gt_max_of_ge_three`, `twoCut_two_iff`, `transpose_twoCut`, `twoCut_three_three_iff` |
| Theorem 4 (Witnesses) | `Witnesses.lean` | `clifford_twoCut`, `exact_of_border_coeffs`, `tc45_twoCut`, `tc46_twoCut`, `tc88_twoCut`, `border44_identity_field` |
| Proposition 5 ($`T_{-1}`$) | `ReflectionPowers.lean` | `reflOp_involutive`, `reflOp_selfadjoint`, `wordPoly_eval_B`, `reflection_slice_constraint` |
| Theorem 6 (Valuation) | `ReflectionPowers.lean` | `valuation_theorem`, `layer_grouping_le` |
| Lemma 7, Theorem 8 | `ReflectionPowers.lean` | `CertPacking.lower_bound`, `CertPacking.asymptotic_bound`, `packing_K4_quarter_value`, `reflection_wordSpan_nogo` |

**What is not machine-checked.**
1. The Kronecker-product simultaneous-diagonalisation step identifying $`\operatorname{rank} F(M_1,\dots,M_K) + \operatorname{rank}(I - F(M_1,\dots,M_K))^\Gamma = D^K \varphi_K(p; h)`$ for a diagonalisable reflection-type base $`M`$ is proved on paper; Lean kernel-checks `reflection_slice_constraint`, `wordPoly_eval_B`, `valuation_theorem`, `layer_grouping_le`, the certificate packings, and `reflection_wordSpan_nogo`.
2. Theorem 8 applies to word-span decompositions of reflection-type diagonalisable bases over $`\mathbb{R}`$; it does not cover decompositions outside the word algebra, non-reflection spectra, non-diagonalisable bases, or border families.
3. Whether $`\operatorname{SoS}_\mathbb{C}(Q_M) \le \operatorname{PT\text{-}rank}_\mathbb{C}(M)`$ holds for *fully symmetric* matrices $`M`$ remains open.
4. Our citation of [RZ25] refers to v1 (`arXiv:2512.01227`, December 2025).

## References

- **[HWY11]** P. Hrubeš, A. Wigderson, and A. Yehudayoff, *Non-commutative circuits and the sum-of-squares problem*, Journal of the American Mathematical Society 24 (2011), no. 3, 871–898.
- **[RZ25]** B. Rossman and D. Zhu, *Multiquadratic sum-of-squares lower bounds imply $`\mathrm{VNC}^1 \neq \mathrm{VNP}`$*, arXiv:2512.01227v1, December 2025.
- **[Sie26]** J. P. Siemaszko, *On the Hurwitz sum-of-squares problem*, Zenodo, DOI: `10.5281/zenodo.24024689`, November 2026.
