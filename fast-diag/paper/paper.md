# Fast derandomised diagonalisation against linear-size circuits

**PastaPastaPasta** · November 2026

*Markdown rendering of `paper.tex`, which is the reference version.*

## Abstract

For every constant $`c\ge1`$, we construct a language $`L_c`$ (explicit up to the absolute constant of Anthropic’s Theorem B, whose value is not given) decided by a deterministic multitape Turing machine in time $`2^{O(c^2 n\sqrt{\log n})}`$ that has no $`B_2`$-circuits of size $`cn`$ at any large input length $`n`$. Brute-force diagonalisation requires time $`2^{\Theta(cn\log n)}`$.

The construction derandomises a high-moment correlation potential $`\Phi_m(F)=\sum_d \operatorname{cor}(C_d,F)^{2m}`$ over a block-XOR family by conditional expectations. Each conditional expectation is a single exact contraction of a bipartite tensor network with $`\Theta(c^2 n\log n)`$ wires, using a 3-stage Clos network of heavy crossbar vertices to route bundled circuit traces in constant depth. The running time is conditional on a deterministic $`2^{O(S/\sqrt{\log S})}`$ contraction theorem for networks with vertex degrees up to $`S^{0.9}`$. Two October 2026 preprints provide such a theorem: OpenAI’s Theorem D.1 (paper-only appendix) \[OAI26\], and Anthropic’s network theorem (Lemma 8 and Theorem A(a),(b) with the pieces of Theorem B) \[Ant26\], each proved in the authors’ Lean development (with Theorem A(a),(b) and Theorem B on the proof path of their Lean-checked Main Theorem, and Lemma 8 proved separately).

Combined with a tableau argument and Anthropic’s Lean-checked $`\#3`$-CNF counting theorem, this yields $`\mathsf{NE}\cap\mathsf{coNE}\not\subseteq\mathsf{SIZE}(cn)`$ for every $`c`$ (in fact in an oblivious subclass $`\mathsf{ONTIME}\cap\mathsf{coONTIME}`$), as well as a single language with superlinear infinitely-often circuit hardness in $`\mathsf{NTIME}\cap\mathsf{coNTIME}[2^{n g(n)}]`$ for every computable, unbounded, nondecreasing $`g`$.

*What is kernel-checked here (Lean 4, `PastaMath/FastDiag/`):* the unconditional combinatorial core—the moment-potential bound, block-XOR sign-sum identities, integer parameter inequality, 3-stage Clos rearrangeability via König’s edge-colouring theorem from Hall’s theorem, and the $`\sqrt{\log}`$ exponent arithmetic. *What is not machine-checked:* the fan-out-3 normal form, the tensor-network encoding and running-time analysis, the tableau machine steps, the extensions in Section 7, and the external October 2026 contraction and $`\#3`$-CNF theorems (which are AI-written and have not been human-refereed).

## 1. Statements and external inputs

Write $`C_L(n)`$ for the least number of gates in a $`B_2`$-circuit (all 16 binary gates, fan-in 2, unbounded fan-out) computing $`L\cap\{0,1\}^n`$. All logarithms are base 2. We write $`L\notin\mathsf{SIZE}(s)`$ for $`C_L(n)>s(n)`$ infinitely often, and $`L\notin\mathrm{i.o.}\text{-}\mathsf{SIZE}(s)`$ for $`C_L(n)>s(n)`$ for all sufficiently large $`n`$. For a union class $`\mathcal{C}=\bigcup_a \mathcal{C}_a`$, “$`\mathcal{C}\not\subseteq\mathsf{SIZE}(cn)`$” means the class reading: some member of $`\mathcal{C}`$ is not in $`\mathsf{SIZE}(cn)`$. Put $`N:=2^n`$, $`\operatorname{sgn}(b):=(-1)^b`$, $`\operatorname{corr}(g,F):=\sum_{x\in\{0,1\}^n}\operatorname{sgn}(g(x))\operatorname{sgn}(F(x))`$, and $`\operatorname{cor}:=\operatorname{corr}/N`$.

### 1.1 External inputs and their checking status

| Name | Statement used | Source | Checking status |
|:---|:---|:---|:---|
| **(T4)** | Boolean tensor contraction: $`\le Cs`$ edges, max degree $`\le\lceil s^{9/10}\rceil`$, entries in $`(\mathbb{Z}/2^{P_0})[V]/(V^\ell)`$, time $`(s+L)^{O(1)}2^{O(s/\sqrt{\log s})}`$ | OpenAI \[OAI26, Thm D.1\] | Paper appendix only; proof not verified here. |
| **(T4-A)** | Integer network contraction with query-access tables: Lemma 8(i), Thm A(a),(b), Thm B pieces | Anthropic \[Ant26\] | Proved as Lean theorems in the authors’ repo (A(a), A(b), B on Main Theorem path; Lemma 8 proved separately; not human-refereed, not rebuilt here). Composition and cluster construction are paper steps here. |
| **(G)** | Deterministic $`\#3`$-CNF counting for $`m\ge2`$ clauses in $`2^{C\cdot 3m/\sqrt{\log m}}`$ steps (with side conditions) | Anthropic \[Ant26, Main Thm\] | Lean-checked by authors (AI-written, not human-refereed). Multi-stack to multitape simulation and statement fidelity not machine-checked. |
| König/Hall | Every $`r`$-regular bipartite multigraph is properly $`r`$-edge-colourable | Mathlib | Kernel-checked here (`regular_bipartite_coloring`). |

*Table 1: External hypotheses and their verification status.*

### 1.2 Main results

**Theorem 1** (Theorem A; conditional on (T4) or (T4-A)). There is an absolute constant $`K`$ such that for every real $`c\ge1`$ there is a language $`L_c`$ decided by a deterministic multitape Turing machine in time $`2^{K c^2 n\sqrt{\log n}}`$ satisfying $`C_{L_c}(n)>cn`$ whenever
``` math
\log n \ge L_0(c) := \max\!\left\{24\log(15c)+61,\; 16\lceil\log(51c\log n)\rceil,\; 2.5\log(1100 c^{1.5}\log n)\right\}.
```
In finite form: given $`N=2^n`$, a deterministic algorithm outputs a truth table of length $`N`$ with circuit complexity $`>c\log N`$ in time $`N^{K c^2\sqrt{\log\log N}}`$ (versus $`N^{\Theta(c\log\log N)}`$ by brute force).

**Theorem 2** (Theorem $`A_\lambda`$ and Corollary C; conditional on (T4) or (T4-A)). Let $`\kappa_0>0`$ and let $`\lambda:\mathbb{N}\to[1,(\log n)^{\kappa_0}]`$ be computable in $`\mathrm{poly}(n)`$ time. There is a language $`L_\lambda\in\mathsf{DTIME}[2^{K\lambda(n)^2 n\sqrt{\log n}}]`$ with $`C_{L_\lambda}(n)>n\lambda(n)`$ for all $`n\ge n_0(\kappa_0)`$, with $`K`$ absolute. In particular, for every $`c\ge1`$,
``` math
\mathsf{DTIME}[2^{K c^2 n\log n}] \not\subseteq \mathrm{i.o.}\text{-}\mathsf{SIZE}\!\bigl(c\cdot n(\log n)^{1/4}\bigr).
```

**Corollary 3** (Corollary B; conditional on ((T4) or (T4-A)) and (G)). For every $`c\ge1`$, either a language $`\mathrm{Tab}_c\in\mathsf{E}=\mathsf{DTIME}[2^{O(n)}]`$ has $`C(N)>cN`$ for infinitely many $`N`$, or $`L_c\in\mathsf{ONTIME}[2^{a_c n}]\cap\mathsf{coONTIME}[2^{a_c n}]\subseteq\mathsf{NTIME}[2^{a_c n}]\cap\mathsf{coNTIME}[2^{a_c n}]`$ with $`a_c=4AKc^2(3c+2B)+1`$ ($`A=15C_{(\mathrm{G})}`$, $`K,B`$ absolute) and $`C_{L_c}(n)>cn`$ for all large $`n`$. In particular, $`\mathsf{NE}\cap\mathsf{coNE}\not\subseteq\mathsf{SIZE}(cn)`$ for every $`c`$ (class reading).

**Corollary 4** (Corollary $`B_\lambda`$; conditional on ((T4) or (T4-A)) and (G)). Let $`\lambda:\mathbb{N}\to[1,\sqrt{\log n}]`$ be nondecreasing, computable in $`\mathrm{poly}(n)`$ time, with $`\lambda(n^2)\le2\lambda(n)`$. Then some language in $`\mathsf{ONTIME}\cap\mathsf{coONTIME}[2^{a\lambda(n)^3 n}]`$ has $`C(n)>n\lambda(n)`$ infinitely often, with $`a`$ absolute. In particular:

- $`\mathsf{NTIME}\cap\mathsf{coNTIME}[2^{an(\log n)^{3/4}}]\not\subseteq\mathsf{SIZE}(n(\log n)^{1/4})`$;

- for every computable, unbounded, nondecreasing $`g`$, there is a single language in $`\mathsf{NTIME}\cap\mathsf{coNTIME}[2^{n\cdot g(n)}]`$ with $`C(n)>cn`$ infinitely often for every $`c`$.

**Proposition 5** (Proposition M; unconditional). Using only the published Lean-exported $`\#k`$-CNF statement of \[Ant26\] (or OpenAI’s main-text bound) via switch-based circuit encodings of the moment estimator yields at best $`L_c\in\mathsf{DTIME}[2^{O(c^2 n\log^{1.5} n\log\log n)}]`$, slower than brute force $`2^{O(cn\log n)}`$; any bounded-fan-in switch encoding requires $`\Omega(c^2 n\log^2 n)`$ gates/clauses.

### 1.3 What does not follow

This work does *not* establish: (1) $`\mathsf{E}\not\subseteq\mathsf{SIZE}(cn)`$ (which would require $`\log S`$ savings instead of $`\sqrt{\log S}`$); (2) an almost-everywhere bound $`\mathsf{NE}\cap\mathsf{coNE}\not\subseteq\mathrm{i.o.}\text{-}\mathsf{SIZE}(cn)`$; (3) a single language in $`\mathsf{NE}\cap\mathsf{coNE}`$ outside $`\mathsf{SIZE}(O(n))`$; (4) the normalized reading $`\mathsf{NTIME}[2^n]\cap\mathsf{coNTIME}[2^n]\not\subseteq\mathsf{SIZE}(cn)`$ for every $`c`$; (5) $`\mathsf{UE}\cap\mathsf{coUE}`$ or $`\mathsf{ZPE}`$ lower bounds; (6) anything beyond $`s=o(n\sqrt{\log n})`$ below brute force; or (7) any unconditional circuit lower bound beyond the existence of hard block-XOR functions (Proposition 11) and Proposition 5.

## 2. Contraction from (T4-A) and clean-up of (G)

**Theorem 6** (Theorem N; conditional on (T4-A)). There are absolute constants $`C_N,S_0`$ and a deterministic algorithm that, given a bipartite network with $`S`$ edges, maximum degree $`\Delta\le S^{0.9}`$, integer entries in $`\{-1,0,1\}`$, and entry evaluation time $`\tau_0`$, outputs its contraction $`Z\in\mathbb{Z}`$ in at most $`2^{C_N S/\sqrt{\log S}}\cdot\mathrm{poly}(\tau_0,S)`$ operations for $`S\ge S_0`$.

*Proof.* Choose the largest level $`\ell`$ of Anthropic’s Theorem A(a) with $`K_\ell\le S^{1/100}`$; since $`K_{\ell+1}\le K_\ell^{10}`$, we have $`K:=K_\ell\ge S^{1/1000}`$ for $`S\ge K_0^{1000}`$. Set $`g:=3K^8\le 3S^{0.08}`$. Greedily partition vertices into at most $`g`$ clusters, closing a cluster once its degree sum reaches $`2S/g`$; each cluster has degree sum at most $`2S/g+\Delta\le 3S/g=:P`$ since $`\Delta\le S^{0.9}\le S/g`$ for large $`S`$. Pad to $`g`$ clusters with settings $`S_a=\{0,1\}^{P_a}`$, weights $`W_a(z_a)=\prod_{v\in a}T_v(z_a|_{\delta(v)})\in\{-1,0,1\}`$ ($`B=1`$, $`\tau=|a|\tau_0+\mathrm{poly}(S)`$), and equality pair functions $`\Psi_{a,b}`$ factoring through $`c_{a,b}`$ cut bits (total $`U\le 2S`$). Applying Lemma 8(i) and Theorem A(b) with $`\lambda=L\le(2S+3S/K)/K^2+1`$ and $`B'\le 6S/K+1+9K^{16}`$ gives $`\log_2(\text{\#ops})\le g\log K+e_\ell(2S+3S/K+K^2)+C_0 K^2\log(K(L+B'))+6S/K+\log\tau+C_1\log(g(P+1))`$. Since $`e_\ell\le 0.85((3x_0+6)/\log K_\ell)^{1/2}=O(1/\sqrt{\log S})`$ and the remaining terms are $`O(S^{0.999})`$, the total is $`2^{C_N S/\sqrt{\log S}}\cdot\mathrm{poly}(\tau_0,S)`$. Integers have $`\mathrm{poly}(S)`$ bits, so multitape simulation adds polynomial overhead. ∎

**Lemma 7** (Clean-up for (G)). Let $`D`$ be a circuit with $`q`$ inputs, $`|D|\ge1`$ gates, and $`V=q+|D|`$. Using the machine of Anthropic’s `MainTheorem` as a subroutine, a deterministic multitape TM decides satisfiability of $`D`$ in $`2^{15C\cdot V/\sqrt{\log V}}\cdot\mathrm{poly}(V)`$ steps.

*Proof.* Form the Tseitin 3-CNF $`\mathrm{Tseitin}(D)`$ with $`m=4|D|+1\ge5`$ clauses: four 3-clauses per gate (differing in the signs of their first two literals, even when both inputs coincide, so no clause repeats) plus the unit output clause. Drop unused input variables (trying $`\le8`$ assignments if fewer than 4 variables remain), meeting `IsKCNF 3`, $`m\ge2`$, and `AllOccur`. Simulate the multi-stack machine by a multitape TM with $`O(1)`$ slowdown per step. Since $`m\le 5V`$ and $`x/\sqrt{\log x}`$ increases on $`[2,\infty)`$, $`2^{C\cdot 3m/\sqrt{\log m}}\le 2^{15C\cdot V/\sqrt{\log V}}`$. ∎

## 3. Circuit descriptions and Clos routing

**Lemma 8** (Fan-out-3 normal form). For $`n\ge2`$ and $`s\ge1`$, every $`B_2`$-circuit of size $`\le s`$ on $`n`$ inputs is equivalent to one with exactly $`s':=3s`$ gates $`g_1,\dots,g_{s'}`$ whose ports read earlier sources, whose output is $`g_{s'}`$, and where every source has fan-out $`\le3`$.

*Proof.* Prune non-ancestors and order topologically (using $`\mathrm{PROJ}_1(x_h,x_h)`$ if no gates remain); there are $`s_0\le s`$ gates with $`\sum\mathrm{fanout}=2s_0`$. Replace each fan-out $`f>3`$ by a copy chain of $`f-3`$ unary projections (adding at most $`2s_0`$ gates, so $`G\le 3s`$), then pad immediately before the output with a copy chain of $`3s-G`$ gates reading free slots. ∎

Give each of the $`H:=n+s'`$ sources three slots ($`R:=3H`$ slots), pair them with $`2s'`$ real ports and $`R-2s'`$ dummy ports, set $`r:=\lceil\sqrt{R}\rceil`$, $`q:=\lceil R/r\rceil`$, $`R':=rq`$, and identify $`[R']=[q]\times[r]`$. Route slots to ports through a 3-stage Clos network (stage 1: $`q`$ crossbars of size $`r`$; stage 2: $`r`$ crossbars of size $`q`$; stage 3: $`q`$ crossbars of size $`r`$). A crossbar of size $`\rho`$ takes a $`\lceil\log \rho!\rceil`$-bit control word (codes $`\ge\rho!`$ decode to the identity).

**Lemma 9** (Clos rearrangeability; Lean `regular_bipartite_coloring`, `clos_rearrangeable`). Every bijection $`\psi`$ of $`[q]\times[r]`$ is realised by a 3-stage Clos setting $`(s^1_a, s^2_k, s^3_{a'})`$.

*Proof.* The bipartite multigraph on left vertices $`[q]`$ and right vertices $`[q]`$ with edge set $`[q]\times[r]`$ joining $`a`$ to $`(\psi(a,i))_1`$ is $`r`$-regular. By Hall’s theorem and induction on $`r`$ (`regular_bipartite_coloring`), it admits a proper $`r`$-edge-colouring $`\mathrm{col}:[q]\times[r]\to[r]`$. Setting $`s^1_a(i):=\mathrm{col}(a,i)`$, $`s^2_k(a):=(\psi(a,(s^1_a)^{-1}(k)))_1`$, and $`s^3_{a'}(\mathrm{col}(z)):=(\psi(z))_2`$ realises $`\psi`$ (`clos_rearrangeable`). ∎

A description $`d=(\text{gate types}\in\{0,1\}^{4s'},\;\text{control words})`$ has length $`D:=4s'+2q\lceil\log r!\rceil+r\lceil\log q!\rceil`$. Call $`d`$ *valid* ($`d\in\Delta_s`$) if every real port $`(i,p)`$ receives a non-padding slot of a source $`h<n+i-1`$. By Lemmas 8–9, every circuit of size $`\le s`$ equals $`C_d`$ for at least one $`d\in\Delta_s`$, and $`|\Delta_s|\le 2^D`$. For $`s=\lceil cn\rceil`$ ($`c\ge1`$) and $`\log n\ge 24\log(15c)+61`$, a direct calculation gives $`12n\le D\le 25cn\log n`$.

## 4. Moment potential, block-XOR family, and Lean-checked parameters

For $`m\ge1`$, define $`\Phi_m(F):=\sum_{d\in\Delta_s}\operatorname{cor}(C_d,F)^{2m}`$. Clearly $`\Phi_m(F)\ge\#\{d\in\Delta_s:C_d=F\}`$ (`potential_ge_count`, `corr_self`), so $`\Phi_m(F)<1`$ implies $`C_F>s`$. Expanding the power (`corr_pow_expand`) gives
``` math
\operatorname{corr}(g,F)^u = \sum_{x\in(\{0,1\}^n)^u} \prod_{i=1}^u \operatorname{sgn}(g(x_i))\prod_{i=1}^u \operatorname{sgn}(F(x_i)).
```
Partition $`[n]`$ into $`t`$ blocks $`B_\ell`$ of sizes $`b_\ell\le b:=\lceil\log n\rceil`$. A block-XOR function is $`F_T(x):=\bigoplus_{\ell=1}^t T_\ell(x|_{B_\ell})`$ for tables $`T_\ell:\{0,1\}^{B_\ell}\to\{0,1\}`$. Given a partial assignment $`P`$ fixing some table entries, let $`\mathbb{E}_P`$ average uniformly over the unfixed entries.

**Lemma 10** (Block-XOR sign sum and even-tuple bound; Lean `blockXor_partial_sign_sum`, `even_tuples_card_le`, `blockGood_card_le`). For every partial assignment $`P`$ and every $`u`$-tuple $`x=(x_1,\dots,x_u)\in(\{0,1\}^n)^u`$,
``` math
\mathbb{E}_P\prod_{i=1}^u \operatorname{sgn}(F_T(x_i)) = \prod_{\ell=1}^t G_\ell^P(x_1|_{B_\ell},\dots,x_u|_{B_\ell}),
```
where $`G_\ell^P(v):=\prod_w \gamma_{\ell,w}\in\{-1,0,1\}`$, with $`c_w:=\#\{i:v_i=w\}`$ and $`\gamma_{\ell,w}:=\operatorname{sgn}(T_\ell(w))^{c_w}`$ if $`(\ell,w)`$ is fixed in $`P`$ and $`\gamma_{\ell,w}:=[c_w\text{ even}]`$ otherwise. Over an alphabet of size $`A`$, at most $`k^{2k}A^k`$ tuples of length $`2k`$ have every symbol occurring evenly; hence the number of block-even tuples in $`(\{0,1\}^n)^{2m}`$ is at most $`\prod_{\ell=1}^t m^{2m}2^{b_\ell m}`$.

**Proposition 11** (Expected potential and parameter inequality; Lean `potential_sum_le`, `potential_params_lt`, `expected_potential_lt_of_params`, `blocks_le_of_ratio`). We have $`\mathbb{E}_T\Phi_m(F_T)\le |\Delta_s|\cdot N^{-2m}\prod_\ell m^{2m}2^{b_\ell m}`$. Moreover, if $`|\Delta_s|\le 2^D`$, $`\sum_\ell b_\ell=n`$, $`m\le 2^a`$, $`8ta\le n`$, $`2D\le mn`$, and $`mn>0`$, then $`\mathbb{E}_\emptyset\Phi_m(F_T)<1`$ (and $`8ta\le n`$ follows from $`(t-1)b<n`$, $`16a\le b`$, and $`16a\le n`$).

Setting $`b:=\lceil\log n\rceil`$, $`t:=\lceil n/b\rceil`$, $`m:=\lceil 2D/n\rceil`$, $`j:=2m`$, and $`a:=\lceil\log m\rceil`$, the closed-form condition $`\log n\ge L_0(c)`$ implies $`D\le 25cn\log n`$, $`m\le 51c\log n`$, $`16a\le b`$, and the degree bound of Section 5, so Proposition 11 applies. Table 2 reports the numerical thresholds checked by `scripts/params.py`.

| $`c`$ | $`D/(cn\log n)`$ | $`m/(c\log n)`$ | $`S/(c^2 n\log n)`$ | Exact $`\Phi<1`$ | Lean $`8ta\le n`$ | Closed $`16a\le b`$ |
|---:|---:|---:|---:|---:|---:|---:|
| $`1`$ | $`18.12`$ | $`36.25`$ | $`8452.6`$ | $`\log n\ge 43`$ | $`\log n\ge 96`$ | $`\log n\ge 208`$ |
| $`3.5`$ | $`15.01`$ | $`30.02`$ | $`5731.3`$ | $`\log n\ge 50`$ | $`\log n\ge 112`$ | $`\log n\ge 240`$ |
| $`4`$ | $`14.86`$ | $`29.72`$ | $`5611.2`$ | $`\log n\ge 51`$ | $`\log n\ge 112`$ | $`\log n\ge 240`$ |
| $`16`$ | $`14.14`$ | $`28.28`$ | $`5024.8`$ | $`\log n\ge 60`$ | $`\log n\ge 128`$ | $`\log n\ge 272`$ |
| $`64`$ | $`14.06`$ | $`28.11`$ | $`4917.9`$ | $`\log n\ge 68`$ | $`\log n\ge 152`$ | $`\log n\ge 320`$ |

*Table 2: Exact parameter ratios at $`\log n=200`$ and first $`\log n`$ meeting each condition (`scripts/params.py`).*

## 5. Deterministic search and the counting network

Algorithm $`A_c(n)`$ fixes the $`\le 2nt`$ entries of the block tables $`T_\ell`$ one by one: at each entry $`e`$, it evaluates the nonnegative integers $`Z_{P\cup\{e\mapsto 0\}}`$ and $`Z_{P\cup\{e\mapsto 1\}}`$, where
``` math
Z_P := N^{2m}\mathbb{E}_P\Phi_m(F_T) = \sum_{d\in\Delta_s}\sum_{x\in(\{0,1\}^n)^j} \operatorname{sgn}\!\Bigl(\bigoplus_{k=1}^j C_d(x_k)\Bigr)\prod_{\ell=1}^t G_\ell^P(x|_{B_\ell}),
```
and picks the value with smaller $`Z`$. Because $`2Z_P=Z_{P,e\mapsto 0}+Z_{P,e\mapsto 1}`$ and $`Z_\emptyset<N^{2m}`$, the final $`F_T`$ satisfies $`\Phi_m(F_T)<1`$, hence $`C_{F_T}>s`$.

To compute $`Z_P`$ as a single bipartite tensor contraction, set $`\kappa:=\lceil\log(H+1)\rceil`$ (with $`H`$ coding $`\bot`$). A *record* is $`(\sigma\in\{0,1\}^\kappa,\beta\in\{0,1\}^j)`$. The binary variables are: the description $`d`$ ($`D`$ bits), evaluation inputs $`x_{i,h}`$ ($`j n`$ bits), gate traces $`y_{i,g}`$ ($`j s'`$ bits), and records at layers $`L_0,L_1,L_2,L_3`$ ($`4R'(\kappa+j)`$ bits). The constraint vertices are:

- (V1) slot vertices enforcing $`L_0=(h,\mathrm{bundle}_h)`$ (or $`(\bot,0^j)`$ for padding);

- (V2) crossbar vertices enforcing $`\mathrm{out}_{\pi_w(k)}=\mathrm{in}_k`$ for all $`k`$;

- (V3) gate vertices enforcing $`\sigma_1,\sigma_2<n+i-1`$ and $`y_{k,i}=\mathrm{type}_i(\beta_1[k],\beta_2[k])`$;

- (V4) dummy/padding port vertices ($`\equiv 1`$);

- (V5) one output vertex carrying $`\operatorname{sgn}(\bigoplus_k y_{k,s'})`$;

- (V6) block vertices $`\ell`$ carrying $`G_\ell^P`$.

Each variable vertex carries $`\mathrm{EQ}_u`$ (with unary all-ones tensor $`(1,1)`$ on each 1-reader description bit). Every edge joins a variable vertex to a constraint vertex, so the graph is bipartite. For invalid $`d`$, some gate index test fails (since $`\bot=H`$ fails every test); for valid $`d`$, acyclicity forces a unique trace $`y`$ with $`y_{k,s'}=C_d(x_k)`$, so the contraction equals $`Z_P`$.

For $`\log n\ge L_0(c)`$, the edge count is $`S=D+4jn+4js'+j+8R'(\kappa+j)\le 2\cdot10^4 c^2 n\log n`$, every crossbar has degree $`\le 1100 c^{1.5}\sqrt{n}\log n\le n^{0.9}\le S^{0.9}`$, entries lie in $`\{-1,0,1\}`$ and are computable in $`\mathrm{poly}(n)`$ time. Applying (T4) modulo $`2^{P_0}`$ with $`P_0=D+jn+2\le S`$ (or Theorem 6 directly over $`\mathbb{Z}`$) evaluates each $`Z_P`$ in $`2^{K_1 c^2 n\sqrt{\log n}}`$ time. Summing over $`\le 2nt`$ steps proves Theorem 1; replacing $`c`$ by $`\lambda(n)\le(\log n)^{\kappa_0}`$ proves Theorem 2.

## 6. Tableau theorem and Corollaries B and $`B_\lambda`$

Let $`M`$ decide $`L`$ in time $`T(n)`$ (with $`\log T(n)\ge n`$ nondecreasing and $`\mathrm{poly}(n)`$-computable), and let $`M'`$ be its single-tape simulation (time $`T'=O(T^2)`$, space $`\le T`$, returning its head to cell 0 upon halting and freezing both halting states forever). Its tableau 3-CNF $`\Phi_x`$ (variables $`X[t,p,\cdot]`$ and chain variables $`Z_v`$ splitting transition clauses into 3-clauses, with no accept clause) has a unique satisfying $`X`$-part (the run of $`M'`$ on $`x`$) and a canonical satisfying assignment $`\alpha_x`$ setting $`Z_v:=1`$ iff the prefix literals $`l_0,\dots,l_v`$ are all false. Define $`\mathrm{Tab}_L(x,z):=\alpha_x(z)`$ on lengths $`N(n):=n+\ell_{\mathrm{lab}}(n)`$ (and $`0`$ off this image); then $`\mathrm{Tab}_L\in\mathsf{E}`$.

**Theorem 12** (Theorem $`T^*`$; conditional on (G)). Let $`w(N)\ge N`$. Either $`C_{\mathrm{Tab}_L}(N)>w(N)`$ for infinitely many $`N`$, or $`L\in\mathsf{ONTIME}[t]\cap\mathsf{coONTIME}[t]`$ with $`t(n)=2^{A\cdot V/\sqrt{\log V}}\cdot\mathrm{poly}(V)`$ and $`V\le 3w(N(n))+2B\cdot N(n)`$ for large $`n`$ ($`A=15C_{(\mathrm{G})}`$, $`B`$ depending only on $`M'`$).

*Proof.* If $`\mathrm{Tab}_L`$ has circuits $`C^{(n)}`$ of size $`\le w(N(n))`$ for all large $`n`$, a verifier $`V(x,C)`$ substitutes $`x`$ into $`C`$, forms the circuit $`D_{C_x}(i)=[\text{clause }i\text{ of }\Phi_x\text{ is violated by }C_x]`$ of size $`\le 3w(N)+B_0(q+n_{\mathrm{in}})+O(1)`$, decides satisfiability of $`D_{C_x}`$ deterministically via Lemma 7, and if unsatisfiable reads off the frozen halting state at cell $`(2^\tau-1,0)`$ (otherwise outputs $`?`$). Soundness follows from uniqueness of $`X`$; completeness with oblivious witness $`w_n=C^{(n)}`$ holds because $`\alpha_x`$ satisfies $`\Phi_x`$. ∎

Applying Theorem 12 to $`L_c`$ with $`w(N)=cN`$ gives $`N\le 4Kc^2 n\sqrt{\log n}`$ and $`V\le (3c+2B)N`$; the Lean-checked inequality `sqrt_saving_linear` ($`A V/\sqrt{\log V}\le A K' n`$ whenever $`2\le n\le V\le K'n\sqrt{\log n}`$) bounds the verifier’s exponent by $`4AKc^2(3c+2B)n`$, proving Corollary 3. Applying Theorem 12 to $`L_\lambda`$ with $`w(N)=N\lambda(N)`$ proves Corollary 4; for the single-language instance given computable, unbounded, nondecreasing $`g`$, define $`H(0):=1`$ and $`H(t+1):=H(t)+1`$ if some $`j\le t`$ satisfies $`g(j)\ge H(t)+1`$ within $`2^t`$ steps (else $`H(t)`$), set $`G(n):=H(\lfloor\log\log n\rfloor)`$, and take $`\lambda:=\max(1,(G/a)^{1/3})`$.

## 7. Extensions and limits

- **Threshold circuits and relativisation (proof outlines).** Replacing $`B_2`$ gates by linear threshold gates with integer weights in $`[-n^a,n^a]`$ (splitting gates of fan-in $`>\sqrt{n}`$ into partial-sum trees and enumerating fan-in profiles) yields $`L\in\mathsf{DTIME}[2^{K(ca)^2 n\sqrt{\log n}}]`$ with no $`\mathsf{THR}_a`$-circuits of wire count $`\le cn`$. Similarly, for any oracle $`O`$, the construction relativises to $`O`$-circuits measured by *wire count* with oracle fan-in $`\le n^{0.8}`$ (it fails under gate count, and Corollary 3 does not relativise).

- **Switch-encoding lower bound (Proposition 5).** Reducing signed to unsigned counting ($`Z_P=N_0-N_1`$) via a Beneš routing network and a $`j`$-wise independent polynomial block family produces $`O(c^2 n\log^2 n\log\log n)`$ gates. Any encoding routing $`R'`$ records of width $`\kappa+j`$ through $`O(1)`$-fan-in switches with $`\le h`$ settings per switch requires $`\Omega(R'\log R')`$ switches (since $`R'!\le h^{\#\text{switches}}`$), hence $`\Omega(c^2 n\log^2 n)`$ gates or clauses—too large for $`\sqrt{\log}`$-saving $`\#3`$-CNF algorithms to beat brute force.

- **Better contraction theorems.** If a contraction theorem achieved savings $`f(S)`$ in the exponent $`S/f(S)`$, the same proof would give $`\mathsf{DTIME}[2^{O(c^2 n\log n/f(n))}]\not\subseteq\mathrm{i.o.}\text{-}\mathsf{SIZE}(cn)`$; $`f(S)=\log S`$ would give $`\mathsf{E}\not\subseteq\mathrm{i.o.}\text{-}\mathsf{SIZE}(cn)`$.

**AI assistance.**

The proofs, adversarial reviews, and Lean formalisation were produced with AI assistance under the author’s direction. The kernel-checked Lean proofs in `PastaMath/FastDiag/` verify the combinatorial core listed in the abstract; the rest of the paper is a human-readable mathematical argument conditional on the inputs in Table 1.

## References

- \[Ant26\] Anthropic, *A $`2^{o(n)}`$ time algorithm for 3-SAT*, October 2026 (with Lean development `github.com/anthropics/formal-math`, directory `eth/`).
- \[OAI26\] OpenAI, *The Exponential Time Hypothesis is False*, October 2026 (Theorem D.1).
