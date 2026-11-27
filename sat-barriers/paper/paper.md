# Extensions of the Buss–Williams 2cos(π/7) barrier for SAT time–space alternation trading

**PastaPastaPasta** · November 2026

*Markdown rendering of `paper.tex`, which is the reference version.*

## Abstract

Buss and Williams \[BW15\] proved that alternation-trading proofs for $`\mathsf{SAT}\notin\mathsf{DTS}[n^c]`$ using standard speedup and slowdown rules cannot surpass $`r_7=2\cos(\pi/7)\approx1.801938`$, the root of $`c^3-c^2-2c+1=0`$ in $`(1,2)`$. We formalise in Lean 4 a family of extensions of this barrier covering stronger rule sets and proof notions:

1.  **Weakened slowdown envelopes and two-flag slowdowns.** Slowdowns need only satisfy $`e\ge c\max(b,a)`$ and $`e\ge B+\beta(c-1)\max(b,a)`$ for any $`\beta\ge\beta^*:=1/(r_7(r_7-1))\approx0.6920`$ (`no_refutation`, `e1beta_limit`), and even weaker $`\beta_2\ge\beta_{\mathrm{non}}:=r_7(2-r_7)/(r_7-1)\approx0.4450`$ on consecutive slowdowns (`no_refutation2`).

2.  **Rule 2, public-coin protocols, and derived-rule bootstrapping.** Adding two-step rules (`Rule2Step`), perfect-completeness public-coin multi-round protocol steps with $`\sum_i s_i\ge a-v`$ (`ProtoStep`), or the full inductive closure `Der` of arbitrarily nested derived rules at arbitrary scale leaves the barrier at $`r_7`$ (`no_refutation_rule2`, `no_refutation_proto`, `no_refutation_der`). Any derived single-block inclusion $`\mathsf{DTS}[n^a]\subseteq{}^0\exists^s\mathsf{DTS}[n^v]`$ satisfies $`a\le c\max(s,v)`$ and, for $`c\in[r_7,2)`$ with $`\beta=1`$, $`v\ge(c-1/(c-1))a`$ (strictly when $`a>0`$; `AU.derived_ns_lower`), and no $`\kappa<1`$ universal-input-only speedup is derivable (`BS.derived_kappa`, sharp at $`s_2>0`$ via `BS.derived_kappa_sharp`).

3.  **Localized, trace, unconditional, and copy-free speedups.** For input-localized speedups and chunked slowdowns with a $`\beta`$-envelope, a sufficient non-refutation condition is $`(1-\beta)(c-1)^2\le c^3-c^2-2c+1`$ (`no_refutation_locB`), which beats $`r_7`$ at $`\beta=1/2`$ (`beta_half_beats_r7`) and stays at $`r_7`$ when $`\beta=1`$, even with trace speedups (`no_refutation_locT`), max-envelopes (`no_refutation_locX`), unconditional exponent-$`0`$ removal (`no_refutation_locU_r7`), free-kernel trace steps (`no_refutation_locC`), and concrete array-exponent semantics (`no_locs_refutation`).

4.  **Non-strict refutations.** Williams \[W13, Lemma 4.3\] also counts normal-form proofs ending at $`a'=a`$ (with at least one quantified intermediate line) as contradictions. We exclude non-strict refutations for `Step` at $`c\ge r_7`$, $`\beta\ge\beta^*`$ (`AU.no_refutation_nonstrict`) and for `LStepX` at $`\beta=1`$, $`c>r_7`$ (`AU.no_refutation_locX_nonstrict`).

*What is kernel-checked:* every limit theorem, embedding, sharpness witness, and non-vacuity witness listed above in Lean 4 (`PastaMath/SatBarriers/`). *What is not machine-checked:* the complexity-theoretic soundness of concrete speedup/slowdown rules and the informal claim that specific complexity techniques (such as PCPs or particular interactive proofs) fall inside the formal rule families.

## 1. Introduction

Alternation-trading proofs \[W13\] refute the hypothesis $`H_c:\mathsf{SAT}\in\mathsf{DTS}[n^c]`$ by deriving a normal-form chain of inclusions starting and ending at quantifier-free deterministic time–space classes, $`\mathsf{DTS}[n^{a_0}]\subseteq\cdots\subseteq\mathsf{DTS}[n^{a'}]`$ with $`a'<a_0`$ (or $`a'\le a_0`$ with at least one quantified line, \[W13, Lemma 4.3\]). Buss and Williams \[BW15\] proved that standard speedup and slowdown rules cannot reach $`c\ge r_7=2\cos(\pi/7)`$, the unique root of
``` math
\operatorname{cub}(c):=c^3-c^2-2c+1=0
```
in $`(1,2)`$ (`cub_r7`, `cub_eq_zero_iff`).

To understand what genuinely new rule would be required to surpass $`r_7`$, one needs to know which natural enrichments of the calculus—weaker slowdown envelopes, localized or trace-based speedups, public-coin interactive protocols, non-strict contradictions, and bootstrapping by reusing derived inclusions as new rules—still fail to break $`r_7`$. We formalise all of these barrier extensions in Lean 4 under `PastaMath.SatBarriers`, with standard axioms only.

**AI assistance.**

The proofs and Lean formalisation were produced with AI assistance under the author’s direction. The kernel-checked Lean proofs in `PastaMath/SatBarriers/` are the primary evidence for all formal claims.

## 2. The base calculus and weakened envelopes

A reduced line is `RLine` $`= \mathrm{List}\;\mathbb{R} \times \mathbb{R}`$, storing the list of block superscripts outermost first together with the kernel time exponent $`a`$; write $`\operatorname{top}(l)`$ for the last element of $`l`$ (or $`0`$ if empty).

**Definition 1** (Base calculus `Step` $`c\;\beta`$). Fix $`c,\beta\in\mathbb{R}`$. `Step` $`c\;\beta`$ allows:

- `init`: $`([],a)\to([0],a)`$;

- `speed`: $`(\mathrm{bs}\mathbin{++}[b],a)\to(\mathrm{bs}\mathbin{++}[b_1,b_2],a_2)`$ for $`0\le x\le a`$, $`\max(x,b)\le b_1`$, $`b\le b_2`$, $`a-x\le a_2`$;

- `slow`: $`(\mathrm{bs}\mathbin{++}[b],a)\to(\mathrm{bs},e)`$ whenever $`c\max(b,a)\le e`$ and $`\operatorname{top}(\mathrm{bs})+\beta(c-1)\max(b,a)\le e`$;

- `weak`: componentwise raising of superscripts and kernel.

A strict normal-form refutation `RefutesWith` $`R\;n\;L`$ has $`n\ge1`$, $`L(0).1=L(n).1=[]`$, $`0\le L(0).2`$, $`L(n).2<L(0).2`$, $`R(L(i),L(i+1))`$ for all $`i<n`$, and $`L(i).1\ne[]`$ for $`0<i<n`$.

Set $`\beta^*:=1/(r_7(r_7-1))\approx0.69202`$ and $`\beta_{\mathrm{non}}:=r_7(2-r_7)/(r_7-1)\approx0.44504`$.

**Theorem 2** (Buss–Williams limit and envelope relaxations). Let $`c\ge r_7`$.

1.  For every $`\beta\ge\beta^*`$, there is no strict refutation in `Step` $`c\;\beta`$ (`no_refutation`). The same holds for any slowdown function $`S(B,M)`$ satisfying $`S(B,M)\ge cM`$ and $`S(B,M)\ge B+\beta(c-1)M`$ (`e1beta_limit`), and in particular for $`S(B,M)=c\max(B,M)`$ (`bw_limit`).

2.  In the two-flag calculus `Step2` $`c\;\beta_1\;\beta_2`$ (`Derivation2.lean`), which tracks whether the preceding step was a speedup and permits a smaller additive factor $`\beta_2`$ on consecutive slowdowns, no strict refutation exists whenever $`\beta_1\ge\beta^*`$ and $`\beta_2\ge\beta_{\mathrm{non}}`$ (`no_refutation2`).

## 3. Rule 2, protocols, and derived-rule bootstrapping

**Definition 3** (Extended single-stack rules).

- `Rule2Step` $`c\;\beta`$ (`Rule2.lean`) adds two-step transitions $`L\to M\to L'`$ through a quantified line $`M`$ (covering Williams’s Speedup Rule 2).

- `ProtoStep` $`c\;\beta`$ (`Protocol.lean`) adds multi-round protocol steps from $`(P\mathbin{++}[b],a)`$ to $`(P\mathbin{++}b::\mathrm{flat}(rs),v)`$ or $`(P\mathbin{++}\mathrm{flat}(rs),v)`$ with $`0\le b`$, $`0\le a`$, $`0\le v`$, and any nonempty list $`rs`$ of pairs $`(s_i,t_i)`$ with $`s_i,t_i\ge b`$ and $`\sum_i s_i\ge a-v`$.

- `BS.Der` $`R`$ (`Bootstrap.lean`) is the inductive closure of $`R`$ under finite composition through quantified lines, modelling the reuse of derived inclusions as new rules at any nesting depth (and, by scale invariance `step_scale`, at any scale).

Every `ProtoStep` expands into a finite path of `Step` moves (`PR.proto_path`), and `Der (Der R)` collapses to `Der R` (`BS.der_der`).

**Theorem 4** (Protocol and bootstrapping limits). For $`c\ge r_7`$ and $`\beta\ge\beta^*`$, there is no strict refutation in `Rule2Step` $`c\;\beta`$ (`no_refutation_rule2`), in `ProtoStep` $`c\;\beta`$ (`PR.no_refutation_proto`), or in `BS.Der` (`Step` $`c\;\beta`$) (`BS.no_refutation_der`).

**Theorem 5** (Limits on derived inclusions). Let $`c\ge r_7`$ and $`\beta\ge\beta^*`$. Suppose a `Step` $`c\;\beta`$ derivation starts at $`([],a)`$ with $`a\ge0`$ and stays quantified on steps $`1,\dots,n`$.

1.  If $`L(n)=([s_1,s_2],v)`$ with $`s_2\le0`$ (a universal block passing only the input), then $`a\le s_1+v`$ (`BS.derived_kappa`). This is sharp in $`s_2`$: at $`c=181/100>r_7`$, `BS.derived_kappa_sharp` derives $`([0,1/2],181/200)`$ from $`([],1)`$ with $`0+181/200<1`$.

2.  If $`L(n)=([s],v)`$ and $`\beta\le1`$, then $`a\le c\max(s,v)`$ (`BS.derived_ns`).

3.  When $`\beta=1`$ and $`c\in[r_7,2)`$, any derivation ending at $`([s],v)`$ satisfies $`v\ge\tau_0(c)\,a`$ where $`\tau_0(c):=c-1/(c-1)`$, and strictly $`v>\tau_0(c)\,a`$ whenever $`a>0`$ (`AU.derived_ns_lower`).

## 4. Localized, trace, unconditional, and concrete array calculi

In `Localized.lean`–`LocalizedCopy.lean`, a line `LLine` $`= \mathrm{List}\;\texttt{LBlock} \times \mathbb{R} \times \mathbb{R}`$ records each block’s superscript $`b`$, creation split $`x_c`$, and creation locality $`l_c`$, plus the current kernel exponent $`a`$ and locality exponent $`l`$. Localized speedups set the new block’s superscript from $`l`$ rather than from $`b`$; trace speedups (`LStepT`) allow setting $`b_2`$ from $`a-x`$; max-envelopes (`LStepX`) weaken the slowdown constraint to take the maximum of either envelope; unconditional removal (`LStepU`) allows dropping a block with $`b\le0`$ and $`a\le0`$ without paying a factor $`c`$; and `LStepC` allows free kernel time on trace steps.

The potential function (`LocalizedBeta.lean`)
``` math
\Psi_\beta(c,b,d,l) := \min\!\left(\max(b,d),\;\max\!\left(b+\beta(c-1)l,\; cl,\; \frac{d+l}{c}\right)\right)
```
governs all five localized systems simultaneously.

**Theorem 6** (Localized $`\beta`$-envelope threshold). Let $`0\le\beta\le1`$ and $`c\ge1`$ satisfy $`(1-\beta)(c-1)^2\le c^3-c^2-2c+1`$. Then no strict refutation exists in `LStepB` $`c\;\beta`$ (`no_refutation_locB`), `LStepT` $`c\;\beta`$ (`no_refutation_locT`), `LStepX` $`c\;\beta`$ (`no_refutation_locX`), `LStepU` $`c\;\beta`$ (`no_refutation_locU`), or `LStepC` $`c\;\beta`$ (`no_refutation_locC`). In particular, at $`\beta=1`$ none of these systems has a strict refutation for $`c\ge r_7`$ (`no_refutation_loc`, `no_refutation_locU_r7`). Conversely, at $`\beta=1/2`$ there exist $`c>r_7`$ with an `LStepB` $`c\;(1/2)`$ refutation (`beta_half_beats_r7`).

In `LocsEmbed.lean`, we define the concrete array-exponent calculus `LocsStep` $`c`$ with invariant `CInv` tracking creation-time parent bounds, prove that every concrete step abstracts to `LStepX` $`c\;1`$ (`locs_embed`), and conclude that no concrete refutation exists for $`c\ge r_7`$ (`no_locs_refutation`), while Lipton–Viglas gives a 4-step refutation at $`c=7/5`$ (`lv_locs_refutes`).

## 5. Non-strict refutations

Williams \[W13, Lemma 4.3\] also treats a normal-form proof $`\mathsf{DTS}[n^{a_0}]\subseteq\cdots\subseteq\mathsf{DTS}[n^{a'}]`$ with $`a'\le a_0`$ (and $`n\ge2`$, so at least one quantified intermediate line) as a contradiction. In `Audit.lean`, `RefutesNS` and `LRefutesXNS` formalise this non-strict predicate for $`a_0>0`$.

**Theorem 7** (Exclusion of non-strict refutations).

1.  For $`c\ge r_7`$ and $`\beta\ge\beta^*`$, there is no non-strict refutation in `Step` $`c\;\beta`$ (`AU.no_refutation_nonstrict`).

2.  For $`c>r_7`$, there is no non-strict refutation in `LStepX` $`c\;1`$ (`AU.no_refutation_locX_nonstrict`).

Non-vacuity is witnessed by `AU.lv_refutesNS` at $`c=7/5`$.

## 6. Scope and limitations

All theorems above are unconditional statements about the formalised rule systems. They do not rule out new complexity-theoretic rules that violate the formal inequalities (for example, fast-forwarding small-space segments below the derived $`\tau_0(c)`$ floor, or slowdown envelopes with $`\beta<1`$ in the localized setting, which Theorem 6 shows can surpass $`r_7`$).

## References

- \[BW15\] S. Buss and R. Williams, *Limits on alternation-trading proofs for time-space lower bounds*, Computational Complexity **24** (2015), 533–600.
- \[W13\] R. Williams, *Alternation-trading proofs, linear programming, and lower bounds*, ACM Transactions on Computation Theory **5** (2013), no. 2, Article 6.
