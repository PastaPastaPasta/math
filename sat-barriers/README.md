# Extensions of the Buss–Williams 2cos(π/7) barrier for SAT versus DTS

A Lean 4 formalisation extending the Buss–Williams (2015) alternation-trading barrier `r_7 = 2cos(π/7) ≈ 1.801938` for SAT versus deterministic time n^c and space n^{o(1)} (DTS) across stronger rule sets and proof notions:

- **Weakened slowdown envelopes and two-flag slowdowns:** the barrier `r_7` holds whenever slowdowns satisfy `e ≥ c·max(b, a)` and `e ≥ B + β(c − 1)max(b, a)` with `β ≥ β* = 1/(r_7(r_7 − 1)) ≈ 0.692` (`no_refutation`, `e1beta_limit`, `bw_limit`), and with an even smaller additive factor `β_2 ≥ β_non = r_7(2 − r_7)/(r_7 − 1) ≈ 0.445` on consecutive slowdowns (`no_refutation2`).
- **Rule 2, public-coin protocols, and derived-rule bootstrapping:** two-step rules (`Rule2Step`), multi-round perfect-completeness public-coin protocol steps with `Σ s_i ≥ a − v` (`ProtoStep`), and arbitrary nested derived-rule closure (`BS.Der`) all leave the barrier at `r_7` (`no_refutation_rule2`, `PR.no_refutation_proto`, `BS.no_refutation_der`). Derived single-block inclusions satisfy `a ≤ c·max(s, v)` (`BS.derived_ns`) and `v ≥ (c − 1/(c − 1))·a` strictly for `a > 0` at `c ∈ [r_7, 2)`, `β = 1` (`AU.derived_ns_lower`), and no `κ < 1` universal-input-only speedup is derivable (`BS.derived_kappa`, sharp via `BS.derived_kappa_sharp`).
- **Localized, trace, unconditional, copy-free, and concrete array calculi:** for input-localized speedups with a `β`-envelope, `(1 − β)(c − 1)² ≤ c³ − c² − 2c + 1` is a sufficient non-refutation condition (`no_refutation_locB`, `no_refutation_locT`, `no_refutation_locX`, `no_refutation_locU`, `no_refutation_locC`), which beats `r_7` at `β = 1/2` (`beta_half_beats_r7`) and stays at `r_7` at `β = 1`, including concrete array-exponent semantics (`locs_embed`, `no_locs_refutation`).
- **Non-strict refutations (Williams Lemma 4.3):** ending at `a' ≤ a_0` from `a_0 > 0` in at least two steps is excluded for `Step c β` (`c ≥ r_7`, `β ≥ β*`, `AU.no_refutation_nonstrict`) and `LStepX c 1` (`c > r_7`, `AU.no_refutation_locX_nonstrict`).

All results are unconditional theorems about the formalised rule systems, checked in Lean 4 against standard axioms only.

- Paper: [`paper/paper.tex`](paper/paper.tex) (reference version), [`paper/paper.pdf`](paper/paper.pdf), and [`paper/paper.md`](paper/paper.md). Rebuild the PDF with `tectonic paper.tex`; regenerate `paper.md` with `python3 tex2md.py ../paper/paper.tex ../paper/paper.md` from [`scripts/`](scripts/) (needs pandoc).
- Lean code: [`../PastaMath/SatBarriers/`](../PastaMath/SatBarriers/)
- Reproducing the check: [`VERIFICATION.md`](VERIFICATION.md)
