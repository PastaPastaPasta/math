# QBF_k versus DTS: the alternation-trading calculus stops at Williams's exponent

For a Lean 4 formalisation of the alternation-trading calculus of R. Williams, "Alternation-Trading Proofs, Linear Programming, and Lower Bounds" (TOCT 2013, §5), for QBF_k versus deterministic time n^c and space n^{o(1)} (DTS):

- for every integer k ≥ 1 and every real c > k with c³/k − c² − 2c + k ≥ 0 (that is, c ≥ c_k, the root in (k, k+1) of Williams's Theorem 5.1 polynomial), no refutation exists in the formalised calculus `QStep c k` (`qbf_no_refutation`, `qbf_no_refutation_reach`, `not_refutes`);
- strictly above c_k (when c³/k − c² − 2c + k > 0), even non-strict refutations (ending at a′ ≤ a₀ from a₀ > 0 in at least one step) are impossible (`qbf_no_refutation_strict`);
- at k = 1, the threshold parameter equals 2cos(π/7) (`par_one_eq_r7`), recovering the Buss–Williams SAT-versus-DTS limit (`sat_no_refutation`);
- on the lower side, an executable rational checker `checkL` of the literal rules (tracking guesses, input floor 1, and x ≤ a − 1) is proved sound into `QStep` (`checkL_sound`), and explicit literal refutations checked with `decide +kernel` verify the lower endpoints c = 7/4 (k = 1, 140 lines), 289/100 (k = 2, 324 lines), 393/100 (k = 3, 432 lines), and 989/200 (k = 4, 540 lines), bracketing the formal thresholds (`interval_k1`–`interval_k4`).

That the formal rules coincide with Williams's brief prose description in §5 is a modelling claim discussed in Section 2 of the paper. Williams's Theorem 5.1 construction achieving every c < c_k is a paper result, not formalised in general here; only the four concrete rational certificates for k = 1..4 are kernel-checked. The limit applies only to this proof calculus.

- Paper: [`paper/paper.tex`](paper/paper.tex) (reference version), [`paper/paper.pdf`](paper/paper.pdf), and [`paper/paper.md`](paper/paper.md). Rebuild the PDF with `tectonic paper.tex`; regenerate `paper.md` with `python3 tex2md.py ../paper/paper.tex ../paper/paper.md` from [`scripts/`](scripts/) (needs pandoc).
- Lean code: [`../PastaMath/QbfThreshold/`](../PastaMath/QbfThreshold/)
- Independent exact-rational checker and certificate JSON files: [`scripts/`](scripts/)
- Reproducing the check: [`VERIFICATION.md`](VERIFICATION.md)
