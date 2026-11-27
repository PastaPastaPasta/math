# Fast derandomised diagonalisation against linear-size circuits

A moment-potential construction yielding linear-size and weakly superlinear circuit lower bounds in sub-brute-force deterministic time and in `NE ∩ coNE`, **conditional on a `2^{O(S/√log S)}` tensor-network contraction theorem for networks of maximum degree up to `S^{0.9}`**:

- **Theorem A (conditional on (T4) or (T4-A)):** for every `c ≥ 1`, a language `L_c ∈ DTIME[2^{K c² n √log n}]` (explicit up to the absolute constant of Anthropic's Theorem B) has `B₂`-circuit complexity `> cn` at every large `n` (against `2^{Θ(cn log n)}` for brute-force diagonalisation).
- **Theorem A_λ / Corollary C (conditional on (T4) or (T4-A)):** for every `c ≥ 1`, `DTIME[2^{K c² n log n}] ⊄ i.o.-SIZE(c·n (log n)^{1/4})`.
- **Corollaries B and B_λ (conditional on ((T4) or (T4-A)) and (G)):** combined with a canonical-assignment tableau verifier and Anthropic's `#3`-CNF counting theorem, `NE ∩ coNE ⊄ SIZE(cn)` (even in `ONTIME ∩ coONTIME`) for every `c`, and for every computable, unbounded, nondecreasing `g`, a single language in `NTIME ∩ coNTIME[2^{n·g(n)}]` has `C(n) > cn` infinitely often for every `c`.
- **Proposition M (unconditional):** bounded-fan-in switch encodings of the moment estimator require `Ω(c² n log² n)` gates/clauses, explaining why the published Lean-exported `#3`-CNF statement alone does not beat brute force without the heavy-crossbar contraction theorem.

**What is kernel-checked in Lean 4 (`PastaMath/FastDiag/`):** the unconditional combinatorial core — the moment-potential bound (`potential_ge_count`, `potential_sum_le`, `exists_hard_of_potential`), block-XOR sign-sum identities (`blockXor_partial_sign_sum`), even-tuple bound (`even_tuples_card_le`, `blockGood_card_le`), integer parameter inequality (`blocks_le_of_ratio`, `potential_params_lt`, `expected_potential_lt_of_params`), 3-stage Clos rearrangeability via König's theorem from Hall's theorem (`regular_bipartite_coloring`, `clos_rearrangeable`), and the `√log` exponent arithmetic (`sqrt_saving_linear`, `sqrt_saving_superlinear`, `ew_threshold`, `ew_threshold_sharp`).

**What is NOT machine-checked:** the fan-out-3 normal form, the bipartite tensor network and running-time analysis, the tableau verifier, the threshold/relativisation outlines, and the external October 2026 contraction and `#3`-CNF theorems (OpenAI Thm D.1 and Anthropic Lemma 8 / Thm A / Thm B / Main Theorem, which are AI-written and have not been human-refereed).

- Paper: [`paper/paper.tex`](paper/paper.tex) (reference version), [`paper/paper.pdf`](paper/paper.pdf), and [`paper/paper.md`](paper/paper.md). Rebuild the PDF with `tectonic paper.tex`; regenerate `paper.md` with `python3 tex2md.py ../paper/paper.tex ../paper/paper.md` from [`scripts/`](scripts/) (needs pandoc).
- Lean code: [`../PastaMath/FastDiag/`](../PastaMath/FastDiag/)
- Parameter-threshold script: [`scripts/`](scripts/)
- Reproducing the check: [`VERIFICATION.md`](VERIFICATION.md)
