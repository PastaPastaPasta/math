# Scripts

Python 3 standard library only (tested with Python 3.11 and 3.13). Run from this directory. None of these scripts is part of the kernel-checked results; they re-check the Lean data independently, replay proofs from Williams's text, and compute the numbers of the paper that are not in Lean.

| Script | What it does | Written from | Time |
|---|---|---|---|
| `dag_check.py` | Exact re-implementation of `HD.dagCheck` and `HDS.dagCheck`, run on the node lists of `StairD{1,2,3}.lean`; prints nodes, speedup steps, root ratio c·φ, the starting exponent a₀ and an upper bound on the unfolded length (exact, and rounded up) | the Lean definitions | < 1 s |
| `abs_check.py` | Exact re-implementation of `HLM.absCheck`, run on the data of `Ceiling.lean`, and on two perturbations of it that should fail | the Lean definitions | < 1 s |
| `replay39.py` | Replays the 39-line proof `HY.cert39` and prints it; with `--log-one`, `--log-in` or `--log-sp`, in the variant in which the new log n block of Lemma 3.3 has output exactly 1, max(b, 1) or max(1, e); reports the slowdowns at which b_k would matter | Williams's rules (TOCT text) | < 1 s |
| `w13_25line.py` | Replays the 25-line proof printed in Williams's §7.2 under the formal rules, with outputs max(b, e), 1, max(b, 1) and max(1, e) for the new log n block, per transition, and compares the carried superscripts with Williams's default (calibration; a replay of a rounded display, not a proof) | Williams's rules and printed proof | < 1 s |
| `inventory.py` | Replays every other displayed derivation of Williams's §7 (p. A:31 example, Lemma 7.7, Corollary 7.8, the proof of Theorem 7.5, the sketch of Theorem 7.9) at exact rational parameter values against `HY.Step` and its variants, and lists the differences (paper Appendix A) | Williams's displays, transcribed from the rendered pages | < 1 s |
| `staircase.py` | The staircase recursion: levels at a given c, the bisection estimates c_h, an estimate of c*_stair from a bracket with certified verdicts, and r_d, √(1+1/d), 1+1/(d+1) | paper Section 7.2 | < 1 s each |
| `stair_cert.py` | Untrusted generator of staircase certificates (JSON) | the recursion's structure | about 40–55 s (d = 3) to several minutes (d = 1) |
| `tex2md.py` | Regenerates `../paper/paper.md` from `../paper/paper.tex` (needs pandoc; tested with 3.12) | — | < 1 s |

## Commands and expected output

```sh
python3 dag_check.py ../../PastaMath/OneTapeThreshold/StairD1.lean ../../PastaMath/OneTapeThreshold/StairD2.lean ../../PastaMath/OneTapeThreshold/StairD3.lean
```
Both readings accept all three certificates: d = 1, c = 130921174/10⁸, M = 2⁵⁶, 552 nodes, 3915 speedup steps, root c·φ ≈ 0.99916308, a₀ = 141318262916700694 ≈ 1.41·10¹⁷, at most 7,612,424,501,336,017,218,794 ≤ 7.62·10²¹ unfolded lines; d = 2, c = 11915968/10⁷, M = 2⁵⁰, 286 nodes, 1846 steps, ≈ 0.99940456, a₀ ≈ 1.68·10¹⁵, at most 246,214,170,679,702,105 ≤ 2.47·10¹⁷ lines; d = 3, c = 11386523/10⁷, M = 2⁵⁰, 212 nodes, 1255 steps, ≈ 0.99961709, a₀ ≈ 1.50·10¹⁵, at most 1,099,999,000,347,752 ≤ 1.10·10¹⁵ lines. The unfolded length counts the lines of the derivation that `HD.nf_of_SC` builds if no level is closed early, which is an upper bound.

```sh
python3 abs_check.py ../../PastaMath/OneTapeThreshold/Ceiling.lean
```
Accepts the three ceilings: c₀ = 6547/5000, d = 1, 105 abstract states, levels θ = 1.027, 1.017, 1.014; c₀ = 149/125, d = 2, 50 states, θ = 1.011, 1.008; c₀ = 712/625, d = 3, 19 states, θ = 1.0055. In each case θ₀ = c₀² − c₀/(d+1). The script also runs two perturbed checks and prints REJECT for both in each case: c₀ lowered by 10⁻⁴ with θ₀ recomputed (levels and states unchanged), and the last abstract state removed.

```sh
python3 replay39.py ../../PastaMath/OneTapeThreshold/Proof39.lean
```
Prints the 39 lines (exponents divided by 1000); final exponent 99994.12966… < 10⁵; every side condition, alternation, the strict normal form, kernel time ≥ input superscript and space ≤ time hold; the smallest gap time − input is about 4.63·10⁻²⁰ (line 12), and it is below 10⁻⁶ on lines 12, 23 and 36.

```sh
python3 replay39.py --log-one ../../PastaMath/OneTapeThreshold/Proof39.lean
python3 replay39.py --log-in ../../PastaMath/OneTapeThreshold/Proof39.lean
python3 replay39.py --log-sp ../../PastaMath/OneTapeThreshold/Proof39.lean
```
The same tags with output exactly 1 for the new log n block of Lemma 3.3: every side condition, alternation, the strict normal form, time ≥ input and space ≤ time hold; lines 2, 3, 6, 9, 12, 16, 17, 20, 23, 27, 30, 33 and 36 differ from the replay above only in the output superscripts of log n blocks, no kernel differs, and the final exponent is the same. With `--log-in` (output max(b, 1)) no line differs, since e ≤ b at every Lemma 3.3 step; with `--log-sp` (output max(1, e)) the same lines as with `--log-one` differ, again only in log n outputs. In every mode the output b_k of the remaining prefix is never the strict maximum of a Lemma 7.2 step. This is a script check; Lean checks these variants for the staircase certificates (`conjecture_fails_O`), not for the 39-line proof.

```sh
python3 w13_25line.py
```
Every step of Williams's printed 25-line proof (c = 1.297844, d = 1) is a rule of the formal calculus with its side conditions. Compared are the kernel exponents (time, and space on DTISP lines) and, for every block, max(guess, 1), because the display prints guesses below 1 as n^1 (the first block's computed guess is 0.999997582); output superscripts are not printed and not compared. The largest deviation from a printed number is 1.02·10⁻⁸ for kernel exponents and 5.6·10⁻⁹ for guesses; a per-transition table lists them, and the printed existential guess drops at lines 12 and 22 (1.040108911 → 1.040108909, 1.040108908), which no merged rule does (rounding). The replay is run with outputs max(b, e), 1, max(b, 1) and max(1, e) for the new log n block; all give the same deviations and kernels, so the display does not decide between the readings. Under max(b, e) no Lemma 7.2 step has b_k as the strict maximum (under outputs 1 and max(1, e), the slowdowns to lines 10 and 23 have it, by less than 6·10⁻⁹). Under max(b, e) the log n blocks of lines 13, 16, 19 and 22 carry the output ≈ 1.040108914 (inherited from the existential block), where Williams's default for an omitted superscript (max{guess, 1}, p. A:5, read block-wise) is 1; these are the only carried superscripts that differ from the default by more than 10⁻⁷, and the next Lemma 7.2 step hides the difference. The computed last line, 1.7519584642, is 1.02·10⁻⁸ above the printed start 1.751958454 and rounds to 1.751958464, so it does not agree in the last printed digit, and at c = 1.297844 the replay is not a strict normal-form proof: it is a replay of Williams's rounded display, agreeing with it to within 1.02·10⁻⁸, not a verified proof at that c.

```sh
python3 inventory.py
```
Replays every other displayed derivation of Williams's §7 against `HY.Step` at exact rational parameter values satisfying Williams's side conditions, under the outputs max(o, e), 1, max(o, 1) and max(1, e) for the new log n block, from the printed previous line and from the computed one, and ends with a summary of the transitions that differ. The p. A:31 example and Lemma 7.7 agree. In the proof of Theorem 7.5 (d = 1, c = 1.29, a = 1.76, x = 0.26) the slowdown to DTISP[n^c, n^{d/(d+1)}] differs (DTIME_d[n^c] by the rules), and the second use of Corollary 7.8 prints (∀ n) where the rules give (∀ log n) with output x + d(a − 1) (1 for output 1); the line after each is reproduced; the final exponent is 1.697382 < 1.76. Corollary 7.8 is reached exactly from 399 sample exponents in [1, η). In the sketch of Theorem 7.9: the log n output of [1,1,0,0] and Case 2 is matched only by output 1 in general; that of Case 1 only by max(o, 1); Case 1 prints the guess n^y where the rules give n^{y+e}; the 0,1,0 and 0,0 slowdowns omit b′ (45/4 against 15 in the example); the last slowdowns of Case 1 and Case 2 print larger exponents than Lemma 7.2 gives (63/8 against 45/8, 45/4 against 63/8). The paper's Appendix A lists all of these with their coverage.

```sh
python3 staircase.py roots
python3 staircase.py levels 1.3092 1
python3 staircase.py appear 1 6
python3 staircase.py threshold 1 60     # also 2 60, 3 60
```
`roots`: r₁ = 1.3009428844, r₂ = 1.1887894930, r₃ = 1.1372807069; the bisection estimates c₁ = 1.330277691377, 1.199453639736, 1.142696215782 and the roots of the cubics 8c³ − 2c² − 13c + 2, 36c³ − 9c² − 46c + 6, 96c³ − 20c² − 113c + 12. `levels 1.3092 1`: seven levels, c·g = 1.059405, …, 0.994144 (refutes at level 6). `appear 1 6`: c₁, …, c₆ ≈ 1.330278, 1.311714, 1.309609, 1.309287, 1.309228, 1.309215 (`appear 2 6`: 1.199454, 1.192559, 1.191768, …; `appear 3 6`: 1.142696, 1.139159, 1.138747, …). Here c_h is where the predicate `exists_level` — "the recursion reaches level h, or refutes before reaching it" — changes from true to false under float bisection on [1 + 1/(4d), 1 + 1/d]; it is not "level h exists" when the recursion refutes early (at d = 1, c = 5/4 level 0 refutes, so `exists_level(1.25, 1, 2)` is true, although continuing would give a level-2 candidate r₂ = 42375/13639 > 2). `threshold d 60`: first the verdicts at the exact endpoints 1 + 1/(4d) and 1 + 1/d, certified on outward-rounded decimal enclosures (REF at 5/4, 9/8, 13/12; STOP at 2, 3/2, 4/3); then a bracket of width 10⁻⁶⁰ whose two ends, exact decimals, have opposite verdicts, each certified by decimal interval arithmetic with directed rounding, and the digits the two ends share: c*_stair(1) ≈ 1.3092117446776010510221902603497164170365731409176335370894…, c*_stair(2) ≈ 1.19159683545302011311694956315014944535226780478297581606997…, c*_stair(3) ≈ 1.13865239000087119328135666360349492168754860133162470872070…. These are numerical estimates: the bisection assumes that the verdict is monotone in c, which is not proved; without it the bracket locates a change of verdict, not the supremum.

```sh
python3 stair_cert.py 11386523 10000000 3 1125899906842624 110 200 /tmp/d3.json 100000000000000
python3 dag_check.py --json /tmp/d3.json ../../PastaMath/OneTapeThreshold/StairD3.lean
```
The generator is untrusted: its output counts only if the checkers accept it. With TOL = 10¹⁴ it produces accepted certificates for all three cases (d = 3: 212 nodes, 1255 steps, root c·φ = 0.99960299; d = 2 with `11915968 10000000 2 1125899906842624 110 400`: 287 nodes; d = 1 with `130921174 100000000 1 72057594037927936 120 400`: 549 nodes), but not the committed node lists byte for byte; those came from an earlier run, and the Lean files are the reference. The search that produced the potential parameters in `Ceiling.lean` is not included; only their acceptance by `HLM.absCheck` matters.

```sh
python3 tex2md.py ../paper/paper.tex ../paper/paper.md
```
