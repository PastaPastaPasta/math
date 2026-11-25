# Scripts

Python 3 standard library only (tested with Python 3.11 and 3.13). Run from this directory. None of these scripts is part of the kernel-checked results; they re-check the Lean data independently, replay proofs from Williams's text, and compute the numbers of the paper that are not in Lean.

| Script | What it does | Written from | Time |
|---|---|---|---|
| `dag_check.py` | Exact re-implementation of `HD.dagCheck` and `HDS.dagCheck`, run on the node lists of `StairD{1,2,3}.lean`; prints nodes, speedup steps, root ratio c·φ, the starting exponent a₀ and the unfolded length | the Lean definitions | < 1 s |
| `abs_check.py` | Exact re-implementation of `HLM.absCheck`, run on the data of `Ceiling.lean` | the Lean definitions | < 1 s |
| `replay39.py` | Replays the 39-line proof `HY.cert39` and prints it | Williams's rules (TOCT text) | < 1 s |
| `w13_25line.py` | Replays the 25-line proof printed in Williams's §7.2 under the formal rules (calibration) | Williams's rules and printed proof | < 1 s |
| `staircase.py` | The staircase recursion: levels at a given c, the level thresholds c_h, the threshold c*_stair in interval arithmetic, and r_d, √(1+1/d), 1+1/(d+1) | paper Section 7 | < 1 s each |
| `stair_cert.py` | Untrusted generator of staircase certificates (JSON) | the recursion's structure | 40 s (d = 3) to several minutes (d = 1) |
| `tex2md.py` | Regenerates `../paper/paper.md` from `../paper/paper.tex` (needs pandoc; tested with 3.12) | — | < 1 s |

## Commands and expected output

```sh
python3 dag_check.py ../../PastaMath/OneTapeThreshold/StairD1.lean ../../PastaMath/OneTapeThreshold/StairD2.lean ../../PastaMath/OneTapeThreshold/StairD3.lean
```
Both readings accept all three certificates: d = 1, c = 130921174/10⁸, M = 2⁵⁶, 552 nodes, 3915 speedup steps, root c·φ = 0.99916308, a₀ = 141318262916700694 ≈ 1.41·10¹⁷, at most 7.61·10²¹ unfolded lines; d = 2, c = 11915968/10⁷, M = 2⁵⁰, 286 nodes, 1846 steps, 0.99940456, a₀ ≈ 1.68·10¹⁵, ≤ 2.46·10¹⁷ lines; d = 3, c = 11386523/10⁷, M = 2⁵⁰, 212 nodes, 1255 steps, 0.99961709, a₀ ≈ 1.50·10¹⁵, ≤ 1.10·10¹⁵ lines. The unfolded length counts the lines of the derivation that `HD.nf_of_SC` builds if no level is closed early, which is an upper bound.

```sh
python3 abs_check.py ../../PastaMath/OneTapeThreshold/Ceiling.lean
```
Accepts the three ceilings: c₀ = 6547/5000, d = 1, 105 abstract states, levels θ = 1.027, 1.017, 1.014; c₀ = 149/125, d = 2, 50 states, θ = 1.011, 1.008; c₀ = 712/625, d = 3, 19 states, θ = 1.0055. In each case θ₀ = c₀² − c₀/(d+1). (Lowering c₀ by 10⁻⁴ with θ₀ recomputed, or removing the last abstract state, makes each check fail.)

```sh
python3 replay39.py ../../PastaMath/OneTapeThreshold/Proof39.lean
```
Prints the 39 lines (exponents divided by 1000); final exponent 99994.1297 < 10⁵; every side condition, alternation, the strict normal form, kernel time ≥ input superscript and space ≤ time hold; the smallest gap time − input is 4.6·10⁻²⁰ (line 12), and it is below 10⁻⁶ on lines 12, 23 and 36.

```sh
python3 w13_25line.py
```
Every step of Williams's printed 25-line proof (c = 1.297844, d = 1) is a rule of the formal calculus; the largest deviation from a printed number is 1.0·10⁻⁸.

```sh
python3 staircase.py roots
python3 staircase.py levels 1.3092 1
python3 staircase.py appear 1 6
python3 staircase.py threshold 1 60     # also 2 60, 3 60
```
`roots`: r₁ = 1.3009428844, r₂ = 1.1887894930, r₃ = 1.1372807069; the level-1 thresholds c₁ = 1.330277691377, 1.199453639736, 1.142696215782 and the roots of the cubics 8c³ − 2c² − 13c + 2, 36c³ − 9c² − 46c + 6, 96c³ − 20c² − 113c + 12. `levels 1.3092 1`: seven levels, c·g = 1.059405, …, 0.994144 (refutes at level 6). `appear 1 6`: c₁, …, c₆ = 1.330278, 1.311714, 1.309609, 1.309287, 1.309228, 1.309215 (`appear 2 6`: 1.199454, 1.192559, 1.191768, …; `appear 3 6`: 1.142696, 1.139159, 1.138747, …). `threshold d 60`: the bracket of width 10⁻⁶⁰ and its certified common digits, c*_stair(1) = 1.3092117446776010510221902603497164170365731409176335370894…, c*_stair(2) = 1.19159683545302011311694956315014944535226780478297581606997…, c*_stair(3) = 1.13865239000087119328135666360349492168754860133162470872070…. The verdicts at the two ends of the bracket are certified by decimal interval arithmetic with directed rounding; that the verdict is monotone in c, which the bisection assumes, is not proved.

```sh
python3 stair_cert.py 11386523 10000000 3 1125899906842624 110 200 /tmp/d3.json 100000000000000
python3 dag_check.py --json /tmp/d3.json ../../PastaMath/OneTapeThreshold/StairD3.lean
```
The generator is untrusted: its output counts only if the checkers accept it. With TOL = 10¹⁴ it produces accepted certificates for all three cases (d = 3: 212 nodes, 1255 steps, root c·φ = 0.99960299; d = 2 with `11915968 10000000 2 1125899906842624 110 400`: 287 nodes; d = 1 with `130921174 100000000 1 72057594037927936 120 400`: 549 nodes), but not the committed node lists byte for byte; those came from an earlier run, and the Lean files are the reference. The search that produced the potential parameters in `Ceiling.lean` is not included; only their acceptance by `HLM.absCheck` matters.

```sh
python3 tex2md.py ../paper/paper.tex ../paper/paper.md
```
