# Scripts for `qbf-threshold`

- `qbf_check.py`: independent exact-rational (`fractions.Fraction`) checker for the literal QBF_k rules of Williams (TOCT 2013, Def. 4.1 + §5). Run from this directory:

  ```sh
  python3 qbf_check.py cert_k1.json cert_k2.json cert_k3.json cert_k4.json
  ```

  Expected output: all four JSON certificates report `VALID REFUTATION` at k = 1 (c = 7/4, 140 lines), k = 2 (c = 289/100, 324 lines), k = 3 (c = 393/100, 432 lines), and k = 4 (c = 989/200, 540 lines).
- `cert_k1.json` .. `cert_k4.json`: the four literal refutation certificates corresponding to `qcert1_ok` .. `qcert4_ok` in `PastaMath/QbfThreshold/Cert.lean`.
- `tex2md.py`: regenerates `../paper/paper.md` from `../paper/paper.tex` via `pandoc`:

  ```sh
  python3 tex2md.py ../paper/paper.tex ../paper/paper.md
  ```
