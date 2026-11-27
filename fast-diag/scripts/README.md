# Scripts for `fast-diag`

- `params.py`: evaluates the exact description-length, moment, wire-count, and degree formulas from Sections 3–5 of `paper/paper.tex` and checks the threshold `log₂ n` values reported in Table 2. Run from this directory:

  ```sh
  python3 params.py
  ```

- `tex2md.py`: regenerates `../paper/paper.md` from `../paper/paper.tex` via `pandoc`:

  ```sh
  python3 tex2md.py ../paper/paper.tex ../paper/paper.md
  ```
