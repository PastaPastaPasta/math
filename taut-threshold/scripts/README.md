# Scripts

Two exact-rational checks of numbers cited from Section 6.2 of Williams's paper (author copy, https://people.csail.mit.edu/rrw/automated-lbs.pdf), used in Section 9(d) of the paper. Python 3 standard library only; no other dependencies.

- `w13_listing.py`: recomputes every kernel exponent of the printed 11-line proof from Lemmas 6.1 and 6.2, reading the printed block exponent either as the guess exponent or as the input constraint, with and without the term b of Lemma 6.2(1),(2). Runs in well under a second.

  ```sh
  python3 w13_listing.py
  ```

- `w13_lp.py`: for each valid proof annotation with the given numbers of lines, decides feasibility of Williams's linear program exactly (two-phase simplex over the rationals) and bisects for the best c. Use `--no-b` to drop the b term.

  ```sh
  python3 w13_lp.py --lines 5,8,11          # about a minute
  python3 w13_lp.py --lines 5,8,11 --no-b
  python3 w13_lp.py --lines 14 --digits 3   # several minutes
  ```

  With `--at`, it decides feasibility exactly at the given values of c instead of bisecting, and prints the feasible annotations:

  ```sh
  python3 w13_lp.py --lines 14 --at 1.43308,1.43310           # several minutes
  python3 w13_lp.py --lines 14 --no-b --at 1.69261,1.69263
  ```

These scripts are evidence about how Williams's table was computed. They are not part of the kernel-checked results.
