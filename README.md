# Heron's method in Lean–A certified square-root calculator

## Quick install
Clone the repo, and run
```
cd Heron
lake exe cache get
lake build
```
Then open `Heron/Heron.lean` in VS Code (with the Lean 4 extension).

This repository provides an executable program `heron`, and a PDF document containing informal proofs; both are automatically released.

## Goal
Define and prove that the Heron iteration

$$ x_{n+1} = \frac{x_n + \frac{a}{x_n}}{2} $$

**computably** converges to $\sqrt{a}$ to a requested precision. The through-line: *"we prove that the program we run is correct."*

## The proved result
- `heron_error_le` (main theorem): geometric convergence.
- `step_sub_sqrt_le_sq`: **quadratic** convergence.
- `heron_tendsto`: the limit itself.

## Structure of the exercises
Each exercise depends only on the previous ones.

| Block | Exercises | Idea | ~Time |
|------|-----------|------|--------|
| Warm-up | 1 `step_eq`, 2 `step_pos`, 3 `heron_pos` | algebra + first induction | 25 min |
| AM–GM core | 4 `le_sq_step`, 5 `sqrt_le_step`, 6 `sqrt_le_heron` | one step overshoots `√a` | 35 min |
| Error core | 7 `step_sub_sqrt`, 8 `step_sub_sqrt_le` | error identity + contraction | 30 min |
| Theorem | 9 `heron_error_le` | induction + `calc` | 20 min |
| Program | 10 `le_sq_step_rat` + play with `#eval` | run it, vary `a`, `ε` | 15 min |
| Bonus | quadratic, limit | for the fast finishers | spare time |

Core total ≈ 2 h; the bonuses keep early finishers busy (nobody is left idle).

## Hints
Hints are deliberately sparse in the file. Nudges if you're stuck:
- **Ex 4** (the pivot): show that `(step a x)² − a = ((x²−a)/(2x))²`, then `nlinarith [sq_nonneg …]`.
- **Ex 5**: `Real.sqrt_le_sqrt` then `Real.sqrt_sq` (rewrite `√((step)²) = step`).
- **Ex 7**: `field_simp` then **`linear_combination`** with `Real.sq_sqrt` (a good moment to introduce
  this tactic: everything comes from `(√a)² = a`).
- **Ex 8**: form the difference `(x−√a)/2 − (step−√a)` and show it equals `√a·(x−√a)/(2x) ≥ 0`.
- **Ex 9**: induction, then `calc` chaining the contraction (ex 8) and the induction hypothesis.

### Command-line executable
`Main.lean` (at the repo root) is a small CLI: it runs Heron in **exact rational arithmetic**
(the proved `Heron.step`) and prints each iterate, the result, the exact fraction, the squared
error and the number of steps.
