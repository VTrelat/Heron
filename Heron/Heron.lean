import Mathlib

-- Disable mathlib *style* linters (copyright header, etc.); irrelevant here.
set_option linter.style.header false

/-!
# Lab — Heron's method for `√a`

Given `a > 0` and a starting point `x₀ > 0`, **Heron's method** (a.k.a. the Babylonian method)
computes `√a` by iterating the average:

  `xₙ₊₁ = (xₙ + a / xₙ) / 2`.

This lab has two goals:

* **Part A — prove** that the sequence `(xₙ)` converges to `√a`, *with an explicit rate*
  (the error is at least halved at each step).
* **Part B — run it**: since the iteration only uses `+ - * /`, it is *computable*.
  We turn it into a small program that computes `√a` to a requested precision (`#eval`).

## Rules of the game
Replace each `sorry` with a proof. The definitions and the `#eval`s are **given**:
the program already runs, you prove that it is correct.

## Toolbox (useful tactics)
`unfold`, `simp`, `rw [...]`, `calc`, `induction n with | zero => … | succ k ih => …`,
`linarith`, `nlinarith [sq_nonneg …]`, `positivity`, `field_simp`, `ring`, `gcongr`.

Mathlib lemmas about the square root (also search with `exact?`, `apply?`, or mathlib search):
`Real.sq_sqrt : 0 ≤ a → √a ^ 2 = a`, `Real.sqrt_sq : 0 ≤ a → √(a^2) = a`,
`Real.sqrt_le_sqrt`, `Real.sqrt_nonneg`, `Real.sqrt_pos`.
-/

open Filter

namespace Heron

variable {K : Type*} [Field K]

/-- One Heron step: `x ↦ (x + a/x)/2`. Generic over a field (hence computable over `ℚ`). -/
def step (a x : K) : K := (x + a / x) / 2

/-- The Heron sequence `x₀, x₁, x₂, …`. -/
def heron (a x₀ : K) : ℕ → K
  | 0 => x₀
  | (n + 1) => step a (heron a x₀ n)

@[simp] lemma heron_zero (a x₀ : K) : heron a x₀ 0 = x₀ := rfl
@[simp] lemma heron_succ (a x₀ : K) (n : ℕ) : heron a x₀ (n + 1) = step a (heron a x₀ n) := rfl

/-! ## Part A — Convergence (over `ℝ`) -/

/-- **Exercise 1.** Rational form of the step: `step a x = (x² + a) / (2x)`.
Hint: `unfold step`, then clear denominators. -/
lemma step_eq {a x : ℝ} (hx : x ≠ 0) : step a x = (x ^ 2 + a) / (2 * x) := by
  sorry

/-- **Exercise 2.** The step stays strictly positive. -/
lemma step_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : 0 < step a x := by
  sorry

/-- **Exercise 3.** The whole sequence stays strictly positive.
Induction; reuse `step_pos`. -/
lemma heron_pos {a x₀ : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) : ∀ n, 0 < heron a x₀ n := by
  sorry

/-- **Exercise 4 (AM–GM).** One step never underestimates `√a`: `a ≤ (step a x)²`.
Idea: `(step a x)² − a` is a perfect square — which one? (think of `(x² − a)/(2x)`). -/
lemma le_sq_step {a x : ℝ} (hx : x ≠ 0) : a ≤ (step a x) ^ 2 := by
  sorry

/-- **Exercise 5.** Consequence: `√a ≤ step a x` whenever `x > 0`.
Hint: `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, and exercise 4. -/
lemma sqrt_le_step {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : Real.sqrt a ≤ step a x := by
  sorry

/-- **Exercise 6.** From index 1 on, every iterate is at least `√a`. -/
lemma sqrt_le_heron {a x₀ : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) :
    ∀ n, Real.sqrt a ≤ heron a x₀ (n + 1) := by
  sorry

/-- **Exercise 7 (error identity).** `step a x − √a = (x − √a)² / (2x)`.
Idea: everything follows from `(√a)² = a` (`Real.sq_sqrt`). -/
lemma step_sub_sqrt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    step a x - Real.sqrt a = (x - Real.sqrt a) ^ 2 / (2 * x) := by
  sorry

/-- **Exercise 8 (contraction).** If `√a ≤ x`, the error is at least halved.
Idea: `(x−√a)/2 − (step a x − √a) = √a·(x−√a)/(2x) ≥ 0`. -/
lemma step_sub_sqrt_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hge : Real.sqrt a ≤ x) :
    step a x - Real.sqrt a ≤ (x - Real.sqrt a) / 2 := by
  sorry

/-- **Main theorem (Exercise 9) — geometric rate.**
For every `k`, the error at index `k+1` is `≤ (1/2)^k` times the error at index `1`.
The sequence therefore converges (at least) geometrically. Idea: induction on `k`,
combining the contraction (exercise 8) with the induction hypothesis. -/
theorem heron_error_le {a x₀ : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) :
    ∀ k, heron a x₀ (k + 1) - Real.sqrt a ≤ (1 / 2) ^ k * (heron a x₀ 1 - Real.sqrt a) := by
  sorry

/-! ## Part B — An executable program

`heron` is already computable over `ℚ` (exact fractions). These `#eval`s run immediately. -/

#eval heron (2 : ℚ) 1 0      -- 1
#eval heron (2 : ℚ) 1 1      -- 3/2
#eval heron (2 : ℚ) 1 2      -- 17/12
#eval heron (2 : ℚ) 1 3      -- 577/408
#eval heron (2 : ℚ) 1 4      -- 665857/470832  (√2 ≈ 1.41421356…)

/-- `Float` is not a mathlib field: we redefine the step to get a decimal display. -/
def stepF (a x : Float) : Float := (x + a / x) / 2

def heronF (a x₀ : Float) : ℕ → Float
  | 0 => x₀
  | (n + 1) => stepF a (heronF a x₀ n)

#eval heronF 2.0 1.0 5                       -- ≈ 1.4142135623730951
#eval heronF 2.0 1.0 5 - 1.4142135623730951  -- residual error

/-- Iterate Heron until `|x² − a| ≤ ε`, within `fuel` steps. Computable over `ℚ`. -/
def sqrtApprox (a x₀ ε : ℚ) : ℕ → ℚ
  | 0 => x₀
  | (fuel + 1) => if |x₀ ^ 2 - a| ≤ ε then x₀ else sqrtApprox a (step a x₀) ε fuel

#eval sqrtApprox 2 1 (1 / 1000000) 100        -- rational approx of √2 (x² within 1e-6)
#eval sqrtApprox 2 1 (1 / 10 ^ 12) 100        -- precision 1e-12

/-- **Exercise 10 (computable invariant).** Over `ℚ`, after one step the iterate
overestimates `√a`, i.e. `a ≤ (step a x)²`: the *same proof* as exercise 4, but over `ℚ`. -/
lemma le_sq_step_rat {a x : ℚ} (hx : x ≠ 0) : a ≤ (step a x) ^ 2 := by
  sorry

/-! ## Additional exercises: proofs -/

/-- **Bonus 1 — quadratic convergence.** The error is in fact `≤ (x − √a)² / (2√a)`:
it is *squared* at each step (hence the ultra-fast convergence observed).
Idea: start from the error identity (exercise 7), then `gcongr` (smaller denominator). -/
lemma step_sub_sqrt_le_sq {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hge : Real.sqrt a ≤ x) :
    step a x - Real.sqrt a ≤ (x - Real.sqrt a) ^ 2 / (2 * Real.sqrt a) := by
  sorry

/-- **Bonus 2 — the limit.** The sequence converges to `√a` in the `Tendsto` sense.
Idea: bound the error `0 ≤ xₙ₊₁ − √a ≤ (1/2)^n · C` and send it to 0
(`squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`), then shift the index
(`tendsto_add_atTop_iff_nat`). -/
theorem heron_tendsto {a x₀ : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) :
    Tendsto (heron a x₀) atTop (nhds (Real.sqrt a)) := by
  sorry

end Heron
