import Mathlib

set_option linter.style.header false

/-!
# Heron's method for `√a` — SOLUTIONS

Given `a > 0` and a starting point `x₀ > 0`, we iterate

  `xₙ₊₁ = (xₙ + a / xₙ) / 2`.

We prove that this sequence converges to `√a`, **with an explicit rate**
(the error is at least halved at each step), and then turn it into an
**executable program** that computes `√a` to a given precision.

The iteration only uses field operations (never `Real.sqrt`): it is therefore
*computable* over `ℚ`, whereas the *proof* is carried out over `ℝ`.

Outline:
* Part A — convergence over `ℝ` (core + two bonuses: quadratic convergence, the limit).
* Part B — the program: `#eval` over `ℚ`, a `Float` version, and `sqrtApprox`.
-/

open Filter

namespace Heron

variable {K : Type*} [Field K]

/-- One Heron step: `x ↦ (x + a/x)/2`. Generic (hence computable over `ℚ`). -/
def step (a x : K) : K := (x + a / x) / 2

/-- The Heron sequence `x₀, x₁, x₂, …`. -/
def heron (a x₀ : K) : ℕ → K
  | 0 => x₀
  | (n + 1) => step a (heron a x₀ n)

@[simp] lemma heron_zero (a x₀ : K) : heron a x₀ 0 = x₀ := rfl
@[simp] lemma heron_succ (a x₀ : K) (n : ℕ) : heron a x₀ (n + 1) = step a (heron a x₀ n) := rfl

/-! ## Part A — Convergence (over `ℝ`) -/

/-- Rational form of the step: `step a x = (x² + a) / (2x)`. -/
lemma step_eq {a x : ℝ} (hx : x ≠ 0) : step a x = (x ^ 2 + a) / (2 * x) := by
  unfold step
  field_simp

/-- The step stays strictly positive. -/
lemma step_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : 0 < step a x := by
  unfold step
  positivity

/-- The whole sequence stays strictly positive. -/
lemma heron_pos {a x₀ : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) : ∀ n, 0 < heron a x₀ n := by
  intro n
  induction n with
  | zero => rwa [heron]
  | succ k ih => exact step_pos ha ih

/-- **AM–GM**: a Heron step never underestimates `√a` (squared form: `a ≤ (step)²`). -/
lemma le_sq_step {a x : ℝ} (hx : x ≠ 0) : a ≤ (step a x) ^ 2 := by
  have key : (step a x) ^ 2 - a = ((x ^ 2 - a) / (2 * x)) ^ 2 := by
    rw [step_eq hx]
    field_simp
    ring
  nlinarith [sq_nonneg ((x ^ 2 - a) / (2 * x)), key]

/-- Consequence: `√a ≤ step a x` whenever `x > 0`. -/
lemma sqrt_le_step {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : √a ≤ step a x := by
  have hstep : 0 ≤ step a x := (step_pos ha hx).le
  calc √a ≤ √((step a x) ^ 2) := Real.sqrt_le_sqrt (le_sq_step (ne_of_gt hx))
    _ = step a x := Real.sqrt_sq hstep

/-- From index 1 on, every iterate is at least `√a`. -/
lemma sqrt_le_heron {a x₀ : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) :
    ∀ n, √a ≤ heron a x₀ (n + 1) := by
  intro n
  simpa using sqrt_le_step ha (heron_pos ha hx₀ n)

/-- Exact **error identity**: `step a x − √a = (x − √a)² / (2x)`. -/
lemma step_sub_sqrt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    step a x - √a = (x - √a) ^ 2 / (2 * x) := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have hs : √a ^ 2 = a := Real.sq_sqrt ha.le
  rw [step_eq hx']
  field_simp
  linear_combination -hs

/-- **Contraction**: if `√a ≤ x`, the error is at least halved. -/
lemma step_sub_sqrt_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hge : √a ≤ x) :
    step a x - √a ≤ (x - √a) / 2 := by
  have hd : 0 ≤ x - √a := by linarith
  have hnn : 0 ≤ √a * (x - √a) / (2 * x) := by
    apply div_nonneg (mul_nonneg (Real.sqrt_nonneg a) hd); positivity
  have expand : (x - √a) / 2 - (step a x - √a)
      = √a * (x - √a) / (2 * x) := by
    rw [step_sub_sqrt ha hx]; field_simp; ring
  linarith [expand, hnn]

/-- **Theorem (geometric rate).** For every `k`, the error at index `k+1` is at most
`(1/2)^k` times the error at index `1`; so the sequence converges (at least) geometrically. -/
theorem heron_error_le {a x₀ : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) :
    ∀ k, heron a x₀ (k + 1) - √a ≤ (1 / 2) ^ k * (heron a x₀ 1 - √a) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : √a ≤ heron a x₀ (k + 1) := sqrt_le_heron ha hx₀ k
    have hpos : 0 < heron a x₀ (k + 1) := heron_pos ha hx₀ (k + 1)
    have hstep : heron a x₀ (k + 1 + 1) - √a
        ≤ (heron a x₀ (k + 1) - √a) / 2 := by
      simpa using step_sub_sqrt_le ha hpos h1
    calc heron a x₀ (k + 1 + 1) - √a
        ≤ (heron a x₀ (k + 1) - √a) / 2 := hstep
      _ ≤ ((1 / 2) ^ k * (heron a x₀ 1 - √a)) / 2 := by linarith
      _ = (1 / 2) ^ (k + 1) * (heron a x₀ 1 - √a) := by ring

/-! ### Bonus 1 — Quadratic convergence
The error is in fact bounded by `(xₙ − √a)² / (2√a)`: it is *squared* at each step,
which explains the ultra-fast convergence observed numerically. -/
lemma step_sub_sqrt_le_sq {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hge : √a ≤ x) :
    step a x - √a ≤ (x - √a) ^ 2 / (2 * √a) := by
  rw [step_sub_sqrt ha hx]
  gcongr

/-! ### Bonus 2 — The limit
We deduce convergence to `√a` in the `Tendsto` sense. -/
theorem heron_tendsto {a x₀ : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) :
    Tendsto (heron a x₀) atTop (nhds (√a)) := by
  set C := heron a x₀ 1 - √a with hC
  -- the shifted sequence `n ↦ heron a x₀ (n+1)` tends to `√a`
  have hg : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * C) atTop (nhds 0) := by
    have h2 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h2.mul_const C
  have he0 : Tendsto (fun n => heron a x₀ (n + 1) - √a) atTop (nhds 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => heron_error_le ha hx₀ n) hg
    have := sqrt_le_heron ha hx₀ n; linarith
  have hshift : Tendsto (fun n => heron a x₀ (n + 1)) atTop (nhds (√a)) := by
    have := he0.add_const (√a)
    simpa using this
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-! ## Part B — An executable program

`heron` is already computable over `ℚ` (exact fractions). -/

#eval heron (2 : ℚ) 1 0      -- 1
#eval heron (2 : ℚ) 1 1      -- 3/2
#eval heron (2 : ℚ) 1 2      -- 17/12
#eval heron (2 : ℚ) 1 3      -- 577/408
#eval heron (2 : ℚ) 1 4      -- 665857/470832

def heronF (a x₀ : Float) (n : ℕ) : Float :=
  (heron a.toRat0 x₀.toRat0 n).toFloat

#eval heronF 2.0 1.0 5                       -- ≈ 1.4142135623730951
#eval heronF 2.0 1.0 5 - 1.4142135623730951  -- error (essentially machine precision)

/-- Iterate Heron until `|x² − a| ≤ ε`, within `fuel` steps. Computable over `ℚ`. -/
def sqrtApprox (a x₀ ε : ℚ) : ℕ → ℚ
  | 0 => x₀
  | (fuel + 1) => if |x₀ ^ 2 - a| ≤ ε then x₀ else sqrtApprox a (step a x₀) ε fuel

#eval sqrtApprox 2 1 1e-6 100        -- rational approx of √2 within 1e-6 (squared)
#eval sqrtApprox 2 1 1e-12 100        -- precision 1e-12

/-- **Computable invariant** (same proof as `le_sq_step`, but over `ℚ`):
after one step, the iterate overestimates `√a`, i.e. `x² ≥ a`. -/
lemma le_sq_step_rat {a x : ℚ} (hx : x ≠ 0) : a ≤ (step a x) ^ 2 := by
  have key : (step a x) ^ 2 - a = ((x ^ 2 - a) / (2 * x)) ^ 2 := by
    unfold step; field_simp; ring
  nlinarith [sq_nonneg ((x ^ 2 - a) / (2 * x)), key]

end Heron
