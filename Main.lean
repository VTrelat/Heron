import Heron

set_option linter.style.header false

/-!
# `heron` — a command-line certified square-root calculator

Computes `√A` by Heron's method (using `Heron.step`) in **exact rational arithmetic**,
prints each iterate as a decimal, and reports the achieved precision.

Run (fast, via the interpreter — uses the cached oleans):
  `lake env lean --run Main.lean A [DIGITS]`     e.g.  `lake env lean --run Main.lean 2 12`
Native binary (first build links Mathlib, so it is slow): `lake exe heron A [DIGITS]`
-/

open Heron

/-- `digits` decimal digits of `r / d` with `0 ≤ r < d` (truncated). -/
def fracDigits (d : Nat) : Nat → Nat → String
  | _, 0 => ""
  | r, (k + 1) =>
    let r' := r * 10
    toString (r' / d) ++ fracDigits d (r' % d) k

/-- Decimal string of a rational with `digits` places after the point (truncated). -/
def ratToDecimal (q : ℚ) (digits : Nat) : String :=
  let n := q.num.natAbs
  let d := q.den
  (if q.num < 0 then "-" else "") ++ s!"{n / d}.{fracDigits d (n % d) digits}"

/-- Iterate Heron from `x`, printing each iterate, until `|xₙ² − A| ≤ ε` or `maxSteps`. -/
partial def iterate (aQ ε : ℚ) (digits : Nat) (x : ℚ) (n maxSteps : Nat) : IO (ℚ × Nat) := do
  IO.println s!"  {n}   {ratToDecimal x digits}"
  if |x ^ 2 - aQ| ≤ ε ∨ n ≥ maxSteps then
    return (x, n)
  else
    iterate aQ ε digits (step aQ x) (n + 1) maxSteps

def usage (args : List String) : IO Unit := do
  IO.println "usage: heron A [DIGITS]"
  IO.println "  A      : positive integer (the radicand, e.g. 2)"
  IO.println "  DIGITS : target precision; stop once |xₙ² − A| ≤ 1e-D (default 12)"

def main (args : List String) : IO Unit := do
  match args with
  | [] => usage args
  | a :: rest =>
    match a.toNat? with
    | none => IO.eprintln s!"error: '{a}' is not a natural number"
    | some 0 => IO.println "√0 = 0"
    | some A => do
      let digits := (rest.head?.bind (·.toNat?)).getD 12
      let aQ : ℚ := (A : ℚ)
      let ε : ℚ := (1 : ℚ) / (10 : ℚ) ^ digits
      let x₀ : ℚ := (Nat.sqrt A : ℚ)
      IO.println s!"Heron's method for √{A}"
      IO.println s!"  start x₀ = {Nat.sqrt A},  stop when |xₙ² − A| ≤ 1e-{digits}"
      IO.println ""
      IO.println "  n   xₙ"
      let (xN, steps) ← iterate aQ ε digits x₀ 0 50
      IO.println ""
      IO.println s!"result        ≈ {ratToDecimal xN digits}"
      IO.println s!"exact value   = {xN.num}/{xN.den}"
      IO.println s!"squared error = {ratToDecimal (|xN ^ 2 - aQ|) (digits + 6)}   (|xₙ² − A|)"
      IO.println s!"steps         = {steps}"
