-- Define a function `factorial` that takes a natural number `n` and returns its factorial
def factorial : ℕ → ℕ
| 0 := 1 -- The factorial of 0 is defined to be 1 by convention
| (n + 1) := (n + 1) * factorial n -- For a positive integer n+1, compute the factorial of n and multiply it by n+1

-- Define a theorem `factorial_correct` that states that `factorial n` returns the correct value for any natural number `n`
theorem factorial_correct (n : ℕ) : factorial n = n.fact :=
nat.rec_on n -- Perform structural induction on `n`
  (show factorial 0 = 0.fact, by simp [factorial, nat.fact]) -- The base case is n = 0, for which factorial 0 = 1 and 0! = 1 by convention
  (assume k ih,
    have h₁ : factorial (k + 1) = (k + 1) * k.fact, from by simp [factorial, ih],
    have h₂ : (k + 1).fact = (k + 1) * k.fact, from by simp [nat.fact_succ, h₁],
    show factorial (k + 1) = (k + 1).fact, by simp [h₁, h₂])
