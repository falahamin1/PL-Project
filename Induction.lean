-- induction in lean is used using induction keyword similar to coq
theorem minus_n_n : ∀ n : Nat, n - n = 0 := by
intro n
induction n with --lean names the two cases (zero and succ) based on the type definition
  | zero => -- Base case
    simp
  | succ n' ih => -- Inductive case
    simp --simp take care of the rest of the simplification here

-- proofs within proofs
--we use have keyword instead of assert in lean

theorem mult_0_plus' : ∀ n m : Nat, (n + 0 + 0) * m = n * m := by
  intro n m  -- Introduce `n` and `m`
  have H : n + 0 + 0 = n := by  -- Introduce an intermediate result
    rw [Nat.add_comm]
    simp
  rw [H]   -- Using the intermediate result

theorem plus_rearrange : ∀ n m p q : Nat, (n + m) + (p + q) = (m + n) + (p + q) := by
  intro n m p q  -- Introduce variables
  have H : n + m = m + n := by  -- Intermediate result
    rw [Nat.add_comm]  -- Commutativity of addition
  rw [H]  -- Using the intermediate result
