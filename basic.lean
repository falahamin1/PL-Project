-- Define a function to add two natural numbers
def add (n m : Nat) : Nat :=
  n + m

-- Example theorem: Addition is commutative for natural numbers
theorem add_comm (n m : Nat) : add n m = add m n := by
  rw [add, add] -- Rewrite using the definition of 'add'
  exact Nat.add_comm n m -- Use the commutativity of addition in Lean

-- Test the theorem
#eval add 2 3 -- Should output 5
