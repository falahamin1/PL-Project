--In this chapter, we introduce key tactics used in lean
--Apply tactic in lean.
-- When the goal matches exactly.
theorem silly1 (n m : Nat) (h : n = m) : n = m := by
  apply h

--If the statement being applied is an implication, apply introduces subgoals for the premises.
theorem silly2 (n m o p : Nat) (h1 : n = m) (h2 : n = m → [n, o] = [m, p]) : [n, o] = [m, p] := by
  apply h2
  apply h1

--When apply is used with a lemma or hypothesis containing universally quantified variables, Lean automatically attempts to infer the correct instantiations.
theorem silly2a (n m : Nat)
  (h1 : (n, n) = (m, m))
  (h2 : ∀ (q r : Nat), (q, q) = (r, r) → [q] = [r]) :
  [n] = [m] := by
  apply h2
  apply h1

--The apply tactic can be used in Lean with explicit arguments to instantiate variables when they cannot be inferred automatically.
--This mimics Coq's apply __ with __

theorem trans_eq {X : Type} (n m o : X) (h1 : n = m) (h2 : m = o) : n = o := by
  rw [h1]
  rw [h2]

example (a b c d e f : Nat) (h1 : [a, b] = [c, d]) (h2 : [c, d] = [e, f]) :
    [a, b] = [e, f] := by

  apply trans_eq _ _ _ --The underscores indicate that Lean should attempt to infer the values of n, m, and o.
  exact h1
  exact h2

--Lean provides the Eq.trans tactic to perform reasoning by transitivity, similar to transitivity in Coq.
--It is equivalent to Coq's transitivity.
example (a b c d e f : Nat) (h1 : [a, b] = [c, d]) (h2 : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply Eq.trans
  exact h1
  exact h2

--Sometimes, it is necessary to provide type arguments explicitly when Lean cannot infer them.
theorem trans_eq_explicit {X : Type} (n m o : X) (h1 : n = m) (h2 : m = o) : n = o := by
  rw [h1]
  rw [h2]

example (a b c d e f : Nat) (h1 : [a, b] = [c, d]) (h2 : [c, d] = [e, f]) :
    [a, b] = [e, f] := by
  apply @trans_eq_explicit (List Nat) _ _ _ --    @trans_eq_explicit specifies the explicit type List Nat for X.
  exact h1
  exact h2

--Injection in Lean.
theorem S_injective (n m : Nat) (h : Nat.succ n = Nat.succ m) : n = m := by
  injection h with hnm --Decomposes the equality Nat.succ n = Nat.succ m using the injectivity of Nat.succ.

--Lean can derive multiple equalities at once from an injective constructor.
theorem injection_ex1 (n m o : Nat) (h : [n, m] = [o, o]) : n = m := by
  injection h with h1 h2 --ecomposes the equality [n, m] = [o, o] into two equalities
  rw [h1]
  simp at h2
  rw [h2]

--Disjointness of constructors in Lean.
--In Lean, the principle of disjointness of constructors is built into the logic.
--This means Lean automatically knows that two terms beginning with different constructors (e.g., Nat.zero and Nat.succ) can never be equal.
-- When such a situation arises in a proof, you can use tactics like contradiction or cases to handle these scenarios.

--contradiction tactic automatically handles cases where the hypothesis is contradictory (e.g., false = true).
theorem discriminate_ex1 (n m : Nat) (contra : false = true) : n = m := by
  contradiction

--Lean automatically recognizes that Nat.succ and Nat.zero are disjoint and raises a contradiction when contradiction is applied.
theorem discriminate_ex2 (n : Nat) (contra : Nat.succ n = Nat.zero) : 2 + 2 = 5 := by
  contradiction

--Handling equality with cases.
theorem discriminate_ex3 (n : Nat) (h : Nat.succ n = Nat.zero) : 2 + 2 = 5 := by
  cases h
--This tactic analyzes the equality Nat.succ n = Nat.zero. Since the constructors are disjoint, Lean detects that this case is impossible and closes the goal.

--The theorem eqb_0_l establishes a connection between 0 =? n = true and n = 0. In Lean, we can prove this using case analysis and the disjointness of constructors.

theorem eqb_0_l (n : Nat) (h : Nat.beq 0 n = true) : n = 0 := by
  cases n with --Splits the proof into two cases: n = 0 and n = succ n'.
  | zero =>
    rfl   --When n = 0, the hypothesis Nat.beq 0 n = true is trivially true, and the goal is solved by rfl.
  | succ n' =>
    simp [Nat.beq] at h  --When n = succ n', simplify Nat.beq 0 (succ n') using simp [Nat.beq]


--The theorem f_equal states that equality is preserved under the application of functions. This is directly provided in Lean as congrArg.

theorem f_equal {A B : Type} (f : A → B) (x y : A) (h : x = y) : f x = f y :=
  congrArg f h


--We can prove that n = m → succ n = succ m using f_equal (or directly using congrArg in Lean).
theorem eq_implies_succ_equal (n m : Nat) (h : n = m) : Nat.succ n = Nat.succ m := by
  apply congrArg
  exact h

-- congr splits the goal into subgoals for the arguments of the constructors or functions.
theorem eq_implies_list_succ_equal (n m : Nat) (h : n = m) : [Nat.succ n] = [Nat.succ m] := by
  congr  -- Decompose the equality of lists

--Using Tactics on Hypotheses in Lean

--Lean provides similar mechanisms to Coq for reasoning about hypotheses.
-- You can perform operations on hypotheses in the context using appropriate tactics like simp at, rw at, and apply (with its in variant for forward reasoning).
-- Below, we explore these concepts in Lean with examples

--The tactic simp at h simplifies the hypothesis h in the context. This is equivalent to Coq’s simpl in H.
theorem S_inj (n m : Nat) (b : Bool) (h : (Nat.succ n = Nat.succ m) = b) :
    (n = m) = b := by
  simp at h  -- Simplify the hypothesis
  simp
  exact h

--Lean allows forward reasoning by applying a theorem or implication to a hypothesis using apply __ at h.
theorem silly4 (n m p q : Nat) (h1 : n = m → p = q) (h2 : m = n) : q = p := by
  apply Eq.symm  -- Flip the goal from `q = p` to `p = q`
  rw [Eq.symm h2] at h1  -- Rewrite `h2 : m = n` to `n = m` in h1
  exact h1 rfl


--If you have a universally quantified hypothesis, e.g., H : ∀ x : T, P x, you can specialize it for a specific value of x by:
--Explicit substitution: Use have to create a new hypothesis.
--Direct application: Use apply with the hypothesis to work on specific subgoals.

theorem specialize_example : ∀ n : Nat, (∀ m, m * n = 0) → n = 0 := by
  intro n H
  have H1 := H 1
  simp at H1
  exact H1

--Specializing a hypothesis is particularly useful when doing forward reasoning. Forward reasoning starts from the assumptions and deduces conclusions until the goal is reached.
theorem trans_eq' {X : Type} (n m o : X) (H1 : n = m) (H2 : m = o) : n = o :=
  Eq.trans H1 H2

example (a b c d e f : Nat) (eq1 : [a, b] = [c, d]) (eq2 : [c, d] = [e, f]) : [a, b] = [e, f] := by
  -- Specialize trans_eq for m = [c, d]
  have H := trans_eq _ _ _ eq1 eq2
  exact H

--Varying the Induction Hypothesis in Lean
--Consider proving that the double function (a function that multiplies a natural number by 2) is injective:
def double (n : Nat) : Nat := 2 * n

-- The failed attempt to prove injectivity of double
theorem double_injective_FAILED : ∀ n m : Nat, double n = double m → n = m := by
  intro n m
  induction n with
  | zero =>
    intro eq
    cases m with
    | zero => rfl
    | succ _ => contradiction
  | succ n' IHn' =>
    intro eq
    cases m with
    | zero => contradiction
    | succ m' =>
      -- At this point, IHn' is not helpful since we need to prove `S n' = S m'`.
      sorry -- Proof stuck here

-- A successful proof of injectivity
theorem double_injective : ∀ n m : Nat, double n = double m → n = m := by
  intro n
  induction n with
  | zero =>
    intro m eq
    cases m with
    | zero => rfl
    | succ _ => contradiction
  | succ n' IHn' =>
    intro m eq
    cases m with
    | zero => contradiction
    | succ m' =>
      have h := IHn' m'
      injection eq with eq'
      simp [Nat.add, Nat.mul] at eq'
      simp [double] at h
      simp [Nat.succ]
      exact h eq'
--Instead of generalize dependent, lean has revert, which reverts n to the beginning of goal state.
theorem double_injective' : ∀ n m : Nat, double n = double m → n = m := by
  intro n m
  -- Mimic `generalize dependent n by reverting n to the goal
  revert n
  induction m with
  | zero =>
    -- Base case: m = 0
    intro n eq
    cases n with
    | zero => rfl
    | succ _ => contradiction
  | succ m' IHm' =>
    -- Inductive step: m = S m'
    intro n eq
    cases n with
    | zero => contradiction
    | succ n' =>
      injection eq with eq'
      -- Apply the IH to the predecessor values
      have h := IHm' n'
      simp [Nat.add, Nat.mul] at eq'
      simp [double] at h
      simp [Nat.succ]
      exact h eq'

--Unfolding Definitions in lean
-- square function
def square (n : Nat) : Nat := n * n

-- Prove a lemma about `square`
theorem square_mult (n m : Nat) : square (n * m) = square n * square m := by
  unfold square -- Manually unfold the definition of `square`
  rw[Nat.mul_comm]
  rw [←Nat.mul_assoc]
  have h : n * m * n = n * n * m := by rw [Nat.mul_comm, Nat.mul_assoc]
  rw[h, Nat.mul_assoc]

-- A simple constant function
def foo (_ : Nat) : Nat := 5

-- Prove a simple fact about foo
theorem silly_fact_1 (m : Nat) : foo m + 1 = foo (m + 1) + 1 := by
  simp -- Automatically unfolds foo
  rfl

--A function with a match statement
def bar (x : Nat) : Nat :=
  match x with
  | 0 => 5
  | _ => 5

-- A failed attempt at proving a fact about bar
-- This fails because simp does not unfold the match expression
theorem silly_fact_2_FAILED (m : Nat) : bar m + 1 = bar (m + 1) + 1 := by
  simp -- Does nothing!
  sorry -- Proof stuck here

--Using cases or unfold with bar
--Using cases
theorem silly_fact_2 (m : Nat) : bar m + 1 = bar (m + 1) + 1 := by
  cases m with
  | zero => rfl -- Case: m = 0
  | succ _ => rfl -- Case: m = S m'

--Using unfold
theorem silly_fact_2' (m : Nat) : bar m + 1 = bar (m + 1) + 1 := by
  unfold bar -- Manually unfold the definition of bar
  cases m with
  | zero => rfl -- Case: m = 0
  | succ _ => rfl -- Case: m = S m'

--Unpacking compound expressions
--In Lean, we can use match expressions or cases to perform case analysis on the results of arbitrary computations.
--The behavior is similar to destruct in Coq.

def sillyfun (n : Nat) : Bool :=
  if n == 3 then false
  else if n == 5 then false
  else false

--Prove that sillyfun n always evaluates to false
theorem sillyfun_false (n : Nat) : sillyfun n = false := by
  unfold sillyfun -- Manually unfold the definition of sillyfun
  -- Perform case analysis on the result of `n == 3`
  cases (n == 3) with
  | true => rfl -- Case: n == 3 evaluates to true
  | false =>
    -- Perform case analysis on the result of n == 5
    cases (n == 5) with
    | true => rfl -- Case: n == 5 evaluates to true
    | false => rfl -- Case: n == 5 evaluates to false

--Keeping Track of Conditions with Equations
def sillyfun1 (n : Nat) : Bool :=
  if n == 3 then true
  else if n == 5 then true
  else false

--Prove that sillyfun1 n = true implies n is odd
theorem sillyfun1_odd (n : Nat) : sillyfun1 n = true → n % 2 = 1 := by
  intro h
  unfold sillyfun1 at h -- Expand sillyfun1
  -- Case analysis on the result of n == 3
  cases h1 : (n == 3) with
  | true =>
    -- Derive n = 3
    simp at h1
    -- Check that 3 is odd
    simp [h1]
  | false =>
    -- Case analysis on the result of n == 5
    cases h2 : (n == 5) with
    | true =>
      simp at h2
      simp [h2] -- 5 is odd
    |false =>
    rw [h1, h2] at h
    simp at h

--Lean’s cases directly works on expressions, making it powerful for compound expressions.
--The eqn: in Coq’s destruct is similar to Lean’s h : (expression) in cases.
