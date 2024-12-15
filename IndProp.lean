--Inductively defined propositions: Collatz example
-- div2 halves a natural number
def div2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => 1 + div2 n

--function f based on evenness
def f (n : Nat) : Nat :=
  if n % 2 == 0 then div2 n else 3 * n + 1

-- Inductive definition for Collatz_holds_for
inductive CollatzHoldsFor : Nat → Prop where
  | done : CollatzHoldsFor 1
  | more : (n : Nat) → CollatzHoldsFor (f n) → CollatzHoldsFor n

-- Prove that Collatz holds for 1
theorem collatz_holds_for_1 : CollatzHoldsFor 1 :=
  CollatzHoldsFor.done

-- Prove that Collatz holds for 2
theorem collatz_holds_for_2 : CollatzHoldsFor 2 :=
  CollatzHoldsFor.more 2 (CollatzHoldsFor.done)

--The constructors done and more in Lean correspond directly to Coq's Chf_done and Chf_more.
--Similar to Coq, Lean enforces totality for recursive functions. Attempting to define a function like reaches_1_in (which tracks the steps to reach 1) would fail due to the termination checker, as f n is not guaranteed to be smaller than n. This reflects the undecidability of the Collatz conjecture.

--Ordering

inductive Le : Nat → Nat → Prop where
  | refl (n : Nat) : Le n n       -- Base case: n ≤ n
  | step (n m : Nat) : Le n m → Le n (m + 1) -- Inductive step: n ≤ m → n ≤ m + 1

--Example: Proof of 3 ≤ 5
example : Le 3 5 := by
  apply Le.step -- Apply the inductive step for 3 ≤ 4
  apply Le.step -- Apply the inductive step for 3 ≤ 3
  apply Le.refl -- Base case: 3 ≤ 3

--Transitive Closure


-- Transitive closure of a relation R
inductive ClosTrans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | step (x y : X) : R x y → ClosTrans R x y
  | trans (x y z : X) : ClosTrans R x y → ClosTrans R y z → ClosTrans R x z

--Defining People and Parent-of Relation
inductive Person where
  | Sage : Person
  | Cleo : Person
  | Ridley : Person
  | Moss : Person
deriving Repr

inductive ParentOf : Person → Person → Prop where
  | po_SC : ParentOf Person.Sage Person.Cleo
  | po_SR : ParentOf Person.Sage Person.Ridley
  | po_CM : ParentOf Person.Cleo Person.Moss

--Defining Ancestor Relation
def AncestorOf : Person → Person → Prop :=
  ClosTrans ParentOf


-- Proof that Sage is an ancestor of Moss
example : AncestorOf Person.Sage Person.Moss := by
  apply ClosTrans.trans _ Person.Cleo _ -- Use transitivity via Cleo
  · apply ClosTrans.step -- Sage is a parent of Cleo
    exact ParentOf.po_SC
  · apply ClosTrans.step -- Cleo is a parent of Moss
    exact ParentOf.po_CM


--Permutations
--Defining the Permutation Relation for Three-Element Lists
inductive Perm3 {X : Type} : List X → List X → Prop where
  | swap12 (a b c : X) : Perm3 [a, b, c] [b, a, c] -- Swap the first two elements
  | swap23 (a b c : X) : Perm3 [a, b, c] [a, c, b] -- Swap the last two elements
  | trans (l1 l2 l3 : List X) : Perm3 l1 l2 → Perm3 l2 l3 → Perm3 l1 l3 -- Transitivity

example {X : Type} (a b c : X) : Perm3 [a, b, c] [b, c, a] := by
  apply Perm3.trans -- Use transitivity
  apply Perm3.swap12 -- swap the first two elements
  apply Perm3.swap23 -- swap the last two elements

--Evenness
inductive ev : Nat → Prop where
  | ev_0 : ev 0
  | ev_SS (n : Nat) (h : ev n) : ev (n + 2)

--Example: 4 is Even
theorem ev_4 : ev 4 := by
  apply ev.ev_SS -- reduce 4 to 2
  apply ev.ev_SS -- reduce 2 to 0
  apply ev.ev_0    -- Base case: 0 is even

--Example using constructor syntax directly
theorem ev_4' : ev 4 :=
  ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0)

--Example: Adding 4 to an Even Number
theorem ev_plus4 : ∀ n, ev n → ev (4 + n) := by
  intro n h -- Introduce `n` and the hypothesis `Even n`
  rw [Nat.add_comm] --Rewrite 4 + n to n + 4
  apply ev.ev_SS -- Reduce to n + 2
  apply ev.ev_SS -- Reduce to n
  exact h            -- Use the hypothesis h


--Evidence in Proofs
--Inversion on Evidence
-- Inversion Lemma for Even
theorem even_inversion (n : Nat) (h : ev n) :
    n = 0 ∨ (∃ n', n = n' + 2 ∧ ev n') := by
  cases h with
  | ev_0 =>
    -- Case: Even.zero
    left
    rfl
  | ev_SS n' h' =>
    -- Case: Even.add_two
    right
    exists n'

--Prove Even (S (S n)) → Even n
--Lean’s cases tactic on inductive hypotheses acts as an inversion tactic directly.
theorem evSS_ev (n : Nat) (h : ev (n + 2)) : ev n := by
  cases h
  -- The add_two case assigns h' to the evidence of Even n
  case ev_SS h' => exact h'

--¬Even 1. Prove that 1 is not even.
--We use cases tactic
theorem one_not_even' : ¬ ev 1 := by
  intro h
  cases h
--Lean’s cases tactic on inductive evidence directly splits the cases based on constructors.
-- This avoids manually proving and applying inversion lemmas.


--The Lean 4 cases tactic provides a powerful way to handle inductively defined propositions and data types, directly decomposing evidence into its constructors.
-- This is similar to Coq's inversion, but in Lean, cases also handles the equivalent of Coq’s discriminate and injection, making it a streamlined tool for many scenarios.

--Inversion on Lists
theorem inversion_ex1 (n m o : Nat) : [n, m] = [o, o] → [n] = [m] := by
  intro h
  cases h -- Lean automatically decomposes the list equality
  rfl

--Impossible Equality
theorem inversion_ex2 (n : Nat) : n + 1 = 0 → 2 + 2 = 5 := by
  intro contra
  cases contra -- This eliminates the impossible case

--Converting ev to Even
def double (n : Nat) : Nat := 2 * n

def Even (n : Nat) : Prop := ∃ k, n = double k


theorem ev_to_Even (n : Nat) (h : ev n) : Even n := by
  cases h
  case ev_0 =>
    -- Base case: ev 0
    exists 0
  case ev_SS n' h' =>
    -- Inductive case: ev (n + 2)
    cases ev_to_Even n' h' with --Recursively apply the hypothesis (ev_to_Even n' h')
    | intro k eqn =>
      exists k + 1
      rw [eqn]
      simp [double]
      rw [Nat.mul_comm 2 (k + 1)] -- We can provide the specific instance to be rewritten
      rw [Nat.add_mul]
      simp
      rw [Nat.mul_comm]

-- Proving ev n ↔ Even n
--Proving ∀n, ev(double n)
theorem ev_double (n : Nat) : ev (double n) := by
  induction n with
  | zero =>
    apply ev.ev_0
  | succ n' ih =>
    rw [double, Nat.mul_succ]
    apply ev.ev_SS
    exact ih


theorem ev_Even_iff (n : Nat) : ev n ↔ Even n := by
  apply Iff.intro
   -- ev n → Even n
  exact ev_to_Even n
-- (←): Even n → ev n
  intro h
  unfold Even at h
  cases h with
    | intro k hk =>
      rw [hk]
      apply ev_double

inductive le : Nat → Nat → Prop where
  | le_n (n : Nat) : le n n
  | le_S (n m : Nat) (h : le n m) : le n (m + 1)

theorem test_le1 : le 3 3 := by
  apply le.le_n

theorem test_le2 : le 3 6 := by
  apply le.le_S
  apply le.le_S
  apply le.le_S
  apply le.le_n

--Regular expressions in lean
--Definition
inductive RegExp (T : Type) : Type where
  | Empty : RegExp T
  | Char : T → RegExp T
  | App : RegExp T → RegExp T → RegExp T
  | Union : RegExp T → RegExp T → RegExp T
  | Star : RegExp T → RegExp T

--Matching Function
inductive ExpMatch {T : Type} : List T → RegExp T → Prop where
  | empty : ExpMatch [] (RegExp.Empty)
  | char (x : T) : ExpMatch [x] (RegExp.Char x)
  | app (s1 s2 : List T) (r1 r2 : RegExp T)
      (h1 : ExpMatch s1 r1) (h2 : ExpMatch s2 r2) :
      ExpMatch (s1 ++ s2) (RegExp.App r1 r2)
  | unionL (s : List T) (r1 r2 : RegExp T) (h : ExpMatch s r1) :
      ExpMatch s (RegExp.Union r1 r2)
  | unionR (s : List T) (r1 r2 : RegExp T) (h : ExpMatch s r2) :
      ExpMatch s (RegExp.Union r1 r2)
  | star_empty (r : RegExp T) : ExpMatch [] (RegExp.Star r)
  | star_app (s1 s2 : List T) (r : RegExp T)
      (h1 : ExpMatch s1 r) (h2 : ExpMatch s2 (RegExp.Star r)) :
      ExpMatch (s1 ++ s2) (RegExp.Star r)

example : ExpMatch [1] (RegExp.Char 1) := by
  apply ExpMatch.char

example : ExpMatch [1, 2] (RegExp.App (RegExp.Char 1) (RegExp.Char 2)) := by
  have split : [1, 2] = [1] ++ [2] := by simp
  rw [split]
  apply ExpMatch.app
  apply ExpMatch.char
  apply ExpMatch.char



--Helper Function
def regExpOfList {T : Type} : List T → RegExp T
  | [] => RegExp.Empty
  | x :: xs => RegExp.App (RegExp.Char x) (regExpOfList xs)

example : ExpMatch [1, 2,3] (regExpOfList [1, 2,3]) := by
  unfold regExpOfList
  have split : [1, 2, 3] = [1] ++ [2,3] := by simp
  rw [split]
  apply ExpMatch.app
  -- Prove for `[1]` matching `RegExp.Char 1`
  apply ExpMatch.char
  -- Prove for `[2, 3]` matching `regExpOfList [2, 3]`
  unfold regExpOfList -- Expand `regExpOfList [2, 3]`
  have split : [ 2, 3] = [2] ++ [3] := by simp
  rw [split]
  apply ExpMatch.app
  -- Prove for `[2]` matching `RegExp.Char 2`
  apply ExpMatch.char
  -- Prove for `[3]` matching `regExpOfList [3]`
  unfold regExpOfList -- Expand `regExpOfList [3]`
  have split : [3] = [3] ++ [] := by simp
  rw [split]
  apply ExpMatch.app
  -- Prove for `[3]` matching `RegExp.Char 3`
  apply ExpMatch.char
  -- Prove for `[]` matching `RegExp.Empty`
  unfold regExpOfList -- Expand `regExpOfList []`
  apply ExpMatch.empty

--Every Match of re Matches Star re
theorem MStar1 {T : Type} (s : List T) (re : RegExp T) :
    ExpMatch s re → ExpMatch s (RegExp.Star re) := by
  intro h
  have split : s = s ++ [] := by rw [List.append_nil]
  rw [split]
  apply ExpMatch.star_app s []
  exact h
  apply ExpMatch.star_empty

--Defining reChars, which lists all characters occurring in a regular expression
def reChars {T : Type} : RegExp T → List T
  | RegExp.Empty => []
  | RegExp.Char x => [x]
  | RegExp.App re1 re2 => reChars re1 ++ reChars re2
  | RegExp.Union re1 re2 => reChars re1 ++ reChars re2
  | RegExp.Star re => reChars re


--We do not looking into the regular expressions case study further

--We define the reflect type to relate a proposition P : Prop to a boolean value b : Bool.
inductive Reflect (P : Prop) : Bool → Prop
| ReflectT (h : P) : Reflect P true
| ReflectF (h : ¬ P) : Reflect P false

--equivalence between P ↔ b = true and Reflect P b
theorem iff_reflect {P : Prop} {b : Bool} : (P ↔ b = true) → Reflect P b :=
  fun h =>
    match b with
    | true  => Reflect.ReflectT (h.mpr rfl)
    | false => Reflect.ReflectF (fun hp => absurd (h.mp hp) (Bool.noConfusion))

--reflection principle for equality on natural numbers
theorem eqbP (n m : Nat) : Reflect (n = m) (n == m) :=
  iff_reflect (by simp [BEq.beq])
