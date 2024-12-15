--Propositions in lean: Similar to Coq, propositions are first class entitities.
#check ∀ n m : Nat, n + m = m + n -- Outputs: Prop
example : 2 + 2 = 4 := rfl -- Proof that 2 + 2 = 4
#check (2 + 2 = 4) -- Outputs: Prop
#check (rfl : 2 + 2 = 4) -- Outputs: 2 + 2 = 4

--Provable proposition:
theorem add_comm (n m : Nat) : n + m = m + n :=
  Nat.add_comm n m

#check add_comm --Outputs: add_comm (n m : Nat) : n + m = m + n
#check ∀ n m : Nat, n + m = m + n -- Outputs: Prop

--Defining propositions using def
def plus_claim : Prop := 2 + 2 = 4
#check plus_claim -- Outputs: Prop

--You can refer to plus_claim in a theorem or lemma
theorem plus_claim_is_true : plus_claim :=
  rfl -- reflexivity proof for 2 + 2 = 4

--Defining Parameterized Propositions
--The property of being equal to three
def is_three (n : Nat) : Prop := n = 3
#check is_three -- Outputs: (n: Nat) : Prop

--Using is_three in a theorem
theorem three_is_three : is_three 3 :=
  rfl

--Defining Injectivity
def injective {A B : Type} (f : A → B) : Prop :=
  ∀ x y : A, f x = f y → x = y

--Proving Injectivity for successors
theorem succ_injective : injective Nat.succ :=
  fun _ _ h =>
    Nat.noConfusion h (fun h_eq => h_eq)
--Nat.noConfusion is a Lean tactic-like function that performs case analysis on natural numbers.
--It asserts that if Nat.succ n = Nat.succ m, then n = m.

--Logical Connectives
--Conjunction
--In lean, similar to Coq, we write A ∧ B for conjunction
-- Lean provide Add.intro constructor analogous to Coq's conj
example : 3 + 4 = 7 ∧ 2 * 2 = 4 :=
  And.intro rfl rfl

--Decomposing conjunction: We can use cases or And.left or And.right to
-- extract individual components of conjunction.
example (h : 3 + 4 = 7 ∧ 2 * 2 = 4) : 3 + 4 = 7 :=
  h.left -- Extract the first part of the conjunction

--Destructing conjunction. We use cases tactics to decompose the goal.
example (n m : Nat) (H : n = 0 ∧ m = 0) : n + m = 0 := by
  cases H with
  | intro hn hm =>
    rw [hn, hm]

--exercise example from PLF
theorem and_exercise (n m : Nat) (h : n + m = 0) : n = 0 ∧ m = 0 := by
  apply And.intro
   -- Prove n = 0
  have hn : n ≤ n + m := Nat.le_add_right n m --check inequality n ≤ n + m
  rw [h] at hn
  exact Nat.eq_zero_of_le_zero hn
   -- Prove m = 0
  have hm : m ≤ n + m := Nat.le_add_left m n -- check inequality m ≤ n + m
  rw [h] at hm
  exact Nat.eq_zero_of_le_zero hm -- Nat.eq_zero_of_le_zero states that if x ≤ 0, then x = 0 for natural numbers

-- now we use this result to prove n + m = 0 → n × m = 0
theorem and_example3 (n m : Nat) (h : n + m = 0) : n * m = 0 := by
  -- Apply and_exercise to derive n = 0 and m = 0
  have ⟨hn, hm⟩ := and_exercise n m h
  -- Substitute n = 0 and m = 0 into the goal
  rw [hn, hm]

--Removing unneeded conjuct using _
theorem proj1 (P Q : Prop) (h : P ∧ Q) : P := by
  cases h with
  | intro hp _ => -- keep only hp
    exact hp

--Discjuntion
--Similar to conjunction, we can do case analysis using the cases tactic
--Example
theorem factor_is_0 (n m : Nat) (h : n = 0 ∨ m = 0) : n * m = 0 := by
  cases h with
  | inl hn => -- Case: n = 0
    rw [hn]
    exact Nat.zero_mul m
  | inr hm => -- Case: m = 0
    rw [hm]
    exact Nat.mul_zero n

--Or.inl and Or.inr are used similar to Coq's left and right
theorem or_intro_l (A B : Prop) (ha : A) : A ∨ B :=
  Or.inl ha

--Another example
theorem zero_or_succ (n : Nat) : n = 0 ∨ n = Nat.succ (n - 1) := by
  cases n with
  | zero => -- Case: n = 0
    exact Or.inl rfl --Use reflexivity to simplify 0 = 0
  | succ n' => -- Case: n = Nat.succ n'
    exact Or.inr rfl

--Negation
--In lean ¬P is defined similar to Coq that is P → False
--Example
example : ¬(0 = 1) := by
  intro h -- Assume 0 = 1
  cases h -- This leads to a contradiction because 0 and 1 are different constructors

--Example: Using False.elim
example (P : Prop) : False → P :=
  False.elim
--False.elim is Lean's equivalent of Coq's destruct contra.
-- It eliminates a hypothesis of type False by leveraging the fact that False has no constructors.

--inequality is written as A ≠ B which is shorthand for ¬(A = B)
#check (0 ≠ 1) -- Outputs: Prop

--Example
theorem zero_not_one : 0 ≠ 1 := by
  intro h -- Assume  0 = 1
  cases h -- Contradiction

--Proof that False cannot hold ¬False
theorem nfalse : ¬False := by
  intro h -- Assume False
  exact False.elim h -- Derive any contradiction from h

--Contradiction implies anything
theorem contradiction_implies_anything (P Q : Prop) : P ∧ ¬P → Q := by
  intro h
  cases h with
  | intro hp hnp =>
    -- Apply hnp to hp
    have contra := hnp hp
    exact False.elim contra -- Derive Q from False

--Double negation. P → ¬¬P
theorem double_neg (P : Prop) : P → ¬¬P := by
  intro hp
  intro hnp
  exact hnp hp

--The False.elim function serves as Lean's counterpart to Coq's ex_falso_quodlibet.
theorem not_true_is_false (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | true =>
    --  b = true
    have contra := h rfl --  assumption h to rfl : true = true
    exact False.elim contra -- Derive a contradiction
  | false =>
    -- b = false
    rfl -- Reflexivity proves false = false

--Using exfalso
theorem not_true_is_false' (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | true =>
    exfalso -- Explicitly state that we are reasoning from False
    exact h rfl -- Apply h to  rfl to derive the contradiction
  | false =>
    rfl

-- Using True
--Example
def disc_fn (n : Nat): Prop :=
match n with
| 0 => True
| Nat.succ _ => False

theorem disc_example' (n : Nat) : ¬(0 = Nat.succ n) := by
  intro h
  have h2 : disc_fn 0 := True.intro -- disc_fn 0 simplifies to True
  rw [h] at h2
  cases h2 -- Contradiction: disc_fn (Nat.succ n) is False

-- Logical equivalence is defined as P ↔ Q = (P → Q) ∧ (Q → P)
--Symmetry of ↔
theorem iff_sym (P Q : Prop) (h : P ↔ Q) : Q ↔ P := by
  cases h with
  | intro pq qp =>
    apply Iff.intro
    exact qp -- Q → P
    exact pq -- P → Q

--Example
theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  apply Iff.intro
  -- Prove b ≠ true → b = false
  exact not_true_is_false b
  -- Prove b = false → b ≠ true
  intro h
  rw [h]
  intro h'
  exact Bool.noConfusion h' --Bool.noConfusion enforces the disjointness of Boolean constructors and gives a contradiction based on this.

-- Example: If P ↔ Q and Q → R then P → Q
theorem apply_iff_example1 (P Q R : Prop) (hiff : P ↔ Q) (hq_r : Q → R) : P → R := by
  intro hp -- Assume P
  apply hq_r -- Goal becomes Q
  apply hiff.mp -- Use P → Q direction of the equivalence
  exact hp
--Here hiff.mp gives P → Q and hiff.mpr gives Q → P.

--Setoids and Logical Equivalence
theorem mul_eq_zero (n m : Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  rw [Nat.mul_eq_zero]

theorem or_assoc' (P Q R : Prop) : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  apply Iff.intro
  -- Forward direction
  intro h
  cases h with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
      cases hqr with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr
   -- Backward direction
  intro h
  cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)

theorem mul_eq_zero_ternary {n m p : Nat} : n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  rw [mul_eq_zero]
  rw [mul_eq_zero]
  rw [or_assoc']

--Existential Quantifiers
--Example
def Even (x : Nat) := ∃ n : Nat, x = 2 * n --Double definition

--Prove 4 is even
theorem four_is_Even : Even 4 := by
  unfold Even
  exists 2 -- Specify the witness 2

--Example
theorem exists_example_2 (n : Nat) :
    (∃ m, n = 4 + m) → (∃ o, n = 2 + o) := by
  intro h
  cases h with
  | intro m hm =>
    exists (2 + m) -- Provide the new witness 2 + m
    rw [hm] -- Rewrite n using the hypothesis hm
    rw [←Nat.add_assoc]

--Programming with Propositions
-- Defining a function that checks if x is in a list
inductive In {A : Type} : A → List A → Prop
| here {x : A} {xs : List A} : In x (x :: xs) -- x is at the head of the list
| there {x y : A} {xs : List A} : In x xs → In x (y :: xs) -- x is in the tail of the list

-- Example usage
example : In 4 [1, 2, 3, 4, 5] := by
  apply In.there
  apply In.there
  apply In.there
  apply In.here

--Prove that if x is in a list, it remains in the list when mapped.
theorem In_map {A B : Type} (f : A → B) (l : List A) (x : A) :
    In x l → In (f x) (l.map f) := by
  intro h
  induction l with
  | nil =>
    -- Base case: l = []
    cases h
  | cons y l ih =>
    -- Inductive case:l = y :: l'
    cases h with
    | here =>
      -- Case: x = y
      apply In.here
    | there h' =>
      -- Case: x ∈ l
      apply In.there
      exact ih h'
--Using theorems to arguments
-- Theorem add_comm3
theorem add_comm3 (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [add_comm] -- Rewrite using add_comm for x + (y + z)
  rw [add_comm y z] -- add_comm for y and z

-- Using theorems as functions
theorem in_not_nil {A : Type} (x : A) (l : List A) : In x l → l ≠ [] := by
  intro h
  intro contra
  rw [contra] at h
  cases h

theorem in_not_nil_42 (l : List Nat) (h : In 42 l) : l ≠ [] := by
  apply @in_not_nil Nat 42 l --@ used to explicitely state all the arguments
  exact h

--Using apply with arguments and wildcards
theorem in_not_nil_42_take5 (l : List Nat) (h : In 42 l) : l ≠ [] := by
  apply in_not_nil _ _ h -- Wildcards _ allow Lean to infer arguments

--Decidability.
def even : Nat → Bool
| 0 => true
| 1 => false
| n + 2 => even n

theorem even_double (k : Nat) : even (2 * k) = true := by
  induction k with
  | zero =>
    rfl
  | succ k ih =>
    rw [Nat.mul_succ]
    exact ih
