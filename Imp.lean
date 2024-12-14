--Simple Imperative Programs
--Defining arithmetic and boolean expressions
--Arithmetic Expressions
inductive AExp
| ANum (n : Nat) : AExp
| APlus (a1 a2 : AExp) : AExp
| AMinus (a1 a2 : AExp) : AExp
| AMult (a1 a2 : AExp) : AExp

--Boolean Expressions
inductive BExp
| BTrue : BExp
| BFalse : BExp
| BEq (a1 a2 : AExp) : BExp
| BNeq (a1 a2 : AExp) : BExp
| BLe (a1 a2 : AExp) : BExp
| BGt (a1 a2 : AExp) : BExp
| BNot (b : BExp) : BExp
| BAnd (b1 b2 : BExp) : BExp

--Evaluation
--Arithmetic expression evaluations
def aeval : AExp → Nat
| AExp.ANum n => n
| AExp.APlus a1 a2 => aeval a1 + aeval a2
| AExp.AMinus a1 a2 => aeval a1 - aeval a2
| AExp.AMult a1 a2 => aeval a1 * aeval a2

--Boolean expression evaluation
def beval : BExp → Bool
| BExp.BTrue => true
| BExp.BFalse => false
| BExp.BEq a1 a2 => aeval a1 == aeval a2
| BExp.BNeq a1 a2 => !(aeval a1 == aeval a2)
| BExp.BLe a1 a2 => aeval a1 ≤ aeval a2
| BExp.BGt a1 a2 => !(aeval a1 ≤ aeval a2)
| BExp.BNot b1 => !(beval b1)
| BExp.BAnd b1 b2 => beval b1 && beval b2

--Examples
#eval aeval (AExp.APlus (AExp.ANum 3) (AExp.ANum 9)) -- Output: 12

#eval beval (BExp.BEq (AExp.APlus (AExp.ANum 5) (AExp.ANum 3)) (AExp.ANum 8)) -- Output: true

--Optimization
-- Simple optimization that changes every occurance of 0+e to e
def optimize_0plus : AExp → AExp
| AExp.ANum n => AExp.ANum n
| AExp.APlus (AExp.ANum 0) e2 => optimize_0plus e2
| AExp.APlus e1 e2 => AExp.APlus (optimize_0plus e1) (optimize_0plus e2)
| AExp.AMinus e1 e2 => AExp.AMinus (optimize_0plus e1) (optimize_0plus e2)
| AExp.AMult e1 e2 => AExp.AMult (optimize_0plus e1) (optimize_0plus e2)

--Proving correctness of optimize_0plus
  theorem optimize_0plus_sound : ∀ a : AExp, aeval (optimize_0plus a) = aeval a := by
    intro a
    induction a with
    | ANum n => rfl
    | APlus e1 e2 ih1 ih2 =>
      cases e1 with
      | ANum n =>
        cases n with
        | zero =>
          -- Case: e1 = ANum 0
          simp [optimize_0plus, aeval]
          rw [ih2]
        | succ _ =>
          -- Case: e1 = ANum (succ n)
          simp [optimize_0plus, aeval]
          rw [ih2]
      | APlus a1 a2 =>
        -- Case: e1 is a nested APlus
        simp [optimize_0plus, aeval]
        rw [ih1]
        rw [ih2]
        simp [aeval]
      | AMinus a1 a2 =>
        -- Case: e1 is a nested AMinus
        simp [optimize_0plus, aeval]
        simp [aeval] at ih1
        rw [ih1, ih2]
      | AMult a1 a2 =>
        -- Case: e1 is a nested AMult
        simp [optimize_0plus]
        simp [aeval]
        simp [aeval] at ih1
        rw [ih1, ih2]
    | AMinus e1 e2 ih1 ih2 =>
      -- Case: a is AMinus e1 e2
      simp [optimize_0plus, aeval]
      rw [ih1, ih2]
    | AMult e1 e2 ih1 ih2 =>
      -- Case: a is AMult e1 e2
      simp [optimize_0plus, aeval]
      rw [ih1, ih2]

--Tactical
--try tactical in lean
example (P : Prop) (h : P) : P := by
  try { rfl }  -- Does nothing if rfl fails
  exact h      -- Completes the proof

-- <;> for sequential application of tactic
example (P Q : Prop) (h : P ∧ Q) : P := by
  cases h <;> assumption --splits to two goals and applies assumption on both

--repeat tactic in lean
example (P Q R : Prop) (h1 : P) (h2 : Q) (h3 : R) : P ∧ Q ∧ R := by
  repeat ( constructor <;> repeat assumption)
--constructor tactic applies the constructor for conjunction Add.intro
--Assumption tactic looks for a matching assumption in context of the goal

--Lean simp_all simplifies all hypotheses and the goal
example (x : Nat) (_ : x + 0 = x) (_ : 0 + x = x) : x + 0 + 0 = x := by
  simp_all  -- Simplifies both the goal and hypotheses


--Using tacticals in optimize_0plus_sound proof
theorem optimize_0plus_sound' : ∀ a : AExp, aeval (optimize_0plus a) = aeval a := by
  intro a
  induction a with
  | ANum n => rfl
  | APlus e1 e2 ih1 ih2 =>
    cases e1 with
    | ANum n =>
      cases n with
      | _ =>
        simp [optimize_0plus, aeval] <;> rw [ih2]
    | APlus a1 a2 =>
        simp [optimize_0plus, aeval]
        rw [ih1, ih2]
        simp [aeval]
    | _ =>
      -- Handle all compound cases uniformly
      simp [optimize_0plus, aeval] <;>simp [aeval] at ih1 <;>rw [ih1, ih2]<;> simp [aeval]
  | _ e1 e2 ih1 ih2 =>
      simp [optimize_0plus, aeval] <;> rw [ih1, ih2]



--linarith. linarith from Mathlib library is the equivalent of lia in Lean 4
example (m n o p : Nat) : m + n ≤ n + o ∧ o + 3 = p + 3 → m ≤ p := by
  intro h
  linarith

-- Using linarith to create a custom tactic
syntax "lin_solve" : tactic --syntax keyword defines a new tactic notation
--Defining a custom tactic smart_solve
macro_rules
  | `(tactic| lin_solve) =>
    `(tactic| try linarith <;> simp)

--Examples
example (m n : Nat) : m + n = n + m := by
  lin_solve

example (a b : Int) (h : a + b = 0) : b = -a := by
  lin_solve

--More detailed definitions of tactics in https://leanprover.github.io/theorem_proving_in_lean4/tactics.html
--Inductive definition of AExp


--Inductive definition of the evaluation
inductive AExpEval : AExp → Nat → Prop where
  | E_ANum (n : Nat) : AExpEval (AExp.ANum n) n
  | E_APlus (e1 e2 : AExp) (n1 n2 : Nat)
      (h1 : AExpEval e1 n1) (h2 : AExpEval e2 n2) :
      AExpEval (AExp.APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : AExp) (n1 n2 : Nat)
      (h1 : AExpEval e1 n1) (h2 : AExpEval e2 n2) :
      AExpEval (AExp.AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : AExp) (n1 n2 : Nat)
      (h1 : AExpEval e1 n1) (h2 : AExpEval e2 n2) :
      AExpEval (AExp.AMult e1 e2) (n1 * n2)

--Equivalence of the two definitions
theorem aeval_iff_AExpEval' : ∀ a n, AExpEval a n ↔ aeval a = n := by
  intro a n
  apply Iff.intro
  -- Forward direction
  intro h
  induction h with
  |E_ANum n =>
    rfl
  | E_APlus e1 e2 n1 n2 h1 h2 ih1 ih2 =>
      simp [aeval]
      rw [ih1, ih2]
  | E_AMinus e1 e2 n1 n2 h1 h2 ih1 ih2 =>
      simp [aeval]
      rw [ih1, ih2]
  | E_AMult e1 e2 n1 n2 h1 h2 ih1 ih2 =>
      simp [aeval]
      rw [ih1, ih2]
   -- Backward direction
  revert n
  induction a with
    | ANum n =>
      intro n' h
      rw [aeval] at h
      rw [h]
      exact AExpEval.E_ANum n'
    | APlus e1 e2 ih1 ih2 =>
    intro n h
    rw [aeval] at h
    rw [←h]
    apply AExpEval.E_APlus
    apply ih1 <;> rfl
    apply ih2 <;> rfl
    | AMinus e1 e2 ih1 ih2 =>
    intro n h
    simp [aeval] at h
    rw [←h]
    apply AExpEval.E_AMinus
    apply ih1 <;> rfl
    apply ih2 <;> rfl
    | AMult e1 e2 ih1 ih2 =>
    intro n h
    simp [aeval] at h
    rw [←h]
    apply AExpEval.E_AMult
    apply ih1 <;> rfl
    apply ih2 <;> rfl

--Advantages of relational definitions
--Introducing division to AExp
inductive AExp'
| ANum (n : Nat) : AExp'
| APlus (a1 a2 : AExp') : AExp'
| AMinus (a1 a2 : AExp') : AExp'
| AMult (a1 a2 : AExp') : AExp'
| ADiv (a1 a2 : AExp') : AExp' -- New case for division

-- As suggested in the textbook, this definition is not straightforward
-- as we do not give a proper return result for ADiv (ANum 5) (ANum 0)?)

--Relational definition with the newly added division definition
inductive AExpEval' : AExp' → Nat → Prop where
  | E_ANum (n : Nat) : AExpEval' (AExp'.ANum n) n
  | E_APlus (e1 e2 : AExp') (n1 n2 : Nat)
      (h1 : AExpEval' e1 n1) (h2 : AExpEval' e2 n2) :
      AExpEval' (AExp'.APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : AExp') (n1 n2 : Nat)
      (h1 : AExpEval' e1 n1) (h2 : AExpEval' e2 n2) :
      AExpEval' (AExp'.AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : AExp') (n1 n2 : Nat)
      (h1 : AExpEval' e1 n1) (h2 : AExpEval' e2 n2) :
      AExpEval' (AExp'.AMult e1 e2) (n1 * n2)
  | E_ADiv (e1 e2 : AExp') (n1 n2 n3 : Nat)
      (h1 : AExpEval' e1 n1) (h2 : AExpEval' e2 n2)
      (nz : n2 > 0) (div_eq : n1 = n2 * n3) :
      AExpEval' (AExp'.ADiv e1 e2) n3 -- Division only if divisor is non-zero

--Another example: Adding non-determinism
inductive AExp''
| ANum (n : Nat) : AExp''
| APlus (a1 a2 : AExp'') : AExp''
| AMinus (a1 a2 : AExp'') : AExp''
| AMult (a1 a2 : AExp'') : AExp''
| AAny : AExp'' -- New case for non-deterministic numbers

--Again how to have non-determinism is harder to define in the inductive manner.
--Relational definition
inductive AExpEval'' : AExp'' → Nat → Prop where
  | E_ANum (n : Nat) : AExpEval'' (AExp''.ANum n) n
  | E_APlus (e1 e2 : AExp'') (n1 n2 : Nat)
      (h1 : AExpEval'' e1 n1) (h2 : AExpEval'' e2 n2) :
      AExpEval'' (AExp''.APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : AExp'') (n1 n2 : Nat)
      (h1 : AExpEval'' e1 n1) (h2 : AExpEval'' e2 n2) :
      AExpEval'' (AExp''.AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : AExp'') (n1 n2 : Nat)
      (h1 : AExpEval'' e1 n1) (h2 : AExpEval'' e2 n2) :
      AExpEval'' (AExp''.AMult e1 e2) (n1 * n2)
  | E_Any (n : Nat) : AExpEval'' AExp''.AAny n -- Non-deterministic evaluation


--Expressions with Variables
namespace Imp

-- Arithmetic expressions
inductive AExp
| ANum (n : Nat) : AExp
| AId (x : String) : AExp  -- Variables
| APlus (a1 a2 : AExp) : AExp
| AMinus (a1 a2 : AExp) : AExp
| AMult (a1 a2 : AExp) : AExp

-- Boolean expressions
inductive BExp
| BTrue : BExp
| BFalse : BExp
| BEq (a1 a2 : AExp) : BExp
| BNeq (a1 a2 : AExp) : BExp
| BLe (a1 a2 : AExp) : BExp
| BGt (a1 a2 : AExp) : BExp
| BNot (b : BExp) : BExp
| BAnd (b1 b2 : BExp) : BExp

-- States represented as total maps
def State := String → Nat

-- Extend evaluation to handle state
def aeval (st : State) : AExp → Nat
| AExp.ANum n => n
| AExp.AId x => st x -- Look up the variable in the state
| AExp.APlus a1 a2 => aeval st a1 + aeval st a2
| AExp.AMinus a1 a2 => aeval st a1 - aeval st a2
| AExp.AMult a1 a2 => aeval st a1 * aeval st a2

def beval (st : State) : BExp → Bool
| BExp.BTrue => true
| BExp.BFalse => false
| BExp.BEq a1 a2 => aeval st a1 == aeval st a2
| BExp.BNeq a1 a2 => not (aeval st a1 == aeval st a2)
| BExp.BLe a1 a2 => aeval st a1 <= aeval st a2
| BExp.BGt a1 a2 => not (aeval st a1 <= aeval st a2)
| BExp.BNot b1 => not (beval st b1)
| BExp.BAnd b1 b2 => beval st b1 && beval st b2

-- Define variable identifiers
def X : String := "X"
def Y : String := "Y"
def Z : String := "Z"

-- Example state: map all variables to 0
def emptyState : State := fun _ => 0

-- Example state with some values
def exampleState : State := fun x =>
  if x = X then 5 else
  if x = Y then 3 else 0

def exampleAExp : AExp := AExp.APlus (AExp.AId X) (AExp.AMult (AExp.ANum 2) (AExp.AId Y))

#eval aeval exampleState exampleAExp -- Output: 11

def exampleBExp : BExp := BExp.BAnd BExp.BTrue (BExp.BNot (BExp.BLe (AExp.AId X) (AExp.ANum 4)))

#eval beval exampleState exampleBExp --Output: true &&  ¬(5 <= 4) = true

-- Extend commands
inductive Com
| skip : Com
| asgn (x : String) (a : AExp) : Com
| seq (c1 c2 : Com) : Com
| ite (b : BExp) (c1 c2 : Com) : Com  -- if-then-else
| while (b : BExp) (c : Com) : Com    -- while loop

--update function
def update (x : String) (v : Nat) (st : State) : State :=
  fun y => if y = x then v else st y

-- Notations for commands
notation "skip" => Com.skip
notation x ":=" y => Com.assign x y
notation x ";" y => Com.seq x y
notation "if" b "then" c1 "else" c2 "end" => Com.ite b c1 c2
notation "while" b "do" c "end" => Com.while b c
--Evaluation relation
inductive Ceval : Com → State → State → Prop
| skip (st : State) :
    Ceval Com.skip st st
| asgn (st : State) (a : AExp) (x : String) :
    Ceval (Com.asgn x a) st (update x (aeval st a) st)
| seq (c1 c2 : Com) (st st' st'' : State) :
    Ceval c1 st st' → Ceval c2 st' st'' → Ceval (Com.seq c1 c2) st st''
| ite_true (st st' : State) (b : BExp) (c1 c2 : Com) :
    beval st b = true → Ceval c1 st st' → Ceval (Com.ite b c1 c2) st st'
| ite_false (st st' : State) (b : BExp) (c1 c2 : Com) :
    beval st b = false → Ceval c2 st st' → Ceval (Com.ite b c1 c2) st st'
| while_false (b : BExp) (st : State) (c : Com) :
    beval st b = false → Ceval (Com.while b c) st st
| while_true (st st' st'' : State) (b : BExp) (c : Com) :
    beval st b = true → Ceval c st st' → Ceval (Com.while b c) st' st'' →
    Ceval (Com.while b c) st st''
end Imp
