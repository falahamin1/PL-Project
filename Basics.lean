-- Inductive definition of 'day' type
inductive Day : Type
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

-- We use open to avoid using Day.constuctor
open Day


-- Function next_weekday using day type
def next_weekday (d : Day) : Day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday

--To evaluate and display the functions, we require a 'Repr' instance of Day
-- type to tell Lean how to display the output.

instance : Repr Day where
  reprPrec
    | Day.monday, _    => "monday"
    | Day.tuesday, _   => "tuesday"
    | Day.wednesday, _ => "wednesday"
    | Day.thursday, _  => "thursday"
    | Day.friday, _    => "friday"
    | Day.saturday, _  => "saturday"
    | Day.sunday, _    => "sunday"


#eval next_weekday friday
-- Output: monday

#eval next_weekday (next_weekday saturday)
-- Output: tuesday

--Example
theorem test_next_weekday : next_weekday (next_weekday saturday) = tuesday := by
  simp [next_weekday]

-- Standard Boolean definition in Lean. We use t and f for true and false
-- and we use MyBool. This is due to the fact that Bool, true and false
-- are defined by default in lean.
inductive MyBool : Type
  | t
  | f

open MyBool
--functions over our MyBool type
def myNegb (b : MyBool) : MyBool :=
  match b with
  | t  => f
  | f => t

-- Definition of boolean And
def myAndb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | t  => b2
  | f => f

-- Definition of boolean OR
def myOrb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | t  => t
  | f => b2

-- Test case 1
theorem test_myOrb1 : myOrb t f = t := by
  simp [myOrb]

-- Test case 2
theorem test_myOrb2 : myOrb f f = f := by
  simp [myOrb]

-- Test case 3
theorem test_myOrb3 : myOrb f t = t := by
  simp [myOrb]

-- Test case 4
theorem test_myOrb4 : myOrb t t = t := by
  simp [myOrb]

instance : Repr MyBool where
  reprPrec
    | t, _ => "true"
    | f, _ => "false"


-- Giving notations in lean seems to be harder and seems to create ambiguity with the inbuilt keywords.
infixl:50  " and "  => myAndb  -- Left-associative, precedence 50
infixl:50 " or " => myOrb   -- Left-associative, precedence 50


--Example usage of the new notation
theorem test_orb5 : (f or f or t) = t := by
  simp [myOrb]

-- Defining the same functions using conditional expression.
-- for conditional expressions, we need to show that the '=' operator
-- is decidable for our custom myBool type. Therefore, we use the inbuilt Bool type for this expression.


--negation, and operation and or operation using conditional expressions.
def negb' (b : Bool) : Bool :=
  if b then false else true


def andb' (b1 b2 : Bool) : Bool :=
  if b1 then b2 else false

def orb' (b1 b2 : Bool) : Bool :=
  if b1 then true else b2


-- We have #check in lean which corresponds to Check in Coq.
#check true
-- Output: Bool.true : Bool

--to check if true is of type Bool and give error we use following syntax
#check (true : Bool)
-- Output: true : Bool. Gives error otherwise.

#check (negb' true : Bool)
-- Output: negb' true : Bool

#check negb'
-- Gives the type of the function. Output: negb' (b : Bool) : Bool

--New types from Old. This is very similar to Coq.

inductive Rgb : Type
  | red
  | green
  | blue

open Rgb

inductive Color : Type
  | black
  | white
  | primary (p : Rgb)

open Color

-- monochrome definition
def monochrome (c : Color) : Bool :=
  match c with
  | black  => true
  | white  => true
  | primary _ => false
--isRed definition
def isred (c : Color) : Bool :=
  match c with
  | black       => false
  | white       => false
  | primary red => true
  | primary _   => false

-- Instead of Modules we have namespaces
namespace Playground
  -- Defining foo in the Playground namespace
  def foo : Rgb := Rgb.blue
end Playground

-- Defining foo outside the Playground namespace
def foo : Bool := true

-- Checking the values
#check Playground.foo
 -- Output: Playground.foo : Rgb
#check foo
-- Ouput: foo : Bool

-- Tuples
namespace TuplePlayground

inductive Bit : Type
  | B1
  | B0

inductive Nybble : Type
  | bits (b0 b1 b2 b3 : Bit)

open Bit Nybble

def all_zero (nb : Nybble) : Bool :=
  match nb with
  | bits B0 B0 B0 B0 => true
  | bits _ _ _ _     => false

#eval all_zero (bits B1 B0 B1 B0)
-- Output: false
#eval all_zero (bits B0 B0 B0 B0)
-- Output: true

end TuplePlayground

-- Numbers

namespace NatPlayground

inductive Nat : Type
  | O
  | S (n : Nat)
open Nat
inductive OtherNat : Type
  | stop
  | tick (foo : OtherNat)

def pred (n : Nat) : Nat :=
  match n with
  | O     => O
  | S n'  => n'

end NatPlayground
-- We use Nat.succ for S
#eval Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))

def minustwo (n : Nat) : Nat :=
  match n with
  | 0          => 0
  | Nat.succ 0 => 0
  | Nat.succ (Nat.succ n') => n'

#eval minustwo 4
-- Output: 2


--Fixpoints. Lean supports recursion on regular def itself
def even (n : Nat) : Bool :=
  match n with
  | 0              => true
  | Nat.succ 0     => false
  | Nat.succ (Nat.succ n') => even n'

--defining odd using even
def odd (n : Nat) : Bool :=
  !even n

theorem test_odd1 : odd 1 = true := by
  simp [odd]
  simp [even]

theorem test_odd2 : odd 4 = false := by
  simp [odd]
  simp [even]


namespace NatPlayground2

-- Recursive definition of `plus` function
def plus (n m : Nat) : Nat :=
  match n with
  | 0 => m
  | Nat.succ n' => Nat.succ (plus n' m)

#eval plus 2 3

def mult (n m : Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ n' => plus m (mult n' m)

theorem test_mult1 : mult 3 3 = 9 := by
  simp [mult]
  simp [plus]

-- Recursive definition of minus
def minus (n m : Nat) : Nat :=
  match n, m with
  | 0, _         => 0
  | Nat.succ _, 0 => n
  | Nat.succ n', Nat.succ m' => minus n' m'

end NatPlayground2

-- Recursive definition of exp. We use NatPlayground2.mult as we are outside the namespace
def exp (base power : Nat) : Nat :=
  match power with
  | 0 => Nat.succ 0
  | Nat.succ p => NatPlayground2.mult base (exp base p)

-- Equality definition
def eqb (n m : Nat) : Bool :=
  match n, m with
  | 0, 0         => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ n', Nat.succ m' => eqb n' m'

--less than equal to definition
def leb (n m : Nat) : Bool :=
  match n, m with
  | 0, _         => true
  | Nat.succ _, 0 => false
  | Nat.succ n', Nat.succ m' => leb n' m'

theorem test_leb1 : leb 2 2 = true := by
  simp [leb]

theorem test_leb2 : leb 2 4 = true := by
  simp [leb]

theorem test_leb3 : leb 4 2 = false := by
  simp [leb]


-- Proof by simplification. Simp is more powerful and flexible than simpl in coq.
theorem plus_0_n : ∀ n : Nat, 0 + n = n := by
  simp

theorem plus_0_n' : ∀ n : Nat, n + 0 = n := by
  simp

-- rfl tactic is same as reflexivity in coq
theorem plus_1_n : ∀ n : Nat,  n + 1 = Nat.succ n := by
  intro n
  rfl

theorem mult_1_n : ∀ n : Nat,  0 * n = 0 := by
  simp


--Proof by rewriting

theorem plus_id_example : ∀ n m : Nat, n = m → n + n = m + m := by
intro n m H  -- introduce variables `n`, `m`, and hypothesis `H`
rw [H]       -- rewrite keyword in lean

theorem mult_n_0_m_0 : ∀ p q : Nat, (p * 0) + (q * 0) = 0 := by
intros p q
rw [Nat.mul_zero]
rw [Nat.mul_zero] -- We use rewrite for multiplication with 0

-- Proof by case analysis
-- We use Nat.beq instead of =? in coqx
theorem plus_1_neq_0 : ∀ n : Nat, Nat.beq (n + 1) 0 = false := by
intro n
cases n  --cases instead of destruct
case zero =>
--base case
  simp [Nat.beq, Nat.add]
case succ n' =>
-- recursive case
  simp [Nat.beq, Nat.add]

-- We use ! instead of negb
theorem negb_involutive : ∀ b : Bool, !(!b) = b := by
  intro b  -- Introduce the boolean `b`
  cases b  -- case analysis
  case false => rfl
  case true => rfl

-- Theorem: Boolean AND is commutative
theorem andb_commutative : ∀ b c : Bool, (b && c) = (c && b) := by
intro b c  -- Introduce b and c
cases b with -- destruct to each case of b (lean automatically names it true and false)
  | false => -- when b is false
    cases c with -- Each case of c
    | false => rfl  -- When c is false
    | true => rfl   -- When b is true
  | true =>
    cases c with
    | false => rfl
    | true => rfl
