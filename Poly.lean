--example Bool list to show why we need polymorphic inductive type
inductive BoolList : Type where
  | nil : BoolList
  | cons : Bool → BoolList → BoolList

--polymorhic inductive definition of Lists
inductive List' (α : Type) : Type where
  | nil : List' α
  | cons : α → List' α → List' α

--checking the type
#check List' -- Output: Type → Type
#check List'.cons 3 List'.nil   -- Works: List' Nat
#check List'.cons 3 List'.nil  -- Error: List'.nil is ambiguous
#check List'.nil                   -- Output: ∀ α : Type, List' α
#check List'.cons                  -- Output: ∀ α : Type, α → List' α → List' α
#check List'.cons 2 (List'.cons 1 (List'.nil)) -- Output: List' Nat

-- Polymorphic repeat function for List'
def repeat' {α : Type} (x : α) (count : Nat) : List' α :=
  match count with
  | 0 => List'.nil
  | Nat.succ count' => List'.cons x (repeat' x count')

--Type inference in lean.
def repeat'' {α : Type} (x : α) : Nat → List' α
  | 0 => List'.nil
  | Nat.succ count' => List'.cons x (repeat' x count')

-- Lean do not have implicit argument 'Argument' keyword
--List handling functions for polymorphic types

--appending two lists
def app {α : Type} (l1 l2 : List' α) : List' α :=
  match l1 with
  | List'.nil => l2
  | List'.cons h t => List'.cons h (app t l2)

-- reverse of list
def rev {α : Type} (l : List' α) : List' α :=
  match l with
  | List'.nil => List'.nil
  | List'.cons h t => app (rev t) (List'.cons h List'.nil)

--length of list
def length {α : Type} (l : List' α) : Nat :=
  match l with
  | List'.nil => 0
  | List'.cons _ t => Nat.succ (length t)

  --Examples
def list1 : List' Nat := List'.cons 1 (List'.cons 2 List'.nil)
def list2 : List' Bool := List'.cons true List'.nil
def list3 : List' Nat := List'.cons 1 (List'.cons 2 (List'.cons 3 List'.nil))


theorem test_rev1 : rev list1 = List'.cons 2 (List'.cons 1 List'.nil) := by
  rfl

theorem test_rev2 : rev list2 = List'.cons true List'.nil := by
  rfl

theorem test_length1 : length list3 = 3 := by
  rfl

--Polymorphic Pairs. We use Prod' as Prod is present in Lean's pre loaded library
inductive Prod' (X Y : Type) : Type where
  | pair : X → Y → Prod' X Y

-- We are using inbuilt Prod for easier notation
def fst {X Y : Type} (p : X × Y) : X :=
  match p with
  | (x, _) => x

-- Define `snd` for a pair
def snd {X Y : Type} (p : X × Y) : Y :=
  match p with
  | (_, y) => y

--combine function defined in lean
def combine {X Y : Type} : List X → List Y → List (X × Y)
  | [], _ => []  -- If the first list is empty,return an empty list
  | _, [] => []  -- If the second list is empty,return an empty list
  | x :: tx, y :: ty => (x, y) :: combine tx ty  -- Pair the heads and recursively combine tails

--Polymorphic Options. Option keyword is inbuilt.
inductive Option' (X : Type) : Type where
  | some : X → Option' X
  | none : Option' X

--Higher order functions
def doit3times {X : Type} (f : X → X) (n : X) : X :=
  f (f (f n))

-- Testing with minustwo function
def minustwo (n : Nat) : Nat :=
  if n < 2 then 0 else n - 2

-- Example test cases
theorem test_doit3times : doit3times minustwo 9 = 3 := by
  rfl

theorem test_doit3times' : doit3times not true = false := by
  rfl

--Defining filter in lean
def filter {α : Type} (test : α → Bool) : List α → List α
  | [] => []  -- Base case: Empty list
  | h :: t => if test h then h :: filter test t else filter test t

-- The functions checks if a given number is even or not
def even (n : Nat) : Bool :=
  n % 2 == 0

-- Test filter with the even predicate
theorem test_filter1 : filter even [1, 2, 3, 4] = [2, 4] := by
  rfl

--Defining count odd numbers function
-- Checks if a number is odd
def odd (n : Nat) : Bool :=
  n % 2 == 1

def countoddmembers' (l : List Nat) : Nat :=
  (filter odd l).length

--Testing
theorem test_countoddmembers'1 : countoddmembers' [1, 0, 3, 1, 4, 5] = 4 := by
  rfl

theorem test_countoddmembers'2 : countoddmembers' [0, 2, 4] = 0 := by
  rfl

theorem test_countoddmembers'3 : countoddmembers' [] = 0 := by
  rfl
--Anonymous functions. Similar to coq, we use fun keyword for anonymous functions.
theorem test_anon_fun' : doit3times (fun n => n * n) 2 = 256 := by
  rfl

--filter with anonymous function.
theorem test_filter2' :
    filter (fun l => l.length == 1)
           [[1, 2], [3], [4], [5, 6, 7], [], [8]]
    = [[3], [4], [8]] := by
  rfl
--Testing
#eval doit3times (fun n => n * n) 2  -- Output: 256

#eval filter (fun l => l.length == 1)
             [[1, 2], [3], [4], [5, 6, 7], [], [8]]
-- Output: [[3], [4], [8]]

--Map
def map {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | h :: t => f h :: map f t  --Apply f to head and recurse on tail

theorem test_map1 : map (fun x => x + 3) [2, 0, 2] = [5, 3, 5] := by
  rfl

theorem test_map2 : map odd [2, 1, 2, 5] = [false, true, false, true] := by
  rfl

theorem test_map3 : map (fun n => [even n, odd n]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]] := by
  rfl

--map for the option type
def option_map {α β : Type} (f : α → β) : Option α → Option β
  | Option.none => Option.none
  | Option.some x => Option.some (f x)

--Fold
def fold {α β : Type} (f : α → β → β) (b : β) : List α → β
  | [] => b
  | h :: t => f h (fold f b t)

-- Example: Fold with boolean and
theorem fold_example1 : fold Bool.and true [true, true, false, true] = false := by
  rfl

-- Example: Fold with mult. The shorthand (. * .) is the same as fun x y => x * y
theorem fold_example2 : fold (. * .) 1 [1, 2, 3, 4] = 24 := by
  rfl

-- Example: Fold with list concatenation
theorem fold_example3 : fold (· ++ ·) [] [[1], [], [2, 3], [4]] = [1, 2, 3, 4] := by
  rfl

#eval fold (. && .) true [true, true, false, true]
-- Output: false

#eval fold (· * ·) 1 [1, 2, 3, 4]
-- Output: 24

#eval fold (· ++ ·) [] [[1], [], [2, 3], [4]]
-- Output: [1, 2, 3, 4]

-- Functions that construct functions
--Defining costfun that takes a value x of some type X and returns
-- a function from nat to X that yields x whenever it
-- is called, ignoring its nat argument.
def constfun {X : Type} (x : X) : Nat → X :=
  fun _ => x

-- A function that returns true all the time
def ftrue : Nat → Bool := constfun true

-- Tests
theorem constfun_example1 : ftrue 0 = true := by
  rfl

theorem constfun_example2 : (constfun 5) 99 = 5 := by
  rfl

--plus3 function
def plus3 : Nat → Nat := Nat.add 3

-- Test cases
theorem test_plus3 : plus3 4 = 7 := by
  rfl

theorem test_plus3' : doit3times plus3 0 = 9 := by
  rfl

theorem test_plus3'' : doit3times (Nat.add 3) 0 = 9 := by
  rfl
--Tests
#eval ftrue 42  --Output:true
#eval (constfun 5) 99  --Output:5
#eval plus3 4  --Output:7
#eval doit3times plus3 0  --Output:9
