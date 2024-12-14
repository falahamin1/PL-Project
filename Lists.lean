--Inductive type definition in lean
inductive NatProd : Type where
  | pair : Nat → Nat → NatProd

#check NatProd.pair 3 5

--function to extract first and second parts from a pair
def fst (p : NatProd) : Nat :=
  match p with
  | NatProd.pair x _ => x

def snd (p : NatProd) : Nat :=
  match p with
  | NatProd.pair _ y => y

notation "(" x ", " y ")" => NatProd.pair x y

#eval fst (3, 5)


--fst and snd with the new notation and swap function to swap a pair
def fst' (p : NatProd) : Nat :=
  match p with
  | (x, y) => x

def snd' (p : NatProd) : Nat :=
  match p with
  | (x, y) => y

def swap_pair (p : NatProd) : NatProd :=
  match p with
  | (x, y) => (y, x)
--We do not use the notation as this notation has been used for Nat x Nat
theorem surjective_pairing' : ∀ (n m : Nat), NatProd.pair n m = NatProd.pair (fst (NatProd.pair n m)) (snd (NatProd.pair n m)) := by
  intros n m
  rfl

theorem surjective_pairing : ∀ (p : NatProd), p = NatProd.pair (fst p) (snd p) := by
intro p
cases p with --we use cases instead of destruct
| pair x y => rfl

inductive NatList : Type where
  | nil : NatList
  | cons : Nat → NatList → NatList

-- Defining mylist
def mylist : NatList :=
  NatList.cons 1 (NatList.cons 2 (NatList.cons 3 NatList.nil))
--We are using List Nat as notations in Lean is hard
def repeatList (n count : Nat) : List Nat :=
  match count with
  | 0 => []
  | Nat.succ count' => n :: repeatList n count'

--Length of the list
def length (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | _ :: t => 1 + length t

-- Appending
def app (l1 l2 : List Nat) : List Nat :=
  match l1 with
  | [] => l2
  | h :: t => h :: app t l2

theorem test_app1 : app [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := by
  rfl

theorem test_app2 : app [] [4, 5] = [4, 5] := by
  rfl

theorem test_app3 : app [1, 2, 3] [] = [1, 2, 3] := by
  rfl


-- gets head of the list
def hd (default : Nat) (l : List Nat) : Nat :=
  match l with
  | [] => default
  | h :: _ => h

-- get tail of the list
def tl (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | _ :: t => t

theorem test_hd1 : hd 0 [1, 2, 3] = 1 := by
  rfl

theorem test_hd2 : hd 0 [] = 0 := by
  rfl

theorem test_tl : tl [1, 2, 3] = [2, 3] := by
  rfl

-- Reasoning about lists
--Appending an empty list to any list results in the original list
theorem nil_app : ∀ l : List Nat, app [] l = l := by
  intro l
  rfl

theorem tl_length_pred : ∀ l : List Nat, Nat.pred (length l) = length (tl l) := by
  intro l
  cases l with
  | nil =>
    simp [length]
  | cons n l' =>
    simp [length]
    simp [tl]
    rw [Nat.add_comm] -- rewriting 1 + length l' to length l' + 1
    rw [Nat.add_succ]  -- Rewrite length l' + 1 to Nat.succ (length l')
    rw [Nat.pred_succ] -- Simplify Nat.pred (Nat.succ (length l')) to length l

-- Append is associative
theorem app_assoc : ∀ l1 l2 l3 : List Nat, app (app l1 l2) l3 = app l1 (app l2 l3) := by
  intro l1 l2 l3
  induction l1 with
  | nil =>

    simp [app]  -- Simplify appending an empty list
  | cons n l1' ih =>
    simp [app]  -- Simplify appending a non empty list
    rw [ih]     --inductive hypothesis

-- Reversing a list
def rev (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => app (rev t) [h]

#eval rev [1, 2, 3]  -- Output: [3, 2, 1]

-- Theorem: Length of the appended list
theorem app_length : ∀ l1 l2 : List Nat, length (app l1 l2) = length l1 + length l2 := by
  intro l1 l2
  induction l1 with
  | nil =>
    simp [app, length]
  | cons h t ih =>
    simp [app, length]  -- Simplify app and length
    rw [ih]             -- inductive hypothesis
    rw [Nat.add_assoc]  -- Associativity of addition

theorem rev_length : ∀ l : List Nat, length (rev l) = length l := by
  intro l
  induction l with
  | nil =>
    simp [rev, length]
  | cons h t ih =>
    simp [rev, app, length]
    rw [app_length]      -- Apply app_length lemma
    rw [ih]              -- Inductive hypothesis
    rw [Nat.add_comm]    -- Commutativity of addition
    rfl

  -- Id type for nat (We use Id' as Id is an inbuilt function)
inductive Id' : Type where
  | mk : Nat → Id'

-- Equality function for Id'
def eqb_id (x1 x2 : Id') : Bool :=
  match x1, x2 with
  | Id'.mk n1, Id'.mk n2 => n1 == n2  -- == gives equality on nat

--Partial map definition. Construct empty of type partial map or
-- costructor record that takes an Id and value and an existing partial map
inductive PartialMap : Type where
  | empty : PartialMap
  | record : Id' → Nat → PartialMap → PartialMap

-- Update function
def update (d : PartialMap) (x : Id') (value : Nat) : PartialMap :=
  PartialMap.record x value d

--find function: searches through the partial map for a given id and value
def find (x : Id') (d : PartialMap) : Option Nat :=
  match d with
  | PartialMap.empty => none
  | PartialMap.record y v d' =>
    if eqb_id x y then some v else find x d'

--example
def exampleMap : PartialMap := update (update (update PartialMap.empty (Id'.mk 1) 46) (Id'.mk 2) 122) (Id'.mk 3) 132

#eval find (Id'.mk 1) exampleMap  -- Output: some 46
#eval find (Id'.mk 3) exampleMap  -- Output: some 132
