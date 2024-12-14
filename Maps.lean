--We look into the inbuilt string type in lean
-- Lean's String type
#check String  -- Output: Type

-- Equality check on strings
#check String.decEq  -- Output: ∀ (x y : String), Decidable (x = y)

--decEq checks whether two string are the same and the ourput shows that it is decidable.

-- Checking reflexivity of string type
theorem String.eqb_refl (x : String) : (x = x) := by
  rfl

--Tatal maps
def total_map (A : Type) := String → A

-- Map that always returns the default value
def t_empty {A : Type} (v : A) : total_map A :=
  fun _ => v

-- Updates the value for a given key
def t_update {A : Type} (m : total_map A) (x : String) (v : A) : total_map A :=
  fun x' => if x = x' then v else m x'

-- Example map using t_empty and t_update
def examplemap : total_map Bool :=
  t_update (t_update (t_empty false) "foo" true) "bar" true

-- Query the map
#eval examplemap "foo"  -- Output: true
#eval examplemap "bar"  -- Output: true
#eval examplemap "baz"  -- Output: false

--Partial Maps
def partial_map (A : Type) : Type := total_map (Option A)

-- Empty partial map
def empty {A : Type} : partial_map A :=
  t_empty none

-- Update operation for partial maps
def update {A : Type} (m : partial_map A) (x : String) (v : A) : partial_map A :=
  t_update m x (some v)

-- Notations for partial maps
notation x " ↦> " v ";" m => update m x v
notation x " ↦> " v => update empty x v

-- Example partial map
def examplepmap : partial_map Bool :=
  "Church" ↦> true; "Turing" ↦> false

--Tests
#eval examplepmap "Church"  -- Output: some true
#eval examplepmap "Turing"  -- Output: some false
#eval examplepmap "Gödel"   -- Output: none

-- Empty map always returns none
theorem apply_empty {A : Type} (x : String) : (empty : partial_map A) x = none := by
  simp [empty, t_empty]


-- If the updated key is queried, return the new value
theorem update_eq {A : Type} (m : partial_map A) (x : String) (v : A) :
    (x ↦> v; m) x = some v := by
  simp [update, t_update]

-- If a different key is queried, return the old map's value
theorem update_neq {A : Type} (m : partial_map A) (x1 x2 : String) (v : A) (h : x2 ≠ x1) :
    (x2 ↦> v; m) x1 = m x1 := by
  simp [update, t_update, h]


--Proofs of the exercises to use in the next section
theorem t_update_shadow {A : Type} (m : total_map A) (x : String) (v1 v2 : A) :
    (t_update (t_update m x v1) x v2) = (t_update m x v2) := by
  funext k
  simp [t_update]
  by_cases hk : k = x
  case pos =>
    -- Case: k = x
    rw [Eq.symm hk]
    simp
  case neg =>
    -- Case: k  x
  have h1 : ¬(x = k) := Ne.symm hk
  simp [if_neg h1]  -- Simplify the `if` with `h1`

theorem t_update_same {A : Type} (m : total_map A) (x : String) :
    (t_update m x (m x)) = m := by
  funext k
  simp [t_update]
  by_cases hk : k = x
  case pos =>
    -- Case: k = x
    rw [hk]
    simp
  case neg =>
    -- Case: k ≠ x
    have h1 : ¬(x = k) := Ne.symm hk
    simp [h1]

theorem t_update_permute {A : Type} (m : total_map A) (v1 v2 : A) (x1 x2 : String)
    (h : x2 ≠ x1) :
    (t_update (t_update m x1 v1) x2 v2) = (t_update (t_update m x2 v2) x1 v1) := by
  funext k
  simp [t_update]
  by_cases hk1 : k = x1
  case pos =>
    -- Case: k = x1
    rw [hk1]
    simp [h]
  case neg =>
    -- Case: k ≠ x1
    have h1 : ¬(x1 = k) := Ne.symm hk1
    simp [h1]


-- Updating the same key twice keeps the last value
theorem update_shadow {A : Type} (m : partial_map A) (x : String) (v1 v2 : A) :
    (x ↦> v2; x ↦> v1; m) = (x ↦> v2; m) := by
  unfold update  -- Expand the definition of `update`
  apply t_update_shadow

-- Updating a key with its current value does not change the map
theorem update_same {A : Type} (m : partial_map A) (x : String) (v : A) (h : m x = some v) :
    (x ↦> v; m) = m := by
  unfold update  -- Expand the definition of `update`
  rw [←h]        -- Rewrite using the hypothesis `h`
  apply t_update_same
--Update permute
theorem update_permute {A : Type} (m : partial_map A) (x1 x2 : String) (v1 v2 : A) (h : x2 ≠ x1) :
    (x1 ↦> v1; x2 ↦> v2; m) = (x2 ↦> v2; x1 ↦> v1; m) := by
  unfold update  -- Expand the definition of `update`
  apply t_update_permute
  have h1 : ¬(x1 = x2) := Ne.symm h
  apply h1


--map inclusion
def includedin {A : Type} (m m' : partial_map A) : Prop :=
  ∀ x v, m x = some v → m' x = some v

-- Map update preserves map inclusion
theorem includedin_update {A : Type} (m m' : partial_map A) (x : String) (vx : A) :
    includedin m m' → includedin (x ↦> vx; m) (x ↦> vx; m') := by
  intro h_incl
  unfold includedin
  intro y vy
  by_cases h_eq : y = x
  case pos =>
    -- Case: y = x
    subst h_eq  -- Replace y with x
    simp [update, t_update]
  case neg =>
    -- Case: y ≠ x
    simp [update, t_update]
    intro h_some  -- Simplify m at y
    have h1 : ¬(x = y) := Ne.symm h_eq
    have h_int : (if x = y then some vx else m' y) = m' y := by
      rw [if_neg h1]
    rw[h_int]
    apply h_incl
    rw [if_neg h1] at h_some
    apply h_some
