-- Define a predicate `sorted` that takes a list of natural numbers and returns a proposition
-- that is true if the list is sorted in non-decreasing order
def sorted : list ℕ → Prop
| [] := true -- An empty list is always sorted
| [x] := true -- A list with a single element is always sorted
| (x :: y :: rest) := x ≤ y ∧ sorted (y :: rest) -- A list with two or more elements is sorted if the first two elements are in non-decreasing order and the remaining elements are also sorted

-- The following code defines and verifies the correctness of an insertion sort algorithm
-- that uses the `sorted` predicate to ensure that the output is always sorted

-- Define a function `insert` that takes a natural number `x` and a sorted list of natural numbers
-- `ys` and returns a new sorted list with `x` inserted in the correct position
def insert (x : ℕ) : list ℕ → list ℕ
| [] := [x] -- If `ys` is empty, `x` is the only element and is inserted at the front of the list
| (y :: ys) := if x ≤ y then x :: y :: ys else y :: insert ys -- If `ys` is non-empty, compare `x` with the first element `y` and recursively insert `x` into the remaining list `ys`

-- Define a function `insertion_sort` that takes a list of natural numbers and returns a sorted list
-- using the `insert` function to repeatedly insert each element into the correct position
def insertion_sort : list ℕ → list ℕ
| [] := [] -- An empty list is already sorted
| (x :: xs) := insert x (insertion_sort xs) -- For a non-empty list, insert the first element `x` into the sorted list `insertion_sort xs`

-- Define a theorem `insertion_sort_correct` that states that `insertion_sort` always returns a sorted list
theorem insertion_sort_correct (xs : list ℕ) : sorted (insertion_sort xs) :=
list.rec_on xs -- Perform structural induction on `xs`
  (show sorted (insertion_sort []), by simp [insertion_sort]) -- The base case is an empty list, which is already sorted
  (assume x xs ih,
    have h₁ : sorted (insertion_sort xs), from ih, -- Assume that `insertion_sort xs` is sorted
    have h₂ : sorted (insert x (insertion_sort xs)), from
      match insertion_sort xs with
      | [] := by simp [insertion_sort, sorted] -- If `xs` is empty, `insertion_sort xs` is empty and `x` is the only element, which is trivially sorted
      | (y :: ys) := by simp [insertion_sort, sorted] at h₁ ⊢; -- If `xs` is non-empty, use the induction hypothesis to show that `insertion_sort xs` is sorted
        exact ⟨le_total x y, h₁⟩ -- Then use the `sorted` predicate to show that `x` is inserted into the correct position and the resulting list is sorted
      end,
    show sorted (insertion_sort (x :: xs)), by simp [insertion_sort, sorted] at h₂ ⊢; exact h₂) -- Finally, use the `sorted` predicate to show that `insertion_sort (x :: xs)` is sorted by applying the `insert` function to the first element `x` and the sorted list `
