/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 2: Programs and Theorems

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Snoc

1.1. Define the function `snoc` that appends a single element to the end of a
list. Your function should be defined by recursion and not using `++`
(`List.append`). -/

def snoc {α : Type} : List α → α → List α :=
  sorry

/- 1.2. Convince yourself that your definition of `snoc` works by testing it on
a few examples. -/

#eval snoc [1] 2
-- invoke `#eval` or `#reduce` here


/- ## Question 2: Minus 2

2.1. Define the function `minusTwo` that subtracts two from its argument.

Hint: There should be three cases. -/

def minusTwo : ℕ → ℕ :=
  sorry

/- 2.2. Convince yourself that your definition of `minusTwo` works by testing
it on a few examples. -/

#eval minusTwo 0   -- expected: 0
-- invoke `#eval` or `#reduce` here


/- ## Question 3: Sum

3.1. Define a `sum` function that computes the sum of all the numbers in a
list. -/

def sum : List ℕ → ℕ :=
  sorry

#eval sum [1, 12, 3]   -- expected: 16

/- 3.2. State (without proving them) the following properties of `sum` as
theorems. Schematically:

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

Try to give meaningful names to your theorems. Use `sorry` as the proof. -/

-- enter your theorem statements here


/- ## Question 4: Lists

Consider the type `List` described in the lecture and the `append` and
`reverse` functions from the lecture's demo. The `List` type is part of Lean's
core libraries. You will find the definition of `append` and `reverse` in
`LoVe02_ProgramsAndTheorems_Demo.lean`. One way to find them quickly is to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `List`, `append`, or `reverse`;
3. click the identifier. -/

#print List
#check append
#check reverse

/- 4.1. Test that `reverse` behaves as expected on a few examples.

In the first example, the type annotation `: List ℕ` is needed to guide Lean's
type inference. -/

#eval reverse ([] : List ℕ)   -- expected: []
#eval reverse [1, 3, 5]       -- expected: [5, 3, 1]
-- invoke `#eval` here

/- 4.2. State (without proving them) the following properties of
`append` and `reverse`. Schematically:

    `append _ (append _ xs ys) zs = append _ xs (append _ ys zs)`
    `reverse (append _ xs ys) = append _ (reverse ys) (reverse xs)`

for all lists `xs`, `ys`, `zs`. Try to give meaningful names to your theorems.

Hint: Take a look at `reverse_reverse` from the demonstration file. -/

#check SorryTheorems.reverse_reverse

-- enter your theorem statements here

end LoVe
