/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: A Type of Terms

Recall the type of terms from question 3 of exercise 5: -/

inductive Term : Type where
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 1.1. Define an inductive predicate `IsLam` that returns `True` if its
argument is of the form `Term.lam …` and that returns `False` otherwise. -/

-- enter your definition here

/- 1.2. Validate your answer to question 1.1 by proving the following
theorems: -/

theorem IsLam_lam (s : String) (t : Term) :
    IsLam (Term.lam s t) :=
  sorry

theorem not_IsLamVar (s : String) :
    ¬ IsLam (Term.var s) :=
  sorry

theorem not_IsLam_app (t u : Term) :
    ¬ IsLam (Term.app t u) :=
  sorry

/- 1.3. Define an inductive predicate `IsApp` that returns `True` if its
argument is of the form `Term.app …` and that returns `False` otherwise. -/

-- enter your definition here

/- 1.4. Define an inductive predicate `IsLamFree` that is true if and only if
its argument is a term that contains no λ-expressions. -/

-- enter your definition here


/- ## Question 2: Transitive Closure

In mathematics, the transitive closure `R⁺` of a binary relation `R` over a
set `A` can be defined as the smallest solution satisfying the following rules:

    (base) for all `a, b ∈ A`, if `a R b`, then `a R⁺ b`;
    (step) for all `a, b, c ∈ A`, if `a R b` and `b R⁺ c`, then `a R⁺ c`.

In Lean, we can define this notion as follows, by identifying the set `A` with
the type `α`: -/

inductive TCV1 {α : Type} (R : α → α → Prop) : α → α → Prop where
  | base (a b : α)   : R a b → TCV1 R a b
  | step (a b c : α) : R a b → TCV1 R b c → TCV1 R a c

/- 2.1. Rule `(step)` makes it convenient to extend transitive chains by adding
links to the left. Another way to define the transitive closure `R⁺` would use
replace `(step)` with the following right-leaning rule:

    (pets) for all `a, b, c ∈ A`, if `a R⁺ b` and `b R c`, then `a R⁺ c`.

Define a predicate `TCV2` that embodies this alternative definition. -/

-- enter your definition here

/- 2.2. Yet another definition of the transitive closure `R⁺` would use the
following symmetric rule instead of `(step)` or `(pets)`:

    (trans) for all `a, b, c ∈ A`, if `a R⁺ b` and `b R⁺ c`, then `a R⁺ c`.

Define a predicate `TCV3` that embodies this alternative definition. -/

-- enter your definition here

/- 2.3. Prove that `(step)` also holds as a theorem about `TCV3`. -/

theorem TCV3_step {α : Type} (R : α → α → Prop) (a b c : α) (rab : R a b)
      (tbc : TCV3 R b c) :
    TCV3 R a c :=
  sorry

/- 2.4. Prove the following theorem by rule induction: -/

theorem TCV1_pets {α : Type} (R : α → α → Prop) (c : α) :
    ∀a b, TCV1 R a b → R b c → TCV1 R a c :=
  sorry


/- ## Question 3: Even and Odd

Consider the following inductive definition of even numbers: -/

inductive Even : ℕ → Prop where
  | zero            : Even 0
  | add_two (k : ℕ) : Even k → Even (k + 2)

/- 3.1. Define a similar predicate for odd numbers by completing the Lean
definition below. The definition should distinguish two cases, like `Even`, and
should not rely on `Even`. -/

inductive Odd : ℕ → Prop where
-- supply the missing cases here

/- 3.2. Give proof terms for the following propositions, based on your answer
to question 2.1. -/

theorem Odd_3 :
    Odd 3 :=
  sorry

theorem Odd_5 :
    Odd 5 :=
  sorry

/- 3.3. Prove the following theorem by rule induction: -/

theorem Even_Odd {n : ℕ} (heven : Even n) :
    Odd (n + 1) :=
  sorry

/- 3.4. Prove the same theorem again, this time as a "paper" proof. This is a
good exercise to develop a deeper understanding of how rule induction works.
Follow the guidelines given in question 1.4 of exercise 5. -/

-- enter your paper proof here

/- 3.5. Prove the following theorem using rule induction.

Hint: Recall that `¬ a` is defined as `a → False`. -/

theorem Even_Not_Odd {n : ℕ} (heven : Even n) :
    ¬ Odd n :=
  sorry

end LoVe
