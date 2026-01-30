/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe08_Metaprogramming_Demo


/- # LoVe Homework 8: Metaprogramming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## Question 1: A `safe` Tactic

You will develop a tactic that applies all safe introduction and elimination
rules for the connectives and quantifiers exhaustively. A rule is said to be
__safe__ if, given a provable goal, it always gives rise to provable subgoals.
In addition, we will require that safe rules do not introduce metavariables
(since these can easily be instantiated accidentally with the wrong terms).

You will proceed in three steps.

1.1. Develop a `safe_intros` tactic that repeatedly applies the introduction
rules for `True`, `∧`, and `↔` and that invokes `intro _` for `→`/`∀`. The
tactic generalizes `intro_and` from the exercise. -/

macro "safe_intros" : tactic =>
  sorry

theorem abcd (a b c d : Prop) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe_intros
    /- The proof state should be roughly as follows:

        case left
        a b c d : Prop
        a_1 : a
        a_2 : b
        ⊢ False

        case right.mp
        a b c d : Prop
        a_1 : a
        a_2 : c
        ⊢ d

        case right.mpr
        a b c d : Prop
        a_1 : a
        a_2 : d
        ⊢ c -/
    repeat' sorry

/- 1.2. Develop a `safe_cases` tactic that performs case distinctions on
`False`, `∧` (`And`), and `∃` (`Exists`). The tactic generalizes `cases_and`
from the exercise.

Hints:

* The last argument of `Expr.isAppOfArity` is the number of arguments expected
  by the logical symbol. For example, the arity of `∧` is 2.

* The "or" connective on `Bool` is called `||`.

Hint: When iterating over the declarations in the local context, make sure to
skip any declaration that is an implementation detail. -/

#check @False
#check @And
#check @Exists

partial def safeCases : TacticM Unit :=
  sorry

elab "safe_cases" : tactic =>
  safeCases

theorem abcdef (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    False :=
  by
    safe_cases
  /- The proof state should be roughly as follows:

      case intro.intro.intro
      a b c d e f : Prop
      P : ℕ → Prop
      hneg : ¬a
      hor : c ∨ d
      himp : b → e
      hiff : e ↔ f
      left : a
      w : ℕ
      h : P w
      left_1 : b
      right : c
      ⊢ False -/
    sorry

/- 1.3. Implement a `safe` tactic that first invokes `safe_intros` on all
goals, then `safe_cases` on all emerging subgoals, before it tries `assumption`
on all emerging subsubgoals. -/

macro "safe" : tactic =>
  sorry

theorem abcdef_abcd (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe
    /- The proof state should be roughly as follows:

        case left.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : b
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ False

        case right.mp.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : c
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ d -/
    repeat' sorry


/- ## Question 2: A `mindless` Tactic

You will develop a tactic that automates some of the mindless `intro`/`apply`
proofs that formed the core of lecture 3. Unlike `safe`, it will also apply
unsafe rules.

We proceed in three steps.

2.1. Develop a `mindless_safe` tactic that repeatedly tries to invoke
`hypothesis`, invoke `intro _` for `→`/`∀`, and apply the introduction rules
for `∧` and `↔`. The tactic generalizes `intro_and` from the exercise. -/

macro "mindless_safe" : tactic =>
  sorry

theorem abcd2 (a b c d : Prop) (hc : c) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    mindless_safe
    /- The proof state should be roughly as follows:

        case left
        a b c d : Prop
        hc : c
        a_1 : a
        a_2 : b
        ⊢ False

        case right.mp
        abcd : Prop
        hc : c
        a_1 : a
        a_2 : c
        ⊢ d -/
    repeat sorry

/- 2.2. Develop a `mindless_unsafe` tactic that works on the current goal. For
each hypothesis in turn, try the following in a `try`–`catch` block:

1. Apply the hypothesis using `applyTerm`, provided below.

2. Invoke some `followUp` tactic, which is passed as argument.

3. Invoke `done`, which succeeds only if there are no goals left.

4. Return.

If an exception is caught, continue with the next hypothesis.

Once a hypothesis has been found for which steps 1 to 3 succeed,
`mindless_unsafe` succeeds.

Hints:

  * See `prove_direct` in the demo file for an example of a `try`–`catch` block.

  * When iterating over the declarations in the local context, make sure to
    skip any declaration that is an implementation detail. -/

def applyTerm (t : Expr) : TacticM Unit :=
  liftMetaTactic (fun goal ↦ MVarId.apply goal t)

def mindlessUnsafe (followUp : TacticM Unit) : TacticM Unit :=
  sorry

/- A few tests follow, using `followUp := hypothesis`. -/

elab "mindless_unsafe_with_hypothesis" : tactic =>
  mindlessUnsafe hypothesis

theorem modus_ponens (a b : Prop) (ha : a) (hab : a → b) :
    b :=
  by mindless_unsafe_with_hypothesis

theorem junky_modus_ponens (a b c d : Prop) (ha : a) (hcb : c → b) (hab : a → b)
    (hdb : d → b) :
    b :=
  by mindless_unsafe_with_hypothesis

/- Finally, everything comes together with the `mindless` tactic below. The
tactic performs a depth-bounded search for a proof, applying `mindless_safe`
and `mindless_unsafe` on all goals in alternation. The bound is necessary to
eventually backtrack. -/

def mindless : ℕ → TacticM Unit
  | 0         =>
    do
      let mindlessSafe ← `(tactic| mindless_safe)
      evalTactic mindlessSafe
  | depth + 1 =>
    do
      let mindlessSafe ← `(tactic| mindless_safe)
      evalTactic mindlessSafe
      let subgoals ← getUnsolvedGoals
      for subgoal in subgoals do
        let assigned ← MVarId.isAssigned subgoal
        if ! assigned then
          setGoals [subgoal]
          try
            mindlessUnsafe (mindless depth)
          catch _ =>
            continue
      pure ()

elab "mindless5" : tactic =>
  mindless 5

/- Some tests are provided below. All should succeed. -/

theorem I (a : Prop) :
    a → a :=
  by mindless5

theorem K (a b : Prop) :
    a → b → b :=
  by mindless5

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  by mindless5

theorem proj_1st (a : Prop) :
    a → a → a :=
  by mindless5

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  by mindless5

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  by mindless5

theorem B (a b c : Prop) :
    (a → b) → (c → a) → c → b :=
  by mindless5

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c :=
  by mindless5

theorem more_nonsense (a b c : Prop) :
    (c → (a → b) → a) → c → b → a :=
  by mindless5

theorem even_more_nonsense (a b c : Prop) :
    (a → a → b) → (b → c) → a → b → c :=
  by mindless5

theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b :=
  by mindless5

theorem weak_peirce_on_steroids (a b : Prop) :
    ((((((((a → b) → a) → a) → b) → b) → a) → a) → b) → b :=
  by mindless5

theorem one_for_the_road (a c : Prop) (ha : a) (hccc : c → c → c)
      (hac : a → c) :
    c :=
  by mindless5


/- ## Question 3: An `aesop`-Like Tactic

3.1. Develop a simple `aesop`-like tactic.

This tactic should apply all safe introduction and elimination rules. In
addition, it should try potentially unsafe rules (such as `Or.inl` and
`False.elim`) but backtrack at some point (or try several possibilities in
parallel). Iterative deepening may be a valid approach, or best-first search,
or breadth-first search. The tactic should also try to apply assumptions whose
conclusion matches the goal, but backtrack if necessary.

Hint: The `MonadBacktrack` monad class might be useful.

3.2. Test your tactic on some benchmarks.

You can try your tactic on logic puzzles of the kinds we proved in exercise and
homework 3. -/

end LoVe
