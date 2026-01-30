/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 9: Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Arithmetic Expressions

Recall the type of arithmetic expressions from lecture 2 and its evaluation
function: -/

#check AExp
#check eval

/- Let us introduce the following abbreviation for an environment that maps
variable names to values: -/

def Envir : Type :=
  String → ℤ

namespace AExp

/- 1.1. Complete the following Lean definition of a big-step-style semantics
for arithmetic expressions. The predicate `BigStep` (`⟹`) relates an arithmetic
expression, an environment, and the value to which the expression evaluates in
the given environment: -/

inductive BigStep : AExp × Envir → ℤ → Prop where
  | num (i env) : BigStep (AExp.num i, env) i

infix:60 " ⟹ " => BigStep

/- 1.2. Prove the following theorem to validate your definition above.

Hint: It may help to first prove
`(AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 2 + 2`. -/

theorem BigStep_add_two_two (env : Envir) :
    (AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 4 :=
  sorry

/- 1.3. Prove that the big-step semantics is sound with respect to the `eval`
function: -/

theorem BigStep_sound (aenv : AExp × Envir) (i : ℤ) (hstep : aenv ⟹ i) :
    eval (Prod.snd aenv) (Prod.fst aenv) = i :=
  sorry

end AExp


/- ## Question 2: Semantics of the REPEAT Language

We introduce REPEAT, a programming language that resembles the WHILE language
but whose defining feature is a `repeat` loop.

The Lean definition of its abstract syntax tree follows: -/

namespace REPEAT

inductive Stmt : Type where
  | skip     : Stmt
  | assign   : String → (State → ℕ) → Stmt
  | seq      : Stmt → Stmt → Stmt
  | unlessDo : (State → Prop) → Stmt → Stmt
  | repeat   : ℕ → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- The `skip`, `assign`, and `S; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b do S` statement executes `S` unless `b` is true—i.e., it executes
`S` if `b` is false. Otherwise, `unless b do S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S`
has the same effect as `S; S; S; S; S` (as far as the big-step semantics is
concerned), and `repeat 0 S` has the same effect as `skip`.

2.1. Complete the following definition of a big-step semantics: -/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
-- enter the missing cases here

infix:110 " ⟹ " => BigStep

/- 2.2. Complete the following definition of a small-step semantics: -/

inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
-- enter the missing cases here

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

/- 2.3. We will now attempt to prove termination of the REPEAT language. More
precisely, we will show that there cannot be infinite chains of the form

    `(S₀, s₀) ⇒ (S₁, s₁) ⇒ (S₂, s₂) ⇒ ⋯`

Towards this goal, you are asked to define a __measure__ function: a function
`mess` that takes a statement `S` and that returns a natural number indicating
how "big" the statement is. The measure should be defined so that it strictly
decreases with each small-step transition. -/

def mess : Stmt → ℕ
  | Stmt.skip         => 0
-- enter the missing cases here

/- You can validate your answer as follows. Consider the following program
`S₀`: -/

def incr (x : String) : Stmt :=
  Stmt.assign x (fun s ↦ s x + 1)

def S₀ : Stmt :=
  Stmt.repeat 1 (incr "m"; incr "n")

/- Check that `mess` strictly decreases with each step of its small-step
evaluation: -/

def S₁ : Stmt :=
  (incr "m"; incr "n"); Stmt.repeat 0 (incr "m"; incr "n")

def S₂ : Stmt :=
  (Stmt.skip; incr "n"); Stmt.repeat 0 (incr "m"; incr "n")

def S₃ : Stmt :=
  incr "n"; Stmt.repeat 0 (incr "m"; incr "n")

def S₄ : Stmt :=
  Stmt.skip; Stmt.repeat 0 (incr "m"; incr "n")

def S₅ : Stmt :=
  Stmt.repeat 0 (incr "m"; incr "n")

def S₆ : Stmt :=
  Stmt.skip

#eval mess S₀   -- result: e.g., 6
#eval mess S₁   -- result: e.g., 5
#eval mess S₂   -- result: e.g., 4
#eval mess S₃   -- result: e.g., 3
#eval mess S₄   -- result: e.g., 2
#eval mess S₅   -- result: e.g., 1
#eval mess S₆   -- result: e.g., 0

/- 2.4. Prove that the measure decreases with each small-step transition. If
necessary, revise your answer to question 2.3. -/

theorem SmallStep_mess_decreases {Ss Tt : Stmt × State} (h : Ss ⇒ Tt) :
    mess (Prod.fst Ss) > mess (Prod.fst Tt) :=
  sorry

/- 2.5. Prove the following inversion rule for the big-step semantics of
`unless`. -/

theorem BigStep_ite_iff {B S s t} :
    (Stmt.unlessDo B S, s) ⟹ t ↔ (B s ∧ s = t) ∨ (¬ B s ∧ (S, s) ⟹ t) :=
  sorry

/- 2.6. Prove the following inversion rule for the big-step semantics of
`repeat`. -/

theorem BigStep_repeat_iff {n S s u} :
    (Stmt.repeat n S, s) ⟹ u ↔
    (n = 0 ∧ u = s)
    ∨ (∃m t, n = m + 1 ∧ (S, s) ⟹ t ∧ (Stmt.repeat m S, t) ⟹ u) :=
  sorry

end REPEAT


/- ## Question 3: Semantics of Regular Expressions

Regular expressions are a very popular tool for software development. Often,
when textual input needs to be analyzed it is matched against a regular
expression. In this question, we define the syntax of regular expressions and
what it means for a regular expression to match a string.

We define `Regex` to represent the following grammar:

    R  ::=  ∅       -- `nothing`: matches nothing
         |  ε       -- `empty`: matches the empty string
         |  a       -- `atom`: matches the atom `a`
         |  R ⬝ R    -- `concat`: matches the concatenation of two regexes
         |  R + R   -- `alt`: matches either of two regexes
         |  R*      -- `star`: matches arbitrary many repetitions of a Regex

Notice the rough correspondence with a WHILE language:

    `empty`  ~ `skip`
    `atom`   ~ assignment
    `concat` ~ sequential composition
    `alt`    ~ conditional statement
    `star`   ~ while loop -/

inductive Regex (α : Type) : Type where
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- The `Matches r s` predicate indicates that the regular expression `r` matches
the string `s` (where the string is a sequence of atoms). -/

inductive Matches {α : Type} : Regex α → List α → Prop where
  | empty :
    Matches Regex.empty []
  | atom (a : α) :
    Matches (Regex.atom a) [a]
  | concat (r₁ r₂ : Regex α) (s₁ s₂ : List α) (h₁ : Matches r₁ s₁)
      (h₂ : Matches r₂ s₂) :
    Matches (Regex.concat r₁ r₂) (s₁ ++ s₂)
  | alt_left (r₁ r₂ : Regex α) (s : List α) (h : Matches r₁ s) :
    Matches (Regex.alt r₁ r₂) s
  | alt_right (r₁ r₂ : Regex α) (s : List α) (h : Matches r₂ s) :
    Matches (Regex.alt r₁ r₂) s
  | star_base (r : Regex α) :
    Matches (Regex.star r) []
  | star_step (r : Regex α) (s s' : List α) (h₁ : Matches r s)
      (h₂ : Matches (Regex.star r) s') :
    Matches (Regex.star r) (s ++ s')

/- The introduction rules correspond to the following cases:

* match the empty string
* match one atom (e.g., character)
* match two concatenated regexes
* match the left option
* match the right option
* match the empty string (the base case of `R*`)
* match `R` followed again by `R*` (the induction step of `R*`)

3.1. Explain why there is no rule for `nothing`. -/

-- enter your answer here

/- 3.2. Prove the following inversion rules. -/

@[simp] theorem Matches_atom {α : Type} {s : List α} {a : α} :
    Matches (Regex.atom a) s ↔ s = [a] :=
  sorry

@[simp] theorem Matches_nothing {α : Type} {s : List α} :
    ¬ Matches Regex.nothing s :=
  sorry

@[simp] theorem Matches_empty {α : Type} {s : List α} :
    Matches Regex.empty s ↔ s = [] :=
  sorry

@[simp] theorem Matches_concat {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.concat r₁ r₂) s
    ↔ (∃s₁ s₂, Matches r₁ s₁ ∧ Matches r₂ s₂ ∧ s = s₁ ++ s₂) :=
  sorry

@[simp] theorem Matches_alt {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.alt r₁ r₂) s ↔ (Matches r₁ s ∨ Matches r₂ s) :=
  sorry

/- 3.3. Prove the following inversion rule. -/

theorem Matches_star {α : Type} {s : List α} {r : Regex α} :
    Matches (Regex.star r) s ↔
    s = []
    ∨ (∃s₁ s₂, Matches r s₁ ∧ Matches (Regex.star r) s₂ ∧ s = s₁ ++ s₂) :=
  sorry

end LoVe
