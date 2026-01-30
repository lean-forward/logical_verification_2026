/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_ExerciseSheet
import LoVe.LoVe10_HoareLogic_Demo


/- # LoVe Homework 10: Hoare Logic

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Factorial

The following WHILE program is intended to compute the factorial of `n₀`,
leaving the result in `r`. -/

def FACT : Stmt :=
  Stmt.assign "i" (fun s ↦ 0);
  Stmt.assign "r" (fun s ↦ 1);
  Stmt.whileDo (fun s ↦ s "i" ≠ s "n")
    (Stmt.assign "i" (fun s ↦ s "i" + 1);
     Stmt.assign "r" (fun s ↦ s "r" * s "i"))

/- Recall the definition of the `fact` function: -/

#print fact

/- Let us register its recursive equations as simplification rules to
strengthen the simplifier and `aesop`, using some new Lean syntax: -/

attribute [simp] fact

/- 1.1. Prove the correctness of `FACT` using `vcg`.

Hint: Remember to strengthen the loop invariant with `s "n" = n₀` to
capture the fact that the variable `n` does not change. -/

theorem FACT_correct (n₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ *} (FACT) {* fun s ↦ s "r" = fact n₀ *} :=
  sorry


/- ## Question 2: Program Verification

The following WHILE program is intended to compute 2 to the power of `N`,
leaving the result in `r`. -/

def POWER_OF_TWO (N : ℕ) : Stmt :=
  Stmt.assign "r" (fun s ↦ 1);
  Stmt.assign "n" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ N)
    (Stmt.assign "r" (fun s ↦ s "r" * 2);
     Stmt.assign "n" (fun s ↦ s "n" + 1))

/- 2.1. Define a recursive function that computes 2 to the power of `n`. -/

def twoToTheNth : ℕ → ℕ :=
  sorry

/- Remember to test your function. Otherwise, you will have big difficulties
answering question 2.2 below. -/

#eval twoToTheNth 0   -- expected: 1
#eval twoToTheNth 1   -- expected: 2
#eval twoToTheNth 2   -- expected: 4
#eval twoToTheNth 3   -- expected: 8
#eval twoToTheNth 8   -- expected: 256

/- Let us register `twoToTheNth`'s recursive equations as simplification rules
to strengthen the simplifier and `aesop`, using some new Lean syntax: -/

attribute [simp] twoToTheNth

/- 2.2. Prove the correctness of `POWER_OF_TWO` using `vcg`. -/

theorem POWER_OF_TWO_correct (N : ℕ) :
    {* fun s ↦ True *}
    (POWER_OF_TWO N)
    {* fun s ↦ s "r" = twoToTheNth N *} :=
  sorry


/- ## Question 3: Hoare Logic for the Guarded Command Language

Recall the definition of GCL from exercise 9: -/

namespace GCL

#check Stmt
#check BigStep

/- The definition of Hoare triples for partial correctness is unsurprising: -/

def PartialHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s t, P s → (S, s) ⟹ t → Q t

notation (priority := high) "{* " P " *} " "(" S ")" " {* " Q " *}" =>
  PartialHoare P S Q

namespace PartialHoare

/- 3.1. Prove the following Hoare rules: -/

theorem consequence {P P' Q Q' S} (h : {* P *} (S) {* Q *})
      (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
    {* P' *} (S) {* Q' *} :=
  sorry

theorem assign_intro {P x a} :
    {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  sorry

theorem assert_intro {P Q : State → Prop} :
    {* fun s ↦ Q s → P s *} (Stmt.assert Q) {* P *} :=
  sorry

theorem seq_intro {P Q R S T}
      (hS : {* P *} (S) {* Q *}) (hT : {* Q *} (T) {* R *}) :
    {* P *} (Stmt.seq S T) {* R *} :=
  sorry

theorem choice_intro {P Q Ss}
      (h : ∀i (hi : i < List.length Ss), {* P *} (Ss[i]'hi) {* Q *}) :
    {* P *} (Stmt.choice Ss) {* Q *} :=
  sorry

/- 3.2. Prove the Hoare rule for `loop`. Notice the similarity with the rule
for `while` in the WHILE language. -/

theorem loop_intro {P S} (h : {* P *} (S) {* P *}) :
    {* P *} (Stmt.loop S) {* P *} :=
  sorry

end PartialHoare

end GCL


/- ## Question 4: Hoare Logic for LOOP

We introduce the LOOP language: -/

namespace LOOP

inductive Stmt : Type where
  | assign : String → (State → ℕ) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | ifThen : (State → Prop) → Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- The language is similar to WHILE. There are three differences:

* There is no `skip` statement.

* The `ifThen` statement is an `if`–`then` construct with no `else` branch.

* The `loop` construct corresponds to a randomized `while` loop. It executes the
  body an unspecified (possibly infinite) number of times.

The big-step semantics for LOOP is defined below. -/

inductive BigStep : Stmt × State → State → Prop where
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hs : BigStep (S, s) t) (ht : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S s t) (hcond : B s) (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThen B S, s) t
  | if_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.ifThen B S, s) s
  | loop_continue (S s t u) (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.loop S, t) u) :
    BigStep (Stmt.loop S, s) u
  | loop_exit (S s) :
    BigStep (Stmt.loop S, s) s

infix:110 " ⟹ " => BigStep

/- The definition of Hoare triples for partial correctness is unsurprising: -/

def PartialHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s t, P s → (S, s) ⟹ t → Q t

notation (priority := high + 1) "{* " P " *} " "(" S ")" " {* " Q " *}" =>
  PartialHoare P S Q

namespace PartialHoare

/- 4.1. Prove the consequence rule. -/

theorem consequence {P P' Q Q' S} (h : {* P *} (S) {* Q *})
      (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
    {* P' *} (S) {* Q' *} :=
  sorry

/- 4.2. Prove the Hoare rule for `assign`. -/

theorem assign_intro {P x a} :
    {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  sorry

/- 4.3. Prove the Hoare rule for `seq`. -/

theorem seq_intro {P Q R S T} (hS : {* P *} (S) {* Q *})
      (hT : {* Q *} (T) {* R *}) :
    {* P *} (Stmt.seq S T) {* R *} :=
  sorry

/- 4.4. Prove the Hoare rule for `if`–`then`. -/

theorem if_intro {b P Q S}
      (htrue : {* fun s ↦ P s ∧ b s *} (S) {* Q *})
      (hfalse : ∀s, P s ∧ ¬ b s → Q s) :
    {* P *} (Stmt.ifThen b S) {* Q *} :=
  sorry

/- 4.5. Prove the Hoare rule for `loop`. Notice the similarity with the rule for
`while` in the WHILE language. -/

theorem loop_intro {P S} (h : {* P *} (S) {* P *}) :
    {* P *} (Stmt.loop S) {* P *} :=
  sorry

end PartialHoare

end LOOP

end LoVe
