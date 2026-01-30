/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe11_DenotationalSemantics_Demo


/- # LoVe Homework 11: Denotational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe

/- The following command enables noncomputable decidability on every `Prop`.
The `0` argument ensures this is used only when necessary; otherwise, it would
make some computable definitions noncomputable for Lean. Depending on how you
solve question 2.2, this command might help you. -/

attribute [instance 0] Classical.propDecidable

/- Denotational semantics are well suited to functional programming. In this
homework, we will study some representations of functional programs in Lean and
their denotational semantics.

The `Nondet` type represents functional programs that can perform
nondeterministic computations: A program can choose between many different
computation paths / return values. Returning no results at all is represented
by `fail`, and nondeterministic choice between two options, identified by the
`Bool` values `true` and `false`, is represented by `choice`. -/

inductive Nondet (α : Type) : Type where
  | just   : α → Nondet α
  | fail   : Nondet α
  | choice : (Bool → Nondet α) → Nondet α

namespace Nondet


/- ## Question 1: The `Nondet` Monad

The `Nondet` inductive type forms a monad. The `pure` operator is `Nondet.just`.
`bind` is as follows: -/

def bind {α β : Type} : Nondet α → (α → Nondet β) → Nondet β
  | just a,   f => f a
  | fail,     f => fail
  | choice k, f => choice (fun b ↦ bind (k b) f)

instance : Pure Nondet :=
  { pure := just }

instance : Bind Nondet :=
  { bind := bind }

/- 1.1. Prove the three monad laws for `Nondet`.

Hints:

* To unfold the definition of `pure` and `>>=`, invoke
  `simp [Bind.bind, Pure.pure]`.

* To reduce `f = g` to `∀x, f x = g x`, use the theorem `funext`. -/

theorem pure_bind {α β : Type} (a : α) (f : α → Nondet β) :
    pure a >>= f = f a :=
 sorry

theorem bind_pure {α : Type} :
    ∀na : Nondet α, na >>= pure = na :=
  sorry

theorem bind_assoc {α β γ : Type} :
    ∀(na : Nondet α) (f : α → Nondet β) (g : β → Nondet γ),
      ((na >>= f) >>= g) = (na >>= (fun a ↦ f a >>= g)) :=
  sorry

/- The function `portmanteau` computes a portmanteau of two lists: A
portmanteau of `xs` and `ys` has `xs` as a prefix and `ys` as a suffix, and they
overlap. We use `startsWith xs ys` to test that `ys` has `xs` as a prefix. -/

def startsWith : List ℕ → List ℕ → Bool
  | x :: xs, []      => false
  | [],      ys      => true
  | x :: xs, y :: ys => x = y && startsWith xs ys

#eval startsWith [1, 2] [1, 2, 3]
#eval startsWith [1, 2, 3] [1, 2]

def portmanteau : List ℕ → List ℕ → List (List ℕ)
| [],      ys => []
| x :: xs, ys =>
  List.map (List.cons x) (portmanteau xs ys) ++
  (if startsWith (x :: xs) ys then [ys] else [])

/- Here are some examples of portmanteaux: -/

#eval portmanteau [0, 1, 2, 3] [2, 3, 4]
#eval portmanteau [0, 1] [2, 3, 4]
#eval portmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4]

/- 1.2. Translate the `portmanteau` program from the `List`
monad to the `Nondet` monad. -/

def nondetPortmanteau : List ℕ → List ℕ → Nondet (List ℕ) :=
  sorry


/- ## Question 2: Nondeterminism, Denotationally

2.1. Give a denotational semantics for `Nondet`, mapping it into a `List` of
all results. `pure` returns one result, `fail` returns zero, and `choice`
combines the results of either option. -/

def listSem {α : Type} : Nondet α → List α :=
  sorry

/- Check that the following lines give the same output as for `portmanteau` (if
you have answered question 1.2): -/

#reduce listSem (nondetPortmanteau [0, 1, 2, 3] [2, 3, 4])
#reduce listSem (nondetPortmanteau [0, 1] [2, 3, 4])
#reduce listSem (nondetPortmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4])

/- 2.2. Often, we are not interested in getting all outcomes, just the first
successful one. Give a semantics for `Nondet` that produces the first
successful result, if any. Your solution should *not* use `listSem`. -/

noncomputable def optionSem {α : Type} : Nondet α → Option α :=
  sorry

/- 2.3. Prove the theorem `List_Option_compat` below, showing
that the two semantics you defined are compatible.

`List.head?` returns the head of a list wrapped in an `Option.some`, or
`Option.none` for an empty list. It corresponds to the function we called
`headOpt` in lecture 5. -/

theorem List_Option_compat {α : Type} :
    ∀na : Nondet α, optionSem na = List.head? (listSem na) :=
  sorry

end Nondet


/- ## Question 3: Denotational Semantics of DOWHILE -/

namespace DOWHILE

/- Consider the following DOWHILE language: -/

inductive Stmt : Type where
  | skip     : Stmt
  | assign   : String → (State → ℕ) → Stmt
  | seq      : Stmt → Stmt → Stmt
  | unlessDo : Stmt → (State → Prop) → Stmt
  | whileDo  : (State → Prop) → Stmt → Stmt
  | doWhile  : Stmt → (State → Prop) → Stmt

infixr:90 "; " => Stmt.seq

/- The `skip`, `assign`, `seq`, and `while`–`do` constructs are as for the
WHILE language.

`unless S do B` executes `S` if `B` is false in the current state; otherwise, it
does nothing. This statement is inspired by Perl's `unless` conditional.

`do S while B` first executes `S`. Then, if `B` is true in the resulting state,
it re-enters the loop and executes `S` again, and continues executing `S` until
`B` becomes false. The semantics is almost the same as `while B S`, except that
`S` is always executed at least once, even if the condition is not true
initially. This statement is inspired by C's and Java's `do { … } while (…)`
statement.

3.1. Give a denotational semantics of DOWHILE.

Hint: Your definition should make it easy to prove the theorem `doWhile_whileDo`
in question 1.2. -/

def denote : Stmt → Set (State × State)
  | Stmt.skip         => Id
-- enter the missing cases here

notation (priority := high) "⟦" S "⟧" => denote S

/- 3.2. Prove the following correspondence between the two types of loops. -/

theorem doWhile_whileDo (S : Stmt) (B : State → Prop) :
    ⟦Stmt.doWhile S B⟧ = ⟦S⟧ ◯ ⟦Stmt.whileDo B S⟧ :=
  sorry

/- 3.3. Prove the following theorems.

Hint: For all of these, short proofs are possible. It may help, however, to
know what basic expressions such as `P ⇃ (fun x ↦ False)` and
`P ⇃ (fun x ↦ True)` mean. Make sure to simplify the expressions involving
`⇃` before trying to figure out what to do about `lfp`. -/

theorem lfp_const {α : Type} [CompleteLattice α] (a : α) :
    lfp (fun X ↦ a) = a :=
  sorry

theorem whileDo_False (S : Stmt) :
    ⟦Stmt.whileDo (fun _ ↦ False) S⟧ = Id :=
  sorry

theorem comp_Id {α : Type} (r : Set (α × α)) :
    r ◯ Id = r :=
  sorry

theorem DoWhile_False (S : Stmt) :
    ⟦Stmt.doWhile S (fun _ ↦ False)⟧ = ⟦S⟧ :=
  sorry

end DOWHILE


/- ## Question 4: Kleene's Theorem

We can compute the fixpoint by iteration by taking the union of all finite
iterations of `f`:

    `lfp f = ⋃i, (f ^^ i) ∅`

where

    `f ^^ i = f ∘ ⋯ ∘ f`

iterates the function `f` `i` times. However, the above characterization of
`lfp` only holds for continuous functions, a concept we will introduce below. -/

def iter {α : Type} (f : α → α) : ℕ → α → α
  | 0,     a => a
  | n + 1, a => f (iter f n a)

notation f "^^" n => iter f n

/- 4.1. Fill in the missing proofs below.

Hint: Bear in mind that `≤` works on lattices in general, including sets. On
sets, it can be unfolded to `⊆` using `simp [LE.le]`. Moreover, when you see
`h : A ⊆ B` in a goal, you can imagine that you have `?a ∈ A → ?a ∈ B` by
definition, or unfold the definition using
`simp [HasSubset.Subset, Set.Subset]`. -/

def Union {α : Type} (s : ℕ → Set α) : Set α :=
  {a | ∃n, a ∈ s n}

theorem Union_le {α : Type} {s : ℕ → Set α} (A : Set α) (h : ∀i, s i ≤ A) :
    Union s ≤ A :=
  by
    simp [LE.le]
    simp [HasSubset.Subset, Set.Subset]
    sorry

/- A continuous function `f` is a function that commutes with the union of any
monotone sequence `s`: -/

def Continuous {α : Type} (f : Set α → Set α) : Prop :=
  ∀s : ℕ → Set α, Monotone s → f (Union s) = Union (fun i ↦ f (s i))

/- We need to prove that each continuous function is monotone. To achieve this,
we will need the following sequence: -/

def biSeq {α : Type} (A B : Set α) : ℕ → Set α
  | 0     => A
  | n + 1 => B

/- For example, `biSeq A B` is the sequence A, B, B, B, …. -/

theorem Monotone_biSeq {α : Type} (A B : Set α) (h : A ≤ B) :
    Monotone (biSeq A B) :=
  by
    simp [Monotone]
    intro i j hle a ha
    cases i with
    | zero =>
      cases j with
      | zero =>
        simp [biSeq] at *
        assumption
      | succ j' =>
        simp [biSeq] at *
        apply h
        assumption
    | succ i' =>
      cases j with
      | zero    => simp [biSeq] at *
      | succ j' =>
        simp [biSeq] at *
        assumption

theorem Union_biSeq {α : Type} (A B : Set α) (ha : A ≤ B) :
    Union (biSeq A B) = B :=
  by
    apply le_antisymm
    . sorry
    . sorry

theorem Monotone_of_Continuous {α : Type} (f : Set α → Set α)
      (hf : Continuous f) :
    Monotone f :=
  by
    intro A B ha
    rw [← Union_biSeq A B ha]
    rw [hf _ (Monotone_biSeq A B ha)]
    sorry

/- 4.2. Provide the following proof, using a similar case distinction as for
`Monotone_biSeq` above. -/

theorem Monotone_iterate {α : Type} (f : Set α → Set α) (hf : Monotone f) :
    Monotone (fun i ↦ (f ^^ i) ∅) :=
  sorry

/- 4.3. Prove the main theorem. A proof sketch is given below.

You can use the theorem `le_antisymm` to break the proof into two proofs of
inclusion.

Case 1. `lfp f ≤ Union (fun i ↦ (f ^^ i) ∅)`: The key is to use the theorem
`lfp_le` together with continuity of `f`.

Case 2. `Union (fun i ↦ (f ^^ i) ∅) ≤ lfp f`: The theorem `Union_le` gives a
natural number `i` on which you can perform induction. You also need the theorem
`lfp_eq` to unfold one iteration of `lfp f`. -/

theorem lfp_Kleene {α : Type} (f : Set α → Set α) (hf : Continuous f) :
    lfp f = Union (fun i ↦ (f ^^ i) ∅) :=
  sorry

end LoVe
