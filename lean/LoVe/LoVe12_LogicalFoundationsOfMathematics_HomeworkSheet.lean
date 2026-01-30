/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Homework 12: Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Even Numbers as a Subtype

Usually, the most convenient way to represent even natural numbers is to use the
larger type `ℕ`, which also includes the odd natural numbers. If we want to
quantify only over even numbers `n`, we can add an assumption `Even n` to our
theorem statement.

An alternative is to encode evenness in the type, using a subtype. We will
explore this approach.

1.1. Define the type `Eveℕ` of even natural numbers, using the `Even` predicate
introduced in the lecture 5 demo. -/

#print Even

def Eveℕ : Type :=
  sorry

/- 1.2. Prove the following theorem about the `Even` predicate. You will need
it to answer question 1.3.

Hint: The theorems `add_assoc` and `add_comm` might be useful. -/

theorem Even.add {m n : ℕ} (hm : Even m) (hn : Even n) :
    Even (m + n) :=
  sorry

/- 1.3. Define zero and addition of even numbers by filling in the `sorry`
placeholders. -/

def Eveℕ.zero : Eveℕ :=
  sorry

def Eveℕ.add (m n : Eveℕ) : Eveℕ :=
  sorry

/- 1.4. Prove that addition of even numbers is commutative and associative, and
has 0 as an identity element. -/

theorem Eveℕ.add_comm (m n : Eveℕ) :
    Eveℕ.add m n = Eveℕ.add n m :=
  sorry

theorem Eveℕ.add_assoc (l m n : Eveℕ) :
    Eveℕ.add (Eveℕ.add l m) n = Eveℕ.add l (Eveℕ.add m n) :=
  sorry

theorem Eveℕ.add_iden_left (n : Eveℕ) :
    Eveℕ.add Eveℕ.zero n = n :=
  sorry

theorem Eveℕ.add_iden_right (n : Eveℕ) :
    Eveℕ.add n Eveℕ.zero = n :=
  sorry


/- ## Question 2: Multisets as a Quotient Type

A multiset (or bag) is a collection of elements that allows for multiple
(but finitely many) occurrences of its elements. For example, the multiset
`{2, 7}` is equal to the multiset `{7, 2}` but different from `{2, 7, 7}`.

Finite multisets can be defined as a quotient over lists. We start with the
type `List α` of finite lists and consider only the number of occurrences of
elements in the lists, ignoring the order in which elements occur. Following
this scheme, `[2, 7, 7]`, `[7, 2, 7]`, and `[7, 7, 2]` would be three equally
valid representations of the multiset `{2, 7, 7}`.

The `List.count` function returns the number of occurrences of an element in a
list. Since it uses equality on elements of type `α`, it requires `α` to belong
to the `BEq` (Boolean equality) type class. For this reason, the definitions and
theorems below all take `[BEq α]` as type class argument.

2.1. Provide the missing proof below. -/

instance Multiset.Setoid (α : Type) [BEq α] : Setoid (List α) :=
  { r     := fun as bs ↦ ∀x, List.count x as = List.count x bs
    iseqv :=
      { refl  :=
          sorry
        symm  :=
          sorry
        trans :=
          sorry
      } }

/- 2.2. Define the type of multisets as the quotient over the relation
`Multiset.Setoid`. -/

def Multiset (α : Type) [BEq α] : Type :=
  sorry

/- 2.3. Now we have a type `Multiset α` but no operations on it. Basic
operations on multisets include the empty multiset (`∅`), the singleton
multiset (`{x} `for any element `x`), and the sum of two multisets (`A ⊎ B` for
any multisets `A` and `B`). The sum should be defined so that the
multiplicities of elements are added; thus, `{2} ⊎ {2, 2} = {2, 2, 2}`.

Fill in the `sorry` placeholders below to implement the basic multiset
operations. -/

def Multiset.mk {α : Type} [BEq α] : List α → Multiset α :=
  Quotient.mk (Multiset.Setoid α)

def Multiset.empty {α : Type} [BEq α] : Multiset α :=
  sorry

def Multiset.singleton {α : Type} [BEq α] (a : α) : Multiset α :=
  sorry

def Multiset.union {α : Type} [BEq α] : Multiset α → Multiset α → Multiset α :=
  Quotient.lift₂
  sorry
  sorry

/- 2.4. Prove that `Multiset.union` is commutative and associative
and has `Multiset.empty` as identity element. -/

theorem Multiset.union_comm {α : Type} [BEq α] (A B : Multiset α) :
    Multiset.union A B = Multiset.union B A :=
  sorry

theorem Multiset.union_assoc {α : Type} [BEq α] (A B C : Multiset α) :
    Multiset.union (Multiset.union A B) C =
    Multiset.union A (Multiset.union B C) :=
  sorry

theorem Multiset.union_iden_left {α : Type} [BEq α] (A : Multiset α) :
    Multiset.union Multiset.empty A = A :=
  sorry

theorem Multiset.union_iden_right {α : Type} [BEq α] (A : Multiset α) :
    Multiset.union A Multiset.empty = A :=
  sorry


/- ## Question 3: Hilbert Choice

3.1. Prove the following theorem.

Hints:

* A good way to start is to make a case distinction on whether `∃n, f n < x`
  is true or false.

* The theorem `le_of_not_gt` might be useful. -/

theorem exists_minimal_arg_helper (f : ℕ → ℕ) :
    ∀x m, f m = x → ∃n, ∀i, f n ≤ f i
  | x, m, eq =>
    by
      sorry

/- Now this interesting theorem falls off: -/

theorem exists_minimal_arg (f : ℕ → ℕ) :
    ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
  exists_minimal_arg_helper f _ 0 (by rfl)

/- 3.2. Use what you learned about Hilbert choice in the lecture to define the
following function, which returns the (or an) index of the minimal element in
`f`'s image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
  sorry

/- 3.3. Prove the following characteristic theorem about your definition. -/

theorem minimal_arg_spec (f : ℕ → ℕ) :
    ∀i : ℕ, f (minimal_arg f) ≤ f i :=
  sorry


/- ## Question 4: Nonempty Types

In the lecture, we saw the inductive predicate `Nonempty` that states that a
type has at least one element: -/

#print Nonempty

/- The purpose of this question is to think about what would happen if all
types had at least one element. To investigate this, we introduce this fact as
an axiom as follows. Introducing axioms should be generally avoided or done
with great care, since they can easily lead to contradictions, as we will
see. -/

axiom Sort_Nonempty (α : Sort _) :
    Nonempty α

/- This axiom gives us a theorem `Sort_Nonempty` admitted with no proof. It
resembles a theorem proved by `sorry`, but without the warning. -/

#check Sort_Nonempty

/- 4.1. Prove that this axiom leads to a contradiction, i.e., lets us derive
`False`. -/

theorem first_proof_of_False :
    False :=
  sorry

/- 4.2. Prove that even the following weaker axiom leads to a contradiction,
without using the axiom or the theorem from question 4.1.

Hint: Subtypes can help. -/

axiom Type_Nonempty (α : Type _) :
    Nonempty α

theorem second_proof_of_False :
    False :=
  sorry

end LoVe
