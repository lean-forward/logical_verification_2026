/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo
import LoVe.LoVe14_RationalAndRealNumbers_Demo


/- # LoVe Exercise 14: Rational and Real Numbers

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Rationals

1.1. Prove the following theorem.

Hints:

* Start with case distinctions on `a` and `b`.

* When the goal starts getting complicated, use `simp at *` to clean it up. -/

theorem Fraction.ext (a b : Fraction) (hnum : Fraction.num a = Fraction.num b)
      (hdenom : Fraction.denom a = Fraction.denom b) :
    a = b :=
  by
    cases a with
    | mk na da =>
      cases b with
      | mk nb db =>
        simp at *
        exact And.intro hnum hdenom

/- 1.2. Extending the `Fraction.Mul` instance from the lecture, declare
`Fraction` as an instance of `Semigroup`.

Hint: Use the theorem `Fraction.ext` above, and possibly `Fraction.mul_num` and
`Fraction.mul_denom`. -/

#check Fraction.ext
#check Fraction.mul_num
#check Fraction.mul_denom

instance Fraction.Semigroup : Semigroup Fraction :=
  { Fraction.Mul with
    mul_assoc :=
      by
        intro a b c
        apply Fraction.ext <;>
          simp [Fraction.mul_num, Fraction.mul_denom] <;>
          ac_rfl
  }

/- 1.3. Extending the `Rat.Mul` instance from the lecture, declare `Rat` as an
instance of `Semigroup`. -/

instance Rat.Semigroup : Semigroup Rat :=
  { Rat.Mul with
    mul_assoc :=
      by
        intros x y z
        induction x using Quotient.inductionOn with
        | h a =>
          induction y using Quotient.inductionOn with
          | h b =>
            induction z using Quotient.inductionOn with
            | h c =>
              apply Quotient.sound
              simp [mul_assoc]
  }

end LoVe
