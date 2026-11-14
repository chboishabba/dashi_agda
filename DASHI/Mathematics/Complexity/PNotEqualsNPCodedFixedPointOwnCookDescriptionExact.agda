module DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedPointOwnCookDescriptionExact where

------------------------------------------------------------------------
-- BEHAVIOURAL FIXED-POINT QUOTATION -> SAME MACHINE GUARDED-COOK DESCRIPTION
--
-- The generic dependent description cannot be rebuilt from an arbitrary quoted
-- program without transporting its InputWord/rule witnesses across machine
-- equality.  For the actual Kleene fixed point the quoted head machine reduces
-- definitionally to the original coded machine, so the same-object description
-- is recovered with no cast and no universal decoder.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedQuoteSensitiveKleeneExact as Kleene

fixedPointRecoveredDescription :
  (description : Description.GuardedCookFormulaDescription) →
  Description.GuardedCookFormulaDescription
fixedPointRecoveredDescription description = record
  { Description.code =
      Kleene.headMachine
        (Kleene.codedQuoteSensitiveFixedPoint
          (Description.code description))
  ; Description.nonemptyRules = Description.nonemptyRules description
  ; Description.input = Description.input description
  ; Description.steps = Description.steps description
  }

fixedPointRecoveredCodeExact :
  (description : Description.GuardedCookFormulaDescription) →
  Description.code (fixedPointRecoveredDescription description)
  ≡ Description.code description
fixedPointRecoveredCodeExact description = refl

fixedPointRecoveredFormulaExact :
  (description : Description.GuardedCookFormulaDescription) →
  Description.formula (fixedPointRecoveredDescription description)
  ≡ Description.formula description
fixedPointRecoveredFormulaExact description = refl

fixedPointRecoveredQueryExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  Description.atIndex (fixedPointRecoveredDescription description) index
  ≡ Description.atIndex description index
fixedPointRecoveredQueryExact description index = refl

fixedPointRecoveredQueryFormulaExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  Query.queryFormula
    (Description.atIndex
      (fixedPointRecoveredDescription description)
      index)
  ≡ Description.formula description
fixedPointRecoveredQueryFormulaExact description index = refl

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The finite behavioural fixed-point quotation now recovers a guarded-Cook
-- description whose code, formula and every indexed query are definitionally the
-- SAME as the supplied description of the primitive machine.  Raw code equality
-- between helper syntax and generated Cook formula is unnecessary.
--
-- Still unpaid: compile a standard-TM binary body that, when given this quoted
-- syntax, performs the already-owned streamed query computation and closes its
-- runtime/program-size budget on the resulting fixed target.
------------------------------------------------------------------------
