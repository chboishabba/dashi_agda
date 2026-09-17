module DASHI.Physics.YangMills.YMClayF1CanonicalSourceApplicationValidation where

-- RED-first validation for the F1 source-native producer cut.
--
-- The production owner must not manufacture CMP116 authority.  It must only
-- compose the already-existing canonical common-domain source theorem ABI
-- (R338), its selected-T5 same-object/calibration ABI (R339), and the existing
-- direct selected-shell compiler (R320) into the literal R295 carrier consumed
-- downstream.

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayF1CanonicalSourceApplicationExact as F1

-- The bridge itself is theorem-bearing compiler plumbing, not a citation-to-proof
-- coercion and not a fresh clustering estimate.
f1CanonicalCompilerAvailable : Set
f1CanonicalCompilerAvailable = F1.F1CanonicalSourceApplicationCompilerPresent

f1DoesNotCreateSourceTheorem :
  F1.sourceTheoremManufacturedByCompiler ≡ false
f1DoesNotCreateSourceTheorem =
  F1.sourceTheoremManufacturedByCompilerIsFalse

f1DoesNotAddFreshDecayEstimate :
  F1.freshYMDecayEstimateIntroduced ≡ false
f1DoesNotAddFreshDecayEstimate =
  F1.freshYMDecayEstimateIntroducedIsFalse

f1UsesExistingR338R339Cut :
  F1.canonicalR338R339CutCompilesToR295 ≡ true
f1UsesExistingR338R339Cut =
  F1.canonicalR338R339CutCompilesToR295IsTrue

f1OldR318ExternalPresentationNotPrimitive :
  F1.r318ExternalPresentationPairIsPrimitiveCut ≡ false
f1OldR318ExternalPresentationNotPrimitive =
  F1.r318ExternalPresentationPairIsPrimitiveCutIsFalse
