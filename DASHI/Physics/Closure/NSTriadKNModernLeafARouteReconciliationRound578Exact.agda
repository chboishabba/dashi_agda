module DASHI.Physics.Closure.NSTriadKNModernLeafARouteReconciliationRound578Exact where

------------------------------------------------------------------------
-- ROUND578 / INTROSPECTIVE RECONCILIATION: R577 SCHUR IS SUFFICIENT, NOT
-- CANONICAL
--
-- R577 correctly shows how old R328 row/column Schur receipts can build the
-- modern R568 commutator-only budget.  That compiler is useful and sound.
--
-- But R335 predates R577 and already proves a least-privilege correction:
-- once the signed physical aggregate is available, absolute row/column Schur
-- is a redirected fallback.  The preferred producer keeps the literal R329
-- nested cells signed and asks only for the R336 same-final-output physical
-- pairwise-overlap envelope before reusing R29 pre-TT* aggregation.
--
-- This owner reconciles those two facts so the modern scheduler does not turn
-- a sufficient absolute-value producer into a mandatory prerequisite.
--
-- No analytic estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNPreTTStarReuseCorrectionRound335Exact as R335
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPreTTStarAdapterRound336Exact as R336
import DASHI.Physics.Closure.NSTriadKNModernNestedSchurToCommutatorBidiRound577Exact as R577

-- The two producer families remain available, but they do not have the same
-- dependency status.
data ModernLeafAProducerRoute578 : Set where
  signedPairwisePreTTStar578 : ModernLeafAProducerRoute578
  absoluteRowColumnSchur578 : ModernLeafAProducerRoute578

routeDisposition578 : ModernLeafAProducerRoute578 → Admission.RouteDisposition
routeDisposition578 signedPairwisePreTTStar578 = Admission.admitted
routeDisposition578 absoluteRowColumnSchur578 = Admission.redirectedReuse

-- The first preferred theorem debt is the physical local envelope already
-- named by R336.  R29 aggregation is existing infrastructure once that local
-- receipt is supplied.
data PreferredResidual578 : Set where
  missingLiteralNestedPairwiseOverlapEnvelope578 : PreferredResidual578
  missingCutoffUniformSignedPreTTStar578 : PreferredResidual578

currentPreferredResidual578 : PreferredResidual578
currentPreferredResidual578 = missingLiteralNestedPairwiseOverlapEnvelope578

round578R577SchurCompilerStillReusable : Bool
round578R577SchurCompilerStillReusable =
  R577.round577ModernR568CompilerClosedGivenReceipts

round578R577RowColumnMadeMandatory : Bool
round578R577RowColumnMadeMandatory = false

round578R335SignedRouteRestoredAsPreferred : Bool
round578R335SignedRouteRestoredAsPreferred =
  R335.round335HeatWeightedNestedPairwiseOverlapHighestAlpha

round578R336LiteralPairingAdapterAlreadyClosed : Bool
round578R336LiteralPairingAdapterAlreadyClosed =
  R336.round336LiteralR329PairingAdapterClosed

round578PhysicalPairwiseOverlapEnvelopeClosed : Bool
round578PhysicalPairwiseOverlapEnvelopeClosed =
  R336.round336PhysicalPairwiseOverlapEnvelopeClosed

round578CurrentFirstMissingIsPairwiseEnvelope : Bool
round578CurrentFirstMissingIsPairwiseEnvelope = true

round578ClayPromotion : Bool
round578ClayPromotion = false

round578R577RowColumnMadeMandatoryIsFalse :
  round578R577RowColumnMadeMandatory ≡ false
round578R577RowColumnMadeMandatoryIsFalse = refl

round578CurrentFirstMissingIsPairwiseEnvelopeIsTrue :
  round578CurrentFirstMissingIsPairwiseEnvelope ≡ true
round578CurrentFirstMissingIsPairwiseEnvelopeIsTrue = refl

round578ClayPromotionIsFalse : round578ClayPromotion ≡ false
round578ClayPromotionIsFalse = refl
