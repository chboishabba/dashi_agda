module DASHI.Moonshine.SSPJStratifiedQuotientRound7Validation where

open import DASHI.Core.Prelude

import DASHI.Biology.IndexedJExternalGluingExact as Gluing
import DASHI.Biology.IndexedJStratifiedMultiresolutionExact as J
import DASHI.Biology.SSP369JResolutionBifiltrationExact as Bif
import DASHI.Core.MultiscaleMDL as MDL
import DASHI.Foundations.StratifiedResolutionTowerExact as Tower

------------------------------------------------------------------------
-- Stratified fibre witness.
------------------------------------------------------------------------

validationRegularFibreLeftRoundTrip :
  Tower.regularTo (Tower.regularFrom Tower.regularLeft)
  ≡ Tower.regularLeft
validationRegularFibreLeftRoundTrip = Tower.regularToFrom Tower.regularLeft

validationRegularFibreRightRoundTrip :
  Tower.regularTo (Tower.regularFrom Tower.regularRight)
  ≡ Tower.regularRight
validationRegularFibreRightRoundTrip = Tower.regularToFrom Tower.regularRight

validationFixedFibreRoundTrip :
  Tower.fixedTo (Tower.fixedFrom Tower.fixedOnly)
  ≡ Tower.fixedOnly
validationFixedFibreRoundTrip = Tower.fixedToFrom Tower.fixedOnly

------------------------------------------------------------------------
-- Exact coarse/residual factorization on the decimal tower.
------------------------------------------------------------------------

validationDecimalSplitJoin :
  ∀ {r}
    (pair : MDL.CoarseResidual
      J.decimalMultiscaleCarrier J.decimalResidualCodec r) →
  MDL.split J.decimalResidualCodec (MDL.join J.decimalResidualCodec pair)
  ≡ pair
validationDecimalSplitJoin = J.decimalSplitJoin

validationDecimalJoinSplit :
  ∀ {r} (fine : J.DecimalAddress (suc r)) →
  MDL.join J.decimalResidualCodec (MDL.split J.decimalResidualCodec fine)
  ≡ fine
validationDecimalJoinSplit = J.decimalJoinSplit

------------------------------------------------------------------------
-- Per-grade and cumulative counts.
------------------------------------------------------------------------

validationDecimalTen : J.radixGradeCount 10 1 ≡ 10
validationDecimalTen = J.decimalGrade1

validationDecimalHundred : J.radixGradeCount 10 2 ≡ 100
validationDecimalHundred = J.decimalGrade2

validationDecimalThousand : J.radixGradeCount 10 3 ≡ 1000
validationDecimalThousand = J.decimalGrade3

validationDecimalEleven : J.retainedResolutionCount 10 1 ≡ 11
validationDecimalEleven = J.decimalRetained1

validationDecimalOneHundredEleven :
  J.retainedResolutionCount 10 2 ≡ 111
validationDecimalOneHundredEleven = J.decimalRetained2

validationDecimalOneThousandOneHundredEleven :
  J.retainedResolutionCount 10 3 ≡ 1111
validationDecimalOneThousandOneHundredEleven = J.decimalRetained3

validationRound6ElevenMatchesFirstCumulativeNumerically :
  J.retainedResolutionCount 10 1 ≡ Gluing.joinedAddressIndex
validationRound6ElevenMatchesFirstCumulativeNumerically =
  J.firstCumulativeMatchesJoinedIndexNumerically

------------------------------------------------------------------------
-- Compatible-history inverse-limit witness.
------------------------------------------------------------------------

validationAllZeroInverseLimitCoherence :
  (r : Nat) →
  J.prefix (Tower.atResolution J.allZeroInverseLimitPoint (suc r))
  ≡ Tower.atResolution J.allZeroInverseLimitPoint r
validationAllZeroInverseLimitCoherence r =
  Tower.coherent J.allZeroInverseLimitPoint r

------------------------------------------------------------------------
-- 369 depth and j-resolution commute without being identified.
------------------------------------------------------------------------

validationDepthResolutionCommute63 :
  ∀ {r} (x : Bif.H6 (suc r)) →
  Bif.project6to3 (Bif.coarsen6 x)
  ≡ Bif.coarsen3 (Bif.project6to3 x)
validationDepthResolutionCommute63 = Bif.coarsenDepthCommutes63

validationDepthResolutionCommute96 :
  ∀ {r} (x : Bif.H9 (suc r)) →
  Bif.project9to6 (Bif.coarsen9 x)
  ≡ Bif.coarsen6 (Bif.project9to6 x)
validationDepthResolutionCommute96 = Bif.coarsenDepthCommutes96

validationResolutionInclude36 :
  ∀ {r} (x : Bif.H3 (suc r)) →
  Bif.coarsen6 (Bif.include3to6 x)
  ≡ Bif.include3to6 (Bif.coarsen3 x)
validationResolutionInclude36 = Bif.coarsenInclude36Commutes

validationResolutionInclude69 :
  ∀ {r} (x : Bif.H6 (suc r)) →
  Bif.coarsen9 (Bif.include6to9 x)
  ≡ Bif.include6to9 (Bif.coarsen6 x)
validationResolutionInclude69 = Bif.coarsenInclude69Commutes

------------------------------------------------------------------------
-- Boundary validation: do not silently promote the toy models.
------------------------------------------------------------------------

validationDecimalTreeNotAutomaticallyTenAdic :
  J.IndexedJMultiresolutionBoundary.decimalAddressInverseLimitIsAutomaticallyTenAdicRing
    J.canonicalIndexedJMultiresolutionBoundary
  ≡ false
validationDecimalTreeNotAutomaticallyTenAdic = refl

validationFiniteBifiltrationDoesNotProveLimitInterchange :
  Bif.J369BifiltrationBoundary.commutingFiniteBifiltrationProvesTwoInfiniteLimitsCommute
    Bif.canonicalJ369BifiltrationBoundary
  ≡ false
validationFiniteBifiltrationDoesNotProveLimitInterchange = refl

------------------------------------------------------------------------
-- Validation-trigger theorems: deliberately substantive but redundant.
-- They create a PR-visible check run against the Round-7 workflow without
-- changing the Round-7 implementation branch itself.
------------------------------------------------------------------------

validationTriggerRetainsFirstDecimalCut :
  J.retainedResolutionCount 10 1 ≡ 11
validationTriggerRetainsFirstDecimalCut = J.decimalRetained1

validationTriggerRetainsSecondDecimalCut :
  J.retainedResolutionCount 10 2 ≡ 111
validationTriggerRetainsSecondDecimalCut = J.decimalRetained2
