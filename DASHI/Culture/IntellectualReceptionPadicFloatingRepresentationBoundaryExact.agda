module DASHI.Culture.IntellectualReceptionPadicFloatingRepresentationBoundaryExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / P-ADIC + FLOATING REPRESENTATION BOUNDARY
--
-- Cross-pollination only.  The reception path calculus borrows the disciplined
-- distinction between coarse presentation and fine refinement/prefix data.
-- It does not identify historical paths with p-adic numbers, ultrametric
-- distances, IEEE floating-point values, or HME Float interchange fields.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Foundations.RepresentationChartInvariant as Representation
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.HME.Trace as HMETrace
import DASHI.Culture.IntellectualReceptionComposableFibreTransportPathExact as Paths

------------------------------------------------------------------------
-- 1. Reuse exact representation/radix facts already owned by Foundations.
------------------------------------------------------------------------

decimalAndBinaryHalfRemainEquivalent :
  Representation.RatioEquivalent
    Radix.decimalPointFiveReading
    Radix.binaryPointOneReading
decimalAndBinaryHalfRemainEquivalent =
  Radix.decimalBinaryHalfEquivalent

decimalP3DisplayBase :
  Radix.displayBase (Radix.canonicalDecimalPAdicReading 3) ≡ 10
decimalP3DisplayBase = refl

decimalP3ValuationPrime :
  Radix.valuationPrime (Radix.canonicalDecimalPAdicReading 3) ≡ 3
decimalP3ValuationPrime = refl

decimalP3DoesNotRequireDisplayBaseToEqualValuationPrime :
  Radix.displayBaseEqualsValuationPrimeRequired
    (Radix.canonicalDecimalPAdicReading 3)
  ≡ false
decimalP3DoesNotRequireDisplayBaseToEqualValuationPrime = refl

------------------------------------------------------------------------
-- 2. Coarse presentation and fine historical-prefix address are independent.
------------------------------------------------------------------------

data ReceptionRepresentationCase : Set where
  earlyAuthorityRepresentation
  lateAuthorityRepresentation
  : ReceptionRepresentationCase

data CoarseDisplayedEndpoint : Set where
  sameDisplayedMovementEndpoint : CoarseDisplayedEndpoint

data FinePrefixAddressCode : Set where
  acquisitionInFirstPrefix
  acquisitionOnlyInSecondPrefix
  : FinePrefixAddressCode

coarseDisplayedEndpoint : ReceptionRepresentationCase → CoarseDisplayedEndpoint
coarseDisplayedEndpoint _ = sameDisplayedMovementEndpoint

finePrefixAddress : ReceptionRepresentationCase → FinePrefixAddressCode
finePrefixAddress earlyAuthorityRepresentation = acquisitionInFirstPrefix
finePrefixAddress lateAuthorityRepresentation = acquisitionOnlyInSecondPrefix

finePrefixAddressesDiffer :
  finePrefixAddress earlyAuthorityRepresentation
  ≡ finePrefixAddress lateAuthorityRepresentation → ⊥
finePrefixAddressesDiffer ()

sameCoarseDisplayCannotRecoverFinePrefixAddress :
  INF.FactorsThrough coarseDisplayedEndpoint finePrefixAddress → ⊥
sameCoarseDisplayCannotRecoverFinePrefixAddress =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      earlyAuthorityRepresentation
      lateAuthorityRepresentation
      refl
      finePrefixAddressesDiffer)

------------------------------------------------------------------------
-- 3. Path length behaves like a refinement depth coordinate only by analogy.
------------------------------------------------------------------------

earlyPathDepthTwo : Paths.pathLength Paths.earlyAuthorityPath02 ≡ 2
earlyPathDepthTwo = Paths.earlyAuthorityPathHasLengthTwo

latePathDepthTwo : Paths.pathLength Paths.lateAuthorityPath02 ≡ 2
latePathDepthTwo = Paths.lateAuthorityPathHasLengthTwo

data SharedDepthCase : Set where earlyDepthCase lateDepthCase : SharedDepthCase

data CoarseDepthCode : Set where depthTwo : CoarseDepthCode

data FineHistoryCode : Set where earlyHistory lateHistory : FineHistoryCode

coarseDepth : SharedDepthCase → CoarseDepthCode
coarseDepth _ = depthTwo

fineHistory : SharedDepthCase → FineHistoryCode
fineHistory earlyDepthCase = earlyHistory
fineHistory lateDepthCase = lateHistory

fineHistoriesDiffer : fineHistory earlyDepthCase ≡ fineHistory lateDepthCase → ⊥
fineHistoriesDiffer ()

sameRefinementDepthCannotRecoverHistory :
  INF.FactorsThrough coarseDepth fineHistory → ⊥
sameRefinementDepthCannotRecoverHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      earlyDepthCase lateDepthCase refl fineHistoriesDiffer)

------------------------------------------------------------------------
-- 4. Float fields are representation/interchange surfaces, not proof identity.
------------------------------------------------------------------------

-- `HME.Trace` deliberately uses Agda Float fields for normalized vectors,
-- entropy, MDL costs and exported invariants while stating that the module is a
-- boundary contract and supplies no semantics.  We preserve that distinction.

data ReceptionHistoryPromotesHMEFloatTrace : Set where
data SameFloatPresentationPromotesSameHistory : Set where
data ReceptionPrefixPromotesPAdicValuation : Set where
data ReceptionPathPromotesUltrametricDistance : Set where

receptionHistoryDoesNotPromoteHMEFloatTrace :
  ReceptionHistoryPromotesHMEFloatTrace → ⊥
receptionHistoryDoesNotPromoteHMEFloatTrace ()

sameFloatPresentationDoesNotPromoteSameHistory :
  SameFloatPresentationPromotesSameHistory → ⊥
sameFloatPresentationDoesNotPromoteSameHistory ()

receptionPrefixDoesNotPromotePAdicValuation :
  ReceptionPrefixPromotesPAdicValuation → ⊥
receptionPrefixDoesNotPromotePAdicValuation ()

receptionPathDoesNotPromoteUltrametricDistance :
  ReceptionPathPromotesUltrametricDistance → ⊥
receptionPathDoesNotPromoteUltrametricDistance ()

------------------------------------------------------------------------
-- 5. Explicit cross-domain reading.
------------------------------------------------------------------------

record ReceptionPadicFloatingCrossPollination : Set where
  constructor reception-padic-floating-cross-pollination
  field
    coarsePresentationCanHideFineAddress : Bool
    refinementDepthDeterminesFineHistory : Bool
    chartAndValuationMustBeIdentified : Bool
    FloatBoundaryFieldIsProofSemantics : Bool
    receptionPrefixIsLiteralPAdicPrefix : Bool
    receptionPathLengthIsLiteralValuation : Bool
    sharedStructuralLessonRetained : Bool
    sourceAttributionBoundarySurvivesAnalogy : Bool

canonicalReceptionPadicFloatingCrossPollination :
  ReceptionPadicFloatingCrossPollination
canonicalReceptionPadicFloatingCrossPollination =
  reception-padic-floating-cross-pollination
    true false false false false false true true
