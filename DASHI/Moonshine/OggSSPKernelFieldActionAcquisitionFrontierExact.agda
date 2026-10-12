module DASHI.Moonshine.OggSSPKernelFieldActionAcquisitionFrontierExact where

------------------------------------------------------------------------
-- RICHER-ACTION ACQUISITION FRONTIER FOR CANONICAL GF(3^6) RECOGNITION
--
-- The standard finite-Heisenberg/symplectic structure alone does not select
-- the chosen GF(729) multiplication: swap01 preserves that paid structure and
-- changes the selected product.
--
-- The external-acquisition wall is now materially closed by PR #1098.  Exact
-- ATLAS 2.Suz / 2.Suz:2 GF(3)^12 matrix bytes have been acquired, the unique
-- inner alternating form and same-basis normalization have been computed, and
-- a concrete source word
--
--     g2 g1 g2^-1 g1 g2^-1
--
-- yields an X6 compression T with irreducible degree-six minimal polynomial,
-- cyclic rank six and an explicit swap01-breaking witness.
--
-- Crucially the word does NOT stabilize X6.  The correct operator is the
-- compression pi_X g iota_X; Lagrangian stabilization was an unnecessary
-- stronger premise.
--
-- This branch independently closes the selected-presentation gap:
--
--   selected f(alpha) = alpha^6 + alpha^5 + alpha^4 + 1,
--   beta = 1 - alpha,
--   f(1-x) = x^6 - x^5 - x^3 + x^2 + 1,
--
-- exactly the compression polynomial.  An explicit invertible matrix Q with
-- det(Q)=2 mod 3 satisfies Q T = M_beta Q.
--
-- Therefore the remaining field debt is no longer source acquisition or a
-- polynomial/cardinality coincidence.  The finite selected GF729 presentation
-- weld is paid by executable exact arithmetic.  What remains is Agda-kernel
-- certification and the stronger Monster action/orbit/stabilizer semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSPHeisenbergSymplecticFieldNoGoExact as NoGo
import DASHI.Moonshine.OggSSPP2TernaryHeisenbergAxis0Exact as Axis0
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Actual
import DASHI.Moonshine.Base369Monster3BShortestFrontierCandidateCompilerExact as Candidate
import DASHI.Reasoning.Trialectic369Shortest3BActionSourceBridgeExact as ShortestBridge
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as LinearCore
import DASHI.Reasoning.Trialectic369Selected3BProjectedActionMaxCutExact as Projected
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.OggSSPMonster3BSelectedGF729WeldExact as Weld

standardHeisenbergSymplecticSelectsFieldProduct : Bool
standardHeisenbergSymplecticSelectsFieldProduct =
  NoGo.currentHeisenbergSymplecticDataSelectsChosenFieldProduct
    NoGo.canonicalHeisenbergSymplecticFieldNoGoBoundary

standardHeisenbergSymplecticSelectsFieldProductIsFalse :
  standardHeisenbergSymplecticSelectsFieldProduct ≡ false
standardHeisenbergSymplecticSelectsFieldProductIsFalse = refl

rankOneEllipticThreeTorsionTransportPaid : Bool
rankOneEllipticThreeTorsionTransportPaid =
  Axis0.genuineEllipticThreeTorsionTransportPaid Axis0.canonicalAxis0Boundary

rankOneEllipticThreeTorsionTransportPaidIsFalse :
  rankOneEllipticThreeTorsionTransportPaid ≡ false
rankOneEllipticThreeTorsionTransportPaidIsFalse = refl

rankOneActualWeilPairingTransportPaid : Bool
rankOneActualWeilPairingTransportPaid =
  Axis0.actualWeilPairingTransportPaid Axis0.canonicalAxis0Boundary

rankOneActualWeilPairingTransportPaidIsFalse :
  rankOneActualWeilPairingTransportPaid ≡ false
rankOneActualWeilPairingTransportPaidIsFalse = refl

base369ShortestCandidateInhabitedHere : Bool
base369ShortestCandidateInhabitedHere =
  Candidate.base369CandidateInhabitedHere
    Candidate.canonicalBase369ShortestFrontierCandidateBoundary

base369ShortestCandidateInhabitedHereIsFalse :
  base369ShortestCandidateInhabitedHere ≡ false
base369ShortestCandidateInhabitedHereIsFalse = refl

shortestSourceWouldCompileActualMonsterAction : Bool
shortestSourceWouldCompileActualMonsterAction =
  ShortestBridge.actualActionRecognitionCompiled
    ShortestBridge.canonicalTrialectic369Shortest3BActionSourceBridgeBoundary

shortestSourceWouldCompileActualMonsterActionIsTrue :
  shortestSourceWouldCompileActualMonsterAction ≡ true
shortestSourceWouldCompileActualMonsterActionIsTrue = refl

selected3BLinearCoreInhabitedHere : Bool
selected3BLinearCoreInhabitedHere =
  LinearCore.canonicalCoreInhabitedHere
    LinearCore.canonicalTrialectic369CanonicalSelected3BLinearCoreBoundary

selected3BLinearCoreInhabitedHereIsFalse :
  selected3BLinearCoreInhabitedHere ≡ false
selected3BLinearCoreInhabitedHereIsFalse = refl

selected3BLinearActionIntertwiningInhabitedHere : Bool
selected3BLinearActionIntertwiningInhabitedHere =
  LinearCore.actionIntertwiningInhabitedHere
    LinearCore.canonicalTrialectic369CanonicalSelected3BLinearCoreBoundary

selected3BLinearActionIntertwiningInhabitedHereIsFalse :
  selected3BLinearActionIntertwiningInhabitedHere ≡ false
selected3BLinearActionIntertwiningInhabitedHereIsFalse = refl

selected3BProjectedRetractionInhabitedHere : Bool
selected3BProjectedRetractionInhabitedHere =
  Projected.actualLinearRetractionInhabitedHere
    Projected.canonicalTrialectic369Selected3BProjectedActionMaxCutBoundary

selected3BProjectedRetractionInhabitedHereIsFalse :
  selected3BProjectedRetractionInhabitedHere ≡ false
selected3BProjectedRetractionInhabitedHereIsFalse = refl

selected3BProjectedActionEquationInhabitedHere : Bool
selected3BProjectedActionEquationInhabitedHere =
  Projected.actualProjectedActionEquationInhabitedHere
    Projected.canonicalTrialectic369Selected3BProjectedActionMaxCutBoundary

selected3BProjectedActionEquationInhabitedHereIsFalse :
  selected3BProjectedActionEquationInhabitedHere ≡ false
selected3BProjectedActionEquationInhabitedHereIsFalse = refl

actualMonsterActionRecognitionInhabitedLocally : Bool
actualMonsterActionRecognitionInhabitedLocally =
  Actual.actualActionRecognitionInhabitedHere
    Actual.canonicalActualActionRecognitionBoundary

actualMonsterActionRecognitionInhabitedLocallyIsFalse :
  actualMonsterActionRecognitionInhabitedLocally ≡ false
actualMonsterActionRecognitionInhabitedLocallyIsFalse = refl

exceptionalMonsterAlbertSameActionPaid : Bool
exceptionalMonsterAlbertSameActionPaid =
  Exceptional.monsterResidualIdentifiedWithAlbertResidualHere
    Exceptional.canonicalExceptionalResidualBoundary

exceptionalMonsterAlbertSameActionPaidIsFalse :
  exceptionalMonsterAlbertSameActionPaid ≡ false
exceptionalMonsterAlbertSameActionPaidIsFalse = refl

record FieldActionAcquisitionBoundary : Set where
  constructor field-action-acquisition-boundary
  field
    standardHeisenbergSymplecticLaneExhausted : Bool
    rankOneWeilLaneNeedsActualTorsionTransport : Bool
    shortest3BCompilerChainLocated : Bool
    selected3BLargeLinearRouteNotAnX6Operator : Bool
    exceptionalF4E6LaneNeedsSameActionRecognition : Bool
    certifiedExternalTwelveDimensionalSourceLocated : Bool
    actualAtlasMatricesImportedOn1098 : Bool
    fullNormalizerGlobalX6TargetRejected : Bool
    compressionRouteRequiresLagrangianStabilizer : Bool
    actualDegreeSixCompressionPaid : Bool
    actualSwapBreakingPaid : Bool
    selectedGF729AffineGeneratorWeldPaid : Bool
    explicitSelectedGF729IntertwinerRuntimePaid : Bool
    agdaKernelMatrixIntertwinerPaid : Bool
    fullMonsterActionOrbitStabilizerRecognitionPaid : Bool
    note : String
open FieldActionAcquisitionBoundary public

canonicalFieldActionAcquisitionBoundary : FieldActionAcquisitionBoundary
canonicalFieldActionAcquisitionBoundary =
  field-action-acquisition-boundary
    true true true true true
    true
    true
    true
    false
    (Weld.degreeSixCompressionReceiptPaid Weld.canonicalBoundary)
    (Weld.swap01BrokenByCompression Weld.canonicalBoundary)
    (Weld.affineBetaEqualsOneMinusAlphaLocated Weld.canonicalBoundary)
    (Weld.selectedGF729PresentationWeldPaid Weld.canonicalBoundary)
    (Weld.agdaKernelIntertwinerProofPaid Weld.canonicalBoundary)
    (Weld.fullActionOrbitStabilizerRecognitionPaid Weld.canonicalBoundary)
    "The field-source acquisition seam is closed at the exact finite level: real ATLAS bytes -> same-basis 12D computation -> degree-six X6 compression -> beta=1-alpha -> explicit Q conjugacy to the selected GF(729) presentation. The surviving obligations are kernel certification and the stronger Monster action/orbit/stabilizer semantic recognition."
