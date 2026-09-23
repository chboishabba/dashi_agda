module DASHI.Moonshine.EisensteinConvergenceEndgameCutsetExact where

------------------------------------------------------------------------
-- EISENSTEIN q-SERIES CONVERGENCE: CURRENT EXACT ENDGAME
--
-- This is a dependency cutset, not a new analytic assumption.
--
-- Paid compiler chain:
--
--   executable sigma3/sigma5 + polynomial bounds
--        -> complex E4/E6 term majorants
--        -> Step-V polynomial/geometric domination
--        -> Bishop geometric/comparison convergence
--        -> explicit Bishop-to-legacy coordinate transport
--        -> additive coordinate-series limits
--        -> literal E4_N/E6_N truncation limits
--        -> Delta numerator limit
--
-- The remaining inputs are deliberately split by representation:
--
--   A. concrete-complex q/norm laws on the selected legacy package;
--   B. a Step-V domination inhabitant for the resulting scalar radius;
--   C. the explicit Bishop -> legacy series/limit transport and pointwise
--      identification of the four coordinate terms;
--   D. the final same-object identification with the all-SL2(Z) Eisenstein
--      analytic model.
--
-- In particular, no direct successor-ratio theorem for n^4 r^n or n^6 r^n
-- remains necessary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Interop.Round11MachinLeanBindingManifestExact as ReplayManifest

record EisensteinConvergenceEndgameCutset : Set where
  constructor eisenstein-convergence-endgame-cutset
  field
    executableSigma3Sigma5AndGrowthBoundsOwned : Bool
    qExponentCartesianRingAlgebraOwned : Bool
    upperHalfPlaneToQDiskReductionCompilerOwned : Bool
    complexTermPolynomialGeometricMajorantsOwned : Bool
    bishopGeometricSeriesConvergenceOwned : Bool
    stepVPolynomialDominationToBishopConvergenceOwned : Bool
    additiveTruncationSeriesAlignmentOwned : Bool
    componentwiseComplexLimitCompilerOwned : Bool
    bishopLegacyCoordinateTransportCompilerOwned : Bool
    deltaNumeratorLimitCompilerOwned : Bool
    leanMathlibStandardAnalyticParityRecorded : Bool
    agdaActualFiniteRecurrenceExtractionCompilerOwned : Bool
    leanLiteralFiniteRecurrenceTargetOwned : Bool
    leanLiteralFiniteRecurrenceConvergenceOwned : Bool
    leanLiteralLimitsIdentifiedWithMathlibE4E6 : Bool
    leanNormalizedDeltaLimitCompilerOwned : Bool
    primitiveRealExtractionCompilerOwnedOnBothSides : Bool

    agdaBishopSetoidComplexOwned : Bool
    agdaRound11MachinSourceCapstoneOwned : Bool
    leanVendoredBishopEvaluatorOwned : Bool
    leanVendoredBishopEvaluatorFaithful : Bool
    leanExpSinCosMachinSemanticCompilersOwned : Bool
    leanRound11MachinBindingCompilerOwned : Bool
    leanRound11MappedE4E6ConvergenceOwned : Bool
    agdaLiteralNormalizedSourceDeltaOwned : Bool
    leanMappedNormalizedSourceDeltaConvergenceOwned : Bool
    leanEta24PinnedReflectionOwned : Bool
    leanEta24SixfoldPhaseOwned : Bool
    leanFinalDeltaMinCutCompilerOwned : Bool
    normalizedDeltaNonvanishingDownstreamOfMinCut : Bool
    normalizedDeltaSixfoldPhaseDownstreamOfMinCut : Bool
    reciprocalRound11MachinBindingManifestOwned : Bool
    reciprocalManifestMatchesCurrentSourceBlobs : Bool

    selectedConcreteQNormLawsInhabited : Bool
    quarticSexticStepVDominationInhabited : Bool
    bishopLegacySeriesTransportInhabited : Bool
    legacyFunctionSeriesLimitBridgeInhabited : Bool
    fourBishopCoordinateTermIdentificationsInhabited : Bool
    analyticEisensteinSameObjectWeldInhabited : Bool

    actualAgdaRound11MachinBindingInLean : Bool
    eta24NormalizedDeltaSameObjectWeldInhabited : Bool
    legacyBishopToPropositionalRouteRequiredByRouteB : Bool

    obsoleteDirectPolynomialRatioLeaf : Bool

    nextResidual : String

open EisensteinConvergenceEndgameCutset public

canonicalEisensteinConvergenceEndgameCutset :
  EisensteinConvergenceEndgameCutset
canonicalEisensteinConvergenceEndgameCutset =
  eisenstein-convergence-endgame-cutset
    true true true true true true true true true true true true true true true true true
    true true true true true true true
    true true true true
    true true true true true
    false false false false false false
    false true false
    false
    "Route B is source-pinned and setoid-native. Agda owns the actual vendored-Bishop complex carrier, Round11 configured trig package, bishopMachinPi, literal q/E4/E6/discriminant-numerator recurrences, and the normalized finite source Delta defined with the exact Bishop rational embedding 1/1728; all finite objects are setoid-congruent. Lean owns a faithful evaluator of the vendored Bishop quotient into Real, derives the exact resampled arithmetic plus exp/sin/cos/Machin-pi classical semantics from the concrete source convergence receipts, compiles a single Round11MachinSourceBinding to the primitive extraction, and proves mapped source E4_N/E6_N, the discriminant numerator, and the normalized source Delta converge to Mathlib E4/E6 and the canonical normalized Delta target. Independently, eta^24 at the pinned Mathlib v4.28.0 dependency now owns the weight-12 reflection/fixed-locus theorem and the concrete branch-safe sixfold phase theorem arg(eta^24(tau)) + 6 arg(tau) = k*pi on the unit circle. Therefore none of the legacy ConcreteComplex q-norm, Step-V, Bishop-to-legacy, Nat-function, four-coordinate, or phase-quotient leaves is required by route B. The former final classical Delta dependency eta^24 = normalized(E4^3-E6^2)/1728 is now source-written closed in the pinned Lean companion without a dependency bump: a pin-local eta^24 cusp form and first q coefficient, specialized weight-12 scalar rigidity via weight-zero constancy, and normalized-E4/E6 cusp coefficient comparison force the scalar to one. This immediately inhabits the final Delta min-cut compiler and makes normalized-Delta nonvanishing/sixfold phase hypothesis-free on the Lean target. The reciprocal Agda/Lean binding manifests now record matching content hashes for all seven load-bearing Agda blobs plus the theorem-to-field mapping table. The active route-B residual is therefore only observation of the generated Agda->Lean replay/inhabitation of Round11MachinSourceBinding from those pinned source receipts. Legacy ConcreteComplex/Bishop-to-propositional leaves remain off the route-B path."
