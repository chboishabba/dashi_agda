module DASHI.Mathematics.CrossPollination.EisensteinLeanSplitPrimeLocalClosureReceiptExact where

------------------------------------------------------------------------
-- LEAN SPLIT-PRIME / ALL-GOOD-PRIME LOCAL CLOSURE RECEIPT
--
-- Repository-internal formal-source receipt only. It records the Lean #69
-- theorem surface without importing a Lean proof term into Agda.
--
-- Observed source chain on the SAME j=0 Eisenstein programme:
--
--   exact order-3 multiplicative character
--     -> cube subgroup = character kernel
--     -> exact cube-fibre certificate
--     -> Jacobi trace compiler
--     -> J in Z[zeta_6], J*conj(J)=p
--     -> explicit Z[zeta_6] = Z[omega] carrier weld
--     -> literal z_p : EisensteinQA with N(z_p)=p
--     -> a_p = -(2*re(z_p)-im(z_p))
--     -> split local Euler polynomial
--     -> existing six-unit x split-choice normalization
--     -> split/inert classification for every good prime p>3.
--
-- At p=2 and p=3 Lean also records literal singular-reduction facts and exact
-- finite counts. It does NOT manufacture Neron/Kodaira reduction types or the
-- bad-prime elliptic local L-factors.
--
-- Lean also records an EXTERNAL-SOURCE PROVENANCE receipt for the concrete
-- curve metadata: Stein/Cremona-derived table label 36a1/conductor 36 and the
-- PARI/GP short-Weierstrass discriminant formula / F2 singular example. That
-- external metadata is not Lean proof authority and is not re-attributed to
-- DASHI, Mathlib, or Agda.
--
-- Attribution boundary:
-- * Mathlib owns imported generic finite-field, character, primitive-root,
--   Jacobi-sum, quadratic-algebra and complex-conjugation infrastructure.
-- * DASHI/Lean owns specialization/composition on PR #69.
-- * Stein/Cremona and PARI metadata remain externally attributed.
-- * This file is Agda provenance only: no cross-kernel proof authority and no
--   local theorem is fabricated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Interop.Round11MachinCrossProverRecognitionExact as Attribution

record LeanSplitPrimeLocalClosureReceipt : Set where
  constructor lean-split-prime-local-closure-receipt
  field
    repository : String
    pullRequest : String
    branch : String
    observedCommit : String
    cubicCharacterOwner : String
    genericCharacterKernelOwner : String
    cyclotomicJacobiOwner : String
    literalEisensteinCarrierOwner : String
    unitNormalizationOwner : String
    allGoodPrimeOwner : String
    badPrimeTwoOwner : String
    badPrimeThreeOwner : String
    external36a1SourceReceiptOwner : String
    cubeFibreTheorem : String
    genericKernelTheorem : String
    jacobiNormTheorem : String
    literalNormTheorem : String
    splitTraceTheorem : String
    splitEulerTheorem : String
    allGoodPrimeConstructor : String
    verificationStatus : String
    origin : Attribution.ClaimOrigin

open LeanSplitPrimeLocalClosureReceipt public

leanSplitPrimeLocalClosureReceipt : LeanSplitPrimeLocalClosureReceipt
leanSplitPrimeLocalClosureReceipt =
  lean-split-prime-local-closure-receipt
    "chboishabba/dashi_lean4"
    "PR #69"
    "agent/eisenstein-lattice-counting-maxcut-20261012"
    "48168c6d8f24d741ac6401e6d75530d7e2dfc397"
    "Integration/EisensteinJZeroCanonicalCubicCharacterExact.lean"
    "Integration/EisensteinJZeroCubicCharacterCertificateExact.lean"
    "Integration/EisensteinJZeroSplitJacobiCyclotomicExact.lean"
    "Integration/EisensteinJZeroSplitPrimeEisensteinCarrierExact.lean"
    "Integration/EisensteinJZeroSplitPrimeUnitNormalizationExact.lean"
    "Integration/EisensteinJZeroAllGoodPrimeLocalExact.lean"
    "Integration/EisensteinJZeroBadPrimeTwoExact.lean"
    "Integration/EisensteinJZeroBadPrimeThreeExact.lean"
    "Integration/EisensteinJZero36a1ExternalSourceReceipt.lean"
    "canonicalCubicCharacter_eq_one_iff_cube / canonicalCubicCharacter_cubeWeightedReindex"
    "cubeSubgroup_eq_orderThreeCharacterKernel / cubeWeightedReindex_of_orderThree"
    "splitJacobiSum_mul_conj / splitJacobiSum_normSq"
    "splitJacobiEisensteinElement_norm"
    "splitPrime_jZero_trace_formula"
    "splitPrimeLocalEulerPolynomial_formula"
    "goodPrimeLocalData"
    "SOURCE-WRITTEN / RED-FIRST CONTRACTED / PINNED-MATHLIB-4.28-API-AUDITED / KERNEL-PENDING"
    Attribution.leanFormalReconstruction

claimOrigin : Attribution.ClaimOrigin
claimOrigin = origin leanSplitPrimeLocalClosureReceipt

canonicalCubeFibreCertificateObserved : Bool
canonicalCubeFibreCertificateObserved = true

arbitraryOrderThreeKernelEqualsCubesObserved : Bool
arbitraryOrderThreeKernelEqualsCubesObserved = true

splitJacobiCyclotomicIntegralityObserved : Bool
splitJacobiCyclotomicIntegralityObserved = true

splitJacobiNormPrimeObserved : Bool
splitJacobiNormPrimeObserved = true

literalEisensteinQAPullbackObserved : Bool
literalEisensteinQAPullbackObserved = true

splitPrimeTraceObserved : Bool
splitPrimeTraceObserved = true

splitPrimeLocalEulerObserved : Bool
splitPrimeLocalEulerObserved = true

sixUnitNormalizationObserved : Bool
sixUnitNormalizationObserved = true

allGoodPrimeLocalClassificationObserved : Bool
allGoodPrimeLocalClassificationObserved = true

badPrimeTwoLiteralReductionObserved : Bool
badPrimeTwoLiteralReductionObserved = true

badPrimeThreeLiteralReductionObserved : Bool
badPrimeThreeLiteralReductionObserved = true

badPrimeEllipticLocalFactorsObserved : Bool
badPrimeEllipticLocalFactorsObserved = false

external36a1ProvenanceReceiptObserved : Bool
external36a1ProvenanceReceiptObserved = true

externalMetadataPromotedToProofAuthority : Bool
externalMetadataPromotedToProofAuthority = false

geometricEndomorphismDegreeNormObserved : Bool
geometricEndomorphismDegreeNormObserved = false

groessencharacterObserved : Bool
groessencharacterObserved = false

globalEulerProductAgreementObserved : Bool
globalEulerProductAgreementObserved = false

globalEllipticLSeriesAgreementObserved : Bool
globalEllipticLSeriesAgreementObserved = false

leanProofObjectImportedIntoAgda : Bool
leanProofObjectImportedIntoAgda = false

agdaSplitPrimeTheoremInhabitedFromReceipt : Bool
agdaSplitPrimeTheoremInhabitedFromReceipt = false

externalScientificSourceAcquiredByThisReceipt : Bool
externalScientificSourceAcquiredByThisReceipt = false

record LeanSplitPrimeLocalClosureAttributionBoundary : Set where
  constructor lean-split-prime-local-closure-attribution-boundary
  field
    mathlibGenericInfrastructureCredited : Bool
    dashiLeanSpecializationCredited : Bool
    externalCurveMetadataCreditedExternally : Bool
    samePrimeFormalSourceRecorded : Bool
    crossKernelProofImported : Bool
    agdaTheoremManufacturedFromReceipt : Bool
    badPrimeGoodReductionSemanticsManufactured : Bool
    geometricDegreeManufactured : Bool
    heckeAuthorityManufactured : Bool
    externalScientificAuthorityManufactured : Bool

canonicalBoundary : LeanSplitPrimeLocalClosureAttributionBoundary
canonicalBoundary =
  lean-split-prime-local-closure-attribution-boundary
    true true true true false false false false false false
