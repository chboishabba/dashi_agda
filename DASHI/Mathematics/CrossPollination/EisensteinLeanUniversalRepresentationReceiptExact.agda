module DASHI.Mathematics.CrossPollination.EisensteinLeanUniversalRepresentationReceiptExact where

------------------------------------------------------------------------
-- LEAN EISENSTEIN UNIVERSAL REPRESENTATION / L-SERIES CROSS-PROVER RECEIPT
--
-- This owner records a repository-internal formal source, not an imported Agda
-- proof term and not an external scientific source.  It follows the existing
-- cross-prover attribution discipline:
--
--   Lean formal reconstruction
--     != repository cross-module inference
--     != cross-prover replay/import
--     != Agda theorem inhabitation.
--
-- The exact Lean source currently names the positive-n coefficient theorem
--
--   geometricNormShell_eq_signedDivisorShell
--
-- and the re(s)>1 analytic factorisation
--
--   eisensteinGeometricLSeries_factorization
--
-- on dashi_lean4 PR #69.  Agda may retain this as a typed provenance/donor
-- receipt while continuing to require an independent Agda proof object before
-- claiming the corresponding theorem locally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Interop.Round11MachinCrossProverRecognitionExact as Attribution
import DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientExact as Observer

record LeanEisensteinFormalSourceReceipt : Set where
  constructor lean-eisenstein-formal-source-receipt
  field
    repository : String
    pullRequest : String
    branch : String
    commit : String
    coefficientOwner : String
    coefficientTheorem : String
    analyticOwner : String
    analyticTheorem : String
    verificationStatus : String
    origin : Attribution.ClaimOrigin

open LeanEisensteinFormalSourceReceipt public

leanEisensteinUniversalReceipt : LeanEisensteinFormalSourceReceipt
leanEisensteinUniversalReceipt =
  lean-eisenstein-formal-source-receipt
    "chboishabba/dashi_lean4"
    "PR #69"
    "agent/eisenstein-lattice-counting-maxcut-20261012"
    "c9c0b2718c08aa9294e6b8872c2e0e8a0a3bbc0f"
    "Integration/EisensteinGeometricRepresentationFormulaExact.lean"
    "geometricNormShell_eq_signedDivisorShell"
    "Integration/EisensteinDirichletSeriesExact.lean"
    "eisensteinGeometricLSeries_factorization"
    "SOURCE-WRITTEN / PINNED-MATHLIB-4.28-API-AUDITED / KERNEL-PENDING"
    Attribution.leanFormalReconstruction

leanEisensteinClaimOrigin : Attribution.ClaimOrigin
leanEisensteinClaimOrigin = origin leanEisensteinUniversalReceipt

------------------------------------------------------------------------
-- Explicit status/payment surface.
------------------------------------------------------------------------

leanUniversalCoefficientSourceObserved : Bool
leanUniversalCoefficientSourceObserved = true

leanDirichletSeriesSourceObserved : Bool
leanDirichletSeriesSourceObserved = true

leanProofObjectImportedIntoAgda : Bool
leanProofObjectImportedIntoAgda = false

agdaUniversalCoefficientTheoremInhabitedFromReceipt : Bool
agdaUniversalCoefficientTheoremInhabitedFromReceipt = false

agdaDirichletSeriesTheoremInhabitedFromReceipt : Bool
agdaDirichletSeriesTheoremInhabitedFromReceipt = false

crossProverReplayObserved : Bool
crossProverReplayObserved = false

externalScientificSourceAcquiredByThisReceipt : Bool
externalScientificSourceAcquiredByThisReceipt = false

------------------------------------------------------------------------
-- Typed donor bundle.
------------------------------------------------------------------------

record EisensteinObserverLeanDonorBundle : Set where
  constructor eisenstein-observer-lean-donor-bundle
  field
    phaseSufficiency :
      Descent.ConsumerSufficient Observer.phaseOfNat Observer.chiMinus3WeightOfNat
    leanFormalSource : LeanEisensteinFormalSourceReceipt
    coefficientTheoremImported : Bool
    analyticTheoremImported : Bool

open EisensteinObserverLeanDonorBundle public

canonicalObserverLeanDonorBundle : EisensteinObserverLeanDonorBundle
canonicalObserverLeanDonorBundle =
  eisenstein-observer-lean-donor-bundle
    Observer.phaseIsSufficientForChiMinus3
    leanEisensteinUniversalReceipt
    false
    false

------------------------------------------------------------------------
-- Cross-pollination boundary.
------------------------------------------------------------------------

record EisensteinCrossProverAttributionBoundary : Set where
  constructor eisenstein-cross-prover-attribution-boundary
  field
    leanFormalSourceRecorded : Bool
    coefficientClaimRecorded : Bool
    analyticClaimRecorded : Bool
    agdaKernelAuthorityImported : Bool
    agdaCoefficientTheoremManufactured : Bool
    agdaAnalyticTheoremManufactured : Bool
    externalSourceAuthorityManufactured : Bool

canonicalEisensteinCrossProverAttributionBoundary :
  EisensteinCrossProverAttributionBoundary
canonicalEisensteinCrossProverAttributionBoundary =
  eisenstein-cross-prover-attribution-boundary
    true
    true
    true
    false
    false
    false
    false
