module DASHI.Physics.Closure.YMSprint102ProofObligationIndexReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint101ClayBoundaryReconciliationReceipt
  as Sprint101

------------------------------------------------------------------------
-- Sprint 102 YM proof-obligation index.
--
-- This module does not strengthen the Sprint 91-101 candidate chain.  It
-- records the distinction requested by the current audit:
--
--   * receipt/interface surfaces are present in repo;
--   * the corresponding analytic proofs are still not present unless stated;
--   * Clay/YM promotion remains false.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

receiptLayerAvailable : Bool
receiptLayerAvailable = true

analyticProofLayerComplete : Bool
analyticProofLayerComplete = false

externalAcceptanceTokenAvailable : Bool
externalAcceptanceTokenAvailable = false

record ProofObligationStatus : Set where
  constructor mkProofObligationStatus
  field
    lemmaName :
      String
    existsInRepoAsReceiptOrInterface :
      Bool
    analyticProofInRepo :
      Bool
    obligationKind :
      String
    nextRequiredMove :
      String

balabanCMP98LocalOscillationStatus : ProofObligationStatus
balabanCMP98LocalOscillationStatus =
  mkProofObligationStatus
    "BalabanCMP98LocalOscillationBound"
    true
    false
    "scoped authority / analytic local-estimate formalisation"
    "Formalise the CMP98 local oscillation estimate for Q_hp as an inhabited authority record, not only as roadmap prose."

balabanCMP98KernelProbabilityStatus : ProofObligationStatus
balabanCMP98KernelProbabilityStatus =
  mkProofObligationStatus
    "BalabanCMP98AveragingKernelIsProbability"
    true
    false
    "scoped authority import"
    "Inhabit the CMP98 Haar-convolution probability interface giving C_avg <= 1."

balabanCMP116PolymerMassStatus : ProofObligationStatus
balabanCMP116PolymerMassStatus =
  mkProofObligationStatus
    "BalabanCMP116PolymerMassBound"
    true
    false
    "scoped authority import"
    "Inhabit the CMP116 small-field polymer mass positivity interface."

gaugeCovariantDobrushinStatus : ProofObligationStatus
gaugeCovariantDobrushinStatus =
  mkProofObligationStatus
    "GaugeCovariantDobrushinComparison"
    true
    false
    "new DASHI analytic theorem"
    "Turn the Sprint 91 Cauchy-Schwarz architecture and Sprint 92/93 constants into a gauge-covariant Dobrushin contraction proof."

uniformPolymerActivityStatus : ProofObligationStatus
uniformPolymerActivityStatus =
  mkProofObligationStatus
    "UniformPolymerActivityFromDobrushin"
    true
    false
    "analytic quantifier exchange"
    "Derive uniform physical-diameter polymer activity constants from the Dobrushin contraction."

wc3UniformClusterStatus : ProofObligationStatus
wc3UniformClusterStatus =
  mkProofObligationStatus
    "WC3UniformClusterSummability"
    true
    false
    "uniform cluster expansion theorem"
    "Upgrade the eta=4 KP arithmetic and uniform activity bound into a full WC3 summability proof."

continuumLimitMassGapStatus : ProofObligationStatus
continuumLimitMassGapStatus =
  mkProofObligationStatus
    "ContinuumLimitMassGap"
    true
    false
    "new RG/transfer-matrix continuum theorem"
    "Prove the RG-generated physical mass survives the continuum limit via the transfer-gap/effective-mass comparison."

nontrivialSU3MeasureStatus : ProofObligationStatus
nontrivialSU3MeasureStatus =
  mkProofObligationStatus
    "Nontrivial4DSU3YangMillsMeasure"
    true
    false
    "continuum measure non-Gaussianity formalisation"
    "Formalise the SU(3) non-Abelian curvature/self-interaction witness as a continuum-measure nontriviality proof."

record RemainingAnalyticProofObligations : Set where
  constructor mkRemainingAnalyticProofObligations
  field
    cmp98LocalOscillation :
      ProofObligationStatus
    cmp98KernelProbability :
      ProofObligationStatus
    cmp116PolymerMass :
      ProofObligationStatus
    gaugeCovariantDobrushinComparison :
      ProofObligationStatus
    uniformPolymerActivityFromDobrushin :
      ProofObligationStatus
    wc3UniformClusterSummability :
      ProofObligationStatus
    continuumLimitMassGap :
      ProofObligationStatus
    nontrivial4DSU3YangMillsMeasure :
      ProofObligationStatus

canonicalRemainingAnalyticProofObligations :
  RemainingAnalyticProofObligations
canonicalRemainingAnalyticProofObligations =
  mkRemainingAnalyticProofObligations
    balabanCMP98LocalOscillationStatus
    balabanCMP98KernelProbabilityStatus
    balabanCMP116PolymerMassStatus
    gaugeCovariantDobrushinStatus
    uniformPolymerActivityStatus
    wc3UniformClusterStatus
    continuumLimitMassGapStatus
    nontrivialSU3MeasureStatus

record ExternalAcceptanceBoundaryStatus : Set where
  constructor mkExternalAcceptanceBoundaryStatus
  field
    tokenName :
      String
    availableInsideRepo :
      Bool
    selfIssuableByRepo :
      Bool
    boundaryStatement :
      String

canonicalExternalAcceptanceBoundaryStatus :
  ExternalAcceptanceBoundaryStatus
canonicalExternalAcceptanceBoundaryStatus =
  mkExternalAcceptanceBoundaryStatus
    "ExternalAcceptanceToken"
    false
    false
    "External acceptance is a governance/review artifact, not an Agda proof object the repo can self-issue."

record YMSprint102ProofObligationIndexReceipt : Set₁ where
  field
    sprint101Boundary :
      Sprint101.YMSprint101ClayBoundaryReconciliationReceipt
    remainingAnalyticObligations :
      RemainingAnalyticProofObligations
    externalAcceptanceBoundary :
      ExternalAcceptanceBoundaryStatus
    receiptLayerPresent :
      receiptLayerAvailable ≡ true
    analyticProofLayerStillIncomplete :
      analyticProofLayerComplete ≡ false
    externalAcceptanceUnavailable :
      externalAcceptanceTokenAvailable ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint102ProofObligationIndexReceipt :
  YMSprint102ProofObligationIndexReceipt
canonicalYMSprint102ProofObligationIndexReceipt =
  record
    { sprint101Boundary =
        Sprint101.canonicalYMSprint101ClayBoundaryReconciliationReceipt
    ; remainingAnalyticObligations =
        canonicalRemainingAnalyticProofObligations
    ; externalAcceptanceBoundary =
        canonicalExternalAcceptanceBoundaryStatus
    ; receiptLayerPresent =
        refl
    ; analyticProofLayerStillIncomplete =
        refl
    ; externalAcceptanceUnavailable =
        refl
    ; noClayPromotion =
        refl
    }
