module DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationBoundary where

-- Child boundary for the YM-1 Killing/full-degree boundary flux step.
--
-- This module narrows the domain contract to the concrete integration-by-parts
-- boundary mechanism needed for finite self-adjointness:
--
--   finite BT cell faces
--   full-degree/Killing boundary convention
--   oriented/opposing face flux pairing
--   gauge-domain preservation
--   induced-ball collapse exclusion
--   dependency into finite Hodge adjointness and quotient self-adjointness
--
-- It is a proof-contract boundary only.  The child records the precise rows
-- that a future proof must discharge; it does not prove flux cancellation,
-- finite self-adjointness, Hamiltonian domination, OS transfer, YM Clay, or
-- terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMAdmissibleBTBoundaryConventionBoundary
  as Admissible
import DASHI.Physics.Closure.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  as Precondition
import DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary
  as SelfAdjoint
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract
  as DomainContract
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessProxyHarnessResult
  as Harness
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Domination
import DASHI.Physics.Closure.YMSpectralMarginErrorBudgetCompositeBoundary
  as SpectralBudget

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Flux-cancellation vocabulary.

data YMKillingBoundaryFluxCancellationStatus : Set where
  killingBoundaryFluxCancellationBoundaryRecordedProofStillOpen :
    YMKillingBoundaryFluxCancellationStatus

data BTFiniteCellBoundaryFace : Set where
  interiorOrientedCodimensionOneFace :
    BTFiniteCellBoundaryFace

  killingExteriorFullDegreeFace :
    BTFiniteCellBoundaryFace

  gaugeOrbitBoundaryFace :
    BTFiniteCellBoundaryFace

  quotientRepresentativeBoundaryFace :
    BTFiniteCellBoundaryFace

canonicalBTFiniteCellBoundaryFaces :
  List BTFiniteCellBoundaryFace
canonicalBTFiniteCellBoundaryFaces =
  interiorOrientedCodimensionOneFace
  ∷ killingExteriorFullDegreeFace
  ∷ gaugeOrbitBoundaryFace
  ∷ quotientRepresentativeBoundaryFace
  ∷ []

data YMKillingBoundaryFluxPairingMechanism : Set where
  orientedFaceNormalChosen :
    YMKillingBoundaryFluxPairingMechanism

  oppositeFaceInvolutionRecorded :
    YMKillingBoundaryFluxPairingMechanism

  fullDegreeKillingWeightsMatched :
    YMKillingBoundaryFluxPairingMechanism

  finiteHodgeBoundaryTermPaired :
    YMKillingBoundaryFluxPairingMechanism

  gaugeOrbitBoundaryTermInvariant :
    YMKillingBoundaryFluxPairingMechanism

  quotientRepresentativeBoundaryResidualZero :
    YMKillingBoundaryFluxPairingMechanism

canonicalYMKillingBoundaryFluxPairingMechanisms :
  List YMKillingBoundaryFluxPairingMechanism
canonicalYMKillingBoundaryFluxPairingMechanisms =
  orientedFaceNormalChosen
  ∷ oppositeFaceInvolutionRecorded
  ∷ fullDegreeKillingWeightsMatched
  ∷ finiteHodgeBoundaryTermPaired
  ∷ gaugeOrbitBoundaryTermInvariant
  ∷ quotientRepresentativeBoundaryResidualZero
  ∷ []

data YMKillingBoundaryFluxDependency : Set where
  consumesAdmissibleFullDegreeBoundaryConvention :
    YMKillingBoundaryFluxDependency

  consumesFiniteGaugeHamiltonianPrecondition :
    YMKillingBoundaryFluxDependency

  consumesSelfAdjointFiniteHamiltonianBoundary :
    YMKillingBoundaryFluxDependency

  consumesKillingBoundaryDomainContract :
    YMKillingBoundaryFluxDependency

  consumesKillingBoundaryProxyHarnessReceipt :
    YMKillingBoundaryFluxDependency

  feedsFiniteHodgeAdjointnessBoundaryRouting :
    YMKillingBoundaryFluxDependency

  feedsGaugeDomainPreservation :
    YMKillingBoundaryFluxDependency

  feedsQuotientFiniteSelfAdjointness :
    YMKillingBoundaryFluxDependency

  feedsHamiltonianDominationOnlyAfterSelfAdjointness :
    YMKillingBoundaryFluxDependency

canonicalYMKillingBoundaryFluxDependencies :
  List YMKillingBoundaryFluxDependency
canonicalYMKillingBoundaryFluxDependencies =
  consumesAdmissibleFullDegreeBoundaryConvention
  ∷ consumesFiniteGaugeHamiltonianPrecondition
  ∷ consumesSelfAdjointFiniteHamiltonianBoundary
  ∷ consumesKillingBoundaryDomainContract
  ∷ consumesKillingBoundaryProxyHarnessReceipt
  ∷ feedsFiniteHodgeAdjointnessBoundaryRouting
  ∷ feedsGaugeDomainPreservation
  ∷ feedsQuotientFiniteSelfAdjointness
  ∷ feedsHamiltonianDominationOnlyAfterSelfAdjointness
  ∷ []

data YMKillingBoundaryFluxObligation : Set where
  defineFiniteBTCellBoundaryFaceSet :
    YMKillingBoundaryFluxObligation

  defineKillingFullDegreeFaceWeights :
    YMKillingBoundaryFluxObligation

  defineOppositeFaceInvolution :
    YMKillingBoundaryFluxObligation

  proveInvolutionIsWeightPreserving :
    YMKillingBoundaryFluxObligation

  proveOppositeNormalSignsCancel :
    YMKillingBoundaryFluxObligation

  proveFiniteHodgeIBPBoundaryResidualPairsToZero :
    YMKillingBoundaryFluxObligation

  proveGaugeActionPreservesBoundaryFacePairing :
    YMKillingBoundaryFluxObligation

  proveGaugeInvariantProjectionPreservesFluxDomain :
    YMKillingBoundaryFluxObligation

  proveQuotientRepresentativeBoundaryResidualIndependent :
    YMKillingBoundaryFluxObligation

  rejectInducedBallUnpairedExteriorFaces :
    YMKillingBoundaryFluxObligation

  routeCancellationIntoSelfAdjointnessDomainContract :
    YMKillingBoundaryFluxObligation

  keepHamiltonianDominationAndOSTransferSeparate :
    YMKillingBoundaryFluxObligation

canonicalYMKillingBoundaryFluxObligations :
  List YMKillingBoundaryFluxObligation
canonicalYMKillingBoundaryFluxObligations =
  defineFiniteBTCellBoundaryFaceSet
  ∷ defineKillingFullDegreeFaceWeights
  ∷ defineOppositeFaceInvolution
  ∷ proveInvolutionIsWeightPreserving
  ∷ proveOppositeNormalSignsCancel
  ∷ proveFiniteHodgeIBPBoundaryResidualPairsToZero
  ∷ proveGaugeActionPreservesBoundaryFacePairing
  ∷ proveGaugeInvariantProjectionPreservesFluxDomain
  ∷ proveQuotientRepresentativeBoundaryResidualIndependent
  ∷ rejectInducedBallUnpairedExteriorFaces
  ∷ routeCancellationIntoSelfAdjointnessDomainContract
  ∷ keepHamiltonianDominationAndOSTransferSeparate
  ∷ []

data YMKillingBoundaryFluxBlocker : Set where
  missingFiniteBTBoundaryFaceSet :
    YMKillingBoundaryFluxBlocker

  missingFullDegreeKillingWeightFormula :
    YMKillingBoundaryFluxBlocker

  missingOppositeFaceInvolution :
    YMKillingBoundaryFluxBlocker

  missingWeightPreservingInvolutionProof :
    YMKillingBoundaryFluxBlocker

  missingOppositeNormalCancellationProof :
    YMKillingBoundaryFluxBlocker

  missingFiniteHodgeIBPBoundaryResidualProof :
    YMKillingBoundaryFluxBlocker

  missingGaugeActionFacePairingInvariance :
    YMKillingBoundaryFluxBlocker

  missingGaugeProjectionFluxDomainInvariance :
    YMKillingBoundaryFluxBlocker

  missingQuotientRepresentativeResidualIndependence :
    YMKillingBoundaryFluxBlocker

  inducedBallExteriorFacesRemainRejected :
    YMKillingBoundaryFluxBlocker

  missingSelfAdjointnessDomainFeedThrough :
    YMKillingBoundaryFluxBlocker

  missingHamiltonianDominationTheorem :
    YMKillingBoundaryFluxBlocker

  missingOSTransferAndContinuumNoPollution :
    YMKillingBoundaryFluxBlocker

  missingClayYangMillsAuthorityToken :
    YMKillingBoundaryFluxBlocker

canonicalYMKillingBoundaryFluxBlockers :
  List YMKillingBoundaryFluxBlocker
canonicalYMKillingBoundaryFluxBlockers =
  missingFiniteBTBoundaryFaceSet
  ∷ missingFullDegreeKillingWeightFormula
  ∷ missingOppositeFaceInvolution
  ∷ missingWeightPreservingInvolutionProof
  ∷ missingOppositeNormalCancellationProof
  ∷ missingFiniteHodgeIBPBoundaryResidualProof
  ∷ missingGaugeActionFacePairingInvariance
  ∷ missingGaugeProjectionFluxDomainInvariance
  ∷ missingQuotientRepresentativeResidualIndependence
  ∷ inducedBallExteriorFacesRemainRejected
  ∷ missingSelfAdjointnessDomainFeedThrough
  ∷ missingHamiltonianDominationTheorem
  ∷ missingOSTransferAndContinuumNoPollution
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

record YMKillingBoundaryFluxObligationRow : Set where
  field
    obligation :
      YMKillingBoundaryFluxObligation

    label :
      String

    contractText :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open YMKillingBoundaryFluxObligationRow public

mkYMKillingBoundaryFluxObligationRow :
  YMKillingBoundaryFluxObligation →
  String →
  String →
  YMKillingBoundaryFluxObligationRow
mkYMKillingBoundaryFluxObligationRow obligation label contractText =
  record
    { obligation =
        obligation
    ; label =
        label
    ; contractText =
        contractText
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    }

canonicalYMKillingBoundaryFluxObligationRows :
  List YMKillingBoundaryFluxObligationRow
canonicalYMKillingBoundaryFluxObligationRows =
  mkYMKillingBoundaryFluxObligationRow
    defineFiniteBTCellBoundaryFaceSet
    "finite BT faces"
    "Define the oriented codimension-one face set for the finite BT cell complex used by the Killing-boundary Hamiltonian domain."
  ∷ mkYMKillingBoundaryFluxObligationRow
    defineKillingFullDegreeFaceWeights
    "Killing weights"
    "Assign full-degree/Killing weights to every exterior face so the boundary degree is inherited from the ambient BT building, not from the induced finite ball."
  ∷ mkYMKillingBoundaryFluxObligationRow
    defineOppositeFaceInvolution
    "opposing faces"
    "Construct an involution pairing each oriented face with the oppositely oriented full-degree face contributing the cancelling flux term."
  ∷ mkYMKillingBoundaryFluxObligationRow
    proveInvolutionIsWeightPreserving
    "weight preservation"
    "Prove the opposite-face involution preserves Killing/full-degree weights and local gauge representation weights."
  ∷ mkYMKillingBoundaryFluxObligationRow
    proveOppositeNormalSignsCancel
    "normal signs"
    "Prove paired oriented normals have opposite sign in the finite integration-by-parts boundary residual."
  ∷ mkYMKillingBoundaryFluxObligationRow
    proveFiniteHodgeIBPBoundaryResidualPairsToZero
    "Hodge residual"
    "Show the finite d_A / d_A* boundary residual is a sum over paired faces whose two terms cancel exactly."
  ∷ mkYMKillingBoundaryFluxObligationRow
    proveGaugeActionPreservesBoundaryFacePairing
    "gauge action"
    "Show finite gauge transformations send paired boundary faces to paired boundary faces and preserve the Killing boundary convention."
  ∷ mkYMKillingBoundaryFluxObligationRow
    proveGaugeInvariantProjectionPreservesFluxDomain
    "gauge projection"
    "Show the gauge-invariant projection maps the flux-cancellation domain into itself."
  ∷ mkYMKillingBoundaryFluxObligationRow
    proveQuotientRepresentativeBoundaryResidualIndependent
    "quotient residual"
    "Show changing representatives inside a finite gauge orbit does not change the paired boundary residual."
  ∷ mkYMKillingBoundaryFluxObligationRow
    rejectInducedBallUnpairedExteriorFaces
    "induced exclusion"
    "Record that induced-ball exterior faces are not accepted here because the diagnostic route observed unpaired exterior leakage and spectral collapse risk."
  ∷ mkYMKillingBoundaryFluxObligationRow
    routeCancellationIntoSelfAdjointnessDomainContract
    "self-adjoint input"
    "Feed the completed flux cancellation only into the YM-1 domain/self-adjointness contract, not directly into Hamiltonian domination."
  ∷ mkYMKillingBoundaryFluxObligationRow
    keepHamiltonianDominationAndOSTransferSeparate
    "promotion guard"
    "Keep Hamiltonian domination, reflection positivity, OS transfer, continuum no-pollution, YM Clay, and terminal promotion separate and false."
  ∷ []

------------------------------------------------------------------------
-- Boundary flags.

boundaryRecorded : Bool
boundaryRecorded =
  true

admissibleBoundaryImported : Bool
admissibleBoundaryImported =
  true

domainContractImported : Bool
domainContractImported =
  true

proxyHarnessImported : Bool
proxyHarnessImported =
  true

fullDegreeKillingConventionConsumed : Bool
fullDegreeKillingConventionConsumed =
  true

inducedBallExcludedAsFluxCarrier : Bool
inducedBallExcludedAsFluxCarrier =
  true

finiteBTBoundaryFacesDefined : Bool
finiteBTBoundaryFacesDefined =
  false

oppositeFaceInvolutionProved : Bool
oppositeFaceInvolutionProved =
  false

killingWeightPreservationProved : Bool
killingWeightPreservationProved =
  false

oppositeNormalFluxCancellationProved : Bool
oppositeNormalFluxCancellationProved =
  false

finiteHodgeBoundaryResidualCancelled : Bool
finiteHodgeBoundaryResidualCancelled =
  false

gaugeDomainPreservationProved : Bool
gaugeDomainPreservationProved =
  false

quotientFluxResidualIndependenceProved : Bool
quotientFluxResidualIndependenceProved =
  false

selfAdjointnessFeedThroughProved : Bool
selfAdjointnessFeedThroughProved =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

osContinuumTransferProved : Bool
osContinuumTransferProved =
  false

ymClayPromoted : Bool
ymClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

boundaryRecordedIsTrue :
  boundaryRecorded ≡ true
boundaryRecordedIsTrue =
  refl

admissibleBoundaryImportedIsTrue :
  admissibleBoundaryImported ≡ true
admissibleBoundaryImportedIsTrue =
  refl

domainContractImportedIsTrue :
  domainContractImported ≡ true
domainContractImportedIsTrue =
  refl

proxyHarnessImportedIsTrue :
  proxyHarnessImported ≡ true
proxyHarnessImportedIsTrue =
  refl

fullDegreeKillingConventionConsumedIsTrue :
  fullDegreeKillingConventionConsumed ≡ true
fullDegreeKillingConventionConsumedIsTrue =
  refl

inducedBallExcludedAsFluxCarrierIsTrue :
  inducedBallExcludedAsFluxCarrier ≡ true
inducedBallExcludedAsFluxCarrierIsTrue =
  refl

finiteBTBoundaryFacesDefinedIsFalse :
  finiteBTBoundaryFacesDefined ≡ false
finiteBTBoundaryFacesDefinedIsFalse =
  refl

oppositeFaceInvolutionProvedIsFalse :
  oppositeFaceInvolutionProved ≡ false
oppositeFaceInvolutionProvedIsFalse =
  refl

killingWeightPreservationProvedIsFalse :
  killingWeightPreservationProved ≡ false
killingWeightPreservationProvedIsFalse =
  refl

oppositeNormalFluxCancellationProvedIsFalse :
  oppositeNormalFluxCancellationProved ≡ false
oppositeNormalFluxCancellationProvedIsFalse =
  refl

finiteHodgeBoundaryResidualCancelledIsFalse :
  finiteHodgeBoundaryResidualCancelled ≡ false
finiteHodgeBoundaryResidualCancelledIsFalse =
  refl

gaugeDomainPreservationProvedIsFalse :
  gaugeDomainPreservationProved ≡ false
gaugeDomainPreservationProvedIsFalse =
  refl

quotientFluxResidualIndependenceProvedIsFalse :
  quotientFluxResidualIndependenceProved ≡ false
quotientFluxResidualIndependenceProvedIsFalse =
  refl

selfAdjointnessFeedThroughProvedIsFalse :
  selfAdjointnessFeedThroughProved ≡ false
selfAdjointnessFeedThroughProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

osContinuumTransferProvedIsFalse :
  osContinuumTransferProved ≡ false
osContinuumTransferProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

fluxCancellationFormula : String
fluxCancellationFormula =
  "sum_{F in boundary cells} Flux(F) + Flux(opposite(F)) = 0 under full-degree/Killing weights"

selfAdjointnessDependencyFormula : String
selfAdjointnessDependencyFormula =
  "boundary flux cancellation -> finite Hodge adjointness -> quotient symmetric matrix -> finite self-adjoint Hamiltonian"

------------------------------------------------------------------------
-- Canonical child boundary receipt.

record YMKillingBoundaryFluxCancellationBoundary : Setω where
  field
    status :
      YMKillingBoundaryFluxCancellationStatus

    admissibleBoundary :
      Admissible.YMAdmissibleBTBoundaryConventionBoundary

    admissibleBoundaryCanonical :
      Bool

    admissibleBoundaryCanonicalIsTrue :
      admissibleBoundaryCanonical ≡ true

    finiteGaugePrecondition :
      Precondition.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary

    finiteGaugePreconditionCanonical :
      Bool

    finiteGaugePreconditionCanonicalIsTrue :
      finiteGaugePreconditionCanonical ≡ true

    finiteSelfAdjointBoundary :
      SelfAdjoint.YMSelfAdjointFiniteHamiltonianBoundary

    finiteSelfAdjointBoundaryCanonical :
      Bool

    finiteSelfAdjointBoundaryCanonicalIsTrue :
      finiteSelfAdjointBoundaryCanonical ≡ true

    domainContract :
      DomainContract.YMKillingBoundarySelfAdjointnessDomainContract

    domainContractCanonical :
      Bool

    domainContractCanonicalIsTrue :
      domainContractCanonical ≡ true

    proxyHarnessImportedReceipt :
      Bool

    proxyHarnessImportedReceiptIsTrue :
      proxyHarnessImportedReceipt ≡ true

    faces :
      List BTFiniteCellBoundaryFace

    facesAreCanonical :
      faces ≡ canonicalBTFiniteCellBoundaryFaces

    faceCount :
      Nat

    faceCountIs4 :
      faceCount ≡ 4

    pairingMechanisms :
      List YMKillingBoundaryFluxPairingMechanism

    pairingMechanismsAreCanonical :
      pairingMechanisms ≡ canonicalYMKillingBoundaryFluxPairingMechanisms

    pairingMechanismCount :
      Nat

    pairingMechanismCountIs6 :
      pairingMechanismCount ≡ 6

    dependencies :
      List YMKillingBoundaryFluxDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalYMKillingBoundaryFluxDependencies

    dependencyCount :
      Nat

    dependencyCountIs9 :
      dependencyCount ≡ 9

    obligations :
      List YMKillingBoundaryFluxObligation

    obligationsAreCanonical :
      obligations ≡ canonicalYMKillingBoundaryFluxObligations

    obligationCount :
      Nat

    obligationCountIs12 :
      obligationCount ≡ 12

    obligationRows :
      List YMKillingBoundaryFluxObligationRow

    obligationRowsAreCanonical :
      obligationRows ≡ canonicalYMKillingBoundaryFluxObligationRows

    obligationRowCount :
      Nat

    obligationRowCountIs12 :
      obligationRowCount ≡ 12

    blockers :
      List YMKillingBoundaryFluxBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMKillingBoundaryFluxBlockers

    blockerCount :
      Nat

    blockerCountIs14 :
      blockerCount ≡ 14

    firstBlocker :
      YMKillingBoundaryFluxBlocker

    firstBlockerIsMissingFaceSet :
      firstBlocker ≡ missingFiniteBTBoundaryFaceSet

    formula :
      String

    formulaIsCanonical :
      formula ≡ fluxCancellationFormula

    dependencyFormula :
      String

    dependencyFormulaIsCanonical :
      dependencyFormula ≡ selfAdjointnessDependencyFormula

    boundaryRecordedField :
      Bool

    boundaryRecordedFieldIsTrue :
      boundaryRecordedField ≡ true

    fullDegreeKillingConventionConsumedField :
      Bool

    fullDegreeKillingConventionConsumedFieldIsTrue :
      fullDegreeKillingConventionConsumedField ≡ true

    inducedBallExcludedAsFluxCarrierField :
      Bool

    inducedBallExcludedAsFluxCarrierFieldIsTrue :
      inducedBallExcludedAsFluxCarrierField ≡ true

    finiteBTBoundaryFacesDefinedField :
      Bool

    finiteBTBoundaryFacesDefinedFieldIsFalse :
      finiteBTBoundaryFacesDefinedField ≡ false

    oppositeFaceInvolutionProvedField :
      Bool

    oppositeFaceInvolutionProvedFieldIsFalse :
      oppositeFaceInvolutionProvedField ≡ false

    killingWeightPreservationProvedField :
      Bool

    killingWeightPreservationProvedFieldIsFalse :
      killingWeightPreservationProvedField ≡ false

    oppositeNormalFluxCancellationProvedField :
      Bool

    oppositeNormalFluxCancellationProvedFieldIsFalse :
      oppositeNormalFluxCancellationProvedField ≡ false

    finiteHodgeBoundaryResidualCancelledField :
      Bool

    finiteHodgeBoundaryResidualCancelledFieldIsFalse :
      finiteHodgeBoundaryResidualCancelledField ≡ false

    gaugeDomainPreservationProvedField :
      Bool

    gaugeDomainPreservationProvedFieldIsFalse :
      gaugeDomainPreservationProvedField ≡ false

    quotientFluxResidualIndependenceProvedField :
      Bool

    quotientFluxResidualIndependenceProvedFieldIsFalse :
      quotientFluxResidualIndependenceProvedField ≡ false

    selfAdjointnessFeedThroughProvedField :
      Bool

    selfAdjointnessFeedThroughProvedFieldIsFalse :
      selfAdjointnessFeedThroughProvedField ≡ false

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsFalse :
      hamiltonianDominationProvedField ≡ false

    osContinuumTransferProvedField :
      Bool

    osContinuumTransferProvedFieldIsFalse :
      osContinuumTransferProvedField ≡ false

    ymClayPromotedField :
      Bool

    ymClayPromotedFieldIsFalse :
      ymClayPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    importedInducedBallStillRejected :
      Admissible.inducedBallAcceptedAsCurrentGapCarrierField
        admissibleBoundary
      ≡
      false

    importedPreconditionFiniteQuotientStillMissing :
      Precondition.finiteQuotientConstructedField
        finiteGaugePrecondition
      ≡
      false

    importedPreconditionSelfAdjointStillMissing :
      Precondition.selfAdjointHamiltonianProvedField
        finiteGaugePrecondition
      ≡
      false

    importedSelfAdjointBoundaryStillOpen :
      SelfAdjoint.selfAdjointFiniteHamiltonianProvedField
        finiteSelfAdjointBoundary
      ≡
      false

    importedDomainContractFluxStillOpen :
      DomainContract.boundaryFluxCancellationProvedField
        domainContract
      ≡
      false

    importedDomainContractSelfAdjointStillOpen :
      DomainContract.selfAdjointQuotientHamiltonianProvedField
        domainContract
      ≡
      false

    importedHarnessDiagnosticOnly :
      Harness.ym1KillingBoundarySelfAdjointnessProved ≡ false

    importedDominationStillOpen :
      Domination.dominationPlusHolonomyProvedField
        Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
      ≡
      false

    importedSpectralMarginStillOpen :
      SpectralBudget.spectralMarginTheoremProved
        SpectralBudget.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
      ≡
      false

    notes :
      List String

open YMKillingBoundaryFluxCancellationBoundary public

canonicalYMKillingBoundaryFluxCancellationBoundary :
  YMKillingBoundaryFluxCancellationBoundary
canonicalYMKillingBoundaryFluxCancellationBoundary =
  record
    { status =
        killingBoundaryFluxCancellationBoundaryRecordedProofStillOpen
    ; admissibleBoundary =
        Admissible.canonicalYMAdmissibleBTBoundaryConventionBoundary
    ; admissibleBoundaryCanonical =
        true
    ; admissibleBoundaryCanonicalIsTrue =
        refl
    ; finiteGaugePrecondition =
        Precondition.canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
    ; finiteGaugePreconditionCanonical =
        true
    ; finiteGaugePreconditionCanonicalIsTrue =
        refl
    ; finiteSelfAdjointBoundary =
        SelfAdjoint.canonicalYMSelfAdjointFiniteHamiltonianBoundary
    ; finiteSelfAdjointBoundaryCanonical =
        true
    ; finiteSelfAdjointBoundaryCanonicalIsTrue =
        refl
    ; domainContract =
        DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; domainContractCanonical =
        true
    ; domainContractCanonicalIsTrue =
        refl
    ; proxyHarnessImportedReceipt =
        true
    ; proxyHarnessImportedReceiptIsTrue =
        refl
    ; faces =
        canonicalBTFiniteCellBoundaryFaces
    ; facesAreCanonical =
        refl
    ; faceCount =
        listCount canonicalBTFiniteCellBoundaryFaces
    ; faceCountIs4 =
        refl
    ; pairingMechanisms =
        canonicalYMKillingBoundaryFluxPairingMechanisms
    ; pairingMechanismsAreCanonical =
        refl
    ; pairingMechanismCount =
        listCount canonicalYMKillingBoundaryFluxPairingMechanisms
    ; pairingMechanismCountIs6 =
        refl
    ; dependencies =
        canonicalYMKillingBoundaryFluxDependencies
    ; dependenciesAreCanonical =
        refl
    ; dependencyCount =
        listCount canonicalYMKillingBoundaryFluxDependencies
    ; dependencyCountIs9 =
        refl
    ; obligations =
        canonicalYMKillingBoundaryFluxObligations
    ; obligationsAreCanonical =
        refl
    ; obligationCount =
        listCount canonicalYMKillingBoundaryFluxObligations
    ; obligationCountIs12 =
        refl
    ; obligationRows =
        canonicalYMKillingBoundaryFluxObligationRows
    ; obligationRowsAreCanonical =
        refl
    ; obligationRowCount =
        listCount canonicalYMKillingBoundaryFluxObligationRows
    ; obligationRowCountIs12 =
        refl
    ; blockers =
        canonicalYMKillingBoundaryFluxBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMKillingBoundaryFluxBlockers
    ; blockerCountIs14 =
        refl
    ; firstBlocker =
        missingFiniteBTBoundaryFaceSet
    ; firstBlockerIsMissingFaceSet =
        refl
    ; formula =
        fluxCancellationFormula
    ; formulaIsCanonical =
        refl
    ; dependencyFormula =
        selfAdjointnessDependencyFormula
    ; dependencyFormulaIsCanonical =
        refl
    ; boundaryRecordedField =
        boundaryRecorded
    ; boundaryRecordedFieldIsTrue =
        boundaryRecordedIsTrue
    ; fullDegreeKillingConventionConsumedField =
        fullDegreeKillingConventionConsumed
    ; fullDegreeKillingConventionConsumedFieldIsTrue =
        fullDegreeKillingConventionConsumedIsTrue
    ; inducedBallExcludedAsFluxCarrierField =
        inducedBallExcludedAsFluxCarrier
    ; inducedBallExcludedAsFluxCarrierFieldIsTrue =
        inducedBallExcludedAsFluxCarrierIsTrue
    ; finiteBTBoundaryFacesDefinedField =
        finiteBTBoundaryFacesDefined
    ; finiteBTBoundaryFacesDefinedFieldIsFalse =
        finiteBTBoundaryFacesDefinedIsFalse
    ; oppositeFaceInvolutionProvedField =
        oppositeFaceInvolutionProved
    ; oppositeFaceInvolutionProvedFieldIsFalse =
        oppositeFaceInvolutionProvedIsFalse
    ; killingWeightPreservationProvedField =
        killingWeightPreservationProved
    ; killingWeightPreservationProvedFieldIsFalse =
        killingWeightPreservationProvedIsFalse
    ; oppositeNormalFluxCancellationProvedField =
        oppositeNormalFluxCancellationProved
    ; oppositeNormalFluxCancellationProvedFieldIsFalse =
        oppositeNormalFluxCancellationProvedIsFalse
    ; finiteHodgeBoundaryResidualCancelledField =
        finiteHodgeBoundaryResidualCancelled
    ; finiteHodgeBoundaryResidualCancelledFieldIsFalse =
        finiteHodgeBoundaryResidualCancelledIsFalse
    ; gaugeDomainPreservationProvedField =
        gaugeDomainPreservationProved
    ; gaugeDomainPreservationProvedFieldIsFalse =
        gaugeDomainPreservationProvedIsFalse
    ; quotientFluxResidualIndependenceProvedField =
        quotientFluxResidualIndependenceProved
    ; quotientFluxResidualIndependenceProvedFieldIsFalse =
        quotientFluxResidualIndependenceProvedIsFalse
    ; selfAdjointnessFeedThroughProvedField =
        selfAdjointnessFeedThroughProved
    ; selfAdjointnessFeedThroughProvedFieldIsFalse =
        selfAdjointnessFeedThroughProvedIsFalse
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsFalse =
        hamiltonianDominationProvedIsFalse
    ; osContinuumTransferProvedField =
        osContinuumTransferProved
    ; osContinuumTransferProvedFieldIsFalse =
        osContinuumTransferProvedIsFalse
    ; ymClayPromotedField =
        ymClayPromoted
    ; ymClayPromotedFieldIsFalse =
        ymClayPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; importedInducedBallStillRejected =
        Admissible.inducedBallAcceptedAsCurrentGapCarrierIsFalse
    ; importedPreconditionFiniteQuotientStillMissing =
        Precondition.canonicalFiniteQuotientConstructedFalse
    ; importedPreconditionSelfAdjointStillMissing =
        Precondition.canonicalSelfAdjointHamiltonianProvedFalse
    ; importedSelfAdjointBoundaryStillOpen =
        SelfAdjoint.canonicalSelfAdjointFiniteHamiltonianProvedFalse
    ; importedDomainContractFluxStillOpen =
        DomainContract.boundaryFluxCancellationProvedFieldIsFalse
          DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; importedDomainContractSelfAdjointStillOpen =
        DomainContract.canonicalKillingBoundaryDomainSelfAdjointStillFalse
    ; importedHarnessDiagnosticOnly =
        Harness.ym1KillingBoundarySelfAdjointnessProvedIsFalse
    ; importedDominationStillOpen =
        Domination.canonicalYMHamiltonianDominationPlusHolonomyProvedFalse
    ; importedSpectralMarginStillOpen =
        SpectralBudget.spectralMarginTheoremProvedIsFalse
    ; notes =
        "The Killing/full-degree convention must pair every oriented BT boundary face with an opposite weighted face before finite Hodge adjointness can use integration by parts."
        ∷ "Gauge transformations must preserve the paired-face domain and the gauge-invariant projection must keep states inside the same flux-cancellation domain."
        ∷ "Induced-ball boundary conventions remain excluded as current flux carriers because the finite diagnostics record unpaired exterior leakage and gap-collapse risk."
        ∷ "Flux cancellation is a child dependency of YM-1 only; it does not by itself prove quotient self-adjointness, Hamiltonian domination, OS transfer, continuum no-pollution, YM Clay, or terminal promotion."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalKillingBoundaryFluxFaceCountIs4 :
  faceCount canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  4
canonicalKillingBoundaryFluxFaceCountIs4 =
  refl

canonicalKillingBoundaryFluxDependencyCountIs9 :
  dependencyCount canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  9
canonicalKillingBoundaryFluxDependencyCountIs9 =
  refl

canonicalKillingBoundaryFluxObligationCountIs12 :
  obligationCount canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  12
canonicalKillingBoundaryFluxObligationCountIs12 =
  refl

canonicalKillingBoundaryFluxFirstBlocker :
  firstBlocker canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  missingFiniteBTBoundaryFaceSet
canonicalKillingBoundaryFluxFirstBlocker =
  refl

canonicalKillingBoundaryFluxCancellationStillFalse :
  oppositeNormalFluxCancellationProvedField
    canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  false
canonicalKillingBoundaryFluxCancellationStillFalse =
  refl

canonicalKillingBoundaryFluxHodgeResidualStillFalse :
  finiteHodgeBoundaryResidualCancelledField
    canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  false
canonicalKillingBoundaryFluxHodgeResidualStillFalse =
  refl

canonicalKillingBoundaryFluxGaugeDomainStillFalse :
  gaugeDomainPreservationProvedField
    canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  false
canonicalKillingBoundaryFluxGaugeDomainStillFalse =
  refl

canonicalKillingBoundaryFluxSelfAdjointFeedStillFalse :
  selfAdjointnessFeedThroughProvedField
    canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  false
canonicalKillingBoundaryFluxSelfAdjointFeedStillFalse =
  refl

canonicalKillingBoundaryFluxDominationStillFalse :
  hamiltonianDominationProvedField
    canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  false
canonicalKillingBoundaryFluxDominationStillFalse =
  refl

canonicalKillingBoundaryFluxYMClayStillFalse :
  ymClayPromotedField
    canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  false
canonicalKillingBoundaryFluxYMClayStillFalse =
  refl

canonicalKillingBoundaryFluxTerminalStillFalse :
  terminalPromotionField
    canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  false
canonicalKillingBoundaryFluxTerminalStillFalse =
  refl

data YMKillingBoundaryFluxPromotionToken : Set where

ymKillingBoundaryFluxPromotionTokenImpossibleHere :
  YMKillingBoundaryFluxPromotionToken →
  ⊥
ymKillingBoundaryFluxPromotionTokenImpossibleHere ()

noFluxCancellationPromotionFromBoundaryRecordAlone :
  oppositeNormalFluxCancellationProvedField
    canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  true →
  ⊥
noFluxCancellationPromotionFromBoundaryRecordAlone ()

noSelfAdjointnessPromotionFromFluxBoundaryAlone :
  selfAdjointnessFeedThroughProvedField
    canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  true →
  ⊥
noSelfAdjointnessPromotionFromFluxBoundaryAlone ()

noYMClayPromotionFromFluxBoundaryAlone :
  ymClayPromotedField canonicalYMKillingBoundaryFluxCancellationBoundary
  ≡
  true →
  ⊥
noYMClayPromotionFromFluxBoundaryAlone ()
