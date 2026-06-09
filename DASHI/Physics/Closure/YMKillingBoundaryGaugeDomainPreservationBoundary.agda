module DASHI.Physics.Closure.YMKillingBoundaryGaugeDomainPreservationBoundary where

-- YM-1 gauge-domain preservation boundary for the Killing/full-degree
-- finite boundary domain.
--
-- This module is a boundary receipt only.  It consumes the current
-- Killing-boundary flux-cancellation, weight-preservation, and
-- self-adjointness domain-contract surfaces, then records the remaining
-- gauge-domain preservation split:
--
--   domain preservation under finite gauge action
--   quotient descent of the Killing/full-degree domain
--   no spurious gauge-zero mode on the quotient
--   self-adjointness consumer routing
--
-- It does not prove YM-1, finite self-adjointness, Hamiltonian domination,
-- OS transfer, YM Clay, or terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationBoundary
  as Flux
import DASHI.Physics.Closure.YMKillingBoundaryWeightPreservationBoundary
  as Weight
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract
  as Domain
import DASHI.Physics.Closure.YMGaugeZeroModeVacuumRigidityBoundary
  as ZeroMode

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

data YMKillingBoundaryGaugeDomainImportedSupport : Set where
  killingBoundaryFluxCancellationImported :
    YMKillingBoundaryGaugeDomainImportedSupport

  killingBoundaryWeightPreservationImported :
    YMKillingBoundaryGaugeDomainImportedSupport

  killingBoundarySelfAdjointnessDomainContractImported :
    YMKillingBoundaryGaugeDomainImportedSupport

  gaugeZeroModeVacuumRigidityImportedAsGuard :
    YMKillingBoundaryGaugeDomainImportedSupport

canonicalYMKillingBoundaryGaugeDomainImportedSupport :
  List YMKillingBoundaryGaugeDomainImportedSupport
canonicalYMKillingBoundaryGaugeDomainImportedSupport =
  killingBoundaryFluxCancellationImported
  ∷ killingBoundaryWeightPreservationImported
  ∷ killingBoundarySelfAdjointnessDomainContractImported
  ∷ gaugeZeroModeVacuumRigidityImportedAsGuard
  ∷ []

------------------------------------------------------------------------
-- Four separated surfaces.

data GaugeDomainPreservationSurface : Set where
  finiteGaugeActionPreservesKillingFaces :
    GaugeDomainPreservationSurface

  finiteGaugeActionPreservesFullDegreeWeights :
    GaugeDomainPreservationSurface

  finiteGaugeActionPreservesPairedFluxDomain :
    GaugeDomainPreservationSurface

  finiteGaugeProjectionPreservesBoundaryConditions :
    GaugeDomainPreservationSurface

canonicalGaugeDomainPreservationSurfaces :
  List GaugeDomainPreservationSurface
canonicalGaugeDomainPreservationSurfaces =
  finiteGaugeActionPreservesKillingFaces
  ∷ finiteGaugeActionPreservesFullDegreeWeights
  ∷ finiteGaugeActionPreservesPairedFluxDomain
  ∷ finiteGaugeProjectionPreservesBoundaryConditions
  ∷ []

data QuotientDescentSurface : Set where
  quotientRepresentativeIndependenceOfDomain :
    QuotientDescentSurface

  quotientRepresentativeIndependenceOfWeights :
    QuotientDescentSurface

  quotientRepresentativeIndependenceOfFluxResidual :
    QuotientDescentSurface

  quotientHamiltonianActionWellDefined :
    QuotientDescentSurface

canonicalQuotientDescentSurfaces :
  List QuotientDescentSurface
canonicalQuotientDescentSurfaces =
  quotientRepresentativeIndependenceOfDomain
  ∷ quotientRepresentativeIndependenceOfWeights
  ∷ quotientRepresentativeIndependenceOfFluxResidual
  ∷ quotientHamiltonianActionWellDefined
  ∷ []

data NoSpuriousGaugeZeroModeSurface : Set where
  gaugeOrbitTangentModesQuotiented :
    NoSpuriousGaugeZeroModeSurface

  vacuumFlatTrivialModesRemainClassified :
    NoSpuriousGaugeZeroModeSurface

  nonVacuumTopologicalSectorsRequirePositiveEnergy :
    NoSpuriousGaugeZeroModeSurface

  zeroEnergyGaugeCompatibleModesDoNotComeFromBoundaryLeakage :
    NoSpuriousGaugeZeroModeSurface

canonicalNoSpuriousGaugeZeroModeSurfaces :
  List NoSpuriousGaugeZeroModeSurface
canonicalNoSpuriousGaugeZeroModeSurfaces =
  gaugeOrbitTangentModesQuotiented
  ∷ vacuumFlatTrivialModesRemainClassified
  ∷ nonVacuumTopologicalSectorsRequirePositiveEnergy
  ∷ zeroEnergyGaugeCompatibleModesDoNotComeFromBoundaryLeakage
  ∷ []

data SelfAdjointnessConsumerSurface : Set where
  finiteHodgeAdjointnessReceivesGaugeDomain :
    SelfAdjointnessConsumerSurface

  symmetricFiniteQuotientReceivesDescent :
    SelfAdjointnessConsumerSurface

  selfAdjointnessContractReceivesOnlyAfterGaugeProof :
    SelfAdjointnessConsumerSurface

  dominationAndOSRemainDownstreamConsumersOnly :
    SelfAdjointnessConsumerSurface

canonicalSelfAdjointnessConsumerSurfaces :
  List SelfAdjointnessConsumerSurface
canonicalSelfAdjointnessConsumerSurfaces =
  finiteHodgeAdjointnessReceivesGaugeDomain
  ∷ symmetricFiniteQuotientReceivesDescent
  ∷ selfAdjointnessContractReceivesOnlyAfterGaugeProof
  ∷ dominationAndOSRemainDownstreamConsumersOnly
  ∷ []

------------------------------------------------------------------------
-- YM-1 obligations and blockers.

data YMKillingBoundaryGaugeDomainStatus : Set where
  ym1GaugeDomainPreservationBoundaryRecordedProofStillOpen :
    YMKillingBoundaryGaugeDomainStatus

data YMKillingBoundaryGaugeDomainObligation : Set where
  consumeKillingBoundaryFluxCancellationBoundary :
    YMKillingBoundaryGaugeDomainObligation

  consumeKillingBoundaryWeightPreservationBoundary :
    YMKillingBoundaryGaugeDomainObligation

  consumeKillingBoundarySelfAdjointnessDomainContract :
    YMKillingBoundaryGaugeDomainObligation

  proveFiniteGaugeActionPreservesKillingBoundaryDomain :
    YMKillingBoundaryGaugeDomainObligation

  proveGaugeActionPreservesFullDegreeBoundaryWeights :
    YMKillingBoundaryGaugeDomainObligation

  proveGaugeActionPreservesFluxCancellationPairs :
    YMKillingBoundaryGaugeDomainObligation

  proveGaugeInvariantProjectionPreservesKillingDomain :
    YMKillingBoundaryGaugeDomainObligation

  proveQuotientDomainRepresentativeIndependence :
    YMKillingBoundaryGaugeDomainObligation

  proveQuotientHamiltonianActionWellDefined :
    YMKillingBoundaryGaugeDomainObligation

  proveNoSpuriousGaugeZeroModeFromBoundaryQuotient :
    YMKillingBoundaryGaugeDomainObligation

  routeResultOnlyIntoSelfAdjointnessConsumer :
    YMKillingBoundaryGaugeDomainObligation

  keepYMClayAndTerminalPromotionFalse :
    YMKillingBoundaryGaugeDomainObligation

canonicalYMKillingBoundaryGaugeDomainObligations :
  List YMKillingBoundaryGaugeDomainObligation
canonicalYMKillingBoundaryGaugeDomainObligations =
  consumeKillingBoundaryFluxCancellationBoundary
  ∷ consumeKillingBoundaryWeightPreservationBoundary
  ∷ consumeKillingBoundarySelfAdjointnessDomainContract
  ∷ proveFiniteGaugeActionPreservesKillingBoundaryDomain
  ∷ proveGaugeActionPreservesFullDegreeBoundaryWeights
  ∷ proveGaugeActionPreservesFluxCancellationPairs
  ∷ proveGaugeInvariantProjectionPreservesKillingDomain
  ∷ proveQuotientDomainRepresentativeIndependence
  ∷ proveQuotientHamiltonianActionWellDefined
  ∷ proveNoSpuriousGaugeZeroModeFromBoundaryQuotient
  ∷ routeResultOnlyIntoSelfAdjointnessConsumer
  ∷ keepYMClayAndTerminalPromotionFalse
  ∷ []

data YMKillingBoundaryGaugeDomainBlocker : Set where
  missingGaugeActionDomainPreservation :
    YMKillingBoundaryGaugeDomainBlocker

  missingGaugeWeightPreservationFeedThrough :
    YMKillingBoundaryGaugeDomainBlocker

  missingGaugeFluxPairPreservation :
    YMKillingBoundaryGaugeDomainBlocker

  missingGaugeInvariantProjectionDomainPreservation :
    YMKillingBoundaryGaugeDomainBlocker

  missingQuotientDomainRepresentativeIndependence :
    YMKillingBoundaryGaugeDomainBlocker

  missingQuotientHamiltonianActionWellDefined :
    YMKillingBoundaryGaugeDomainBlocker

  missingNoSpuriousGaugeZeroModeProof :
    YMKillingBoundaryGaugeDomainBlocker

  missingSelfAdjointnessConsumerProof :
    YMKillingBoundaryGaugeDomainBlocker

  missingHamiltonianDominationTheorem :
    YMKillingBoundaryGaugeDomainBlocker

  missingOSTransferAndContinuumNoPollution :
    YMKillingBoundaryGaugeDomainBlocker

  missingYMClayAuthorityToken :
    YMKillingBoundaryGaugeDomainBlocker

canonicalYMKillingBoundaryGaugeDomainBlockers :
  List YMKillingBoundaryGaugeDomainBlocker
canonicalYMKillingBoundaryGaugeDomainBlockers =
  missingGaugeActionDomainPreservation
  ∷ missingGaugeWeightPreservationFeedThrough
  ∷ missingGaugeFluxPairPreservation
  ∷ missingGaugeInvariantProjectionDomainPreservation
  ∷ missingQuotientDomainRepresentativeIndependence
  ∷ missingQuotientHamiltonianActionWellDefined
  ∷ missingNoSpuriousGaugeZeroModeProof
  ∷ missingSelfAdjointnessConsumerProof
  ∷ missingHamiltonianDominationTheorem
  ∷ missingOSTransferAndContinuumNoPollution
  ∷ missingYMClayAuthorityToken
  ∷ []

record YMKillingBoundaryGaugeDomainObligationRow : Set where
  field
    obligation :
      YMKillingBoundaryGaugeDomainObligation

    section :
      String

    label :
      String

    contractText :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open YMKillingBoundaryGaugeDomainObligationRow public

mkYMKillingBoundaryGaugeDomainObligationRow :
  YMKillingBoundaryGaugeDomainObligation →
  String →
  String →
  String →
  YMKillingBoundaryGaugeDomainObligationRow
mkYMKillingBoundaryGaugeDomainObligationRow obligation section label contractText =
  record
    { obligation =
        obligation
    ; section =
        section
    ; label =
        label
    ; contractText =
        contractText
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    }

canonicalYMKillingBoundaryGaugeDomainObligationRows :
  List YMKillingBoundaryGaugeDomainObligationRow
canonicalYMKillingBoundaryGaugeDomainObligationRows =
  mkYMKillingBoundaryGaugeDomainObligationRow
    consumeKillingBoundaryFluxCancellationBoundary
    "import"
    "flux cancellation"
    "Consume the Killing/full-degree flux-cancellation boundary as an open input; do not treat it as proved by this module."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    consumeKillingBoundaryWeightPreservationBoundary
    "import"
    "weight preservation"
    "Consume the weight-preservation boundary as the required full-degree/Killing gauge-weight interface."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    consumeKillingBoundarySelfAdjointnessDomainContract
    "import"
    "domain contract"
    "Consume the self-adjointness domain contract as the downstream consumer and keep its theorem obligations open."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    proveFiniteGaugeActionPreservesKillingBoundaryDomain
    "domain preservation"
    "gauge action"
    "Prove every finite gauge transform maps the Killing/full-degree finite boundary domain back into itself."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    proveGaugeActionPreservesFullDegreeBoundaryWeights
    "domain preservation"
    "gauge weights"
    "Prove gauge action preserves full-degree/Killing face weights and does not switch to the rejected induced-ball convention."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    proveGaugeActionPreservesFluxCancellationPairs
    "domain preservation"
    "flux pairs"
    "Prove gauge action sends opposite-face flux pairs to opposite-face flux pairs with the same cancellation structure."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    proveGaugeInvariantProjectionPreservesKillingDomain
    "quotient descent"
    "projection"
    "Prove the gauge-invariant projection is defined on, and lands inside, the Killing/full-degree boundary domain."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    proveQuotientDomainRepresentativeIndependence
    "quotient descent"
    "representatives"
    "Prove the quotient domain is independent of finite gauge-orbit representatives, including weights and boundary residuals."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    proveQuotientHamiltonianActionWellDefined
    "quotient descent"
    "Hamiltonian action"
    "Prove the finite Hamiltonian action descends to the quotient domain before finite self-adjointness consumes it."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    proveNoSpuriousGaugeZeroModeFromBoundaryQuotient
    "zero mode"
    "spurious modes"
    "Exclude new zero-energy gauge-compatible modes produced only by quotienting or by Killing-boundary residual leakage."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    routeResultOnlyIntoSelfAdjointnessConsumer
    "self-adjointness consumer"
    "consumer route"
    "Route a completed YM-1 gauge-domain theorem only into finite Hodge adjointness and quotient self-adjointness consumers."
  ∷ mkYMKillingBoundaryGaugeDomainObligationRow
    keepYMClayAndTerminalPromotionFalse
    "promotion guard"
    "promotion false"
    "Keep Hamiltonian domination, OS transfer, continuum no-pollution, YM Clay, and terminal promotion false."
  ∷ []

------------------------------------------------------------------------
-- Boundary flags.

boundaryRecorded : Bool
boundaryRecorded =
  true

fluxCancellationBoundaryImported : Bool
fluxCancellationBoundaryImported =
  true

weightPreservationBoundaryImported : Bool
weightPreservationBoundaryImported =
  true

selfAdjointnessDomainContractImported : Bool
selfAdjointnessDomainContractImported =
  true

zeroModeGuardImported : Bool
zeroModeGuardImported =
  true

ym1ScopeRecorded : Bool
ym1ScopeRecorded =
  true

domainPreservationSurfaceSeparated : Bool
domainPreservationSurfaceSeparated =
  true

quotientDescentSurfaceSeparated : Bool
quotientDescentSurfaceSeparated =
  true

noSpuriousGaugeZeroModeSurfaceSeparated : Bool
noSpuriousGaugeZeroModeSurfaceSeparated =
  true

selfAdjointnessConsumerSurfaceSeparated : Bool
selfAdjointnessConsumerSurfaceSeparated =
  true

gaugeActionDomainPreservationProved : Bool
gaugeActionDomainPreservationProved =
  false

gaugeWeightPreservationFeedThroughProved : Bool
gaugeWeightPreservationFeedThroughProved =
  false

gaugeFluxPairPreservationProved : Bool
gaugeFluxPairPreservationProved =
  false

gaugeInvariantProjectionPreservesDomainProved : Bool
gaugeInvariantProjectionPreservesDomainProved =
  false

quotientDomainDescentProved : Bool
quotientDomainDescentProved =
  false

quotientHamiltonianActionWellDefinedProved : Bool
quotientHamiltonianActionWellDefinedProved =
  false

noSpuriousGaugeZeroModeProved : Bool
noSpuriousGaugeZeroModeProved =
  false

selfAdjointnessConsumerProved : Bool
selfAdjointnessConsumerProved =
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

fluxCancellationBoundaryImportedIsTrue :
  fluxCancellationBoundaryImported ≡ true
fluxCancellationBoundaryImportedIsTrue =
  refl

weightPreservationBoundaryImportedIsTrue :
  weightPreservationBoundaryImported ≡ true
weightPreservationBoundaryImportedIsTrue =
  refl

selfAdjointnessDomainContractImportedIsTrue :
  selfAdjointnessDomainContractImported ≡ true
selfAdjointnessDomainContractImportedIsTrue =
  refl

zeroModeGuardImportedIsTrue :
  zeroModeGuardImported ≡ true
zeroModeGuardImportedIsTrue =
  refl

ym1ScopeRecordedIsTrue :
  ym1ScopeRecorded ≡ true
ym1ScopeRecordedIsTrue =
  refl

domainPreservationSurfaceSeparatedIsTrue :
  domainPreservationSurfaceSeparated ≡ true
domainPreservationSurfaceSeparatedIsTrue =
  refl

quotientDescentSurfaceSeparatedIsTrue :
  quotientDescentSurfaceSeparated ≡ true
quotientDescentSurfaceSeparatedIsTrue =
  refl

noSpuriousGaugeZeroModeSurfaceSeparatedIsTrue :
  noSpuriousGaugeZeroModeSurfaceSeparated ≡ true
noSpuriousGaugeZeroModeSurfaceSeparatedIsTrue =
  refl

selfAdjointnessConsumerSurfaceSeparatedIsTrue :
  selfAdjointnessConsumerSurfaceSeparated ≡ true
selfAdjointnessConsumerSurfaceSeparatedIsTrue =
  refl

gaugeActionDomainPreservationProvedIsFalse :
  gaugeActionDomainPreservationProved ≡ false
gaugeActionDomainPreservationProvedIsFalse =
  refl

gaugeWeightPreservationFeedThroughProvedIsFalse :
  gaugeWeightPreservationFeedThroughProved ≡ false
gaugeWeightPreservationFeedThroughProvedIsFalse =
  refl

gaugeFluxPairPreservationProvedIsFalse :
  gaugeFluxPairPreservationProved ≡ false
gaugeFluxPairPreservationProvedIsFalse =
  refl

gaugeInvariantProjectionPreservesDomainProvedIsFalse :
  gaugeInvariantProjectionPreservesDomainProved ≡ false
gaugeInvariantProjectionPreservesDomainProvedIsFalse =
  refl

quotientDomainDescentProvedIsFalse :
  quotientDomainDescentProved ≡ false
quotientDomainDescentProvedIsFalse =
  refl

quotientHamiltonianActionWellDefinedProvedIsFalse :
  quotientHamiltonianActionWellDefinedProved ≡ false
quotientHamiltonianActionWellDefinedProvedIsFalse =
  refl

noSpuriousGaugeZeroModeProvedIsFalse :
  noSpuriousGaugeZeroModeProved ≡ false
noSpuriousGaugeZeroModeProvedIsFalse =
  refl

selfAdjointnessConsumerProvedIsFalse :
  selfAdjointnessConsumerProved ≡ false
selfAdjointnessConsumerProvedIsFalse =
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

gaugeDomainPreservationFormula : String
gaugeDomainPreservationFormula =
  "g in G_finite and phi in Dom_Killing imply g.phi in Dom_Killing"

quotientDescentFormula : String
quotientDescentFormula =
  "phi ~_g psi implies [phi] and [psi] determine the same Killing-boundary domain element and H_d action"

noSpuriousGaugeZeroModeFormula : String
noSpuriousGaugeZeroModeFormula =
  "ker(H_d on quotient) contains no boundary-created gauge-zero mode beyond classified vacuum/positive-energy sectors"

selfAdjointnessConsumerFormula : String
selfAdjointnessConsumerFormula =
  "domain preservation + quotient descent + zero-mode exclusion -> self-adjointness domain consumer only"

------------------------------------------------------------------------
-- Canonical boundary receipt.

record YMKillingBoundaryGaugeDomainPreservationBoundary : Setω where
  field
    status :
      YMKillingBoundaryGaugeDomainStatus

    fluxCancellationBoundary :
      Flux.YMKillingBoundaryFluxCancellationBoundary

    fluxCancellationBoundaryCanonical :
      Bool

    fluxCancellationBoundaryCanonicalIsTrue :
      fluxCancellationBoundaryCanonical ≡ true

    weightPreservationBoundary :
      Weight.YMKillingBoundaryWeightPreservationBoundary

    weightPreservationBoundaryCanonical :
      Bool

    weightPreservationBoundaryCanonicalIsTrue :
      weightPreservationBoundaryCanonical ≡ true

    selfAdjointnessDomainContract :
      Domain.YMKillingBoundarySelfAdjointnessDomainContract

    selfAdjointnessDomainContractCanonical :
      Bool

    selfAdjointnessDomainContractCanonicalIsTrue :
      selfAdjointnessDomainContractCanonical ≡ true

    zeroModeBoundary :
      ZeroMode.YMGaugeZeroModeVacuumRigidityBoundary

    zeroModeBoundaryCanonical :
      Bool

    zeroModeBoundaryCanonicalIsTrue :
      zeroModeBoundaryCanonical ≡ true

    importedSupport :
      List YMKillingBoundaryGaugeDomainImportedSupport

    importedSupportIsCanonical :
      importedSupport
      ≡
      canonicalYMKillingBoundaryGaugeDomainImportedSupport

    importedSupportCount :
      Nat

    importedSupportCountIs4 :
      importedSupportCount ≡ 4

    domainPreservationSurfaces :
      List GaugeDomainPreservationSurface

    domainPreservationSurfacesAreCanonical :
      domainPreservationSurfaces
      ≡
      canonicalGaugeDomainPreservationSurfaces

    domainPreservationSurfaceCount :
      Nat

    domainPreservationSurfaceCountIs4 :
      domainPreservationSurfaceCount ≡ 4

    quotientDescentSurfaces :
      List QuotientDescentSurface

    quotientDescentSurfacesAreCanonical :
      quotientDescentSurfaces
      ≡
      canonicalQuotientDescentSurfaces

    quotientDescentSurfaceCount :
      Nat

    quotientDescentSurfaceCountIs4 :
      quotientDescentSurfaceCount ≡ 4

    noSpuriousGaugeZeroModeSurfaces :
      List NoSpuriousGaugeZeroModeSurface

    noSpuriousGaugeZeroModeSurfacesAreCanonical :
      noSpuriousGaugeZeroModeSurfaces
      ≡
      canonicalNoSpuriousGaugeZeroModeSurfaces

    noSpuriousGaugeZeroModeSurfaceCount :
      Nat

    noSpuriousGaugeZeroModeSurfaceCountIs4 :
      noSpuriousGaugeZeroModeSurfaceCount ≡ 4

    selfAdjointnessConsumerSurfaces :
      List SelfAdjointnessConsumerSurface

    selfAdjointnessConsumerSurfacesAreCanonical :
      selfAdjointnessConsumerSurfaces
      ≡
      canonicalSelfAdjointnessConsumerSurfaces

    selfAdjointnessConsumerSurfaceCount :
      Nat

    selfAdjointnessConsumerSurfaceCountIs4 :
      selfAdjointnessConsumerSurfaceCount ≡ 4

    obligations :
      List YMKillingBoundaryGaugeDomainObligation

    obligationsAreCanonical :
      obligations ≡ canonicalYMKillingBoundaryGaugeDomainObligations

    obligationCount :
      Nat

    obligationCountIs12 :
      obligationCount ≡ 12

    obligationRows :
      List YMKillingBoundaryGaugeDomainObligationRow

    obligationRowsAreCanonical :
      obligationRows ≡ canonicalYMKillingBoundaryGaugeDomainObligationRows

    obligationRowCount :
      Nat

    obligationRowCountIs12 :
      obligationRowCount ≡ 12

    blockers :
      List YMKillingBoundaryGaugeDomainBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMKillingBoundaryGaugeDomainBlockers

    blockerCount :
      Nat

    blockerCountIs11 :
      blockerCount ≡ 11

    firstBlocker :
      YMKillingBoundaryGaugeDomainBlocker

    firstBlockerIsGaugeActionDomain :
      firstBlocker ≡ missingGaugeActionDomainPreservation

    gaugeDomainFormula :
      String

    gaugeDomainFormulaIsCanonical :
      gaugeDomainFormula ≡ gaugeDomainPreservationFormula

    quotientFormula :
      String

    quotientFormulaIsCanonical :
      quotientFormula ≡ quotientDescentFormula

    zeroModeFormula :
      String

    zeroModeFormulaIsCanonical :
      zeroModeFormula ≡ noSpuriousGaugeZeroModeFormula

    consumerFormula :
      String

    consumerFormulaIsCanonical :
      consumerFormula ≡ selfAdjointnessConsumerFormula

    boundaryRecordedField :
      Bool

    boundaryRecordedFieldIsTrue :
      boundaryRecordedField ≡ true

    ym1ScopeRecordedField :
      Bool

    ym1ScopeRecordedFieldIsTrue :
      ym1ScopeRecordedField ≡ true

    domainPreservationSurfaceSeparatedField :
      Bool

    domainPreservationSurfaceSeparatedFieldIsTrue :
      domainPreservationSurfaceSeparatedField ≡ true

    quotientDescentSurfaceSeparatedField :
      Bool

    quotientDescentSurfaceSeparatedFieldIsTrue :
      quotientDescentSurfaceSeparatedField ≡ true

    noSpuriousGaugeZeroModeSurfaceSeparatedField :
      Bool

    noSpuriousGaugeZeroModeSurfaceSeparatedFieldIsTrue :
      noSpuriousGaugeZeroModeSurfaceSeparatedField ≡ true

    selfAdjointnessConsumerSurfaceSeparatedField :
      Bool

    selfAdjointnessConsumerSurfaceSeparatedFieldIsTrue :
      selfAdjointnessConsumerSurfaceSeparatedField ≡ true

    gaugeActionDomainPreservationProvedField :
      Bool

    gaugeActionDomainPreservationProvedFieldIsFalse :
      gaugeActionDomainPreservationProvedField ≡ false

    gaugeWeightPreservationFeedThroughProvedField :
      Bool

    gaugeWeightPreservationFeedThroughProvedFieldIsFalse :
      gaugeWeightPreservationFeedThroughProvedField ≡ false

    gaugeFluxPairPreservationProvedField :
      Bool

    gaugeFluxPairPreservationProvedFieldIsFalse :
      gaugeFluxPairPreservationProvedField ≡ false

    gaugeInvariantProjectionPreservesDomainProvedField :
      Bool

    gaugeInvariantProjectionPreservesDomainProvedFieldIsFalse :
      gaugeInvariantProjectionPreservesDomainProvedField ≡ false

    quotientDomainDescentProvedField :
      Bool

    quotientDomainDescentProvedFieldIsFalse :
      quotientDomainDescentProvedField ≡ false

    quotientHamiltonianActionWellDefinedProvedField :
      Bool

    quotientHamiltonianActionWellDefinedProvedFieldIsFalse :
      quotientHamiltonianActionWellDefinedProvedField ≡ false

    noSpuriousGaugeZeroModeProvedField :
      Bool

    noSpuriousGaugeZeroModeProvedFieldIsFalse :
      noSpuriousGaugeZeroModeProvedField ≡ false

    selfAdjointnessConsumerProvedField :
      Bool

    selfAdjointnessConsumerProvedFieldIsFalse :
      selfAdjointnessConsumerProvedField ≡ false

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

    importedFluxGaugeDomainStillOpen :
      Flux.gaugeDomainPreservationProvedField
        fluxCancellationBoundary
      ≡
      false

    importedFluxQuotientResidualStillOpen :
      Flux.quotientFluxResidualIndependenceProvedField
        fluxCancellationBoundary
      ≡
      false

    importedWeightGaugeStillOpen :
      Weight.gaugeWeightInvarianceProvedField
        weightPreservationBoundary
      ≡
      false

    importedWeightConsumerStillOpen :
      Weight.selfAdjointnessFeedThroughProvedField
        weightPreservationBoundary
      ≡
      false

    importedDomainGaugeCompatibilityStillOpen :
      Domain.gaugeCompatibilityProvedField
        selfAdjointnessDomainContract
      ≡
      false

    importedDomainQuotientDescentStillOpen :
      Domain.quotientDomainDescentProvedField
        selfAdjointnessDomainContract
      ≡
      false

    importedDomainSelfAdjointStillOpen :
      Domain.selfAdjointQuotientHamiltonianProvedField
        selfAdjointnessDomainContract
      ≡
      false

    importedZeroModeExclusionStillOpen :
      ZeroMode.nonVacuumZeroEnergyModesExcluded
      ≡
      false

    importedZeroModeClayStillFalse :
      ZeroMode.clayYangMillsPromoted
      ≡
      false

    notes :
      List String

open YMKillingBoundaryGaugeDomainPreservationBoundary public

canonicalYMKillingBoundaryGaugeDomainPreservationBoundary :
  YMKillingBoundaryGaugeDomainPreservationBoundary
canonicalYMKillingBoundaryGaugeDomainPreservationBoundary =
  record
    { status =
        ym1GaugeDomainPreservationBoundaryRecordedProofStillOpen
    ; fluxCancellationBoundary =
        Flux.canonicalYMKillingBoundaryFluxCancellationBoundary
    ; fluxCancellationBoundaryCanonical =
        true
    ; fluxCancellationBoundaryCanonicalIsTrue =
        refl
    ; weightPreservationBoundary =
        Weight.canonicalYMKillingBoundaryWeightPreservationBoundary
    ; weightPreservationBoundaryCanonical =
        true
    ; weightPreservationBoundaryCanonicalIsTrue =
        refl
    ; selfAdjointnessDomainContract =
        Domain.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; selfAdjointnessDomainContractCanonical =
        true
    ; selfAdjointnessDomainContractCanonicalIsTrue =
        refl
    ; zeroModeBoundary =
        ZeroMode.canonicalYMGaugeZeroModeVacuumRigidityBoundary
    ; zeroModeBoundaryCanonical =
        true
    ; zeroModeBoundaryCanonicalIsTrue =
        refl
    ; importedSupport =
        canonicalYMKillingBoundaryGaugeDomainImportedSupport
    ; importedSupportIsCanonical =
        refl
    ; importedSupportCount =
        listCount canonicalYMKillingBoundaryGaugeDomainImportedSupport
    ; importedSupportCountIs4 =
        refl
    ; domainPreservationSurfaces =
        canonicalGaugeDomainPreservationSurfaces
    ; domainPreservationSurfacesAreCanonical =
        refl
    ; domainPreservationSurfaceCount =
        listCount canonicalGaugeDomainPreservationSurfaces
    ; domainPreservationSurfaceCountIs4 =
        refl
    ; quotientDescentSurfaces =
        canonicalQuotientDescentSurfaces
    ; quotientDescentSurfacesAreCanonical =
        refl
    ; quotientDescentSurfaceCount =
        listCount canonicalQuotientDescentSurfaces
    ; quotientDescentSurfaceCountIs4 =
        refl
    ; noSpuriousGaugeZeroModeSurfaces =
        canonicalNoSpuriousGaugeZeroModeSurfaces
    ; noSpuriousGaugeZeroModeSurfacesAreCanonical =
        refl
    ; noSpuriousGaugeZeroModeSurfaceCount =
        listCount canonicalNoSpuriousGaugeZeroModeSurfaces
    ; noSpuriousGaugeZeroModeSurfaceCountIs4 =
        refl
    ; selfAdjointnessConsumerSurfaces =
        canonicalSelfAdjointnessConsumerSurfaces
    ; selfAdjointnessConsumerSurfacesAreCanonical =
        refl
    ; selfAdjointnessConsumerSurfaceCount =
        listCount canonicalSelfAdjointnessConsumerSurfaces
    ; selfAdjointnessConsumerSurfaceCountIs4 =
        refl
    ; obligations =
        canonicalYMKillingBoundaryGaugeDomainObligations
    ; obligationsAreCanonical =
        refl
    ; obligationCount =
        listCount canonicalYMKillingBoundaryGaugeDomainObligations
    ; obligationCountIs12 =
        refl
    ; obligationRows =
        canonicalYMKillingBoundaryGaugeDomainObligationRows
    ; obligationRowsAreCanonical =
        refl
    ; obligationRowCount =
        listCount canonicalYMKillingBoundaryGaugeDomainObligationRows
    ; obligationRowCountIs12 =
        refl
    ; blockers =
        canonicalYMKillingBoundaryGaugeDomainBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMKillingBoundaryGaugeDomainBlockers
    ; blockerCountIs11 =
        refl
    ; firstBlocker =
        missingGaugeActionDomainPreservation
    ; firstBlockerIsGaugeActionDomain =
        refl
    ; gaugeDomainFormula =
        gaugeDomainPreservationFormula
    ; gaugeDomainFormulaIsCanonical =
        refl
    ; quotientFormula =
        quotientDescentFormula
    ; quotientFormulaIsCanonical =
        refl
    ; zeroModeFormula =
        noSpuriousGaugeZeroModeFormula
    ; zeroModeFormulaIsCanonical =
        refl
    ; consumerFormula =
        selfAdjointnessConsumerFormula
    ; consumerFormulaIsCanonical =
        refl
    ; boundaryRecordedField =
        boundaryRecorded
    ; boundaryRecordedFieldIsTrue =
        boundaryRecordedIsTrue
    ; ym1ScopeRecordedField =
        ym1ScopeRecorded
    ; ym1ScopeRecordedFieldIsTrue =
        ym1ScopeRecordedIsTrue
    ; domainPreservationSurfaceSeparatedField =
        domainPreservationSurfaceSeparated
    ; domainPreservationSurfaceSeparatedFieldIsTrue =
        domainPreservationSurfaceSeparatedIsTrue
    ; quotientDescentSurfaceSeparatedField =
        quotientDescentSurfaceSeparated
    ; quotientDescentSurfaceSeparatedFieldIsTrue =
        quotientDescentSurfaceSeparatedIsTrue
    ; noSpuriousGaugeZeroModeSurfaceSeparatedField =
        noSpuriousGaugeZeroModeSurfaceSeparated
    ; noSpuriousGaugeZeroModeSurfaceSeparatedFieldIsTrue =
        noSpuriousGaugeZeroModeSurfaceSeparatedIsTrue
    ; selfAdjointnessConsumerSurfaceSeparatedField =
        selfAdjointnessConsumerSurfaceSeparated
    ; selfAdjointnessConsumerSurfaceSeparatedFieldIsTrue =
        selfAdjointnessConsumerSurfaceSeparatedIsTrue
    ; gaugeActionDomainPreservationProvedField =
        gaugeActionDomainPreservationProved
    ; gaugeActionDomainPreservationProvedFieldIsFalse =
        gaugeActionDomainPreservationProvedIsFalse
    ; gaugeWeightPreservationFeedThroughProvedField =
        gaugeWeightPreservationFeedThroughProved
    ; gaugeWeightPreservationFeedThroughProvedFieldIsFalse =
        gaugeWeightPreservationFeedThroughProvedIsFalse
    ; gaugeFluxPairPreservationProvedField =
        gaugeFluxPairPreservationProved
    ; gaugeFluxPairPreservationProvedFieldIsFalse =
        gaugeFluxPairPreservationProvedIsFalse
    ; gaugeInvariantProjectionPreservesDomainProvedField =
        gaugeInvariantProjectionPreservesDomainProved
    ; gaugeInvariantProjectionPreservesDomainProvedFieldIsFalse =
        gaugeInvariantProjectionPreservesDomainProvedIsFalse
    ; quotientDomainDescentProvedField =
        quotientDomainDescentProved
    ; quotientDomainDescentProvedFieldIsFalse =
        quotientDomainDescentProvedIsFalse
    ; quotientHamiltonianActionWellDefinedProvedField =
        quotientHamiltonianActionWellDefinedProved
    ; quotientHamiltonianActionWellDefinedProvedFieldIsFalse =
        quotientHamiltonianActionWellDefinedProvedIsFalse
    ; noSpuriousGaugeZeroModeProvedField =
        noSpuriousGaugeZeroModeProved
    ; noSpuriousGaugeZeroModeProvedFieldIsFalse =
        noSpuriousGaugeZeroModeProvedIsFalse
    ; selfAdjointnessConsumerProvedField =
        selfAdjointnessConsumerProved
    ; selfAdjointnessConsumerProvedFieldIsFalse =
        selfAdjointnessConsumerProvedIsFalse
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
    ; importedFluxGaugeDomainStillOpen =
        Flux.gaugeDomainPreservationProvedIsFalse
    ; importedFluxQuotientResidualStillOpen =
        Flux.quotientFluxResidualIndependenceProvedIsFalse
    ; importedWeightGaugeStillOpen =
        Weight.gaugeWeightInvarianceProvedIsFalse
    ; importedWeightConsumerStillOpen =
        Weight.selfAdjointnessFeedThroughProvedIsFalse
    ; importedDomainGaugeCompatibilityStillOpen =
        Domain.gaugeCompatibilityProvedFieldIsFalse
          Domain.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; importedDomainQuotientDescentStillOpen =
        Domain.quotientDomainDescentProvedFieldIsFalse
          Domain.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; importedDomainSelfAdjointStillOpen =
        Domain.canonicalKillingBoundaryDomainSelfAdjointStillFalse
    ; importedZeroModeExclusionStillOpen =
        ZeroMode.nonVacuumZeroEnergyModesExcludedIsFalse
    ; importedZeroModeClayStillFalse =
        ZeroMode.clayYangMillsPromotedIsFalse
    ; notes =
        "YM-1 scope is recorded as gauge-domain preservation for the Killing/full-degree boundary domain, not as a Clay or terminal theorem."
        ∷ "Domain preservation, quotient descent, no spurious gauge-zero mode, and self-adjointness consumer routing are kept as distinct surfaces."
        ∷ "Flux cancellation and weight preservation are consumed as open boundary inputs; their gauge rows still block this receipt."
        ∷ "The self-adjointness domain contract remains the only immediate consumer; domination, OS transfer, continuum no-pollution, YM Clay, and terminal promotion stay false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalGaugeDomainImportedSupportCountIs4 :
  importedSupportCount canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  4
canonicalGaugeDomainImportedSupportCountIs4 =
  refl

canonicalGaugeDomainObligationCountIs12 :
  obligationCount canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  12
canonicalGaugeDomainObligationCountIs12 =
  refl

canonicalGaugeDomainFirstBlocker :
  firstBlocker canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  missingGaugeActionDomainPreservation
canonicalGaugeDomainFirstBlocker =
  refl

canonicalGaugeDomainPreservationStillFalse :
  gaugeActionDomainPreservationProvedField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  false
canonicalGaugeDomainPreservationStillFalse =
  refl

canonicalGaugeQuotientDescentStillFalse :
  quotientDomainDescentProvedField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  false
canonicalGaugeQuotientDescentStillFalse =
  refl

canonicalNoSpuriousGaugeZeroModeStillFalse :
  noSpuriousGaugeZeroModeProvedField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  false
canonicalNoSpuriousGaugeZeroModeStillFalse =
  refl

canonicalGaugeSelfAdjointConsumerStillFalse :
  selfAdjointnessConsumerProvedField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  false
canonicalGaugeSelfAdjointConsumerStillFalse =
  refl

canonicalGaugeDomainYMClayStillFalse :
  ymClayPromotedField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  false
canonicalGaugeDomainYMClayStillFalse =
  refl

canonicalGaugeDomainTerminalStillFalse :
  terminalPromotionField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  false
canonicalGaugeDomainTerminalStillFalse =
  refl

data YMKillingBoundaryGaugeDomainPromotionToken : Set where

ymKillingBoundaryGaugeDomainPromotionTokenImpossibleHere :
  YMKillingBoundaryGaugeDomainPromotionToken →
  ⊥
ymKillingBoundaryGaugeDomainPromotionTokenImpossibleHere ()

noYM1GaugeDomainTheoremFromBoundaryReceiptAlone :
  gaugeActionDomainPreservationProvedField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  true →
  ⊥
noYM1GaugeDomainTheoremFromBoundaryReceiptAlone ()

noSpuriousGaugeZeroModeExclusionFromBoundaryReceiptAlone :
  noSpuriousGaugeZeroModeProvedField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  true →
  ⊥
noSpuriousGaugeZeroModeExclusionFromBoundaryReceiptAlone ()

noSelfAdjointnessConsumerPromotionFromBoundaryReceiptAlone :
  selfAdjointnessConsumerProvedField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  true →
  ⊥
noSelfAdjointnessConsumerPromotionFromBoundaryReceiptAlone ()

noYMClayPromotionFromGaugeDomainBoundaryReceipt :
  ymClayPromotedField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  true →
  ⊥
noYMClayPromotionFromGaugeDomainBoundaryReceipt ()

noTerminalPromotionFromGaugeDomainBoundaryReceipt :
  terminalPromotionField
    canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
  ≡
  true →
  ⊥
noTerminalPromotionFromGaugeDomainBoundaryReceipt ()
