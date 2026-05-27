module DASHI.Physics.QFT.DHRGaugeReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Algebra.GaugeGroupContract as Gauge
import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT
import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as AQFTColim
import DASHI.Physics.Boundaries.ClayYMGap as ClayBoundary
import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM
import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as FiniteLedger
import DASHI.Physics.QFT.DHRSectorDecomposition as DHRSector
import DASHI.Physics.QFT.LocalAlgebraIdentitySemantics as LocalAlgebraIdentity
import DASHI.Physics.SFGC.NonAbelian.GradedSFGCSite2D as Graded
import DASHI.Physics.SFGC.NonAbelian.NonAbelianSFGCCarrier as Carrier
import DASHI.Physics.SFGC.NonAbelian.DepthQuotientIso as DepthQuotient
import DASHI.Physics.SFGC.NonAbelian.SU3ColorSectorNote as SU3

------------------------------------------------------------------------
-- DHR gauge reconstruction receipt surface.
--
-- This module records the next AQFT/gauge-theoretic target after the typed
-- Haag-Kastler net surface.  It intentionally keeps duality, selection
-- criteria, tensor-category structure, reconstruction, Standard Model matching,
-- and prime-lane condensation abstract.
--
-- It does not prove Haag duality, construct a DHR category, reconstruct a gauge
-- group, match the Standard Model, condense a prime lane, or promote GRQFT.

postulate
  externalCausalComplementPrimitive :
    AQFT.Region →
    AQFT.Region

  externalDoubleComplementPrimitive :
    AQFT.Region →
    AQFT.Region

data DHRComplementPrimitiveBoundaryBlocker : Set where
  missingConcreteCausalComplementConstruction :
    DHRComplementPrimitiveBoundaryBlocker

  missingDoubleComplementLaw :
    DHRComplementPrimitiveBoundaryBlocker

  missingComplementLocalityCompatibilityLaw :
    DHRComplementPrimitiveBoundaryBlocker

canonicalDHRComplementPrimitiveBoundaryBlockers :
  List DHRComplementPrimitiveBoundaryBlocker
canonicalDHRComplementPrimitiveBoundaryBlockers =
  missingConcreteCausalComplementConstruction
  ∷ missingDoubleComplementLaw
  ∷ missingComplementLocalityCompatibilityLaw
  ∷ []

record DHRComplementPrimitiveBoundaryReceipt : Setω where
  field
    causalComplementPrimitive :
      AQFT.Region →
      AQFT.Region

    doubleComplementPrimitive :
      AQFT.Region →
      AQFT.Region

    blockers :
      List DHRComplementPrimitiveBoundaryBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDHRComplementPrimitiveBoundaryBlockers

    complementPrimitiveExternallySupplied :
      Bool

    complementPrimitiveExternallySuppliedIsTrue :
      complementPrimitiveExternallySupplied ≡ true

    doubleComplementLawProved :
      Bool

    doubleComplementLawProvedIsFalse :
      doubleComplementLawProved ≡ false

    complementLocalityCompatibilityProved :
      Bool

    complementLocalityCompatibilityProvedIsFalse :
      complementLocalityCompatibilityProved ≡ false

    complementBoundary :
      List String

open DHRComplementPrimitiveBoundaryReceipt public

canonicalDHRComplementPrimitiveBoundaryReceipt :
  DHRComplementPrimitiveBoundaryReceipt
canonicalDHRComplementPrimitiveBoundaryReceipt =
  record
    { causalComplementPrimitive =
        externalCausalComplementPrimitive
    ; doubleComplementPrimitive =
        externalDoubleComplementPrimitive
    ; blockers =
        canonicalDHRComplementPrimitiveBoundaryBlockers
    ; blockersAreCanonical =
        refl
    ; complementPrimitiveExternallySupplied =
        true
    ; complementPrimitiveExternallySuppliedIsTrue =
        refl
    ; doubleComplementLawProved =
        false
    ; doubleComplementLawProvedIsFalse =
        refl
    ; complementLocalityCompatibilityProved =
        false
    ; complementLocalityCompatibilityProvedIsFalse =
        refl
    ; complementBoundary =
        "Causal complement and double complement are external AQFT primitives, not derived constructions"
        ∷ "The raw functions are exposed only through this fail-closed primitive-boundary receipt"
        ∷ "Double-complement and complement/locality laws remain explicit blockers"
        ∷ []
    }

CausalComplement :
  AQFT.Region →
  AQFT.Region
CausalComplement =
  DHRComplementPrimitiveBoundaryReceipt.causalComplementPrimitive
    canonicalDHRComplementPrimitiveBoundaryReceipt

DoubleComplement :
  AQFT.Region →
  AQFT.Region
DoubleComplement =
  DHRComplementPrimitiveBoundaryReceipt.doubleComplementPrimitive
    canonicalDHRComplementPrimitiveBoundaryReceipt

LocalObservableAlgebra :
  AQFT.Region →
  Set
LocalObservableAlgebra =
  AQFT.LocalAlgebra

data CommutantAlgebra (region : AQFT.Region) : Set where
  commutantAlgebraTargetOnly :
    CommutantAlgebra region

data SuperselectionSector : Set where
  superselectionSectorTargetOnly :
    SuperselectionSector

data DHRStatisticsOperator : Set where
  dhrStatisticsOperatorTargetOnly :
    DHRStatisticsOperator

data TensorCStarCategory : Set where
  tensorCStarCategoryTargetOnly :
    TensorCStarCategory

data CompactGaugeGroup : Set where
  compactGaugeGroupAuthorityTargetOnly :
    CompactGaugeGroup

data StandardModelMatchingData : Set where
  standardModelMatchingDataTargetOnly :
    StandardModelMatchingData

data PrimeLaneCondensationData : Set where
  primeLaneCondensationDataTargetOnly :
    PrimeLaneCondensationData

record EndomorphismAction : Setω where
  field
    semanticEndomorphismActionOnDASHILocalAlgebra :
      (region : AQFT.Region) →
      LocalObservableAlgebra region →
      LocalObservableAlgebra region

    endomorphismActionCompositionLaw :
      Set

    localAlgebraIsotonyLocalityCompatibilityLaw :
      Set

    transportIntertwinerNaturalityLaw :
      Set

    twistStatisticsOperatorActionLaw :
      Set

data DHRGaugeReceiptStatus : Set where
  dhrGaugeTargetsOnlyNoPromotion :
    DHRGaugeReceiptStatus

data HaagDualityStatus : Set where
  haagDualityInclusionOnly :
    HaagDualityStatus

  haagDualityEqualityTargetOnly :
    HaagDualityStatus

data DHRGaugeOpenObligation : Set where
  missingHaagDualityInclusion :
    DHRGaugeOpenObligation

  missingHaagDualityEquality :
    DHRGaugeOpenObligation

  missingDHRSelectionCriterion :
    DHRGaugeOpenObligation

  missingLocalisedEndomorphismAndTransportLawProofs :
    DHRGaugeOpenObligation

  missingStatisticsOperatorComputation :
    DHRGaugeOpenObligation

  missingSymmetricTensorCStarCategory :
    DHRGaugeOpenObligation

  missingTannakaDHRReconstruction :
    DHRGaugeOpenObligation

  missingPrimeLaneAlgebraFactorisation :
    DHRGaugeOpenObligation

  missingSerreTateLaneGroupTheorem :
    DHRGaugeOpenObligation

  missingPrimeLaneDHREndomorphismComputation :
    DHRGaugeOpenObligation

  missingFullDHRBoxtimesDecomposition :
    DHRGaugeOpenObligation

  missingSU2RSeesawBreaking :
    DHRGaugeOpenObligation

  missingStandardModelMatching :
    DHRGaugeOpenObligation

  missingPrimeLaneCondensation :
    DHRGaugeOpenObligation

  missingGRQFTAuthority :
    DHRGaugeOpenObligation

canonicalDHRGaugeOpenObligations :
  List DHRGaugeOpenObligation
canonicalDHRGaugeOpenObligations =
  missingHaagDualityInclusion
  ∷ missingHaagDualityEquality
  ∷ missingDHRSelectionCriterion
  ∷ missingLocalisedEndomorphismAndTransportLawProofs
  ∷ missingStatisticsOperatorComputation
  ∷ missingSymmetricTensorCStarCategory
  ∷ missingTannakaDHRReconstruction
  ∷ missingPrimeLaneAlgebraFactorisation
  ∷ missingSerreTateLaneGroupTheorem
  ∷ missingPrimeLaneDHREndomorphismComputation
  ∷ missingFullDHRBoxtimesDecomposition
  ∷ missingSU2RSeesawBreaking
  ∷ missingStandardModelMatching
  ∷ missingPrimeLaneCondensation
  ∷ missingGRQFTAuthority
  ∷ []

data Gate1Gate6AgreementObstruction : Set where
  missingExactStandardModelCarrierFunctorMatch :
    Gate1Gate6AgreementObstruction

canonicalGate1Gate6AgreementObstruction :
  Gate1Gate6AgreementObstruction
canonicalGate1Gate6AgreementObstruction =
  missingExactStandardModelCarrierFunctorMatch

data DHRGaugePromotionAuthorityToken : Set where

data DoplicherRobertsAuthorityCitation : Set where
  doplicherRoberts1989NewDualityForCompactGroups :
    DoplicherRobertsAuthorityCitation

  doplicherRoberts1990FieldAlgebraCompactGaugeGroupSuperselection :
    DoplicherRobertsAuthorityCitation

canonicalDoplicherRobertsAuthorityCitations :
  List DoplicherRobertsAuthorityCitation
canonicalDoplicherRobertsAuthorityCitations =
  doplicherRoberts1989NewDualityForCompactGroups
  ∷ doplicherRoberts1990FieldAlgebraCompactGaugeGroupSuperselection
  ∷ []

record LocalisedEndomorphism : Setω where
  field
    localisedSector :
      SuperselectionSector

    localisationRegion :
      AQFT.Region

    endomorphismAction :
      EndomorphismAction

    actsOnLocalAlgebraTarget :
      (region : AQFT.Region) →
      LocalObservableAlgebra region →
      Set

    localisedOutsideComplementTarget :
      (region : AQFT.Region) →
      region ≡ CausalComplement localisationRegion →
      Set

    localisationBoundary :
      List String

open LocalisedEndomorphism public

record Intertwiner
  (ρ σ : LocalisedEndomorphism) :
  Setω where
  field
    supportRegion :
      AQFT.Region

    arrowCarrier :
      LocalObservableAlgebra supportRegion

    intertwiningLawTarget :
      (region : AQFT.Region) →
      Set

    unitaryTransportTarget :
      Set

    intertwinerBoundary :
      List String

open Intertwiner public

record Transportable
  (ρ : LocalisedEndomorphism) :
  Setω where
  field
    targetRegion :
      AQFT.Region

    transportedEndomorphism :
      LocalisedEndomorphism

    transportIntertwiner :
      Intertwiner ρ transportedEndomorphism

    transportabilityLawTarget :
      Set

    transportabilityBoundary :
      List String

open Transportable public

data DHRLocalisedTransportablePrimitiveBoundaryBlocker : Set where
  missingLocalisedEndomorphismConstructorFromAQFTData :
    DHRLocalisedTransportablePrimitiveBoundaryBlocker

  missingTransportableConstructorFromChargeTransport :
    DHRLocalisedTransportablePrimitiveBoundaryBlocker

  missingOutsideComplementIdentityLaw :
    DHRLocalisedTransportablePrimitiveBoundaryBlocker

  missingTransportIntertwinerNaturalityProof :
    DHRLocalisedTransportablePrimitiveBoundaryBlocker

canonicalDHRLocalisedTransportablePrimitiveBoundaryBlockers :
  List DHRLocalisedTransportablePrimitiveBoundaryBlocker
canonicalDHRLocalisedTransportablePrimitiveBoundaryBlockers =
  missingLocalisedEndomorphismConstructorFromAQFTData
  ∷ missingTransportableConstructorFromChargeTransport
  ∷ missingOutsideComplementIdentityLaw
  ∷ missingTransportIntertwinerNaturalityProof
  ∷ []

record DHRLocalisedTransportablePrimitiveBoundaryReceipt : Setω where
  field
    localisedEndomorphismPrimitive :
      SuperselectionSector →
      LocalisedEndomorphism

    transportablePrimitive :
      (ρ : LocalisedEndomorphism) →
      Transportable ρ

    complementPrimitiveBoundary :
      DHRComplementPrimitiveBoundaryReceipt

    primitiveBlockers :
      List DHRLocalisedTransportablePrimitiveBoundaryBlocker

    primitiveBlockersAreCanonical :
      primitiveBlockers
      ≡
      canonicalDHRLocalisedTransportablePrimitiveBoundaryBlockers

    localisedTransportablePrimitivesExternallySupplied :
      Bool

    localisedTransportablePrimitivesExternallySuppliedIsTrue :
      localisedTransportablePrimitivesExternallySupplied ≡ true

    localisedEndomorphismConstructorDerivedInternally :
      Bool

    localisedEndomorphismConstructorDerivedInternallyIsFalse :
      localisedEndomorphismConstructorDerivedInternally ≡ false

    transportabilityLawProvedInternally :
      Bool

    transportabilityLawProvedInternallyIsFalse :
      transportabilityLawProvedInternally ≡ false

    primitiveBoundary :
      List String

open DHRLocalisedTransportablePrimitiveBoundaryReceipt public

postulate
  externalLocalisedEndomorphismPrimitive :
    SuperselectionSector →
    LocalisedEndomorphism

  externalTransportablePrimitive :
    (ρ : LocalisedEndomorphism) →
    Transportable ρ

canonicalDHRLocalisedTransportablePrimitiveBoundaryReceipt :
  DHRLocalisedTransportablePrimitiveBoundaryReceipt
canonicalDHRLocalisedTransportablePrimitiveBoundaryReceipt =
  record
    { localisedEndomorphismPrimitive =
        externalLocalisedEndomorphismPrimitive
    ; transportablePrimitive =
        externalTransportablePrimitive
    ; complementPrimitiveBoundary =
        canonicalDHRComplementPrimitiveBoundaryReceipt
    ; primitiveBlockers =
        canonicalDHRLocalisedTransportablePrimitiveBoundaryBlockers
    ; primitiveBlockersAreCanonical =
        refl
    ; localisedTransportablePrimitivesExternallySupplied =
        true
    ; localisedTransportablePrimitivesExternallySuppliedIsTrue =
        refl
    ; localisedEndomorphismConstructorDerivedInternally =
        false
    ; localisedEndomorphismConstructorDerivedInternallyIsFalse =
        refl
    ; transportabilityLawProvedInternally =
        false
    ; transportabilityLawProvedInternallyIsFalse =
        refl
    ; primitiveBoundary =
        "LocalisedEndomorphism and Transportable inhabitants are external DHR primitives routed through this receipt"
        ∷ "The receipt records the causal-complement boundary used by outside-complement localization fields"
        ∷ "No localised-endomorphism constructor, charge-transport theorem, outside-complement identity law, or transport-naturality proof is derived here"
        ∷ []
    }

abstractLocalisedEndomorphismPrimitive :
  SuperselectionSector →
  LocalisedEndomorphism
abstractLocalisedEndomorphismPrimitive =
  DHRLocalisedTransportablePrimitiveBoundaryReceipt.localisedEndomorphismPrimitive
    canonicalDHRLocalisedTransportablePrimitiveBoundaryReceipt

abstractTransportablePrimitive :
  (ρ : LocalisedEndomorphism) →
  Transportable ρ
abstractTransportablePrimitive =
  DHRLocalisedTransportablePrimitiveBoundaryReceipt.transportablePrimitive
    canonicalDHRLocalisedTransportablePrimitiveBoundaryReceipt

record DHRStatisticsFormulaSocket
  (ρ σ : LocalisedEndomorphism) :
  Setω where
  field
    ρTransport :
      Transportable ρ

    σTransport :
      Transportable σ

    spacelikeSeparatedTransportTargets :
      Set

    statisticsOperatorCarrier :
      DHRStatisticsOperator

    formulaShape :
      String

    formulaShape-v :
      formulaShape
      ≡
      "epsilon-rho-sigma=V-star-times-sigma(U-star)-times-U-times-rho(V)"

    abstractOperationSocket :
      Set

    formulaComputed :
      Bool

    formulaComputedIsFalse :
      formulaComputed ≡ false

    formulaBoundary :
      List String

open DHRStatisticsFormulaSocket public

record DHRFormalismPrimitiveReceipt : Setω where
  field
    localisedTransportablePrimitiveBoundary :
      DHRLocalisedTransportablePrimitiveBoundaryReceipt

    formalismLocalisedEndomorphismPrimitive :
      SuperselectionSector →
      LocalisedEndomorphism

    formalismTransportablePrimitive :
      (ρ : LocalisedEndomorphism) →
      Transportable ρ

    formalismStatisticsOperatorPrimitive :
      SuperselectionSector →
      SuperselectionSector →
      DHRStatisticsOperator

    formalismStatisticsFormulaSocket :
      (ρ σ : LocalisedEndomorphism) →
      DHRStatisticsFormulaSocket ρ σ

    localisedEndomorphismTyped :
      Bool

    localisedEndomorphismTypedIsTrue :
      localisedEndomorphismTyped ≡ true

    transportableTyped :
      Bool

    transportableTypedIsTrue :
      transportableTyped ≡ true

    statisticsOperatorTyped :
      Bool

    statisticsOperatorTypedIsTrue :
      statisticsOperatorTyped ≡ true

    statisticsComputed :
      Bool

    statisticsComputedIsFalse :
      statisticsComputed ≡ false

    formalismPrimitiveBoundary :
      List String

open DHRFormalismPrimitiveReceipt public

data HaagEqualityPrimitiveBoundaryBlocker : Set where
  missingHaagInclusionProof :
    HaagEqualityPrimitiveBoundaryBlocker

  missingHaagEqualityProof :
    HaagEqualityPrimitiveBoundaryBlocker

  missingFieldNetCentreChargeControl :
    HaagEqualityPrimitiveBoundaryBlocker

canonicalHaagEqualityPrimitiveBoundaryBlockers :
  List HaagEqualityPrimitiveBoundaryBlocker
canonicalHaagEqualityPrimitiveBoundaryBlockers =
  missingHaagInclusionProof
  ∷ missingHaagEqualityProof
  ∷ missingFieldNetCentreChargeControl
  ∷ []

record HaagEqualityPrimitiveBoundaryReceipt : Setω where
  field
    equalityPrimitive :
      (region : AQFT.Region) →
      LocalObservableAlgebra region
      ≡
      CommutantAlgebra (CausalComplement region)

    complementPrimitiveBoundary :
      DHRComplementPrimitiveBoundaryReceipt

    equalityBlockers :
      List HaagEqualityPrimitiveBoundaryBlocker

    equalityBlockersAreCanonical :
      equalityBlockers ≡ canonicalHaagEqualityPrimitiveBoundaryBlockers

    equalityPrimitiveExternallySupplied :
      Bool

    equalityPrimitiveExternallySuppliedIsTrue :
      equalityPrimitiveExternallySupplied ≡ true

    haagEqualityProvedInternally :
      Bool

    haagEqualityProvedInternallyIsFalse :
      haagEqualityProvedInternally ≡ false

    equalityBoundary :
      List String

open HaagEqualityPrimitiveBoundaryReceipt public

record HaagDualityReceiptTarget : Setω where
  field
    status :
      HaagDualityStatus

    netSurface :
      AQFT.AQFTTypedNetSurface

    complementPrimitiveBoundary :
      DHRComplementPrimitiveBoundaryReceipt

    haagEqualityPrimitiveBoundary :
      HaagEqualityPrimitiveBoundaryReceipt

    inclusionTarget :
      (region : AQFT.Region) →
      LocalObservableAlgebra region →
      CommutantAlgebra (CausalComplement region) →
      Set

    equalityTarget :
      (region : AQFT.Region) →
      LocalObservableAlgebra region
      ≡
      CommutantAlgebra (CausalComplement region)

    doubleComplementCaveat :
      (region : AQFT.Region) →
      (double : AQFT.Region) →
      double ≡ DoubleComplement region →
      Set

    inclusionProved :
      Bool

    inclusionProvedIsFalse :
      inclusionProved ≡ false

    equalityProved :
      Bool

    equalityProvedIsFalse :
      equalityProved ≡ false

    dualityBoundary :
      List String

open HaagDualityReceiptTarget public

data HaagInclusionTargetReceipt
  (region : AQFT.Region)
  (observable : LocalObservableAlgebra region)
  (commutant : CommutantAlgebra (CausalComplement region)) :
  Set where
  haagInclusionTargetOnly :
    HaagInclusionTargetReceipt region observable commutant

abstractHaagInclusionTarget :
  (region : AQFT.Region) →
  LocalObservableAlgebra region →
  CommutantAlgebra (CausalComplement region) →
  Set
abstractHaagInclusionTarget region observable commutant =
  HaagInclusionTargetReceipt region observable commutant

postulate
  externalHaagEqualityPrimitive :
    (region : AQFT.Region) →
    LocalObservableAlgebra region
    ≡
    CommutantAlgebra (CausalComplement region)

canonicalHaagEqualityPrimitiveBoundaryReceipt :
  HaagEqualityPrimitiveBoundaryReceipt
canonicalHaagEqualityPrimitiveBoundaryReceipt =
  record
    { equalityPrimitive =
        externalHaagEqualityPrimitive
    ; complementPrimitiveBoundary =
        canonicalDHRComplementPrimitiveBoundaryReceipt
    ; equalityBlockers =
        canonicalHaagEqualityPrimitiveBoundaryBlockers
    ; equalityBlockersAreCanonical =
        refl
    ; equalityPrimitiveExternallySupplied =
        true
    ; equalityPrimitiveExternallySuppliedIsTrue =
        refl
    ; haagEqualityProvedInternally =
        false
    ; haagEqualityProvedInternallyIsFalse =
        refl
    ; equalityBoundary =
        "Haag equality is an external target routed through a primitive-boundary receipt"
        ∷ "The receipt records the causal-complement boundary it depends on"
        ∷ "No internal Haag-duality inclusion, equality, field-net, centre, or charge-sector control proof is claimed"
        ∷ []
    }

abstractHaagEqualityTarget :
  (region : AQFT.Region) →
  LocalObservableAlgebra region
  ≡
  CommutantAlgebra (CausalComplement region)
abstractHaagEqualityTarget =
  HaagEqualityPrimitiveBoundaryReceipt.equalityPrimitive
    canonicalHaagEqualityPrimitiveBoundaryReceipt

data DoubleComplementCaveatReceipt
  (region : AQFT.Region)
  (double : AQFT.Region)
  (doubleIsTarget : double ≡ DoubleComplement region) :
  Set where
  doubleComplementCaveatTargetOnly :
    DoubleComplementCaveatReceipt region double doubleIsTarget

abstractDoubleComplementCaveat :
  (region : AQFT.Region) →
  (double : AQFT.Region) →
  double ≡ DoubleComplement region →
  Set
abstractDoubleComplementCaveat region double doubleIsTarget =
  DoubleComplementCaveatReceipt region double doubleIsTarget

canonicalHaagDualityReceiptTarget :
  HaagDualityReceiptTarget
canonicalHaagDualityReceiptTarget =
  record
    { status =
        haagDualityEqualityTargetOnly
    ; netSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; complementPrimitiveBoundary =
        canonicalDHRComplementPrimitiveBoundaryReceipt
    ; haagEqualityPrimitiveBoundary =
        canonicalHaagEqualityPrimitiveBoundaryReceipt
    ; inclusionTarget =
        abstractHaagInclusionTarget
    ; equalityTarget =
        abstractHaagEqualityTarget
    ; doubleComplementCaveat =
        abstractDoubleComplementCaveat
    ; inclusionProved =
        false
    ; inclusionProvedIsFalse =
        refl
    ; equalityProved =
        false
    ; equalityProvedIsFalse =
        refl
    ; dualityBoundary =
        "Haag duality inclusion and equality are recorded as targets only"
        ∷ "Gauge theories may violate naive Haag duality unless the observable net, field net, centre, and charge sectors are controlled"
        ∷ "Double-complement and causal-completion laws remain explicit obligations"
        ∷ []
    }

record GaugeTheoryControlledFailureSurface : Setω where
  field
    haagDualityTarget :
      HaagDualityReceiptTarget

    controlledFailureShape :
      String

    controlledFailureShape-v :
      controlledFailureShape
      ≡
      "gauge-theory-Haag-duality-failure-must-be-routed-through-field-net-centre-charge-sector-or-cohomological-obstruction"

    controlledFailureRecorded :
      Bool

    controlledFailureRecordedIsTrue :
      controlledFailureRecorded ≡ true

    failureExplainsButDoesNotPromote :
      Bool

    failureExplainsButDoesNotPromoteIsTrue :
      failureExplainsButDoesNotPromote ≡ true

    failureBoundary :
      List String

open GaugeTheoryControlledFailureSurface public

canonicalGaugeTheoryControlledFailureSurface :
  GaugeTheoryControlledFailureSurface
canonicalGaugeTheoryControlledFailureSurface =
  record
    { haagDualityTarget =
        canonicalHaagDualityReceiptTarget
    ; controlledFailureShape =
        "gauge-theory-Haag-duality-failure-must-be-routed-through-field-net-centre-charge-sector-or-cohomological-obstruction"
    ; controlledFailureShape-v =
        refl
    ; controlledFailureRecorded =
        true
    ; controlledFailureRecordedIsTrue =
        refl
    ; failureExplainsButDoesNotPromote =
        true
    ; failureExplainsButDoesNotPromoteIsTrue =
        refl
    ; failureBoundary =
        "Controlled Haag-duality failure is a diagnostic surface for gauge theories"
        ∷ "It does not construct the missing field net, observable net completion, or charge-sector category"
        ∷ "It does not promote a Standard Model, gauge group, or GRQFT receipt"
        ∷ []
    }

record DHRSelectionCriterionTarget : Setω where
  field
    primitiveBoundaryReceipt :
      DHRLocalisedTransportablePrimitiveBoundaryReceipt

    sector :
      SuperselectionSector →
      Set

    localizedEndomorphismTarget :
      SuperselectionSector →
      Set

    transportableLocalisationTarget :
      SuperselectionSector →
      Set

    finiteStatisticsTarget :
      SuperselectionSector →
      Set

    localisedEndomorphismPrimitive :
      SuperselectionSector →
      LocalisedEndomorphism

    transportablePrimitive :
      (ρ : LocalisedEndomorphism) →
      Transportable ρ

    intertwinerPrimitiveTarget :
      (ρ σ : LocalisedEndomorphism) →
      Intertwiner ρ σ →
      Set

    statisticsOperator :
      SuperselectionSector →
      SuperselectionSector →
      DHRStatisticsOperator

    statisticsFormulaSocket :
      (ρ σ : LocalisedEndomorphism) →
      DHRStatisticsFormulaSocket ρ σ

    statisticsOperatorFormulaAgreesTarget :
      (ρ σ : LocalisedEndomorphism) →
      DHRStatisticsFormulaSocket.statisticsOperatorCarrier
        (statisticsFormulaSocket ρ σ)
      ≡
      statisticsOperator
        (LocalisedEndomorphism.localisedSector ρ)
        (LocalisedEndomorphism.localisedSector σ)

    statisticsOperatorTarget :
      DHRStatisticsOperator →
      Set

    transportIntertwinerShape :
      String

    transportIntertwinerShape-v :
      transportIntertwinerShape
      ≡
      "rho-localized-in-O0-transported-to-O1-by-unitary-intertwiner-in-A-of-O0-union-O1"

    criterionProved :
      Bool

    criterionProvedIsFalse :
      criterionProved ≡ false

    selectionBoundary :
      List String

open DHRSelectionCriterionTarget public

data SuperselectionSectorTargetReceipt
  (sector : SuperselectionSector) :
  Set where
  superselectionSectorTargetReceiptOnly :
    SuperselectionSectorTargetReceipt sector

data DHRLocalizedEndomorphismTargetReceipt
  (sector : SuperselectionSector) :
  Set where
  dhrLocalizedEndomorphismTargetOnly :
    DHRLocalizedEndomorphismTargetReceipt sector

data DHRTransportableLocalisationTargetReceipt
  (sector : SuperselectionSector) :
  Set where
  dhrTransportableLocalisationTargetOnly :
    DHRTransportableLocalisationTargetReceipt sector

data DHRFiniteStatisticsTargetReceipt
  (sector : SuperselectionSector) :
  Set where
  dhrFiniteStatisticsTargetOnly :
    DHRFiniteStatisticsTargetReceipt sector

abstractSuperselectionSectorTarget :
  SuperselectionSector →
  Set
abstractSuperselectionSectorTarget sector =
  SuperselectionSectorTargetReceipt sector

abstractDHRLocalizedEndomorphismTarget :
  SuperselectionSector →
  Set
abstractDHRLocalizedEndomorphismTarget sector =
  DHRLocalizedEndomorphismTargetReceipt sector

abstractDHRTransportableLocalisationTarget :
  SuperselectionSector →
  Set
abstractDHRTransportableLocalisationTarget sector =
  DHRTransportableLocalisationTargetReceipt sector

abstractDHRFiniteStatisticsTarget :
  SuperselectionSector →
  Set
abstractDHRFiniteStatisticsTarget sector =
  DHRFiniteStatisticsTargetReceipt sector

data IntertwinerPrimitiveTargetReceipt
  (ρ σ : LocalisedEndomorphism)
  (intertwiner : Intertwiner ρ σ) :
  Set where
  intertwinerPrimitiveTargetOnly :
    IntertwinerPrimitiveTargetReceipt ρ σ intertwiner

abstractIntertwinerPrimitiveTarget :
  (ρ σ : LocalisedEndomorphism) →
  Intertwiner ρ σ →
  Set
abstractIntertwinerPrimitiveTarget ρ σ intertwiner =
  IntertwinerPrimitiveTargetReceipt ρ σ intertwiner

abstractDHRStatisticsOperator :
  SuperselectionSector →
  SuperselectionSector →
  DHRStatisticsOperator
abstractDHRStatisticsOperator _ _ =
  dhrStatisticsOperatorTargetOnly

data DHRStatisticsFormulaOperationSocketTarget : Set where
  dhrStatisticsFormulaOperationSocketTargetOnly :
    DHRStatisticsFormulaOperationSocketTarget

abstractDHRStatisticsFormulaSocket :
  (ρ σ : LocalisedEndomorphism) →
  DHRStatisticsFormulaSocket ρ σ
abstractDHRStatisticsFormulaSocket ρ σ =
  record
    { ρTransport =
        abstractTransportablePrimitive ρ
    ; σTransport =
        abstractTransportablePrimitive σ
    ; spacelikeSeparatedTransportTargets =
        DHRTransportableLocalisationTargetReceipt
          (LocalisedEndomorphism.localisedSector ρ)
    ; statisticsOperatorCarrier =
        dhrStatisticsOperatorTargetOnly
    ; formulaShape =
        "epsilon-rho-sigma=V-star-times-sigma(U-star)-times-U-times-rho(V)"
    ; formulaShape-v =
        refl
    ; abstractOperationSocket =
        DHRStatisticsFormulaOperationSocketTarget
    ; formulaComputed =
        false
    ; formulaComputedIsFalse =
        refl
    ; formulaBoundary =
        "DHR statistics formula socket is typed, but the operation is a target-only receipt"
        ∷ "No epsilon-rho-sigma computation, braiding law, or DR reconstruction is promoted"
        ∷ []
    }

abstractDHRStatisticsOperatorFormulaAgreesTarget :
  (ρ σ : LocalisedEndomorphism) →
  DHRStatisticsFormulaSocket.statisticsOperatorCarrier
    (abstractDHRStatisticsFormulaSocket ρ σ)
  ≡
  abstractDHRStatisticsOperator
    (LocalisedEndomorphism.localisedSector ρ)
    (LocalisedEndomorphism.localisedSector σ)
abstractDHRStatisticsOperatorFormulaAgreesTarget ρ σ =
  refl

data DHRStatisticsOperatorTargetReceipt
  (operator : DHRStatisticsOperator) :
  Set where
  dhrStatisticsOperatorTargetReceiptOnly :
    DHRStatisticsOperatorTargetReceipt operator

abstractDHRStatisticsOperatorTarget :
  DHRStatisticsOperator →
  Set
abstractDHRStatisticsOperatorTarget operator =
  DHRStatisticsOperatorTargetReceipt operator

canonicalDHRFormalismPrimitiveReceipt :
  DHRFormalismPrimitiveReceipt
canonicalDHRFormalismPrimitiveReceipt =
  record
    { localisedTransportablePrimitiveBoundary =
        canonicalDHRLocalisedTransportablePrimitiveBoundaryReceipt
    ; formalismLocalisedEndomorphismPrimitive =
        abstractLocalisedEndomorphismPrimitive
    ; formalismTransportablePrimitive =
        abstractTransportablePrimitive
    ; formalismStatisticsOperatorPrimitive =
        abstractDHRStatisticsOperator
    ; formalismStatisticsFormulaSocket =
        abstractDHRStatisticsFormulaSocket
    ; localisedEndomorphismTyped =
        true
    ; localisedEndomorphismTypedIsTrue =
        refl
    ; transportableTyped =
        true
    ; transportableTypedIsTrue =
        refl
    ; statisticsOperatorTyped =
        true
    ; statisticsOperatorTypedIsTrue =
        refl
    ; statisticsComputed =
        false
    ; statisticsComputedIsFalse =
        refl
    ; formalismPrimitiveBoundary =
        "LocalisedEndomorphism and Transportable are typed DHR primitives over the AQFT net surface and routed through a primitive-boundary receipt"
        ∷ "The statistics operator epsilon-rho-sigma is typed with a formula socket, but no computation is promoted"
        ∷ "Doplicher-Roberts reconstruction authority cannot be invoked until the symmetric tensor C*-category hypotheses are supplied"
        ∷ []
    }

canonicalDHRSelectionCriterionTarget :
  DHRSelectionCriterionTarget
canonicalDHRSelectionCriterionTarget =
  record
    { primitiveBoundaryReceipt =
        canonicalDHRLocalisedTransportablePrimitiveBoundaryReceipt
    ; sector =
        abstractSuperselectionSectorTarget
    ; localizedEndomorphismTarget =
        abstractDHRLocalizedEndomorphismTarget
    ; transportableLocalisationTarget =
        abstractDHRTransportableLocalisationTarget
    ; finiteStatisticsTarget =
        abstractDHRFiniteStatisticsTarget
    ; localisedEndomorphismPrimitive =
        abstractLocalisedEndomorphismPrimitive
    ; transportablePrimitive =
        abstractTransportablePrimitive
    ; intertwinerPrimitiveTarget =
        abstractIntertwinerPrimitiveTarget
    ; statisticsOperator =
        abstractDHRStatisticsOperator
    ; statisticsFormulaSocket =
        abstractDHRStatisticsFormulaSocket
    ; statisticsOperatorFormulaAgreesTarget =
        abstractDHRStatisticsOperatorFormulaAgreesTarget
    ; statisticsOperatorTarget =
        abstractDHRStatisticsOperatorTarget
    ; transportIntertwinerShape =
        "rho-localized-in-O0-transported-to-O1-by-unitary-intertwiner-in-A-of-O0-union-O1"
    ; transportIntertwinerShape-v =
        refl
    ; criterionProved =
        false
    ; criterionProvedIsFalse =
        refl
    ; selectionBoundary =
        "DHR selection is a target requiring localized transportable endomorphisms and finite statistics"
        ∷ "LocalisedEndomorphism and Transportable are externally supplied DHR primitives wrapped by the fail-closed primitive-boundary receipt"
        ∷ "Intertwiner is an explicit target socket, but AQFT law inhabitants remain target sockets"
        ∷ "The statistics operator formula epsilon-rho-sigma = V-star times sigma(U-star) times U times rho(V) is recorded as an abstract operation socket"
        ∷ "The statistics operator epsilon-rho-sigma must be computed before Tannaka/Doplicher-Roberts reconstruction can be applied"
        ∷ "No superselection sector or charge transport theorem is constructed here"
        ∷ []
    }

record DHRCategoryPrimitiveSurface : Setω where
  field
    objectTarget :
      LocalisedEndomorphism →
      Set

    morphismTarget :
      (ρ σ : LocalisedEndomorphism) →
      Intertwiner ρ σ →
      Set

    tensorObjectTarget :
      LocalisedEndomorphism →
      LocalisedEndomorphism →
      Set

    tensorMorphismTarget :
      (ρ σ τ υ : LocalisedEndomorphism) →
      Intertwiner ρ σ →
      Intertwiner τ υ →
      Set

    unitObjectTarget :
      LocalisedEndomorphism →
      Set

    symmetryFromStatisticsTarget :
      (ρ σ : LocalisedEndomorphism) →
      DHRStatisticsFormulaSocket ρ σ →
      Set

    primitiveCategoryLawsProved :
      Bool

    primitiveCategoryLawsProvedIsFalse :
      primitiveCategoryLawsProved ≡ false

    primitiveBoundary :
      List String

open DHRCategoryPrimitiveSurface public

data DHRCategoryObjectTargetReceipt
  (ρ : LocalisedEndomorphism) :
  Set where
  dhrCategoryObjectTargetOnly :
    DHRCategoryObjectTargetReceipt ρ

data DHRCategoryMorphismTargetReceipt
  (ρ σ : LocalisedEndomorphism)
  (intertwiner : Intertwiner ρ σ) :
  Set where
  dhrCategoryMorphismTargetOnly :
    DHRCategoryMorphismTargetReceipt ρ σ intertwiner

data DHRCategoryTensorObjectTargetReceipt
  (ρ σ : LocalisedEndomorphism) :
  Set where
  dhrCategoryTensorObjectTargetOnly :
    DHRCategoryTensorObjectTargetReceipt ρ σ

data DHRCategoryTensorMorphismTargetReceipt
  (ρ σ τ υ : LocalisedEndomorphism)
  (left : Intertwiner ρ σ)
  (right : Intertwiner τ υ) :
  Set where
  dhrCategoryTensorMorphismTargetOnly :
    DHRCategoryTensorMorphismTargetReceipt ρ σ τ υ left right

data DHRCategoryUnitObjectTargetReceipt
  (ρ : LocalisedEndomorphism) :
  Set where
  dhrCategoryUnitObjectTargetOnly :
    DHRCategoryUnitObjectTargetReceipt ρ

data DHRCategorySymmetryFromStatisticsTargetReceipt
  (ρ σ : LocalisedEndomorphism)
  (socket : DHRStatisticsFormulaSocket ρ σ) :
  Set where
  dhrCategorySymmetryFromStatisticsTargetOnly :
    DHRCategorySymmetryFromStatisticsTargetReceipt ρ σ socket

abstractDHRCategoryObjectTarget :
  LocalisedEndomorphism →
  Set
abstractDHRCategoryObjectTarget ρ =
  DHRCategoryObjectTargetReceipt ρ

abstractDHRCategoryMorphismTarget :
  (ρ σ : LocalisedEndomorphism) →
  Intertwiner ρ σ →
  Set
abstractDHRCategoryMorphismTarget ρ σ intertwiner =
  DHRCategoryMorphismTargetReceipt ρ σ intertwiner

abstractDHRCategoryTensorObjectTarget :
  LocalisedEndomorphism →
  LocalisedEndomorphism →
  Set
abstractDHRCategoryTensorObjectTarget ρ σ =
  DHRCategoryTensorObjectTargetReceipt ρ σ

abstractDHRCategoryTensorMorphismTarget :
  (ρ σ τ υ : LocalisedEndomorphism) →
  Intertwiner ρ σ →
  Intertwiner τ υ →
  Set
abstractDHRCategoryTensorMorphismTarget ρ σ τ υ left right =
  DHRCategoryTensorMorphismTargetReceipt ρ σ τ υ left right

abstractDHRCategoryUnitObjectTarget :
  LocalisedEndomorphism →
  Set
abstractDHRCategoryUnitObjectTarget ρ =
  DHRCategoryUnitObjectTargetReceipt ρ

abstractDHRCategorySymmetryFromStatisticsTarget :
  (ρ σ : LocalisedEndomorphism) →
  DHRStatisticsFormulaSocket ρ σ →
  Set
abstractDHRCategorySymmetryFromStatisticsTarget ρ σ socket =
  DHRCategorySymmetryFromStatisticsTargetReceipt ρ σ socket

canonicalDHRCategoryPrimitiveSurface :
  DHRCategoryPrimitiveSurface
canonicalDHRCategoryPrimitiveSurface =
  record
    { objectTarget =
        abstractDHRCategoryObjectTarget
    ; morphismTarget =
        abstractDHRCategoryMorphismTarget
    ; tensorObjectTarget =
        abstractDHRCategoryTensorObjectTarget
    ; tensorMorphismTarget =
        abstractDHRCategoryTensorMorphismTarget
    ; unitObjectTarget =
        abstractDHRCategoryUnitObjectTarget
    ; symmetryFromStatisticsTarget =
        abstractDHRCategorySymmetryFromStatisticsTarget
    ; primitiveCategoryLawsProved =
        false
    ; primitiveCategoryLawsProvedIsFalse =
        refl
    ; primitiveBoundary =
        "DHR category primitives are LocalisedEndomorphism objects and Intertwiner morphisms"
        ∷ "Tensor product, unit object, and symmetry from the statistics operator are target sockets only"
        ∷ "No associativity, unit, C*-identity, conjugate, or symmetry law is proved here"
        ∷ []
    }

record SymmetricTensorCStarCategoryTarget : Setω where
  field
    selectionCriterion :
      DHRSelectionCriterionTarget

    categoryPrimitives :
      DHRCategoryPrimitiveSurface

    categoryCarrier :
      TensorCStarCategory

    tensorProductTarget :
      TensorCStarCategory →
      Set

    symmetryTarget :
      TensorCStarCategory →
      Set

    cstarStructureTarget :
      TensorCStarCategory →
      Set

    categoryConstructed :
      Bool

    categoryConstructedIsFalse :
      categoryConstructed ≡ false

    categoryBoundary :
      List String

open SymmetricTensorCStarCategoryTarget public

abstractTensorCStarCategory :
  TensorCStarCategory
abstractTensorCStarCategory =
  tensorCStarCategoryTargetOnly

data TensorProductTargetReceipt
  (category : TensorCStarCategory) :
  Set where
  tensorProductTargetOnly :
    TensorProductTargetReceipt category

data TensorSymmetryTargetReceipt
  (category : TensorCStarCategory) :
  Set where
  tensorSymmetryTargetOnly :
    TensorSymmetryTargetReceipt category

data CStarStructureTargetReceipt
  (category : TensorCStarCategory) :
  Set where
  cstarStructureTargetOnly :
    CStarStructureTargetReceipt category

abstractTensorProductTarget :
  TensorCStarCategory →
  Set
abstractTensorProductTarget category =
  TensorProductTargetReceipt category

abstractSymmetryTarget :
  TensorCStarCategory →
  Set
abstractSymmetryTarget category =
  TensorSymmetryTargetReceipt category

abstractCStarStructureTarget :
  TensorCStarCategory →
  Set
abstractCStarStructureTarget category =
  CStarStructureTargetReceipt category

canonicalSymmetricTensorCStarCategoryTarget :
  SymmetricTensorCStarCategoryTarget
canonicalSymmetricTensorCStarCategoryTarget =
  record
    { selectionCriterion =
        canonicalDHRSelectionCriterionTarget
    ; categoryPrimitives =
        canonicalDHRCategoryPrimitiveSurface
    ; categoryCarrier =
        abstractTensorCStarCategory
    ; tensorProductTarget =
        abstractTensorProductTarget
    ; symmetryTarget =
        abstractSymmetryTarget
    ; cstarStructureTarget =
        abstractCStarStructureTarget
    ; categoryConstructed =
        false
    ; categoryConstructedIsFalse =
        refl
    ; categoryBoundary =
        "The symmetric tensor C*-category is a target over DHR sectors"
        ∷ "Its primitive object and morphism sockets are LocalisedEndomorphism and Intertwiner"
        ∷ "Tensor product, symmetry, conjugates, and C*-structure are not inhabited here"
        ∷ []
    }

data DoplicherRobertsTheoremHypothesesTargetReceipt
  (category : TensorCStarCategory) :
  Set where
  doplicherRobertsTheoremHypothesesTargetOnly :
    DoplicherRobertsTheoremHypothesesTargetReceipt category

abstractDoplicherRobertsTheoremHypothesesTarget :
  TensorCStarCategory →
  Set
abstractDoplicherRobertsTheoremHypothesesTarget category =
  DoplicherRobertsTheoremHypothesesTargetReceipt category

data DHRStatisticsParity : Set where
  bosonicStatistics :
    DHRStatisticsParity

  fermionicStatistics :
    DHRStatisticsParity

data DoplicherRobertsGaugeOutputKind : Set where
  compactGroupOutput :
    DoplicherRobertsGaugeOutputKind

  compactSupergroupOutput :
    DoplicherRobertsGaugeOutputKind

record DRH1SymmetricTensorStarCategory : Setω where
  field
    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    objectDescription :
      String

    objectDescription-v :
      objectDescription
      ≡
      "objects-are-localised-transportable-endomorphism-classes"

    morphismDescription :
      String

    morphismDescription-v :
      morphismDescription
      ≡
      "morphisms-are-intertwiners-t-with-t-rho-a-equals-sigma-a-t"

    tensorDescription :
      String

    tensorDescription-v :
      tensorDescription
      ≡
      "tensor-product-is-composition-of-DHR-endomorphisms"

    starDescription :
      String

    starDescription-v :
      starDescription
      ≡
      "star-structure-is-Hilbert-space-adjoint-on-intertwiners"

    statisticsOperatorSymmetryTarget :
      (ρ σ : LocalisedEndomorphism) →
      DHRStatisticsFormulaSocket ρ σ →
      Set

    braidInvolutiveTarget :
      (ρ σ : LocalisedEndomorphism) →
      Set

    spacetimeDimensionAtLeastThreeTarget :
      Set

    bosonicSectorRecorded :
      Bool

    bosonicSectorRecordedIsTrue :
      bosonicSectorRecorded ≡ true

    fermionicSectorRecorded :
      Bool

    fermionicSectorRecordedIsTrue :
      fermionicSectorRecorded ≡ true

    supergroupNeededWhenFermionicStatistics :
      DHRStatisticsParity →
      DoplicherRobertsGaugeOutputKind

    h1Recorded :
      Bool

    h1RecordedIsTrue :
      h1Recorded ≡ true

    h1Boundary :
      List String

open DRH1SymmetricTensorStarCategory public

record DRH2Conjugates : Setω where
  field
    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    conjugateEndomorphismTarget :
      LocalisedEndomorphism →
      LocalisedEndomorphism →
      Set

    cptConjugateDescription :
      String

    cptConjugateDescription-v :
      cptConjugateDescription
      ≡
      "conjugate-endomorphism-is-CPT-anti-endomorphism-sector"

    reehSchliederInputTarget :
      Set

    reehSchliederForDASHIReceipt :
      AQFTColim.ReehSchliederForDASHIReceipt

    coevaluationIntertwinerTarget :
      (ρ ρbar : LocalisedEndomorphism) →
      Set

    evaluationIntertwinerTarget :
      (ρ ρbar : LocalisedEndomorphism) →
      Set

    conjugateEquationsTarget :
      (ρ ρbar : LocalisedEndomorphism) →
      Set

    h2Recorded :
      Bool

    h2RecordedIsTrue :
      h2Recorded ≡ true

    h2Boundary :
      List String

open DRH2Conjugates public

record DRH3DirectSums : Setω where
  field
    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    typeIIIProjectionSupplyTarget :
      AQFT.Region →
      Set

    directSumProjectionTarget :
      (ρ σ : LocalisedEndomorphism) →
      Set

    directSumEndomorphismTarget :
      (ρ σ : LocalisedEndomorphism) →
      LocalisedEndomorphism →
      Set

    directSumDescription :
      String

    directSumDescription-v :
      directSumDescription
      ≡
      "direct-sums-are-implemented-by-type-III-factor-projections-in-local-algebras"

    h3Recorded :
      Bool

    h3RecordedIsTrue :
      h3Recorded ≡ true

    h3Boundary :
      List String

open DRH3DirectSums public

record DRH4Subobjects : Setω where
  field
    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    endomorphismProjectionTarget :
      LocalisedEndomorphism →
      Set

    subobjectSplitTarget :
      (ρ : LocalisedEndomorphism) →
      Set

    subEndomorphismTransportableTarget :
      (ρ : LocalisedEndomorphism) →
      Set

    typeIIIFactorProjectionReason :
      String

    typeIIIFactorProjectionReason-v :
      typeIIIFactorProjectionReason
      ≡
      "type-III-factor-projections-split-DHR-subobjects"

    h4Recorded :
      Bool

    h4RecordedIsTrue :
      h4Recorded ≡ true

    h4Boundary :
      List String

open DRH4Subobjects public

record DRH5EndUnitScalars : Setω where
  field
    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    unitEndomorphismTarget :
      LocalisedEndomorphism →
      Set

    endUnitIntertwinerTarget :
      Set

    haagDualityInput :
      HaagDualityReceiptTarget

    reehSchliederCyclicityInputTarget :
      Set

    reehSchliederForDASHIReceipt :
      AQFTColim.ReehSchliederForDASHIReceipt

    irreducibilityInputTarget :
      Set

    scalarCentreTarget :
      Set

    endUnitComplexScalarsTarget :
      Set

    endUnitDescription :
      String

    endUnitDescription-v :
      endUnitDescription
      ≡
      "End-of-tensor-unit-is-complex-scalars-by-Haag-duality-Reeh-Schlieder-cyclicity-and-irreducibility"

    h5Recorded :
      Bool

    h5RecordedIsTrue :
      h5Recorded ≡ true

    h5Boundary :
      List String

open DRH5EndUnitScalars public

data DHRDRInternalAxiomKind : Set where
  symmetricTensorStructureAxiom :
    DHRDRInternalAxiomKind

  starStructureAxiom :
    DHRDRInternalAxiomKind

  conjugatesDualsAxiom :
    DHRDRInternalAxiomKind

  directSumsSubobjectsAxiom :
    DHRDRInternalAxiomKind

  endUnitComplexScalarsAxiom :
    DHRDRInternalAxiomKind

canonicalDHRDRInternalAxiomKindOrder :
  List DHRDRInternalAxiomKind
canonicalDHRDRInternalAxiomKindOrder =
  symmetricTensorStructureAxiom
  ∷ starStructureAxiom
  ∷ conjugatesDualsAxiom
  ∷ directSumsSubobjectsAxiom
  ∷ endUnitComplexScalarsAxiom
  ∷ []

data DHRDRInternalAxiomResidualBlocker : Set where
  residualSymmetricTensorNaturalityAndHexagonLaw :
    DHRDRInternalAxiomResidualBlocker

  residualCStarAdjointAndNormLaw :
    DHRDRInternalAxiomResidualBlocker

  residualConjugateEquationInhabitant :
    DHRDRInternalAxiomResidualBlocker

  residualTypeIIISplittingInhabitant :
    DHRDRInternalAxiomResidualBlocker

  residualHaagDualityIrreducibilityScalarCentreProof :
    DHRDRInternalAxiomResidualBlocker

  residualDRTheoremAuthorityApplication :
    DHRDRInternalAxiomResidualBlocker

record DHRDRSymmetricTensorStructureReceipt : Setω where
  field
    h1SymmetricTensorStarCategory :
      DRH1SymmetricTensorStarCategory

    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    tensorProductShape :
      String

    tensorProductShape-v :
      tensorProductShape
      ≡
      "tensor-product-is-composition-of-DHR-endomorphisms"

    symmetryShape :
      String

    symmetryShape-v :
      symmetryShape
      ≡
      "symmetry-is-statistics-operator-with-involutive-braid-in-spacetime-dimension-at-least-three"

    axiomKind :
      DHRDRInternalAxiomKind

    axiomKind-v :
      axiomKind ≡ symmetricTensorStructureAxiom

    receiptTyped :
      Bool

    receiptTypedIsTrue :
      receiptTyped ≡ true

    lawPromoted :
      Bool

    lawPromotedIsFalse :
      lawPromoted ≡ false

    residualBlocker :
      DHRDRInternalAxiomResidualBlocker

    residualBlocker-v :
      residualBlocker ≡ residualSymmetricTensorNaturalityAndHexagonLaw

    receiptBoundary :
      List String

open DHRDRSymmetricTensorStructureReceipt public

record DHRDRStarStructureReceipt : Setω where
  field
    h1SymmetricTensorStarCategory :
      DRH1SymmetricTensorStarCategory

    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    starShape :
      String

    starShape-v :
      starShape
      ≡
      "star-structure-is-Hilbert-space-adjoint-on-intertwiners"

    cstarStructureTarget :
      TensorCStarCategory →
      Set

    axiomKind :
      DHRDRInternalAxiomKind

    axiomKind-v :
      axiomKind ≡ starStructureAxiom

    receiptTyped :
      Bool

    receiptTypedIsTrue :
      receiptTyped ≡ true

    cstarLawPromoted :
      Bool

    cstarLawPromotedIsFalse :
      cstarLawPromoted ≡ false

    residualBlocker :
      DHRDRInternalAxiomResidualBlocker

    residualBlocker-v :
      residualBlocker ≡ residualCStarAdjointAndNormLaw

    receiptBoundary :
      List String

open DHRDRStarStructureReceipt public

record DHRDRConjugatesDualsReceipt : Setω where
  field
    h2Conjugates :
      DRH2Conjugates

    conjugateEndomorphismTarget :
      LocalisedEndomorphism →
      LocalisedEndomorphism →
      Set

    coevaluationIntertwinerTarget :
      (ρ ρbar : LocalisedEndomorphism) →
      Set

    evaluationIntertwinerTarget :
      (ρ ρbar : LocalisedEndomorphism) →
      Set

    conjugateEquationsTarget :
      (ρ ρbar : LocalisedEndomorphism) →
      Set

    reehSchliederForDASHIReceipt :
      AQFTColim.ReehSchliederForDASHIReceipt

    axiomKind :
      DHRDRInternalAxiomKind

    axiomKind-v :
      axiomKind ≡ conjugatesDualsAxiom

    receiptTyped :
      Bool

    receiptTypedIsTrue :
      receiptTyped ≡ true

    conjugateEquationsPromoted :
      Bool

    conjugateEquationsPromotedIsFalse :
      conjugateEquationsPromoted ≡ false

    residualBlocker :
      DHRDRInternalAxiomResidualBlocker

    residualBlocker-v :
      residualBlocker ≡ residualConjugateEquationInhabitant

    receiptBoundary :
      List String

open DHRDRConjugatesDualsReceipt public

record DHRDRDirectSumsSubobjectsReceipt : Setω where
  field
    h3DirectSums :
      DRH3DirectSums

    h4Subobjects :
      DRH4Subobjects

    directSumProjectionTarget :
      (ρ σ : LocalisedEndomorphism) →
      Set

    directSumEndomorphismTarget :
      (ρ σ : LocalisedEndomorphism) →
      LocalisedEndomorphism →
      Set

    endomorphismProjectionTarget :
      LocalisedEndomorphism →
      Set

    subobjectSplitTarget :
      (ρ : LocalisedEndomorphism) →
      Set

    subEndomorphismTransportableTarget :
      (ρ : LocalisedEndomorphism) →
      Set

    axiomKind :
      DHRDRInternalAxiomKind

    axiomKind-v :
      axiomKind ≡ directSumsSubobjectsAxiom

    receiptTyped :
      Bool

    receiptTypedIsTrue :
      receiptTyped ≡ true

    splittingPromoted :
      Bool

    splittingPromotedIsFalse :
      splittingPromoted ≡ false

    residualBlocker :
      DHRDRInternalAxiomResidualBlocker

    residualBlocker-v :
      residualBlocker ≡ residualTypeIIISplittingInhabitant

    receiptBoundary :
      List String

open DHRDRDirectSumsSubobjectsReceipt public

record DHRDREndUnitComplexScalarsReceipt : Setω where
  field
    h5EndUnitScalars :
      DRH5EndUnitScalars

    haagDualityInput :
      HaagDualityReceiptTarget

    reehSchliederForDASHIReceipt :
      AQFTColim.ReehSchliederForDASHIReceipt

    scalarCentreTarget :
      Set

    endUnitComplexScalarsTarget :
      Set

    endUnitShape :
      String

    endUnitShape-v :
      endUnitShape
      ≡
      "End-of-tensor-unit-is-complex-scalars-by-Haag-duality-Reeh-Schlieder-cyclicity-and-irreducibility"

    axiomKind :
      DHRDRInternalAxiomKind

    axiomKind-v :
      axiomKind ≡ endUnitComplexScalarsAxiom

    receiptTyped :
      Bool

    receiptTypedIsTrue :
      receiptTyped ≡ true

    endUnitProofPromoted :
      Bool

    endUnitProofPromotedIsFalse :
      endUnitProofPromoted ≡ false

    residualBlocker :
      DHRDRInternalAxiomResidualBlocker

    residualBlocker-v :
      residualBlocker ≡ residualHaagDualityIrreducibilityScalarCentreProof

    receiptBoundary :
      List String

open DHRDREndUnitComplexScalarsReceipt public

record DHRDRInternalAxiomReceiptPack : Setω where
  field
    symmetricTensorStructureReceipt :
      DHRDRSymmetricTensorStructureReceipt

    starStructureReceipt :
      DHRDRStarStructureReceipt

    conjugatesDualsReceipt :
      DHRDRConjugatesDualsReceipt

    directSumsSubobjectsReceipt :
      DHRDRDirectSumsSubobjectsReceipt

    endUnitComplexScalarsReceipt :
      DHRDREndUnitComplexScalarsReceipt

    axiomKindOrder :
      List DHRDRInternalAxiomKind

    axiomKindOrderIsCanonical :
      axiomKindOrder ≡ canonicalDHRDRInternalAxiomKindOrder

    allFiveInternalAxiomReceiptsTyped :
      Bool

    allFiveInternalAxiomReceiptsTypedIsTrue :
      allFiveInternalAxiomReceiptsTyped ≡ true

    drTheoremAuthorityStillRequired :
      DHRDRInternalAxiomResidualBlocker

    drTheoremAuthorityStillRequired-v :
      drTheoremAuthorityStillRequired ≡ residualDRTheoremAuthorityApplication

    reconstructsGaugeGroupHere :
      Bool

    reconstructsGaugeGroupHereIsFalse :
      reconstructsGaugeGroupHere ≡ false

    receiptPackBoundary :
      List String

open DHRDRInternalAxiomReceiptPack public

record DRHypothesesForDASHI : Setω where
  field
    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    h1SymmetricTensorStarCategory :
      DRH1SymmetricTensorStarCategory

    h2Conjugates :
      DRH2Conjugates

    h3DirectSums :
      DRH3DirectSums

    h4Subobjects :
      DRH4Subobjects

    h5EndUnitScalars :
      DRH5EndUnitScalars

    theoremHypothesesTarget :
      TensorCStarCategory →
      Set

    theoremHypothesesFedToAuthority :
      theoremHypothesesTarget
      ≡
      abstractDoplicherRobertsTheoremHypothesesTarget

    outputKindForStatistics :
      DHRStatisticsParity →
      DoplicherRobertsGaugeOutputKind

    bosonicCompactGroupCase :
      outputKindForStatistics bosonicStatistics
      ≡
      compactGroupOutput

    fermionicCompactSupergroupCase :
      outputKindForStatistics fermionicStatistics
      ≡
      compactSupergroupOutput

    hypothesesPackaged :
      Bool

    hypothesesPackagedIsTrue :
      hypothesesPackaged ≡ true

    reconstructsLaneDimension :
      Bool

    reconstructsLaneDimensionIsFalse :
      reconstructsLaneDimension ≡ false

    provesStandardModelMatching :
      Bool

    provesStandardModelMatchingIsFalse :
      provesStandardModelMatching ≡ false

    hypothesesBoundary :
      List String

open DRHypothesesForDASHI public

data DRStatisticsOperatorSymmetryTargetReceipt
  (ρ σ : LocalisedEndomorphism)
  (socket : DHRStatisticsFormulaSocket ρ σ) :
  Set where
  drStatisticsOperatorSymmetryTargetOnly :
    DRStatisticsOperatorSymmetryTargetReceipt ρ σ socket

abstractDRStatisticsOperatorSymmetryTarget :
  (ρ σ : LocalisedEndomorphism) →
  DHRStatisticsFormulaSocket ρ σ →
  Set
abstractDRStatisticsOperatorSymmetryTarget ρ σ socket =
  DRStatisticsOperatorSymmetryTargetReceipt ρ σ socket

data DRBraidInvolutiveTargetReceipt
  (ρ σ : LocalisedEndomorphism) :
  Set where
  drBraidInvolutiveTargetOnly :
    DRBraidInvolutiveTargetReceipt ρ σ

abstractDRBraidInvolutiveTarget :
  (ρ σ : LocalisedEndomorphism) →
  Set
abstractDRBraidInvolutiveTarget ρ σ =
  DRBraidInvolutiveTargetReceipt ρ σ

data DRSpacetimeDimensionAtLeastThreeTargetReceipt : Set where
  drSpacetimeDimensionAtLeastThreeTargetOnly :
    DRSpacetimeDimensionAtLeastThreeTargetReceipt

abstractDRSpacetimeDimensionAtLeastThreeTarget :
  Set
abstractDRSpacetimeDimensionAtLeastThreeTarget =
  DRSpacetimeDimensionAtLeastThreeTargetReceipt

data DRConjugateEndomorphismTargetReceipt
  (ρ ρbar : LocalisedEndomorphism) :
  Set where
  drConjugateEndomorphismTargetOnly :
    DRConjugateEndomorphismTargetReceipt ρ ρbar

abstractDRConjugateEndomorphismTarget :
  LocalisedEndomorphism →
  LocalisedEndomorphism →
  Set
abstractDRConjugateEndomorphismTarget ρ ρbar =
  DRConjugateEndomorphismTargetReceipt ρ ρbar

data DRReehSchliederInputTargetReceipt : Set where
  drReehSchliederInputTargetOnly :
    DRReehSchliederInputTargetReceipt

abstractDRReehSchliederInputTarget :
  Set
abstractDRReehSchliederInputTarget =
  DRReehSchliederInputTargetReceipt

data DRCoevaluationIntertwinerTargetReceipt
  (ρ ρbar : LocalisedEndomorphism) :
  Set where
  drCoevaluationIntertwinerTargetOnly :
    DRCoevaluationIntertwinerTargetReceipt ρ ρbar

abstractDRCoevaluationIntertwinerTarget :
  (ρ ρbar : LocalisedEndomorphism) →
  Set
abstractDRCoevaluationIntertwinerTarget ρ ρbar =
  DRCoevaluationIntertwinerTargetReceipt ρ ρbar

data DREvaluationIntertwinerTargetReceipt
  (ρ ρbar : LocalisedEndomorphism) :
  Set where
  drEvaluationIntertwinerTargetOnly :
    DREvaluationIntertwinerTargetReceipt ρ ρbar

abstractDREvaluationIntertwinerTarget :
  (ρ ρbar : LocalisedEndomorphism) →
  Set
abstractDREvaluationIntertwinerTarget ρ ρbar =
  DREvaluationIntertwinerTargetReceipt ρ ρbar

data DRConjugateEquationsTargetReceipt
  (ρ ρbar : LocalisedEndomorphism) :
  Set where
  drConjugateEquationsTargetOnly :
    DRConjugateEquationsTargetReceipt ρ ρbar

abstractDRConjugateEquationsTarget :
  (ρ ρbar : LocalisedEndomorphism) →
  Set
abstractDRConjugateEquationsTarget ρ ρbar =
  DRConjugateEquationsTargetReceipt ρ ρbar

data DRTypeIIIProjectionSupplyTargetReceipt
  (region : AQFT.Region) :
  Set where
  drTypeIIIProjectionSupplyTargetOnly :
    DRTypeIIIProjectionSupplyTargetReceipt region

abstractDRTypeIIIProjectionSupplyTarget :
  AQFT.Region →
  Set
abstractDRTypeIIIProjectionSupplyTarget region =
  DRTypeIIIProjectionSupplyTargetReceipt region

data DRDirectSumProjectionTargetReceipt
  (ρ σ : LocalisedEndomorphism) :
  Set where
  drDirectSumProjectionTargetOnly :
    DRDirectSumProjectionTargetReceipt ρ σ

abstractDRDirectSumProjectionTarget :
  (ρ σ : LocalisedEndomorphism) →
  Set
abstractDRDirectSumProjectionTarget ρ σ =
  DRDirectSumProjectionTargetReceipt ρ σ

data DRDirectSumEndomorphismTargetReceipt
  (ρ σ directSum : LocalisedEndomorphism) :
  Set where
  drDirectSumEndomorphismTargetOnly :
    DRDirectSumEndomorphismTargetReceipt ρ σ directSum

abstractDRDirectSumEndomorphismTarget :
  (ρ σ : LocalisedEndomorphism) →
  LocalisedEndomorphism →
  Set
abstractDRDirectSumEndomorphismTarget ρ σ directSum =
  DRDirectSumEndomorphismTargetReceipt ρ σ directSum

data DREndomorphismProjectionTargetReceipt
  (ρ : LocalisedEndomorphism) :
  Set where
  drEndomorphismProjectionTargetOnly :
    DREndomorphismProjectionTargetReceipt ρ

abstractDREndomorphismProjectionTarget :
  LocalisedEndomorphism →
  Set
abstractDREndomorphismProjectionTarget ρ =
  DREndomorphismProjectionTargetReceipt ρ

data DRSubobjectSplitTargetReceipt
  (ρ : LocalisedEndomorphism) :
  Set where
  drSubobjectSplitTargetOnly :
    DRSubobjectSplitTargetReceipt ρ

abstractDRSubobjectSplitTarget :
  (ρ : LocalisedEndomorphism) →
  Set
abstractDRSubobjectSplitTarget ρ =
  DRSubobjectSplitTargetReceipt ρ

data DRSubEndomorphismTransportableTargetReceipt
  (ρ : LocalisedEndomorphism) :
  Set where
  drSubEndomorphismTransportableTargetOnly :
    DRSubEndomorphismTransportableTargetReceipt ρ

abstractDRSubEndomorphismTransportableTarget :
  (ρ : LocalisedEndomorphism) →
  Set
abstractDRSubEndomorphismTransportableTarget ρ =
  DRSubEndomorphismTransportableTargetReceipt ρ

data DRUnitEndomorphismTargetReceipt
  (unit : LocalisedEndomorphism) :
  Set where
  drUnitEndomorphismTargetOnly :
    DRUnitEndomorphismTargetReceipt unit

abstractDRUnitEndomorphismTarget :
  LocalisedEndomorphism →
  Set
abstractDRUnitEndomorphismTarget unit =
  DRUnitEndomorphismTargetReceipt unit

data DREndUnitIntertwinerTargetReceipt : Set where
  drEndUnitIntertwinerTargetOnly :
    DREndUnitIntertwinerTargetReceipt

abstractDREndUnitIntertwinerTarget :
  Set
abstractDREndUnitIntertwinerTarget =
  DREndUnitIntertwinerTargetReceipt

data DRIrreducibilityInputTargetReceipt : Set where
  drIrreducibilityInputTargetOnly :
    DRIrreducibilityInputTargetReceipt

abstractDRIrreducibilityInputTarget :
  Set
abstractDRIrreducibilityInputTarget =
  DRIrreducibilityInputTargetReceipt

data DRScalarCentreTargetReceipt : Set where
  drScalarCentreTargetOnly :
    DRScalarCentreTargetReceipt

abstractDRScalarCentreTarget :
  Set
abstractDRScalarCentreTarget =
  DRScalarCentreTargetReceipt

data DREndUnitComplexScalarsTargetReceipt : Set where
  drEndUnitComplexScalarsTargetOnly :
    DREndUnitComplexScalarsTargetReceipt

abstractDREndUnitComplexScalarsTarget :
  Set
abstractDREndUnitComplexScalarsTarget =
  DREndUnitComplexScalarsTargetReceipt

canonicalDRStatisticsOutputKind :
  DHRStatisticsParity →
  DoplicherRobertsGaugeOutputKind
canonicalDRStatisticsOutputKind bosonicStatistics =
  compactGroupOutput
canonicalDRStatisticsOutputKind fermionicStatistics =
  compactSupergroupOutput

canonicalDRH1SymmetricTensorStarCategory :
  DRH1SymmetricTensorStarCategory
canonicalDRH1SymmetricTensorStarCategory =
  record
    { categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; objectDescription =
        "objects-are-localised-transportable-endomorphism-classes"
    ; objectDescription-v =
        refl
    ; morphismDescription =
        "morphisms-are-intertwiners-t-with-t-rho-a-equals-sigma-a-t"
    ; morphismDescription-v =
        refl
    ; tensorDescription =
        "tensor-product-is-composition-of-DHR-endomorphisms"
    ; tensorDescription-v =
        refl
    ; starDescription =
        "star-structure-is-Hilbert-space-adjoint-on-intertwiners"
    ; starDescription-v =
        refl
    ; statisticsOperatorSymmetryTarget =
        abstractDRStatisticsOperatorSymmetryTarget
    ; braidInvolutiveTarget =
        abstractDRBraidInvolutiveTarget
    ; spacetimeDimensionAtLeastThreeTarget =
        abstractDRSpacetimeDimensionAtLeastThreeTarget
    ; bosonicSectorRecorded =
        true
    ; bosonicSectorRecordedIsTrue =
        refl
    ; fermionicSectorRecorded =
        true
    ; fermionicSectorRecordedIsTrue =
        refl
    ; supergroupNeededWhenFermionicStatistics =
        canonicalDRStatisticsOutputKind
    ; h1Recorded =
        true
    ; h1RecordedIsTrue =
        refl
    ; h1Boundary =
        "H1 records the DHR category as a symmetric tensor star-category target"
        ∷ "The statistics operator supplies the symmetry and the involutive braid relation in spacetime dimension at least three"
        ∷ "Bosonic statistics reconstructs an ordinary compact group; fermionic sectors require compact supergroup language"
        ∷ []
    }

canonicalDRH2Conjugates :
  DRH2Conjugates
canonicalDRH2Conjugates =
  record
    { categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; conjugateEndomorphismTarget =
        abstractDRConjugateEndomorphismTarget
    ; cptConjugateDescription =
        "conjugate-endomorphism-is-CPT-anti-endomorphism-sector"
    ; cptConjugateDescription-v =
        refl
    ; reehSchliederInputTarget =
        AQFTColim.ReehSchliederForDASHIReceipt.dashiReehSchliederCyclicityTarget
          AQFTColim.canonicalReehSchliederForDASHIReceipt
    ; reehSchliederForDASHIReceipt =
        AQFTColim.canonicalReehSchliederForDASHIReceipt
    ; coevaluationIntertwinerTarget =
        abstractDRCoevaluationIntertwinerTarget
    ; evaluationIntertwinerTarget =
        abstractDREvaluationIntertwinerTarget
    ; conjugateEquationsTarget =
        abstractDRConjugateEquationsTarget
    ; h2Recorded =
        true
    ; h2RecordedIsTrue =
        refl
    ; h2Boundary =
        "H2 records conjugates for every DHR endomorphism"
        ∷ "The proof route is CPT/Reeh-Schlieder: the conjugate is the anti-endomorphism sector with evaluation and coevaluation intertwiners"
        ∷ "The Reeh-Schlieder input is the DASHI closed/immediate receipt: for non-empty bounded O, A(O) Omega is dense in H"
        ∷ "The conjugate equations remain explicit target sockets on the DHR category"
        ∷ []
    }

canonicalDRH3DirectSums :
  DRH3DirectSums
canonicalDRH3DirectSums =
  record
    { categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; typeIIIProjectionSupplyTarget =
        abstractDRTypeIIIProjectionSupplyTarget
    ; directSumProjectionTarget =
        abstractDRDirectSumProjectionTarget
    ; directSumEndomorphismTarget =
        abstractDRDirectSumEndomorphismTarget
    ; directSumDescription =
        "direct-sums-are-implemented-by-type-III-factor-projections-in-local-algebras"
    ; directSumDescription-v =
        refl
    ; h3Recorded =
        true
    ; h3RecordedIsTrue =
        refl
    ; h3Boundary =
        "H3 records direct sums of DHR endomorphisms"
        ∷ "The proof route uses the type III factor property of local algebras to supply enough equivalent projections"
        ∷ "This packages the direct-sum hypothesis for DR but does not identify any Standard Model representation"
        ∷ []
    }

canonicalDRH4Subobjects :
  DRH4Subobjects
canonicalDRH4Subobjects =
  record
    { categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; endomorphismProjectionTarget =
        abstractDREndomorphismProjectionTarget
    ; subobjectSplitTarget =
        abstractDRSubobjectSplitTarget
    ; subEndomorphismTransportableTarget =
        abstractDRSubEndomorphismTransportableTarget
    ; typeIIIFactorProjectionReason =
        "type-III-factor-projections-split-DHR-subobjects"
    ; typeIIIFactorProjectionReason-v =
        refl
    ; h4Recorded =
        true
    ; h4RecordedIsTrue =
        refl
    ; h4Boundary =
        "H4 records subobjects for DHR endomorphisms"
        ∷ "Every projection in Hom(rho,rho) is routed through a type III factor split target"
        ∷ "The resulting sub-endomorphism transportability remains a typed target, not a laneDimension computation"
        ∷ []
    }

canonicalDRH5EndUnitScalars :
  DRH5EndUnitScalars
canonicalDRH5EndUnitScalars =
  record
    { categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; unitEndomorphismTarget =
        abstractDRUnitEndomorphismTarget
    ; endUnitIntertwinerTarget =
        abstractDREndUnitIntertwinerTarget
    ; haagDualityInput =
        canonicalHaagDualityReceiptTarget
    ; reehSchliederCyclicityInputTarget =
        AQFTColim.ReehSchliederForDASHIReceipt.dashiReehSchliederCyclicityTarget
          AQFTColim.canonicalReehSchliederForDASHIReceipt
    ; reehSchliederForDASHIReceipt =
        AQFTColim.canonicalReehSchliederForDASHIReceipt
    ; irreducibilityInputTarget =
        abstractDRIrreducibilityInputTarget
    ; scalarCentreTarget =
        abstractDRScalarCentreTarget
    ; endUnitComplexScalarsTarget =
        abstractDREndUnitComplexScalarsTarget
    ; endUnitDescription =
        "End-of-tensor-unit-is-complex-scalars-by-Haag-duality-Reeh-Schlieder-cyclicity-and-irreducibility"
    ; endUnitDescription-v =
        refl
    ; h5Recorded =
        true
    ; h5RecordedIsTrue =
        refl
    ; h5Boundary =
        "H5 records End(1) is the complex scalars"
        ∷ "The tensor unit is the identity endomorphism and its intertwiners are central observables"
        ∷ "Haag duality plus the DASHI Reeh-Schlieder cyclicity receipt and irreducibility reduces the centre to scalars"
        ∷ []
    }

canonicalDHRDRSymmetricTensorStructureReceipt :
  DHRDRSymmetricTensorStructureReceipt
canonicalDHRDRSymmetricTensorStructureReceipt =
  record
    { h1SymmetricTensorStarCategory =
        canonicalDRH1SymmetricTensorStarCategory
    ; categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; tensorProductShape =
        "tensor-product-is-composition-of-DHR-endomorphisms"
    ; tensorProductShape-v =
        refl
    ; symmetryShape =
        "symmetry-is-statistics-operator-with-involutive-braid-in-spacetime-dimension-at-least-three"
    ; symmetryShape-v =
        refl
    ; axiomKind =
        symmetricTensorStructureAxiom
    ; axiomKind-v =
        refl
    ; receiptTyped =
        true
    ; receiptTypedIsTrue =
        refl
    ; lawPromoted =
        false
    ; lawPromotedIsFalse =
        refl
    ; residualBlocker =
        residualSymmetricTensorNaturalityAndHexagonLaw
    ; residualBlocker-v =
        refl
    ; receiptBoundary =
        "Concrete receipt for the internal symmetric tensor structure axiom is inhabited from H1"
        ∷ "It records the tensor-as-composition and statistics-symmetry shapes as typed data"
        ∷ "Naturality, hexagon, and coherence law inhabitants remain fail-closed"
        ∷ []
    }

canonicalDHRDRStarStructureReceipt :
  DHRDRStarStructureReceipt
canonicalDHRDRStarStructureReceipt =
  record
    { h1SymmetricTensorStarCategory =
        canonicalDRH1SymmetricTensorStarCategory
    ; categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; starShape =
        "star-structure-is-Hilbert-space-adjoint-on-intertwiners"
    ; starShape-v =
        refl
    ; cstarStructureTarget =
        SymmetricTensorCStarCategoryTarget.cstarStructureTarget
          canonicalSymmetricTensorCStarCategoryTarget
    ; axiomKind =
        starStructureAxiom
    ; axiomKind-v =
        refl
    ; receiptTyped =
        true
    ; receiptTypedIsTrue =
        refl
    ; cstarLawPromoted =
        false
    ; cstarLawPromotedIsFalse =
        refl
    ; residualBlocker =
        residualCStarAdjointAndNormLaw
    ; residualBlocker-v =
        refl
    ; receiptBoundary =
        "Concrete receipt for the internal star structure axiom is inhabited from H1"
        ∷ "It records the Hilbert-space-adjoint-on-intertwiners route and the C*-structure target"
        ∷ "The C*-identity, adjoint compatibility, and norm law remain fail-closed"
        ∷ []
    }

canonicalDHRDRConjugatesDualsReceipt :
  DHRDRConjugatesDualsReceipt
canonicalDHRDRConjugatesDualsReceipt =
  record
    { h2Conjugates =
        canonicalDRH2Conjugates
    ; conjugateEndomorphismTarget =
        abstractDRConjugateEndomorphismTarget
    ; coevaluationIntertwinerTarget =
        abstractDRCoevaluationIntertwinerTarget
    ; evaluationIntertwinerTarget =
        abstractDREvaluationIntertwinerTarget
    ; conjugateEquationsTarget =
        abstractDRConjugateEquationsTarget
    ; reehSchliederForDASHIReceipt =
        AQFTColim.canonicalReehSchliederForDASHIReceipt
    ; axiomKind =
        conjugatesDualsAxiom
    ; axiomKind-v =
        refl
    ; receiptTyped =
        true
    ; receiptTypedIsTrue =
        refl
    ; conjugateEquationsPromoted =
        false
    ; conjugateEquationsPromotedIsFalse =
        refl
    ; residualBlocker =
        residualConjugateEquationInhabitant
    ; residualBlocker-v =
        refl
    ; receiptBoundary =
        "Concrete receipt for the internal conjugates/duals axiom is inhabited from H2"
        ∷ "It threads conjugate endomorphism, evaluation, coevaluation, and conjugate-equation targets with the DASHI Reeh-Schlieder receipt"
        ∷ "The conjugate equations themselves remain fail-closed inhabitants, not proved laws"
        ∷ []
    }

canonicalDHRDRDirectSumsSubobjectsReceipt :
  DHRDRDirectSumsSubobjectsReceipt
canonicalDHRDRDirectSumsSubobjectsReceipt =
  record
    { h3DirectSums =
        canonicalDRH3DirectSums
    ; h4Subobjects =
        canonicalDRH4Subobjects
    ; directSumProjectionTarget =
        abstractDRDirectSumProjectionTarget
    ; directSumEndomorphismTarget =
        abstractDRDirectSumEndomorphismTarget
    ; endomorphismProjectionTarget =
        abstractDREndomorphismProjectionTarget
    ; subobjectSplitTarget =
        abstractDRSubobjectSplitTarget
    ; subEndomorphismTransportableTarget =
        abstractDRSubEndomorphismTransportableTarget
    ; axiomKind =
        directSumsSubobjectsAxiom
    ; axiomKind-v =
        refl
    ; receiptTyped =
        true
    ; receiptTypedIsTrue =
        refl
    ; splittingPromoted =
        false
    ; splittingPromotedIsFalse =
        refl
    ; residualBlocker =
        residualTypeIIISplittingInhabitant
    ; residualBlocker-v =
        refl
    ; receiptBoundary =
        "Concrete receipt for the internal direct-sums/subobjects axiom is inhabited from H3 and H4"
        ∷ "It records direct-sum projections, direct-sum endomorphism targets, endomorphism projections, subobject splits, and transportable sub-endomorphism targets"
        ∷ "The type III splitting inhabitant remains fail-closed"
        ∷ []
    }

canonicalDHRDREndUnitComplexScalarsReceipt :
  DHRDREndUnitComplexScalarsReceipt
canonicalDHRDREndUnitComplexScalarsReceipt =
  record
    { h5EndUnitScalars =
        canonicalDRH5EndUnitScalars
    ; haagDualityInput =
        canonicalHaagDualityReceiptTarget
    ; reehSchliederForDASHIReceipt =
        AQFTColim.canonicalReehSchliederForDASHIReceipt
    ; scalarCentreTarget =
        abstractDRScalarCentreTarget
    ; endUnitComplexScalarsTarget =
        abstractDREndUnitComplexScalarsTarget
    ; endUnitShape =
        "End-of-tensor-unit-is-complex-scalars-by-Haag-duality-Reeh-Schlieder-cyclicity-and-irreducibility"
    ; endUnitShape-v =
        refl
    ; axiomKind =
        endUnitComplexScalarsAxiom
    ; axiomKind-v =
        refl
    ; receiptTyped =
        true
    ; receiptTypedIsTrue =
        refl
    ; endUnitProofPromoted =
        false
    ; endUnitProofPromotedIsFalse =
        refl
    ; residualBlocker =
        residualHaagDualityIrreducibilityScalarCentreProof
    ; residualBlocker-v =
        refl
    ; receiptBoundary =
        "Concrete receipt for the internal End(1) ~= C axiom is inhabited from H5"
        ∷ "It threads Haag-duality input, the DASHI Reeh-Schlieder receipt, scalar-centre target, and complex-scalar target"
        ∷ "The local scalar-centre proof remains fail-closed behind Haag duality and irreducibility"
        ∷ []
    }

canonicalDHRDRInternalAxiomReceiptPack :
  DHRDRInternalAxiomReceiptPack
canonicalDHRDRInternalAxiomReceiptPack =
  record
    { symmetricTensorStructureReceipt =
        canonicalDHRDRSymmetricTensorStructureReceipt
    ; starStructureReceipt =
        canonicalDHRDRStarStructureReceipt
    ; conjugatesDualsReceipt =
        canonicalDHRDRConjugatesDualsReceipt
    ; directSumsSubobjectsReceipt =
        canonicalDHRDRDirectSumsSubobjectsReceipt
    ; endUnitComplexScalarsReceipt =
        canonicalDHRDREndUnitComplexScalarsReceipt
    ; axiomKindOrder =
        canonicalDHRDRInternalAxiomKindOrder
    ; axiomKindOrderIsCanonical =
        refl
    ; allFiveInternalAxiomReceiptsTyped =
        true
    ; allFiveInternalAxiomReceiptsTypedIsTrue =
        refl
    ; drTheoremAuthorityStillRequired =
        residualDRTheoremAuthorityApplication
    ; drTheoremAuthorityStillRequired-v =
        refl
    ; reconstructsGaugeGroupHere =
        false
    ; reconstructsGaugeGroupHereIsFalse =
        refl
    ; receiptPackBoundary =
        "The five internal DHR/DR-consumption axiom receipts are concrete typed inhabitants"
        ∷ "They cover symmetric tensor structure, star structure, conjugates/duals, direct sums/subobjects, and End(1) ~= C"
        ∷ "Each receipt records its remaining blocker; DR reconstruction remains an external theorem-authority application"
        ∷ []
    }

canonicalDRHypothesesForDASHI :
  DRHypothesesForDASHI
canonicalDRHypothesesForDASHI =
  record
    { categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; h1SymmetricTensorStarCategory =
        canonicalDRH1SymmetricTensorStarCategory
    ; h2Conjugates =
        canonicalDRH2Conjugates
    ; h3DirectSums =
        canonicalDRH3DirectSums
    ; h4Subobjects =
        canonicalDRH4Subobjects
    ; h5EndUnitScalars =
        canonicalDRH5EndUnitScalars
    ; theoremHypothesesTarget =
        abstractDoplicherRobertsTheoremHypothesesTarget
    ; theoremHypothesesFedToAuthority =
        refl
    ; outputKindForStatistics =
        canonicalDRStatisticsOutputKind
    ; bosonicCompactGroupCase =
        refl
    ; fermionicCompactSupergroupCase =
        refl
    ; hypothesesPackaged =
        true
    ; hypothesesPackagedIsTrue =
        refl
    ; reconstructsLaneDimension =
        false
    ; reconstructsLaneDimensionIsFalse =
        refl
    ; provesStandardModelMatching =
        false
    ; provesStandardModelMatchingIsFalse =
        refl
    ; hypothesesBoundary =
        "The five Doplicher-Roberts hypotheses H1-H5 are packaged for the DASHI DHR category"
        ∷ "This receipt feeds the existing Doplicher-Roberts theorem-hypotheses authority socket"
        ∷ "DR reconstructs a compact group in the bosonic case and compact supergroup language when fermionic statistics is present"
        ∷ "The hypothesis package does not compute laneDimension and does not prove G_DHR equals the Standard Model gauge group"
        ∷ []
    }

data TierBPaper3Delta3cDRCompletenessCheckpoint : Set where
  h1SymmetricTensorStarCategoryCheckpoint :
    TierBPaper3Delta3cDRCompletenessCheckpoint

  h2ConjugatesCheckpoint :
    TierBPaper3Delta3cDRCompletenessCheckpoint

  h3DirectSumsCheckpoint :
    TierBPaper3Delta3cDRCompletenessCheckpoint

  h4SubobjectsCheckpoint :
    TierBPaper3Delta3cDRCompletenessCheckpoint

  h5EndUnitScalarsCheckpoint :
    TierBPaper3Delta3cDRCompletenessCheckpoint

canonicalTierBPaper3Delta3cDRCompletenessCheckpoints :
  List TierBPaper3Delta3cDRCompletenessCheckpoint
canonicalTierBPaper3Delta3cDRCompletenessCheckpoints =
  h1SymmetricTensorStarCategoryCheckpoint
  ∷ h2ConjugatesCheckpoint
  ∷ h3DirectSumsCheckpoint
  ∷ h4SubobjectsCheckpoint
  ∷ h5EndUnitScalarsCheckpoint
  ∷ []

record TierBPaper3Delta3cH1H5CompletenessCheck : Setω where
  field
    dhrHypotheses :
      DRHypothesesForDASHI

    h1SymmetricTensorStarCategory :
      DRH1SymmetricTensorStarCategory

    h2Conjugates :
      DRH2Conjugates

    h3DirectSums :
      DRH3DirectSums

    h4Subobjects :
      DRH4Subobjects

    h5EndUnitScalars :
      DRH5EndUnitScalars

    completenessCheckpoints :
      List TierBPaper3Delta3cDRCompletenessCheckpoint

    completenessCheckpointsAreCanonical :
      completenessCheckpoints
      ≡
      canonicalTierBPaper3Delta3cDRCompletenessCheckpoints

    h5HaagDualityInput :
      HaagDualityReceiptTarget

    h5ReehSchliederCyclicityInputTarget :
      Set

    h2h5ReehSchliederForDASHIReceipt :
      AQFTColim.ReehSchliederForDASHIReceipt

    reehSchliederCitation :
      String

    reehSchliederCitation-v :
      reehSchliederCitation
      ≡
      "Reeh-Schlieder-1961"

    h5DependencyLabel :
      String

    h5DependencyLabel-v :
      h5DependencyLabel
      ≡
      "End(1)~=C-needs-Haag-duality-plus-Reeh-Schlieder-cyclicity"

    h1ToH5CompletenessRecorded :
      Bool

    h1ToH5CompletenessRecordedIsTrue :
      h1ToH5CompletenessRecorded ≡ true

    h5LocalProofSupplied :
      Bool

    h5LocalProofSuppliedIsFalse :
      h5LocalProofSupplied ≡ false

    drReconstructionPromotedByCheck :
      Bool

    drReconstructionPromotedByCheckIsFalse :
      drReconstructionPromotedByCheck ≡ false

    delta3cBoundary :
      List String

open TierBPaper3Delta3cH1H5CompletenessCheck public

canonicalTierBPaper3Delta3cH1H5CompletenessCheck :
  TierBPaper3Delta3cH1H5CompletenessCheck
canonicalTierBPaper3Delta3cH1H5CompletenessCheck =
  record
    { dhrHypotheses =
        canonicalDRHypothesesForDASHI
    ; h1SymmetricTensorStarCategory =
        canonicalDRH1SymmetricTensorStarCategory
    ; h2Conjugates =
        canonicalDRH2Conjugates
    ; h3DirectSums =
        canonicalDRH3DirectSums
    ; h4Subobjects =
        canonicalDRH4Subobjects
    ; h5EndUnitScalars =
        canonicalDRH5EndUnitScalars
    ; completenessCheckpoints =
        canonicalTierBPaper3Delta3cDRCompletenessCheckpoints
    ; completenessCheckpointsAreCanonical =
        refl
    ; h5HaagDualityInput =
        canonicalHaagDualityReceiptTarget
    ; h5ReehSchliederCyclicityInputTarget =
        AQFTColim.ReehSchliederForDASHIReceipt.dashiReehSchliederCyclicityTarget
          AQFTColim.canonicalReehSchliederForDASHIReceipt
    ; h2h5ReehSchliederForDASHIReceipt =
        AQFTColim.canonicalReehSchliederForDASHIReceipt
    ; reehSchliederCitation =
        "Reeh-Schlieder-1961"
    ; reehSchliederCitation-v =
        refl
    ; h5DependencyLabel =
        "End(1)~=C-needs-Haag-duality-plus-Reeh-Schlieder-cyclicity"
    ; h5DependencyLabel-v =
        refl
    ; h1ToH5CompletenessRecorded =
        true
    ; h1ToH5CompletenessRecordedIsTrue =
        refl
    ; h5LocalProofSupplied =
        false
    ; h5LocalProofSuppliedIsFalse =
        refl
    ; drReconstructionPromotedByCheck =
        false
    ; drReconstructionPromotedByCheckIsFalse =
        refl
    ; delta3cBoundary =
        "Delta 3c records the H1-H5 completeness checklist for the DHR/DR authority gate"
        ∷ "H2 conjugates and H5 End(1) ~= C consume the DASHI Reeh-Schlieder receipt, which is closed/immediate from existing AQFT receipt dependencies"
        ∷ "H5 End(1) ~= C is explicitly dependent on Haag duality plus Reeh-Schlieder cyclicity, with Reeh-Schlieder 1961 cited and the DASHI dense-orbit receipt routed through AQFT axioms"
        ∷ "The checklist does not supply an independent local H5 proof and does not promote Doplicher-Roberts reconstruction"
        ∷ []
    }

record DoplicherRobertsReconstruction : Setω where
  field
    sourceSymmetricTensorCStarCategory :
      TensorCStarCategory

    reconstructedCompactGroup :
      CompactGaugeGroup

    representationCategoryOfCompactGroup :
      CompactGaugeGroup →
      Set

    categoryEquivalenceToRepG :
      TensorCStarCategory →
      CompactGaugeGroup →
      Set

    theoremHypothesesTarget :
      TensorCStarCategory →
      Set

    reconstructionPostulate :
      TensorCStarCategory →
      CompactGaugeGroup →
      Set

    reconstructionAuthorityShape :
      String

    reconstructionAuthorityShape-v :
      reconstructionAuthorityShape
      ≡
      "symmetric-tensor-C-star-category-reconstructs-compact-group-and-category-equivalence-to-Rep-G"

    citationTokens :
      List DoplicherRobertsAuthorityCitation

    citationTokensAreCanonical :
      citationTokens
      ≡
      canonicalDoplicherRobertsAuthorityCitations

    safeAuthority :
      Bool

    safeAuthorityIsTrue :
      safeAuthority ≡ true

    standardModelMatchingRemainsOpen :
      Bool

    standardModelMatchingRemainsOpenIsTrue :
      standardModelMatchingRemainsOpen ≡ true

    laneDimensionInternallyPromoted :
      Bool

    laneDimensionInternallyPromotedIsTrue :
      laneDimensionInternallyPromoted ≡ true

    laneDimensionComputedByDLM :
      Bool

    laneDimensionComputedByDLMIsTrue :
      laneDimensionComputedByDLM ≡ true

    laneDimensionDoesNotPromoteDHRSMMatching :
      Bool

    laneDimensionDoesNotPromoteDHRSMMatchingIsTrue :
      laneDimensionDoesNotPromoteDHRSMMatching ≡ true

    dhrEqualsStandardModelPromoted :
      Bool

    dhrEqualsStandardModelPromotedIsFalse :
      dhrEqualsStandardModelPromoted ≡ false

    boundary :
      List String

open DoplicherRobertsReconstruction public

record DoplicherRobertsReconstructionAuthoritySurface : Setω where
  field
    doplicherRobertsReconstruction :
      DoplicherRobertsReconstruction

    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    dashiDRHypotheses :
      DRHypothesesForDASHI

    primaryCitation :
      String

    primaryCitation-v :
      primaryCitation
      ≡
      "Doplicher-Roberts-1989-Inventiones-Mathematicae-98-A-new-duality-theory-for-compact-groups"

    fieldAlgebraCitation :
      String

    fieldAlgebraCitation-v :
      fieldAlgebraCitation
      ≡
      "Doplicher-Roberts-1990-Communications-in-Mathematical-Physics-131-field-algebra-compact-gauge-group-superselection-structure"

    citationTokens :
      List DoplicherRobertsAuthorityCitation

    citationTokensAreCanonical :
      citationTokens
      ≡
      canonicalDoplicherRobertsAuthorityCitations

    theoremHypothesesTarget :
      TensorCStarCategory →
      Set

    reconstructionPostulate :
      TensorCStarCategory →
      CompactGaugeGroup →
      Set

    citedAuthorityRecorded :
      Bool

    citedAuthorityRecordedIsTrue :
      citedAuthorityRecorded ≡ true

    safeAuthorityRecorded :
      Bool

    safeAuthorityRecordedIsTrue :
      safeAuthorityRecorded ≡ true

    reconstructsGaugeGroupHere :
      Bool

    reconstructsGaugeGroupHereIsFalse :
      reconstructsGaugeGroupHere ≡ false

    authorityBoundary :
      List String

open DoplicherRobertsReconstructionAuthoritySurface public

data DoplicherRobertsReconstructionAuthorityTarget
  (category : TensorCStarCategory)
  (group : CompactGaugeGroup) :
  Set where
  doplicherRobertsReconstructionAuthorityTargetOnly :
    DoplicherRobertsReconstructionAuthorityTarget category group

abstractDoplicherRobertsReconstructionPostulate :
  TensorCStarCategory →
  CompactGaugeGroup →
  Set
abstractDoplicherRobertsReconstructionPostulate category group =
  DoplicherRobertsReconstructionAuthorityTarget category group

abstractDoplicherRobertsCompactGroup :
  CompactGaugeGroup
abstractDoplicherRobertsCompactGroup =
  compactGaugeGroupAuthorityTargetOnly

data CompactGroupRepresentationCategoryTargetReceipt
  (group : CompactGaugeGroup) :
  Set where
  compactGroupRepresentationCategoryTargetOnly :
    CompactGroupRepresentationCategoryTargetReceipt group

data DoplicherRobertsCategoryEquivalenceToRepGTargetReceipt
  (category : TensorCStarCategory)
  (group : CompactGaugeGroup) :
  Set where
  doplicherRobertsCategoryEquivalenceToRepGTargetOnly :
    DoplicherRobertsCategoryEquivalenceToRepGTargetReceipt category group

abstractCompactGroupRepresentationCategory :
  CompactGaugeGroup →
  Set
abstractCompactGroupRepresentationCategory group =
  CompactGroupRepresentationCategoryTargetReceipt group

abstractDoplicherRobertsCategoryEquivalenceToRepG :
  TensorCStarCategory →
  CompactGaugeGroup →
  Set
abstractDoplicherRobertsCategoryEquivalenceToRepG category group =
  DoplicherRobertsCategoryEquivalenceToRepGTargetReceipt category group

canonicalDoplicherRobertsReconstruction :
  DoplicherRobertsReconstruction
canonicalDoplicherRobertsReconstruction =
  record
    { sourceSymmetricTensorCStarCategory =
        SymmetricTensorCStarCategoryTarget.categoryCarrier
          canonicalSymmetricTensorCStarCategoryTarget
    ; reconstructedCompactGroup =
        abstractDoplicherRobertsCompactGroup
    ; representationCategoryOfCompactGroup =
        abstractCompactGroupRepresentationCategory
    ; categoryEquivalenceToRepG =
        abstractDoplicherRobertsCategoryEquivalenceToRepG
    ; theoremHypothesesTarget =
        abstractDoplicherRobertsTheoremHypothesesTarget
    ; reconstructionPostulate =
        abstractDoplicherRobertsReconstructionPostulate
    ; reconstructionAuthorityShape =
        "symmetric-tensor-C-star-category-reconstructs-compact-group-and-category-equivalence-to-Rep-G"
    ; reconstructionAuthorityShape-v =
        refl
    ; citationTokens =
        canonicalDoplicherRobertsAuthorityCitations
    ; citationTokensAreCanonical =
        refl
    ; safeAuthority =
        true
    ; safeAuthorityIsTrue =
        refl
    ; standardModelMatchingRemainsOpen =
        true
    ; standardModelMatchingRemainsOpenIsTrue =
        refl
    ; laneDimensionInternallyPromoted =
        true
    ; laneDimensionInternallyPromotedIsTrue =
        refl
    ; laneDimensionComputedByDLM =
        true
    ; laneDimensionComputedByDLMIsTrue =
        refl
    ; laneDimensionDoesNotPromoteDHRSMMatching =
        true
    ; laneDimensionDoesNotPromoteDHRSMMatchingIsTrue =
        refl
    ; dhrEqualsStandardModelPromoted =
        false
    ; dhrEqualsStandardModelPromotedIsFalse =
        refl
    ; boundary =
        "Doplicher-Roberts reconstruction is safe authority for reconstructing a compact group from a symmetric tensor C*-category"
        ∷ "The authority also records the target category equivalence to Rep(G)"
        ∷ "laneDimension is authority-backed and conditional on the DLM route; Standard Model matching remains a downstream obligation"
        ∷ "No DHR equals Standard Model gauge-group claim is promoted"
        ∷ []
    }

canonicalDoplicherRobertsReconstructionAuthoritySurface :
  DoplicherRobertsReconstructionAuthoritySurface
canonicalDoplicherRobertsReconstructionAuthoritySurface =
  record
    { doplicherRobertsReconstruction =
        canonicalDoplicherRobertsReconstruction
    ; categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; dashiDRHypotheses =
        canonicalDRHypothesesForDASHI
    ; primaryCitation =
        "Doplicher-Roberts-1989-Inventiones-Mathematicae-98-A-new-duality-theory-for-compact-groups"
    ; primaryCitation-v =
        refl
    ; fieldAlgebraCitation =
        "Doplicher-Roberts-1990-Communications-in-Mathematical-Physics-131-field-algebra-compact-gauge-group-superselection-structure"
    ; fieldAlgebraCitation-v =
        refl
    ; citationTokens =
        canonicalDoplicherRobertsAuthorityCitations
    ; citationTokensAreCanonical =
        refl
    ; theoremHypothesesTarget =
        abstractDoplicherRobertsTheoremHypothesesTarget
    ; reconstructionPostulate =
        abstractDoplicherRobertsReconstructionPostulate
    ; citedAuthorityRecorded =
        true
    ; citedAuthorityRecordedIsTrue =
        refl
    ; safeAuthorityRecorded =
        true
    ; safeAuthorityRecordedIsTrue =
        refl
    ; reconstructsGaugeGroupHere =
        false
    ; reconstructsGaugeGroupHereIsFalse =
        refl
    ; authorityBoundary =
        "Doplicher-Roberts reconstruction is recorded as cited theorem authority and a postulate target"
        ∷ "The cited authority applies only after the five DR hypotheses H1-H5 packaged in DRHypothesesForDASHI are supplied"
        ∷ "It is safe authority for compact-group or compact-supergroup reconstruction and category equivalence to Rep(G), not for Standard Model matching"
        ∷ "laneDimension is authority-backed and conditional outside this Doplicher-Roberts authority item; DHR/Standard Model matching remains non-promoted"
        ∷ "This surface does not construct the compact gauge group or identify it with the Standard Model gauge group"
        ∷ []
    }

------------------------------------------------------------------------
-- Tranche 1B: conditional DHR endomorphism computation by prime lane.
--
-- This layer records the calculation target:
--   A(O) ~= tensor_p A_p(O)
--   Delta_DHR^(p) ~= Rep(G_p)
--   Delta_DHR^DASHI ~= boxtimes_p Delta_DHR^(p) ~= Rep(product_p G_p)
-- and then DR reconstructs the high-energy Pati-Salam group once the
-- SerreTate/Heterotic lane group theorem supplies the lane groups.
--
-- It deliberately does not prove laneDimension, LaneGroupTheorem, or the
-- low-energy Standard Model breaking.  Those remain explicit hypotheses.

data PrimeLane : Set where
  primeLaneTargetOnly :
    PrimeLane

data PrimeLaneAlgebra
  (lane : PrimeLane)
  (region : AQFT.Region) :
  Set where
  primeLaneAlgebraTargetOnly :
    PrimeLaneAlgebra lane region

data PrimeLaneDHRCategory (lane : PrimeLane) : Set where
  primeLaneDHRCategoryTargetOnly :
    PrimeLaneDHRCategory lane

data ProductPrimeLaneGaugeGroup : Set where
  productPrimeLaneGaugeGroupTargetOnly :
    ProductPrimeLaneGaugeGroup

data HighEnergyPatiSalamGroup : Set where
  highEnergyPatiSalamGroupTargetOnly :
    HighEnergyPatiSalamGroup

data LowEnergyStandardModelGroup : Set where
  lowEnergyStandardModelGroupTargetOnly :
    LowEnergyStandardModelGroup

data LaneGroupTheorem
  (lane : PrimeLane)
  (group : CompactGaugeGroup) :
  Set where
  laneGroupTheoremAuthorityTargetOnly :
    LaneGroupTheorem lane group

data SerreTateLaneGroupTheorem
  (lane : PrimeLane)
  (group : CompactGaugeGroup) :
  Set where
  serreTateLaneGroupTheoremAuthorityTargetOnly :
    SerreTateLaneGroupTheorem lane group

data G4PrimeLaneIndependenceReceipt : Set where
  g4PrimeLaneIndependenceReceiptTargetOnly :
    G4PrimeLaneIndependenceReceipt

data SU2RSeesawBreakingReceipt : Set where
  su2RSeesawBreakingReceiptTargetOnly :
    SU2RSeesawBreakingReceipt

abstractG4PrimeLaneIndependenceReceipt :
  G4PrimeLaneIndependenceReceipt
abstractG4PrimeLaneIndependenceReceipt =
  g4PrimeLaneIndependenceReceiptTargetOnly

abstractProductPrimeLaneGaugeGroup :
  ProductPrimeLaneGaugeGroup
abstractProductPrimeLaneGaugeGroup =
  productPrimeLaneGaugeGroupTargetOnly

abstractHighEnergyPatiSalamGroup :
  HighEnergyPatiSalamGroup
abstractHighEnergyPatiSalamGroup =
  highEnergyPatiSalamGroupTargetOnly

abstractLowEnergyStandardModelGroup :
  LowEnergyStandardModelGroup
abstractLowEnergyStandardModelGroup =
  lowEnergyStandardModelGroupTargetOnly

data PrimeLaneTensorFactorisationTargetReceipt
  (region : AQFT.Region)
  (algebra : LocalObservableAlgebra region) :
  Set where
  primeLaneTensorFactorisationTargetOnly :
    PrimeLaneTensorFactorisationTargetReceipt region algebra

abstractPrimeLaneTensorFactorisationTarget :
  (region : AQFT.Region) →
  LocalObservableAlgebra region →
  Set
abstractPrimeLaneTensorFactorisationTarget region algebra =
  PrimeLaneTensorFactorisationTargetReceipt region algebra

data PrimeLaneAlgebraComponentTargetReceipt
  (lane : PrimeLane)
  (region : AQFT.Region)
  (algebra : PrimeLaneAlgebra lane region) :
  Set where
  primeLaneAlgebraComponentTargetOnly :
    PrimeLaneAlgebraComponentTargetReceipt lane region algebra

abstractPrimeLaneAlgebraComponentTarget :
  (lane : PrimeLane) →
  (region : AQFT.Region) →
  PrimeLaneAlgebra lane region →
  Set
abstractPrimeLaneAlgebraComponentTarget lane region algebra =
  PrimeLaneAlgebraComponentTargetReceipt lane region algebra

data LaneDHRRepClassificationTargetReceipt
  (lane : PrimeLane)
  (group : CompactGaugeGroup)
  (category : PrimeLaneDHRCategory lane) :
  Set where
  laneDHRRepClassificationTargetOnly :
    LaneDHRRepClassificationTargetReceipt lane group category

abstractLaneDHRRepClassificationTarget :
  (lane : PrimeLane) →
  (group : CompactGaugeGroup) →
  PrimeLaneDHRCategory lane →
  Set
abstractLaneDHRRepClassificationTarget lane group category =
  LaneDHRRepClassificationTargetReceipt lane group category

data FullDHRBoxtimesTargetReceipt
  (category : TensorCStarCategory) :
  Set where
  fullDHRBoxtimesTargetOnly :
    FullDHRBoxtimesTargetReceipt category

abstractFullDHRBoxtimesTarget :
  TensorCStarCategory →
  Set
abstractFullDHRBoxtimesTarget category =
  FullDHRBoxtimesTargetReceipt category

data FullDHRRepProductEquivalenceTargetReceipt
  (category : TensorCStarCategory)
  (group : ProductPrimeLaneGaugeGroup) :
  Set where
  fullDHRRepProductEquivalenceTargetOnly :
    FullDHRRepProductEquivalenceTargetReceipt category group

abstractFullDHRRepProductEquivalenceTarget :
  TensorCStarCategory →
  ProductPrimeLaneGaugeGroup →
  Set
abstractFullDHRRepProductEquivalenceTarget category group =
  FullDHRRepProductEquivalenceTargetReceipt category group

data ProductGroupIsHighEnergyPatiSalamTargetReceipt
  (productGroup : ProductPrimeLaneGaugeGroup)
  (patiSalamGroup : HighEnergyPatiSalamGroup) :
  Set where
  productGroupIsHighEnergyPatiSalamTargetOnly :
    ProductGroupIsHighEnergyPatiSalamTargetReceipt productGroup patiSalamGroup

abstractProductGroupIsHighEnergyPatiSalamTarget :
  ProductPrimeLaneGaugeGroup →
  HighEnergyPatiSalamGroup →
  Set
abstractProductGroupIsHighEnergyPatiSalamTarget productGroup patiSalamGroup =
  ProductGroupIsHighEnergyPatiSalamTargetReceipt productGroup patiSalamGroup

data DRHighEnergyPatiSalamReconstructionTargetReceipt
  (reconstruction : DoplicherRobertsReconstruction)
  (productGroup : ProductPrimeLaneGaugeGroup)
  (patiSalamGroup : HighEnergyPatiSalamGroup) :
  Set where
  drHighEnergyPatiSalamReconstructionTargetOnly :
    DRHighEnergyPatiSalamReconstructionTargetReceipt
      reconstruction productGroup patiSalamGroup

abstractDRHighEnergyPatiSalamReconstructionTarget :
  DoplicherRobertsReconstruction →
  ProductPrimeLaneGaugeGroup →
  HighEnergyPatiSalamGroup →
  Set
abstractDRHighEnergyPatiSalamReconstructionTarget
  reconstruction productGroup patiSalamGroup =
  DRHighEnergyPatiSalamReconstructionTargetReceipt
    reconstruction productGroup patiSalamGroup

data LowEnergySMFromSU2RBreakingTargetReceipt
  (patiSalamGroup : HighEnergyPatiSalamGroup)
  (breaking : SU2RSeesawBreakingReceipt)
  (smGroup : LowEnergyStandardModelGroup) :
  Set where
  lowEnergySMFromSU2RBreakingTargetOnly :
    LowEnergySMFromSU2RBreakingTargetReceipt
      patiSalamGroup breaking smGroup

abstractLowEnergySMFromSU2RBreakingTarget :
  HighEnergyPatiSalamGroup →
  SU2RSeesawBreakingReceipt →
  LowEnergyStandardModelGroup →
  Set
abstractLowEnergySMFromSU2RBreakingTarget patiSalamGroup breaking smGroup =
  LowEnergySMFromSU2RBreakingTargetReceipt patiSalamGroup breaking smGroup

record PrimeLaneAlgebraFactorisationReceipt : Setω where
  field
    g4PrimeLaneIndependenceInput :
      G4PrimeLaneIndependenceReceipt

    factorisationShape :
      String

    factorisationShape-v :
      factorisationShape
      ≡
      "A-of-O-is-tensor-product-over-prime-lanes-of-A-p-of-O"

    factorisationFormula :
      String

    factorisationFormula-v :
      factorisationFormula
      ≡
      "A(O) ~= tensor_p A_p(O)"

    primeLaneAlgebra :
      PrimeLane →
      AQFT.Region →
      Set

    componentTarget :
      (lane : PrimeLane) →
      (region : AQFT.Region) →
      PrimeLaneAlgebra lane region →
      Set

    tensorFactorisationTarget :
      (region : AQFT.Region) →
      LocalObservableAlgebra region →
      Set

    factorisationFromG4Recorded :
      Bool

    factorisationFromG4RecordedIsTrue :
      factorisationFromG4Recorded ≡ true

    factorisationProvedHere :
      Bool

    factorisationProvedHereIsFalse :
      factorisationProvedHere ≡ false

    factorisationBoundary :
      List String

open PrimeLaneAlgebraFactorisationReceipt public

record PrimeLaneDHREndomorphismClassificationReceipt : Setω where
  field
    algebraFactorisation :
      PrimeLaneAlgebraFactorisationReceipt

    laneGroupTheorem :
      PrimeLane →
      CompactGaugeGroup →
      Set

    serreTateLaneGroupTheorem :
      PrimeLane →
      CompactGaugeGroup →
      Set

    laneDHRCategory :
      PrimeLane →
      Set

    laneRepClassificationTarget :
      (lane : PrimeLane) →
      (group : CompactGaugeGroup) →
      PrimeLaneDHRCategory lane →
      Set

    classificationShape :
      String

    classificationShape-v :
      classificationShape
      ≡
      "DHR-endomorphisms-of-A-p-of-O-are-classified-by-Rep-of-G-p"

    conditionalOnSerreTate :
      Bool

    conditionalOnSerreTateIsTrue :
      conditionalOnSerreTate ≡ true

    provesSerreTateLaneGroupTheoremHere :
      Bool

    provesSerreTateLaneGroupTheoremHereIsFalse :
      provesSerreTateLaneGroupTheoremHere ≡ false

    provesLaneDimensionHere :
      Bool

    provesLaneDimensionHereIsFalse :
      provesLaneDimensionHere ≡ false

    classificationBoundary :
      List String

open PrimeLaneDHREndomorphismClassificationReceipt public

record FullDHRBoxtimesDecompositionReceipt : Setω where
  field
    laneClassification :
      PrimeLaneDHREndomorphismClassificationReceipt

    fullDHRCategory :
      TensorCStarCategory

    productPrimeLaneGaugeGroup :
      ProductPrimeLaneGaugeGroup

    boxtimesShape :
      String

    boxtimesShape-v :
      boxtimesShape
      ≡
      "Delta-DHR-DASHI-is-boxtimes-over-p-of-Delta-DHR-p"

    repProductShape :
      String

    repProductShape-v :
      repProductShape
      ≡
      "boxtimes-over-p-Rep-G-p-is-Rep-of-product-over-p-G-p"

    fullFactorisationFormula :
      String

    fullFactorisationFormula-v :
      fullFactorisationFormula
      ≡
      "Delta_DHR ~= boxtimes_p Delta_DHR^(p) ~= Rep(product_p G_p)"

    fullDHRBoxtimesTarget :
      TensorCStarCategory →
      Set

    fullDHRRepProductEquivalenceTarget :
      TensorCStarCategory →
      ProductPrimeLaneGaugeGroup →
      Set

    decompositionConditionalOnLaneGroups :
      Bool

    decompositionConditionalOnLaneGroupsIsTrue :
      decompositionConditionalOnLaneGroups ≡ true

    decompositionProvedHere :
      Bool

    decompositionProvedHereIsFalse :
      decompositionProvedHere ≡ false

    decompositionBoundary :
      List String

open FullDHRBoxtimesDecompositionReceipt public

record ConditionalPatiSalamDHRReconstructionReceipt : Setω where
  field
    fullDHRDecomposition :
      FullDHRBoxtimesDecompositionReceipt

    doplicherRobertsAuthority :
      DoplicherRobertsReconstructionAuthoritySurface

    productPrimeLaneGaugeGroup :
      ProductPrimeLaneGaugeGroup

    highEnergyPatiSalamGroup :
      HighEnergyPatiSalamGroup

    lowEnergyStandardModelGroup :
      LowEnergyStandardModelGroup

    productGroupIsPatiSalamTarget :
      ProductPrimeLaneGaugeGroup →
      HighEnergyPatiSalamGroup →
      Set

    drHighEnergyPatiSalamReconstructionTarget :
      DoplicherRobertsReconstruction →
      ProductPrimeLaneGaugeGroup →
      HighEnergyPatiSalamGroup →
      Set

    lowEnergySMFromSU2RBreakingTarget :
      HighEnergyPatiSalamGroup →
      SU2RSeesawBreakingReceipt →
      LowEnergyStandardModelGroup →
      Set

    highEnergyGroupShape :
      String

    highEnergyGroupShape-v :
      highEnergyGroupShape
      ≡
      "G-DHR-equals-product-p-G-p-equals-U1-times-SU2L-times-SU3c-times-SU2R"

    lowEnergyShape :
      String

    lowEnergyShape-v :
      lowEnergyShape
      ≡
      "Standard-Model-low-energy-result-requires-SU2R-breaking-at-seesaw-scale"

    highEnergyPatiSalamOutput :
      String

    highEnergyPatiSalamOutput-v :
      highEnergyPatiSalamOutput
      ≡
      "Pati-Salam high-energy output is U1 x SU2L x SU3c x SU2R"

    conditionalOnLaneDimensionTheorem :
      Bool

    conditionalOnLaneDimensionTheoremIsTrue :
      conditionalOnLaneDimensionTheorem ≡ true

    conditionalPatiSalamRecorded :
      Bool

    conditionalPatiSalamRecordedIsTrue :
      conditionalPatiSalamRecorded ≡ true

    provesGDHREqualsStandardModelUnconditionally :
      Bool

    provesGDHREqualsStandardModelUnconditionallyIsFalse :
      provesGDHREqualsStandardModelUnconditionally ≡ false

    flipsDHRGaugePromotionAuthority :
      Bool

    flipsDHRGaugePromotionAuthorityIsFalse :
      flipsDHRGaugePromotionAuthority ≡ false

    reconstructionBoundary :
      List String

open ConditionalPatiSalamDHRReconstructionReceipt public

canonicalPrimeLaneAlgebraFactorisationReceipt :
  PrimeLaneAlgebraFactorisationReceipt
canonicalPrimeLaneAlgebraFactorisationReceipt =
  record
    { g4PrimeLaneIndependenceInput =
        abstractG4PrimeLaneIndependenceReceipt
    ; factorisationShape =
        "A-of-O-is-tensor-product-over-prime-lanes-of-A-p-of-O"
    ; factorisationShape-v =
        refl
    ; factorisationFormula =
        "A(O) ~= tensor_p A_p(O)"
    ; factorisationFormula-v =
        refl
    ; primeLaneAlgebra =
        PrimeLaneAlgebra
    ; componentTarget =
        abstractPrimeLaneAlgebraComponentTarget
    ; tensorFactorisationTarget =
        abstractPrimeLaneTensorFactorisationTarget
    ; factorisationFromG4Recorded =
        true
    ; factorisationFromG4RecordedIsTrue =
        refl
    ; factorisationProvedHere =
        false
    ; factorisationProvedHereIsFalse =
        refl
    ; factorisationBoundary =
        "Prime-lane independence G4 is recorded as the input for A(O) factorisation"
        ∷ "Receipt formula: A(O) ~= tensor_p A_p(O)"
        ∷ "The target shape is A(O) equivalent to the tensor product over prime lanes of A_p(O)"
        ∷ "This surface does not prove the tensor-product factorisation law locally"
        ∷ []
    }

canonicalPrimeLaneDHREndomorphismClassificationReceipt :
  PrimeLaneDHREndomorphismClassificationReceipt
canonicalPrimeLaneDHREndomorphismClassificationReceipt =
  record
    { algebraFactorisation =
        canonicalPrimeLaneAlgebraFactorisationReceipt
    ; laneGroupTheorem =
        LaneGroupTheorem
    ; serreTateLaneGroupTheorem =
        LaneGroupTheorem
    ; laneDHRCategory =
        PrimeLaneDHRCategory
    ; laneRepClassificationTarget =
        abstractLaneDHRRepClassificationTarget
    ; classificationShape =
        "DHR-endomorphisms-of-A-p-of-O-are-classified-by-Rep-of-G-p"
    ; classificationShape-v =
        refl
    ; conditionalOnSerreTate =
        true
    ; conditionalOnSerreTateIsTrue =
        refl
    ; provesSerreTateLaneGroupTheoremHere =
        false
    ; provesSerreTateLaneGroupTheoremHereIsFalse =
        refl
    ; provesLaneDimensionHere =
        false
    ; provesLaneDimensionHereIsFalse =
        refl
    ; classificationBoundary =
        "For each prime lane p, the DHR endomorphisms of A_p(O) are targeted as Rep(G_p)"
        ∷ "The group G_p is supplied elsewhere by LaneGroupTheorem, i.e. the SerreTate/Heterotic lane group theorem, not computed in this module"
        ∷ "This receipt records the DHR computation shape without proving LaneGroupTheorem or laneDimension"
        ∷ []
    }

canonicalFullDHRBoxtimesDecompositionReceipt :
  FullDHRBoxtimesDecompositionReceipt
canonicalFullDHRBoxtimesDecompositionReceipt =
  record
    { laneClassification =
        canonicalPrimeLaneDHREndomorphismClassificationReceipt
    ; fullDHRCategory =
        SymmetricTensorCStarCategoryTarget.categoryCarrier
          canonicalSymmetricTensorCStarCategoryTarget
    ; productPrimeLaneGaugeGroup =
        abstractProductPrimeLaneGaugeGroup
    ; boxtimesShape =
        "Delta-DHR-DASHI-is-boxtimes-over-p-of-Delta-DHR-p"
    ; boxtimesShape-v =
        refl
    ; repProductShape =
        "boxtimes-over-p-Rep-G-p-is-Rep-of-product-over-p-G-p"
    ; repProductShape-v =
        refl
    ; fullFactorisationFormula =
        "Delta_DHR ~= boxtimes_p Delta_DHR^(p) ~= Rep(product_p G_p)"
    ; fullFactorisationFormula-v =
        refl
    ; fullDHRBoxtimesTarget =
        abstractFullDHRBoxtimesTarget
    ; fullDHRRepProductEquivalenceTarget =
        abstractFullDHRRepProductEquivalenceTarget
    ; decompositionConditionalOnLaneGroups =
        true
    ; decompositionConditionalOnLaneGroupsIsTrue =
        refl
    ; decompositionProvedHere =
        false
    ; decompositionProvedHereIsFalse =
        refl
    ; decompositionBoundary =
        "The full DASHI DHR category is targeted as the Deligne boxtimes product of the prime-lane DHR categories"
        ∷ "Recorded factorisation: Delta_DHR ~= boxtimes_p Delta_DHR^(p) ~= Rep(product_p G_p)"
        ∷ "After lane classification, boxtimes_p Rep(G_p) is targeted as Rep(product_p G_p)"
        ∷ "This is conditional on the lane groups supplied elsewhere by LaneGroupTheorem, not on a local proof"
        ∷ []
    }

canonicalConditionalPatiSalamDHRReconstructionReceipt :
  ConditionalPatiSalamDHRReconstructionReceipt
canonicalConditionalPatiSalamDHRReconstructionReceipt =
  record
    { fullDHRDecomposition =
        canonicalFullDHRBoxtimesDecompositionReceipt
    ; doplicherRobertsAuthority =
        canonicalDoplicherRobertsReconstructionAuthoritySurface
    ; productPrimeLaneGaugeGroup =
        abstractProductPrimeLaneGaugeGroup
    ; highEnergyPatiSalamGroup =
        abstractHighEnergyPatiSalamGroup
    ; lowEnergyStandardModelGroup =
        abstractLowEnergyStandardModelGroup
    ; productGroupIsPatiSalamTarget =
        abstractProductGroupIsHighEnergyPatiSalamTarget
    ; drHighEnergyPatiSalamReconstructionTarget =
        abstractDRHighEnergyPatiSalamReconstructionTarget
    ; lowEnergySMFromSU2RBreakingTarget =
        abstractLowEnergySMFromSU2RBreakingTarget
    ; highEnergyGroupShape =
        "G-DHR-equals-product-p-G-p-equals-U1-times-SU2L-times-SU3c-times-SU2R"
    ; highEnergyGroupShape-v =
        refl
    ; lowEnergyShape =
        "Standard-Model-low-energy-result-requires-SU2R-breaking-at-seesaw-scale"
    ; lowEnergyShape-v =
        refl
    ; highEnergyPatiSalamOutput =
        "Pati-Salam high-energy output is U1 x SU2L x SU3c x SU2R"
    ; highEnergyPatiSalamOutput-v =
        refl
    ; conditionalOnLaneDimensionTheorem =
        true
    ; conditionalOnLaneDimensionTheoremIsTrue =
        refl
    ; conditionalPatiSalamRecorded =
        true
    ; conditionalPatiSalamRecordedIsTrue =
        refl
    ; provesGDHREqualsStandardModelUnconditionally =
        false
    ; provesGDHREqualsStandardModelUnconditionallyIsFalse =
        refl
    ; flipsDHRGaugePromotionAuthority =
        false
    ; flipsDHRGaugePromotionAuthorityIsFalse =
        refl
    ; reconstructionBoundary =
        "Conditional on LaneGroupTheorem supplied elsewhere, DR reconstructs product_p G_p"
        ∷ "With lane groups U1, SU2L, SU3c, and SU2R, the high-energy output is the Pati-Salam-side group U1 x SU2L x SU3c x SU2R"
        ∷ "The low-energy Standard Model requires an additional SU2R breaking receipt at the seesaw scale"
        ∷ "This conditional receipt does not prove LaneGroupTheorem or laneDimension and does not flip the DHR gauge promotion authority token"
        ∷ []
    }

record TannakaDHRReconstructionTarget : Setω where
  field
    categoryTarget :
      SymmetricTensorCStarCategoryTarget

    doplicherRobertsAuthority :
      DoplicherRobertsReconstructionAuthoritySurface

    reconstructedGaugeGroup :
      CompactGaugeGroup

    fibreFunctorTarget :
      TensorCStarCategory →
      Set

    reconstructionTheoremTarget :
      TensorCStarCategory →
      CompactGaugeGroup →
      Set

    reconstructionProved :
      Bool

    reconstructionProvedIsFalse :
      reconstructionProved ≡ false

    reconstructionBoundary :
      List String

open TannakaDHRReconstructionTarget public

abstractCompactGaugeGroup :
  CompactGaugeGroup
abstractCompactGaugeGroup =
  compactGaugeGroupAuthorityTargetOnly

data FibreFunctorTargetReceipt
  (category : TensorCStarCategory) :
  Set where
  fibreFunctorTargetOnly :
    FibreFunctorTargetReceipt category

data ReconstructionTheoremTargetReceipt
  (category : TensorCStarCategory)
  (group : CompactGaugeGroup) :
  Set where
  reconstructionTheoremTargetOnly :
    ReconstructionTheoremTargetReceipt category group

abstractFibreFunctorTarget :
  TensorCStarCategory →
  Set
abstractFibreFunctorTarget category =
  FibreFunctorTargetReceipt category

abstractReconstructionTheoremTarget :
  TensorCStarCategory →
  CompactGaugeGroup →
  Set
abstractReconstructionTheoremTarget category group =
  ReconstructionTheoremTargetReceipt category group

canonicalTannakaDHRReconstructionTarget :
  TannakaDHRReconstructionTarget
canonicalTannakaDHRReconstructionTarget =
  record
    { categoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; doplicherRobertsAuthority =
        canonicalDoplicherRobertsReconstructionAuthoritySurface
    ; reconstructedGaugeGroup =
        abstractCompactGaugeGroup
    ; fibreFunctorTarget =
        abstractFibreFunctorTarget
    ; reconstructionTheoremTarget =
        abstractReconstructionTheoremTarget
    ; reconstructionProved =
        false
    ; reconstructionProvedIsFalse =
        refl
    ; reconstructionBoundary =
        "Tannaka/DHR reconstruction is a target from the DHR tensor category to a compact gauge group"
        ∷ "Doplicher-Roberts cited authority is explicit, but its hypotheses are postulate targets here"
        ∷ "No fibre functor, compact gauge group reconstruction, or gauge-field dynamics is constructed here"
        ∷ []
    }

record StandardModelPrimeLaneCondensationTarget : Setω where
  field
    reconstructionTarget :
      TannakaDHRReconstructionTarget

    standardModelMatchingData :
      StandardModelMatchingData

    primeLaneCondensationData :
      PrimeLaneCondensationData

    standardModelMatchingTarget :
      StandardModelMatchingData →
      Set

    primeLaneCondensationTarget :
      PrimeLaneCondensationData →
      Set

    standardModelMatched :
      Bool

    standardModelMatchedIsFalse :
      standardModelMatched ≡ false

    primeLaneCondensed :
      Bool

    primeLaneCondensedIsFalse :
      primeLaneCondensed ≡ false

    matchingBoundary :
      List String

open StandardModelPrimeLaneCondensationTarget public

abstractStandardModelMatchingData :
  StandardModelMatchingData
abstractStandardModelMatchingData =
  standardModelMatchingDataTargetOnly

abstractPrimeLaneCondensationData :
  PrimeLaneCondensationData
abstractPrimeLaneCondensationData =
  primeLaneCondensationDataTargetOnly

data StandardModelMatchingTargetReceipt
  (matchingData : StandardModelMatchingData) :
  Set where
  standardModelMatchingTargetOnly :
    StandardModelMatchingTargetReceipt matchingData

data PrimeLaneCondensationTargetReceipt
  (condensationData : PrimeLaneCondensationData) :
  Set where
  primeLaneCondensationTargetOnly :
    PrimeLaneCondensationTargetReceipt condensationData

abstractStandardModelMatchingTarget :
  StandardModelMatchingData →
  Set
abstractStandardModelMatchingTarget matchingData =
  StandardModelMatchingTargetReceipt matchingData

abstractPrimeLaneCondensationTarget :
  PrimeLaneCondensationData →
  Set
abstractPrimeLaneCondensationTarget condensationData =
  PrimeLaneCondensationTargetReceipt condensationData

canonicalStandardModelPrimeLaneCondensationTarget :
  StandardModelPrimeLaneCondensationTarget
canonicalStandardModelPrimeLaneCondensationTarget =
  record
    { reconstructionTarget =
        canonicalTannakaDHRReconstructionTarget
    ; standardModelMatchingData =
        abstractStandardModelMatchingData
    ; primeLaneCondensationData =
        abstractPrimeLaneCondensationData
    ; standardModelMatchingTarget =
        abstractStandardModelMatchingTarget
    ; primeLaneCondensationTarget =
        abstractPrimeLaneCondensationTarget
    ; standardModelMatched =
        false
    ; standardModelMatchedIsFalse =
        refl
    ; primeLaneCondensed =
        false
    ; primeLaneCondensedIsFalse =
        refl
    ; matchingBoundary =
        "Standard Model matching remains an open target after DHR reconstruction"
        ∷ "Prime-lane condensation is an open obligation and not a gauge-group reconstruction theorem"
        ∷ "No Standard Model multiplet table, hypercharge convention, coupling normalisation, or empirical authority is supplied here"
        ∷ []
    }

record Gate1Gate6AgreementObstructionReceipt : Setω where
  field
    localAlgebraTarget :
      HaagDualityReceiptTarget

    dhrFormalismPrimitives :
      DHRFormalismPrimitiveReceipt

    drFiveHypotheses :
      DRHypothesesForDASHI

    tannakaDHRTarget :
      TannakaDHRReconstructionTarget

    standardModelCarrierFunctorMatchTarget :
      StandardModelPrimeLaneCondensationTarget

    exactStandardModelCarrierFunctorMatchEvidence :
      ExactSM.ExactSMMatchReceipt

    dhrGaugeGroup :
      CompactGaugeGroup

    carrierFunctorGaugeGroup :
      CompactGaugeGroup

    agreementTarget :
      CompactGaugeGroup →
      CompactGaugeGroup →
      StandardModelMatchingData →
      Set

    agreementShape :
      String

    agreementShape-v :
      agreementShape
      ≡
      "G-DHR-equals-carrier-functor-gauge-group-only-after-local-algebra-localized-transportable-endomorphisms-DR-five-hypotheses-and-exact-Standard-Model-carrier-functor-match"

    localAlgebraTyped :
      Bool

    localAlgebraTypedIsTrue :
      localAlgebraTyped ≡ true

    localizedTransportableEndomorphismsTyped :
      Bool

    localizedTransportableEndomorphismsTypedIsTrue :
      localizedTransportableEndomorphismsTyped ≡ true

    drFiveHypothesesTyped :
      Bool

    drFiveHypothesesTypedIsTrue :
      drFiveHypothesesTyped ≡ true

    exactStandardModelCarrierFunctorMatchProvided :
      Bool

    exactStandardModelCarrierFunctorMatchProvidedIsFalse :
      exactStandardModelCarrierFunctorMatchProvided ≡ true

    gate1Gate6AgreementPromoted :
      Bool

    gate1Gate6AgreementPromotedIsFalse :
      gate1Gate6AgreementPromoted ≡ false

    flipsDHRGaugePromotionAuthority :
      Bool

    flipsDHRGaugePromotionAuthorityIsFalse :
      flipsDHRGaugePromotionAuthority ≡ false

    firstResidualBlocker :
      Gate1Gate6AgreementObstruction

    firstResidualBlockerIsExactStandardModelCarrierFunctorMatch :
      firstResidualBlocker
      ≡
      canonicalGate1Gate6AgreementObstruction

    obstructionBoundary :
      List String

record DHRGate1Gate6BoundaryThreadingReceipt : Setω where
  field
    exactStandardModelMatchToken :
      ExactSM.ExactSMMatchReceipt

    clayYMGapBoundary :
      ClayBoundary.ClayYMGapReceipt

    gate1Gate6BoundaryThreadingOpen :
      Bool

    gate1Gate6BoundaryThreadingOpenIsFalse :
      gate1Gate6BoundaryThreadingOpen ≡ false

    boundary :
      List String

open DHRGate1Gate6BoundaryThreadingReceipt public

canonicalDHRGate1Gate6BoundaryThreadingReceipt :
  DHRGate1Gate6BoundaryThreadingReceipt
canonicalDHRGate1Gate6BoundaryThreadingReceipt =
  record
    { exactStandardModelMatchToken =
        ExactSM.canonicalExactSMMatchReceipt
    ; clayYMGapBoundary =
        ClayBoundary.canonicalClayYMGapReceipt
    ; gate1Gate6BoundaryThreadingOpen =
        false
    ; gate1Gate6BoundaryThreadingOpenIsFalse =
        refl
    ; boundary =
        "This receipt threads the Clay/YM and Higgs/PDG boundary tokens into Gate 1/Gate 6"
        ∷ "The exact SM witness remains the canonical token bundle"
        ∷ "The Gate 1/Gate 6 agreement obstruction remains open"
        ∷ []
    }

open Gate1Gate6AgreementObstructionReceipt public

abstractCarrierFunctorGaugeGroup :
  CompactGaugeGroup
abstractCarrierFunctorGaugeGroup =
  compactGaugeGroupAuthorityTargetOnly

data Gate1Gate6AgreementTargetReceipt
  (dhrGroup carrierGroup : CompactGaugeGroup)
  (matchingData : StandardModelMatchingData) :
  Set where
  gate1Gate6AgreementTargetOnly :
    Gate1Gate6AgreementTargetReceipt dhrGroup carrierGroup matchingData

abstractGate1Gate6AgreementTarget :
  CompactGaugeGroup →
  CompactGaugeGroup →
  StandardModelMatchingData →
  Set
abstractGate1Gate6AgreementTarget dhrGroup carrierGroup matchingData =
  Gate1Gate6AgreementTargetReceipt dhrGroup carrierGroup matchingData

canonicalGate1Gate6AgreementObstructionReceipt :
  Gate1Gate6AgreementObstructionReceipt
canonicalGate1Gate6AgreementObstructionReceipt =
  record
    { localAlgebraTarget =
        canonicalHaagDualityReceiptTarget
    ; dhrFormalismPrimitives =
        canonicalDHRFormalismPrimitiveReceipt
    ; drFiveHypotheses =
        canonicalDRHypothesesForDASHI
    ; tannakaDHRTarget =
        canonicalTannakaDHRReconstructionTarget
    ; standardModelCarrierFunctorMatchTarget =
        canonicalStandardModelPrimeLaneCondensationTarget
    ; exactStandardModelCarrierFunctorMatchEvidence =
        ExactSM.canonicalExactSMMatchReceipt
    ; dhrGaugeGroup =
        TannakaDHRReconstructionTarget.reconstructedGaugeGroup
          canonicalTannakaDHRReconstructionTarget
    ; carrierFunctorGaugeGroup =
        abstractCarrierFunctorGaugeGroup
    ; agreementTarget =
        abstractGate1Gate6AgreementTarget
    ; agreementShape =
        "G-DHR-equals-carrier-functor-gauge-group-only-after-local-algebra-localized-transportable-endomorphisms-DR-five-hypotheses-and-exact-Standard-Model-carrier-functor-match"
    ; agreementShape-v =
        refl
    ; localAlgebraTyped =
        true
    ; localAlgebraTypedIsTrue =
        refl
    ; localizedTransportableEndomorphismsTyped =
        true
    ; localizedTransportableEndomorphismsTypedIsTrue =
        refl
    ; drFiveHypothesesTyped =
        true
    ; drFiveHypothesesTypedIsTrue =
        refl
    ; exactStandardModelCarrierFunctorMatchProvided =
        true
    ; exactStandardModelCarrierFunctorMatchProvidedIsFalse =
        refl
    ; gate1Gate6AgreementPromoted =
        false
    ; gate1Gate6AgreementPromotedIsFalse =
        refl
    ; flipsDHRGaugePromotionAuthority =
        false
    ; flipsDHRGaugePromotionAuthorityIsFalse =
        refl
    ; firstResidualBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; firstResidualBlockerIsExactStandardModelCarrierFunctorMatch =
        refl
    ; obstructionBoundary =
        "Gate 1/Gate 6 agreement is bounded to the typed receipt surface"
        ∷ "G_DHR can equal the carrier-functor gauge group only after the local algebra target, localized transportable endomorphisms, the DR H1-H5 package, and exact Standard Model/carrier-functor matching are all supplied"
        ∷ "This receipt records the local-algebra, DHR primitive, and DR-hypothesis inputs as typed/request inputs only"
        ∷ "The exact Standard Model/carrier-functor target is carried here as canonical evidence, but the Gate 1/Gate 6 agreement remains blocked until the obstruction constructor is retired"
        ∷ "No reconstruction theorem, Standard Model identification, or DHR gauge promotion follows from this receipt"
        ∷ []
    }

record DHRGaugeReceiptSurface : Setω where
  field
    status :
      DHRGaugeReceiptStatus

    aqftTypedNetSurface :
      AQFT.AQFTTypedNetSurface

    haagDualityTarget :
      HaagDualityReceiptTarget

    controlledGaugeFailure :
      GaugeTheoryControlledFailureSurface

    dhrFormalismPrimitiveReceipt :
      DHRFormalismPrimitiveReceipt

    dhrSelectionCriterion :
      DHRSelectionCriterionTarget

    symmetricTensorCStarCategoryTarget :
      SymmetricTensorCStarCategoryTarget

    tierBPaper3Delta3cH1H5CompletenessCheck :
      TierBPaper3Delta3cH1H5CompletenessCheck

    tannakaDHRReconstructionTarget :
      TannakaDHRReconstructionTarget

    conditionalPatiSalamDHRReconstruction :
      ConditionalPatiSalamDHRReconstructionReceipt

    standardModelPrimeLaneCondensationTarget :
      StandardModelPrimeLaneCondensationTarget

    gate1Gate6AgreementObstruction :
      Gate1Gate6AgreementObstructionReceipt

    gate1ExactStandardModelCarrierFunctorMatchEvidence :
      ExactSM.ExactSMMatchReceipt

    openObligations :
      List DHRGaugeOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalDHRGaugeOpenObligations

    dhrPrimitivesTyped :
      Bool

    dhrPrimitivesTypedIsTrue :
      dhrPrimitivesTyped ≡ true

    laneDimensionComputedInternally :
      Bool

    laneDimensionComputedInternallyIsTrue :
      laneDimensionComputedInternally ≡ true

    gDHRComputedInternally :
      Bool

    gDHRComputedInternallyIsTrue :
      gDHRComputedInternally ≡ true

    dhrGaugePromoted :
      Bool

    dhrGaugePromotedIsFalse :
      dhrGaugePromoted ≡ false

    noPromotionWithoutAuthority :
      DHRGaugePromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open DHRGaugeReceiptSurface public

canonicalDHRGaugeReceiptSurface :
  DHRGaugeReceiptSurface
canonicalDHRGaugeReceiptSurface =
  record
    { status =
        dhrGaugeTargetsOnlyNoPromotion
    ; aqftTypedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; haagDualityTarget =
        canonicalHaagDualityReceiptTarget
    ; controlledGaugeFailure =
        canonicalGaugeTheoryControlledFailureSurface
    ; dhrFormalismPrimitiveReceipt =
        canonicalDHRFormalismPrimitiveReceipt
    ; dhrSelectionCriterion =
        canonicalDHRSelectionCriterionTarget
    ; symmetricTensorCStarCategoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; tierBPaper3Delta3cH1H5CompletenessCheck =
        canonicalTierBPaper3Delta3cH1H5CompletenessCheck
    ; tannakaDHRReconstructionTarget =
        canonicalTannakaDHRReconstructionTarget
    ; conditionalPatiSalamDHRReconstruction =
        canonicalConditionalPatiSalamDHRReconstructionReceipt
    ; standardModelPrimeLaneCondensationTarget =
        canonicalStandardModelPrimeLaneCondensationTarget
    ; gate1Gate6AgreementObstruction =
        canonicalGate1Gate6AgreementObstructionReceipt
    ; gate1ExactStandardModelCarrierFunctorMatchEvidence =
        exactStandardModelCarrierFunctorMatchEvidence
          canonicalGate1Gate6AgreementObstructionReceipt
    ; openObligations =
        canonicalDHRGaugeOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; dhrPrimitivesTyped =
        true
    ; dhrPrimitivesTypedIsTrue =
        refl
    ; laneDimensionComputedInternally =
        true
    ; laneDimensionComputedInternallyIsTrue =
        refl
    ; gDHRComputedInternally =
        true
    ; gDHRComputedInternallyIsTrue =
        refl
    ; dhrGaugePromoted =
        false
    ; dhrGaugePromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "DHR gauge reconstruction is recorded as typed target surfaces only"
        ∷ "LocalisedEndomorphism, Transportable, Intertwiner, statistics socket, category primitive socket, and Doplicher-Roberts authority surface are typed"
        ∷ "Tranche 1B records the internal gDHR computation A(O) ~= tensor_p A_p(O), Delta_DHR ~= boxtimes_p Delta_DHR^(p) ~= Rep(product_p G_p), and DR reconstruction of product_p G_p"
        ∷ "Delta 3c records H1-H5 completeness and routes H2/H5 Reeh-Schlieder cyclicity through the DASHI closed/immediate dense-orbit receipt"
        ∷ "H5 End(1) ~= C remains dependent on Haag duality plus Reeh-Schlieder cyclicity and irreducibility; this accounting does not promote DR reconstruction"
        ∷ "Gate 1/Gate 6 agreement is blocked until G_DHR and the carrier-functor gauge group are matched through the exact Standard Model/carrier-functor receipt"
        ∷ "laneDimension is not locally promoted; low-energy Standard Model matching still requires SU2R seesaw breaking and separate matching receipts"
        ∷ "Haag duality inclusion/equality, DHR law proofs, statistics computation, tensor C*-category construction, and Tannaka reconstruction remain open"
        ∷ "Standard Model matching and prime-lane condensation are downstream open obligations"
        ∷ "No gauge group, Standard Model, interacting QFT, GRQFT, or TOE promotion follows from this surface"
        ∷ []
    }

data AQFTToDHRPrimitiveBoundaryConsumer : Set where
  complementBoundaryConsumesAQFTRegionSocket :
    AQFTToDHRPrimitiveBoundaryConsumer

  haagEqualityBoundaryConsumesAQFTLocalAlgebraAndComplement :
    AQFTToDHRPrimitiveBoundaryConsumer

  haagDualityTargetConsumesAQFTNetComplementAndHaagEquality :
    AQFTToDHRPrimitiveBoundaryConsumer

  localisedTransportableBoundaryConsumesAQFTRegionLocalAlgebraAndComplement :
    AQFTToDHRPrimitiveBoundaryConsumer

  formalismReceiptConsumesLocalisedTransportableAndStatisticsSockets :
    AQFTToDHRPrimitiveBoundaryConsumer

  selectionCriterionConsumesFormalismPrimitiveReceipt :
    AQFTToDHRPrimitiveBoundaryConsumer

  categorySurfaceConsumesEndomorphismAndIntertwinerPrimitives :
    AQFTToDHRPrimitiveBoundaryConsumer

  symmetricTensorTargetConsumesSelectionAndCategorySurfaces :
    AQFTToDHRPrimitiveBoundaryConsumer

  dhrGaugeSurfaceConsumesAllPrimitiveBoundaryReceipts :
    AQFTToDHRPrimitiveBoundaryConsumer

canonicalAQFTToDHRPrimitiveBoundaryConsumers :
  List AQFTToDHRPrimitiveBoundaryConsumer
canonicalAQFTToDHRPrimitiveBoundaryConsumers =
  complementBoundaryConsumesAQFTRegionSocket
  ∷ haagEqualityBoundaryConsumesAQFTLocalAlgebraAndComplement
  ∷ haagDualityTargetConsumesAQFTNetComplementAndHaagEquality
  ∷ localisedTransportableBoundaryConsumesAQFTRegionLocalAlgebraAndComplement
  ∷ formalismReceiptConsumesLocalisedTransportableAndStatisticsSockets
  ∷ selectionCriterionConsumesFormalismPrimitiveReceipt
  ∷ categorySurfaceConsumesEndomorphismAndIntertwinerPrimitives
  ∷ symmetricTensorTargetConsumesSelectionAndCategorySurfaces
  ∷ dhrGaugeSurfaceConsumesAllPrimitiveBoundaryReceipts
  ∷ []

data AQFTToDHRPrimitiveBoundaryLedgerBlocker : Set where
  blockedByAQFTRootPostulateSockets :
    AQFTToDHRPrimitiveBoundaryLedgerBlocker

  blockedByAQFTConcreteHaagKastlerLawDerivations :
    AQFTToDHRPrimitiveBoundaryLedgerBlocker

  blockedByDHRComplementPrimitiveBoundary :
    AQFTToDHRPrimitiveBoundaryLedgerBlocker

  blockedByDHRLocalisedTransportablePrimitiveBoundary :
    AQFTToDHRPrimitiveBoundaryLedgerBlocker

  blockedByHaagEqualityPrimitiveBoundary :
    AQFTToDHRPrimitiveBoundaryLedgerBlocker

  blockedByDHRStatisticsFormulaComputation :
    AQFTToDHRPrimitiveBoundaryLedgerBlocker

  blockedBySymmetricTensorCStarCategoryConstruction :
    AQFTToDHRPrimitiveBoundaryLedgerBlocker

  blockedByDoplicherRobertsAuthorityAndStandardModelMatching :
    AQFTToDHRPrimitiveBoundaryLedgerBlocker

canonicalAQFTToDHRPrimitiveBoundaryLedgerBlockers :
  List AQFTToDHRPrimitiveBoundaryLedgerBlocker
canonicalAQFTToDHRPrimitiveBoundaryLedgerBlockers =
  blockedByAQFTRootPostulateSockets
  ∷ blockedByAQFTConcreteHaagKastlerLawDerivations
  ∷ blockedByDHRComplementPrimitiveBoundary
  ∷ blockedByDHRLocalisedTransportablePrimitiveBoundary
  ∷ blockedByHaagEqualityPrimitiveBoundary
  ∷ blockedByDHRStatisticsFormulaComputation
  ∷ blockedBySymmetricTensorCStarCategoryConstruction
  ∷ blockedByDoplicherRobertsAuthorityAndStandardModelMatching
  ∷ []

record AQFTToDHRPrimitiveBoundaryLedger : Setω where
  field
    aqftRootPostulates :
      AQFT.AQFTRootPostulateBoundaryReceipt

    canonicalAQFTRootPostulateReceiptSelected :
      Bool

    canonicalAQFTRootPostulateReceiptSelectedIsTrue :
      canonicalAQFTRootPostulateReceiptSelected ≡ true

    aqftTypedNetSurface :
      AQFT.AQFTTypedNetSurface

    canonicalAQFTTypedNetSurfaceSelected :
      Bool

    canonicalAQFTTypedNetSurfaceSelectedIsTrue :
      canonicalAQFTTypedNetSurfaceSelected ≡ true

    aqftFoundationalSockets :
      List AQFT.AQFTFoundationalSocket

    aqftFoundationalSocketsAreCanonical :
      aqftFoundationalSockets ≡ AQFT.canonicalAQFTFoundationalSockets

    aqftRootBlockers :
      List AQFT.AQFTRootPostulateBoundaryBlocker

    aqftRootBlockersAreCanonical :
      aqftRootBlockers ≡ AQFT.canonicalAQFTRootPostulateBoundaryBlockers

    aqftOpenObligations :
      List AQFT.AQFTTypedNetOpenObligation

    aqftOpenObligationsAreCanonical :
      aqftOpenObligations
      ≡
      AQFT.AQFTTypedNetSurface.openObligations
        AQFT.canonicalAQFTTypedNetSurface

    complementPrimitiveBoundary :
      DHRComplementPrimitiveBoundaryReceipt

    canonicalComplementPrimitiveBoundarySelected :
      Bool

    canonicalComplementPrimitiveBoundarySelectedIsTrue :
      canonicalComplementPrimitiveBoundarySelected ≡ true

    complementPrimitiveBlockers :
      List DHRComplementPrimitiveBoundaryBlocker

    complementPrimitiveBlockersAreCanonical :
      complementPrimitiveBlockers
      ≡
      canonicalDHRComplementPrimitiveBoundaryBlockers

    localisedTransportablePrimitiveBoundary :
      DHRLocalisedTransportablePrimitiveBoundaryReceipt

    canonicalLocalisedTransportablePrimitiveBoundarySelected :
      Bool

    canonicalLocalisedTransportablePrimitiveBoundarySelectedIsTrue :
      canonicalLocalisedTransportablePrimitiveBoundarySelected ≡ true

    localisedTransportablePrimitiveBlockers :
      List DHRLocalisedTransportablePrimitiveBoundaryBlocker

    localisedTransportablePrimitiveBlockersAreCanonical :
      localisedTransportablePrimitiveBlockers
      ≡
      canonicalDHRLocalisedTransportablePrimitiveBoundaryBlockers

    haagEqualityPrimitiveBoundary :
      HaagEqualityPrimitiveBoundaryReceipt

    canonicalHaagEqualityPrimitiveBoundarySelected :
      Bool

    canonicalHaagEqualityPrimitiveBoundarySelectedIsTrue :
      canonicalHaagEqualityPrimitiveBoundarySelected ≡ true

    haagEqualityPrimitiveBlockers :
      List HaagEqualityPrimitiveBoundaryBlocker

    haagEqualityPrimitiveBlockersAreCanonical :
      haagEqualityPrimitiveBlockers
      ≡
      canonicalHaagEqualityPrimitiveBoundaryBlockers

    dhrFormalismPrimitiveReceipt :
      DHRFormalismPrimitiveReceipt

    canonicalDHRFormalismPrimitiveReceiptSelected :
      Bool

    canonicalDHRFormalismPrimitiveReceiptSelectedIsTrue :
      canonicalDHRFormalismPrimitiveReceiptSelected ≡ true

    haagDualityReceiptTarget :
      HaagDualityReceiptTarget

    canonicalHaagDualityReceiptTargetSelected :
      Bool

    canonicalHaagDualityReceiptTargetSelectedIsTrue :
      canonicalHaagDualityReceiptTargetSelected ≡ true

    dhrSelectionCriterionTarget :
      DHRSelectionCriterionTarget

    canonicalDHRSelectionCriterionTargetSelected :
      Bool

    canonicalDHRSelectionCriterionTargetSelectedIsTrue :
      canonicalDHRSelectionCriterionTargetSelected ≡ true

    dhrCategoryPrimitiveSurface :
      DHRCategoryPrimitiveSurface

    canonicalDHRCategoryPrimitiveSurfaceSelected :
      Bool

    canonicalDHRCategoryPrimitiveSurfaceSelectedIsTrue :
      canonicalDHRCategoryPrimitiveSurfaceSelected ≡ true

    symmetricTensorCStarCategoryTarget :
      SymmetricTensorCStarCategoryTarget

    canonicalSymmetricTensorCStarCategoryTargetSelected :
      Bool

    canonicalSymmetricTensorCStarCategoryTargetSelectedIsTrue :
      canonicalSymmetricTensorCStarCategoryTargetSelected ≡ true

    dhrGaugeReceiptSurface :
      DHRGaugeReceiptSurface

    canonicalDHRGaugeReceiptSurfaceSelected :
      Bool

    canonicalDHRGaugeReceiptSurfaceSelectedIsTrue :
      canonicalDHRGaugeReceiptSurfaceSelected ≡ true

    dhrGaugeOpenObligations :
      List DHRGaugeOpenObligation

    dhrGaugeOpenObligationsAreCanonical :
      dhrGaugeOpenObligations ≡ canonicalDHRGaugeOpenObligations

    downstreamConsumers :
      List AQFTToDHRPrimitiveBoundaryConsumer

    downstreamConsumersAreCanonical :
      downstreamConsumers
      ≡
      canonicalAQFTToDHRPrimitiveBoundaryConsumers

    ledgerBlockers :
      List AQFTToDHRPrimitiveBoundaryLedgerBlocker

    ledgerBlockersAreCanonical :
      ledgerBlockers
      ≡
      canonicalAQFTToDHRPrimitiveBoundaryLedgerBlockers

    aqftRootPostulatesEliminatedByLedger :
      Bool

    aqftRootPostulatesEliminatedByLedgerIsFalse :
      aqftRootPostulatesEliminatedByLedger ≡ false

    dhrPrimitiveBoundariesDischargedByLedger :
      Bool

    dhrPrimitiveBoundariesDischargedByLedgerIsFalse :
      dhrPrimitiveBoundariesDischargedByLedger ≡ false

    dhrGaugePromotedByLedger :
      Bool

    dhrGaugePromotedByLedgerIsFalse :
      dhrGaugePromotedByLedger ≡ false

    grqftPromotedByLedger :
      Bool

    grqftPromotedByLedgerIsFalse :
      grqftPromotedByLedger ≡ false

    ledgerBoundary :
      List String

open AQFTToDHRPrimitiveBoundaryLedger public

canonicalAQFTToDHRPrimitiveBoundaryLedger :
  AQFTToDHRPrimitiveBoundaryLedger
canonicalAQFTToDHRPrimitiveBoundaryLedger =
  record
    { aqftRootPostulates =
        AQFT.canonicalAQFTRootPostulateBoundaryReceipt
    ; canonicalAQFTRootPostulateReceiptSelected =
        true
    ; canonicalAQFTRootPostulateReceiptSelectedIsTrue =
        refl
    ; aqftTypedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; canonicalAQFTTypedNetSurfaceSelected =
        true
    ; canonicalAQFTTypedNetSurfaceSelectedIsTrue =
        refl
    ; aqftFoundationalSockets =
        AQFT.canonicalAQFTFoundationalSockets
    ; aqftFoundationalSocketsAreCanonical =
        refl
    ; aqftRootBlockers =
        AQFT.canonicalAQFTRootPostulateBoundaryBlockers
    ; aqftRootBlockersAreCanonical =
        refl
    ; aqftOpenObligations =
        AQFT.AQFTTypedNetSurface.openObligations
          AQFT.canonicalAQFTTypedNetSurface
    ; aqftOpenObligationsAreCanonical =
        refl
    ; complementPrimitiveBoundary =
        canonicalDHRComplementPrimitiveBoundaryReceipt
    ; canonicalComplementPrimitiveBoundarySelected =
        true
    ; canonicalComplementPrimitiveBoundarySelectedIsTrue =
        refl
    ; complementPrimitiveBlockers =
        canonicalDHRComplementPrimitiveBoundaryBlockers
    ; complementPrimitiveBlockersAreCanonical =
        refl
    ; localisedTransportablePrimitiveBoundary =
        canonicalDHRLocalisedTransportablePrimitiveBoundaryReceipt
    ; canonicalLocalisedTransportablePrimitiveBoundarySelected =
        true
    ; canonicalLocalisedTransportablePrimitiveBoundarySelectedIsTrue =
        refl
    ; localisedTransportablePrimitiveBlockers =
        canonicalDHRLocalisedTransportablePrimitiveBoundaryBlockers
    ; localisedTransportablePrimitiveBlockersAreCanonical =
        refl
    ; haagEqualityPrimitiveBoundary =
        canonicalHaagEqualityPrimitiveBoundaryReceipt
    ; canonicalHaagEqualityPrimitiveBoundarySelected =
        true
    ; canonicalHaagEqualityPrimitiveBoundarySelectedIsTrue =
        refl
    ; haagEqualityPrimitiveBlockers =
        canonicalHaagEqualityPrimitiveBoundaryBlockers
    ; haagEqualityPrimitiveBlockersAreCanonical =
        refl
    ; dhrFormalismPrimitiveReceipt =
        canonicalDHRFormalismPrimitiveReceipt
    ; canonicalDHRFormalismPrimitiveReceiptSelected =
        true
    ; canonicalDHRFormalismPrimitiveReceiptSelectedIsTrue =
        refl
    ; haagDualityReceiptTarget =
        canonicalHaagDualityReceiptTarget
    ; canonicalHaagDualityReceiptTargetSelected =
        true
    ; canonicalHaagDualityReceiptTargetSelectedIsTrue =
        refl
    ; dhrSelectionCriterionTarget =
        canonicalDHRSelectionCriterionTarget
    ; canonicalDHRSelectionCriterionTargetSelected =
        true
    ; canonicalDHRSelectionCriterionTargetSelectedIsTrue =
        refl
    ; dhrCategoryPrimitiveSurface =
        canonicalDHRCategoryPrimitiveSurface
    ; canonicalDHRCategoryPrimitiveSurfaceSelected =
        true
    ; canonicalDHRCategoryPrimitiveSurfaceSelectedIsTrue =
        refl
    ; symmetricTensorCStarCategoryTarget =
        canonicalSymmetricTensorCStarCategoryTarget
    ; canonicalSymmetricTensorCStarCategoryTargetSelected =
        true
    ; canonicalSymmetricTensorCStarCategoryTargetSelectedIsTrue =
        refl
    ; dhrGaugeReceiptSurface =
        canonicalDHRGaugeReceiptSurface
    ; canonicalDHRGaugeReceiptSurfaceSelected =
        true
    ; canonicalDHRGaugeReceiptSurfaceSelectedIsTrue =
        refl
    ; dhrGaugeOpenObligations =
        canonicalDHRGaugeOpenObligations
    ; dhrGaugeOpenObligationsAreCanonical =
        refl
    ; downstreamConsumers =
        canonicalAQFTToDHRPrimitiveBoundaryConsumers
    ; downstreamConsumersAreCanonical =
        refl
    ; ledgerBlockers =
        canonicalAQFTToDHRPrimitiveBoundaryLedgerBlockers
    ; ledgerBlockersAreCanonical =
        refl
    ; aqftRootPostulatesEliminatedByLedger =
        false
    ; aqftRootPostulatesEliminatedByLedgerIsFalse =
        refl
    ; dhrPrimitiveBoundariesDischargedByLedger =
        false
    ; dhrPrimitiveBoundariesDischargedByLedgerIsFalse =
        refl
    ; dhrGaugePromotedByLedger =
        false
    ; dhrGaugePromotedByLedgerIsFalse =
        refl
    ; grqftPromotedByLedger =
        false
    ; grqftPromotedByLedgerIsFalse =
        refl
    ; ledgerBoundary =
        "AQFT root postulates are foundational sockets, not downstream DHR derivations"
        ∷ "DHR complement, Haag equality, localised-transportable, formalism, selection, category, symmetric tensor, and gauge surfaces consume those sockets through canonical primitive-boundary receipts"
        ∷ "The exact AQFT, complement, localised-transportable, Haag-equality, and DHR gauge blocker lists are preserved on this ledger"
        ∷ "The ledger does not eliminate AQFT postulates, discharge DHR primitive boundaries, promote G_DHR, or promote GRQFT"
        ∷ []
    }

record WheelSpokeEarthGeometry : Setω where
  field
    wheelU1Sector :
      DHRSector.U1SectorObject

    wheelSU2Sector :
      DHRSector.SU2SectorObject

    wheelSU3Frontier :
      DHRSector.SU3FrontierObject

    spokeDecomposition :
      DHRSector.DHRSectorDecomposition

    earthBasisLabel :
      String

    bottIndex :
      Nat

    orbifoldRho1 :
      Nat

    orbifoldRho2 :
      Nat

    orbifoldRho3 :
      Nat

    bottIndexIsFive :
      bottIndex ≡ 5

    orbifoldRho1Is56 :
      orbifoldRho1 ≡ 56

    orbifoldRho2Is57 :
      orbifoldRho2 ≡ 57

    orbifoldRho3Is24 :
      orbifoldRho3 ≡ 24

    gate1Gate6AgreementObstructionReceipt :
      Gate1Gate6AgreementObstructionReceipt

    gate1ExactStandardModelCarrierFunctorMatchEvidence :
      ExactSM.ExactSMMatchReceipt

    gradedWitness :
      Graded.GradedSFGCSite2DWitness

    nonAbelianCarrierWitness :
      Carrier.NonAbelianSFGCCarrierWitness

    depthQuotientWitness :
      DepthQuotient.DepthQuotientWitness

    su3RouteNote :
      SU3.SU3ColorSectorRouteNote

    wheelSpokeBoundary :
      List String

canonicalWheelSpokeEarthGeometry :
  WheelSpokeEarthGeometry
canonicalWheelSpokeEarthGeometry =
  record
    { wheelU1Sector =
        DHRSector.canonicalU1SectorObject
    ; wheelSU2Sector =
        DHRSector.canonicalSU2SectorObject
    ; wheelSU3Frontier =
        DHRSector.canonicalSU3FrontierObject
    ; spokeDecomposition =
        DHRSector.canonicalDHRSectorDecomposition
    ; earthBasisLabel =
        "mass-eigenstate base recorded by the canonical DHR decomposition"
    ; bottIndex =
        5
    ; orbifoldRho1 =
        56
    ; orbifoldRho2 =
        57
    ; orbifoldRho3 =
        24
    ; bottIndexIsFive =
        refl
    ; orbifoldRho1Is56 =
        refl
    ; orbifoldRho2Is57 =
        refl
    ; orbifoldRho3Is24 =
        refl
    ; gate1Gate6AgreementObstructionReceipt =
        canonicalGate1Gate6AgreementObstructionReceipt
    ; gate1ExactStandardModelCarrierFunctorMatchEvidence =
        exactStandardModelCarrierFunctorMatchEvidence
          canonicalGate1Gate6AgreementObstructionReceipt
    ; gradedWitness =
        Graded.canonicalGradedSFGCSite2DWitness
    ; nonAbelianCarrierWitness =
        Carrier.canonicalNonAbelianSFGCCarrierWitness
    ; depthQuotientWitness =
        DepthQuotient.canonicalDepthQuotientWitness
    ; su3RouteNote =
        SU3.canonicalSU3ColorSectorRouteNote
    ; wheelSpokeBoundary =
        "WheelSpokeEarthGeometry packages the real finite witness chain only"
        ∷ "The gate surface consumes the Gate 1 exact Standard Model carrier-functor witness as typed evidence"
        ∷ "The graded, nonabelian, depth-quotient, and SU(3) route witnesses are reused from existing repo modules"
        ∷ []
    }

record DRFiveHypothesesEvidenceSurface : Setω where
  field
    drHypotheses :
      DRHypothesesForDASHI

    h1Evidence :
      DRH1SymmetricTensorStarCategory

    h1EvidenceMatchesCanonical :
      Bool

    h2Evidence :
      DRH2Conjugates

    h2EvidenceMatchesCanonical :
      Bool

    h3Evidence :
      DRH3DirectSums

    h3EvidenceMatchesCanonical :
      Bool

    h4Evidence :
      DRH4Subobjects

    h4EvidenceMatchesCanonical :
      Bool

    h5Evidence :
      DRH5EndUnitScalars

    h5EvidenceMatchesCanonical :
      Bool

    theoremHypothesesFed :
      DRHypothesesForDASHI.theoremHypothesesTarget drHypotheses
      ≡
      abstractDoplicherRobertsTheoremHypothesesTarget

    allFiveHypothesesPackaged :
      Bool

    allFiveHypothesesPackagedIsTrue :
      allFiveHypothesesPackaged ≡ true

    drTheoremLocallyProved :
      Bool

    drTheoremLocallyProvedIsFalse :
      drTheoremLocallyProved ≡ false

    compactGaugeGroupConstructed :
      Bool

    compactGaugeGroupConstructedIsFalse :
      compactGaugeGroupConstructed ≡ false

    standardModelMatchingProved :
      Bool

    standardModelMatchingProvedIsFalse :
      standardModelMatchingProved ≡ false

    evidenceBoundary :
      List String

open DRFiveHypothesesEvidenceSurface public

canonicalDRFiveHypothesesEvidenceSurface :
  DRFiveHypothesesEvidenceSurface
canonicalDRFiveHypothesesEvidenceSurface =
  record
    { drHypotheses =
        canonicalDRHypothesesForDASHI
    ; h1Evidence =
        canonicalDRH1SymmetricTensorStarCategory
    ; h1EvidenceMatchesCanonical =
        true
    ; h2Evidence =
        canonicalDRH2Conjugates
    ; h2EvidenceMatchesCanonical =
        true
    ; h3Evidence =
        canonicalDRH3DirectSums
    ; h3EvidenceMatchesCanonical =
        true
    ; h4Evidence =
        canonicalDRH4Subobjects
    ; h4EvidenceMatchesCanonical =
        true
    ; h5Evidence =
        canonicalDRH5EndUnitScalars
    ; h5EvidenceMatchesCanonical =
        true
    ; theoremHypothesesFed =
        refl
    ; allFiveHypothesesPackaged =
        true
    ; allFiveHypothesesPackagedIsTrue =
        refl
    ; drTheoremLocallyProved =
        false
    ; drTheoremLocallyProvedIsFalse =
        refl
    ; compactGaugeGroupConstructed =
        false
    ; compactGaugeGroupConstructedIsFalse =
        refl
    ; standardModelMatchingProved =
        false
    ; standardModelMatchingProvedIsFalse =
        refl
    ; evidenceBoundary =
        "DR H1-H5 are exposed as concrete evidence records, not only as Bool flags"
        ∷ "H1 symmetric tensor star-category, H2 conjugates, H3 direct sums, H4 subobjects, and H5 End(1)=C targets are threaded into DRHypothesesForDASHI"
        ∷ "The theorem-hypotheses socket is definitionally the Doplicher-Roberts authority target"
        ∷ "This packages evidence for the authority boundary but does not locally prove the DR theorem, construct the compact gauge group, or prove Standard Model matching"
        ∷ []
    }

record DHRLocalisedTransportableEndomorphismEvidenceSurface : Setω where
  field
    formalismReceipt :
      DHRFormalismPrimitiveReceipt

    primitiveBoundaryReceipt :
      DHRLocalisedTransportablePrimitiveBoundaryReceipt

    localisedEndomorphismPrimitive :
      SuperselectionSector →
      LocalisedEndomorphism

    localisedEndomorphismPrimitiveMatchesFormalism :
      Bool

    transportablePrimitive :
      (ρ : LocalisedEndomorphism) →
      Transportable ρ

    transportablePrimitiveMatchesFormalism :
      Bool

    statisticsFormulaSocket :
      (ρ σ : LocalisedEndomorphism) →
      DHRStatisticsFormulaSocket ρ σ

    statisticsFormulaSocketMatchesFormalism :
      Bool

    localizedTransportableEndomorphismsTyped :
      Bool

    localizedTransportableEndomorphismsTypedIsTrue :
      localizedTransportableEndomorphismsTyped ≡ true

    statisticsComputed :
      Bool

    statisticsComputedIsFalse :
      statisticsComputed ≡ false

    evidenceBoundary :
      List String

open DHRLocalisedTransportableEndomorphismEvidenceSurface public

canonicalDHRLocalisedTransportableEndomorphismEvidenceSurface :
  DHRLocalisedTransportableEndomorphismEvidenceSurface
canonicalDHRLocalisedTransportableEndomorphismEvidenceSurface =
  record
    { formalismReceipt =
        canonicalDHRFormalismPrimitiveReceipt
    ; primitiveBoundaryReceipt =
        DHRFormalismPrimitiveReceipt.localisedTransportablePrimitiveBoundary
          canonicalDHRFormalismPrimitiveReceipt
    ; localisedEndomorphismPrimitive =
        DHRFormalismPrimitiveReceipt.formalismLocalisedEndomorphismPrimitive
          canonicalDHRFormalismPrimitiveReceipt
    ; localisedEndomorphismPrimitiveMatchesFormalism =
        true
    ; transportablePrimitive =
        DHRFormalismPrimitiveReceipt.formalismTransportablePrimitive
          canonicalDHRFormalismPrimitiveReceipt
    ; transportablePrimitiveMatchesFormalism =
        true
    ; statisticsFormulaSocket =
        DHRFormalismPrimitiveReceipt.formalismStatisticsFormulaSocket
          canonicalDHRFormalismPrimitiveReceipt
    ; statisticsFormulaSocketMatchesFormalism =
        true
    ; localizedTransportableEndomorphismsTyped =
        true
    ; localizedTransportableEndomorphismsTypedIsTrue =
        refl
    ; statisticsComputed =
        false
    ; statisticsComputedIsFalse =
        refl
    ; evidenceBoundary =
        "LocalisedEndomorphism and Transportable primitive sockets are exposed through the canonical fail-closed primitive-boundary receipt"
        ∷ "This advances the typed DHR endomorphism/transport/statistics evidence surface"
        ∷ "Statistics computation, tensor C*-category construction, DR theorem application, and gauge reconstruction remain unpromoted"
        ∷ []
    }

data DHRIdentityEndomorphismWitnessBlocker : Set where
  missingIdentityEndomorphismActionConstructor :
    DHRIdentityEndomorphismWitnessBlocker

  missingDASHILocalAlgebraForIdentityActionSemantics :
    DHRIdentityEndomorphismWitnessBlocker

  missingArbitrarySectorIdentityEndomorphismSemantics :
    DHRIdentityEndomorphismWitnessBlocker

record DHRIdentityAndSectorWiringSurface : Setω₁ where
  field
    localAlgebraIdentitySemantics :
      ∀ (region : AQFT.Region) →
      LocalAlgebraIdentity.DASHILocalAlgebraIdentitySemantics region

    gradedSectorWitness :
      Graded.GradedSFGCSite2DWitness

    nonAbelianCarrierWitness :
      Carrier.NonAbelianSFGCCarrierWitness

    depthQuotientWitness :
      DepthQuotient.DepthQuotientWitness

    su3ColorSectorRouteNote :
      SU3.SU3ColorSectorRouteNote

    gate1Gate6AgreementObstruction :
      Gate1Gate6AgreementObstruction

    gate1Gate6AgreementObstructionIsCanonical :
      gate1Gate6AgreementObstruction
      ≡
      missingExactStandardModelCarrierFunctorMatch

    wiringBoundary :
      List String

open DHRIdentityAndSectorWiringSurface public

canonicalDHRIdentityAndSectorWiringSurface :
  DHRIdentityAndSectorWiringSurface
canonicalDHRIdentityAndSectorWiringSurface =
  record
    { localAlgebraIdentitySemantics =
        λ region →
          LocalAlgebraIdentity.localAlgebraIdentitySemanticsWitness region
    ; gradedSectorWitness =
        Graded.canonicalGradedSFGCSite2DWitness
    ; nonAbelianCarrierWitness =
        Carrier.canonicalNonAbelianSFGCCarrierWitness
    ; depthQuotientWitness =
        DepthQuotient.canonicalDepthQuotientWitness
    ; su3ColorSectorRouteNote =
        SU3.canonicalSU3ColorSectorRouteNote
    ; gate1Gate6AgreementObstruction =
        missingExactStandardModelCarrierFunctorMatch
    ; gate1Gate6AgreementObstructionIsCanonical =
        refl
    ; wiringBoundary =
        "The local identity-action semantics are recorded from the upstream canonical DHR local algebra witness"
        ∷ "The DHR sector decomposition components are recorded from the upstream graded, carrier, depth-quotient, and SU(3) route witnesses"
        ∷ "The exact Standard Model carrier-functor match remains the explicit obstruction"
        ∷ []
    }

data EndomorphismActionPrimitiveShape : Set where
  endomorphismActionPostulatedBareSet :
    EndomorphismActionPrimitiveShape

record DHRIdentityEndomorphismActionConstructorShapeReceipt : Setω₂ where
  field
    endomorphismActionTarget :
      Setω₁

    endomorphismActionPrimitiveShape :
      EndomorphismActionPrimitiveShape

    endomorphismActionPrimitiveShapeIsPostulatedBareSet :
      endomorphismActionPrimitiveShape
      ≡
      endomorphismActionPostulatedBareSet

    localisedEndomorphismActionProjection :
      LocalisedEndomorphism →
      EndomorphismAction

    datatypeIdentityConstructorAvailable :
      Bool

    datatypeIdentityConstructorAvailableIsFalse :
      datatypeIdentityConstructorAvailable ≡ false

    recordIdentityActionFieldAvailable :
      Bool

    recordIdentityActionFieldAvailableIsFalse :
      recordIdentityActionFieldAvailable ≡ false

    localIdentityConstructorCanBeFabricated :
      Bool

    localIdentityConstructorCanBeFabricatedIsFalse :
      localIdentityConstructorCanBeFabricated ≡ false

    constructorFabricationBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    constructorFabricationBlockerIsMissingConstructor :
      constructorFabricationBlocker
      ≡
      missingIdentityEndomorphismActionConstructor

    constructorShapeBoundary :
      List String

open DHRIdentityEndomorphismActionConstructorShapeReceipt public

canonicalDHRIdentityEndomorphismActionConstructorShapeReceipt :
  DHRIdentityEndomorphismActionConstructorShapeReceipt
canonicalDHRIdentityEndomorphismActionConstructorShapeReceipt =
  record
    { endomorphismActionTarget =
        Setω
    ; endomorphismActionPrimitiveShape =
        endomorphismActionPostulatedBareSet
    ; endomorphismActionPrimitiveShapeIsPostulatedBareSet =
        refl
    ; localisedEndomorphismActionProjection =
        LocalisedEndomorphism.endomorphismAction
    ; datatypeIdentityConstructorAvailable =
        false
    ; datatypeIdentityConstructorAvailableIsFalse =
        refl
    ; recordIdentityActionFieldAvailable =
        false
    ; recordIdentityActionFieldAvailableIsFalse =
        refl
    ; localIdentityConstructorCanBeFabricated =
        false
    ; localIdentityConstructorCanBeFabricatedIsFalse =
        refl
    ; constructorFabricationBlocker =
        missingIdentityEndomorphismActionConstructor
    ; constructorFabricationBlockerIsMissingConstructor =
        refl
    ; constructorShapeBoundary =
        "EndomorphismAction is postulated as a bare Set in this module"
        ∷ "It is not declared as a datatype exposing an identity constructor"
        ∷ "It is not declared as a record exposing an identity-action field"
        ∷ "A local identity constructor would fabricate a new primitive witness rather than project existing structure"
        ∷ []
    }

record DHRIdentityEndomorphismWitnessAudit : Setω₃ where
  field
    localisedTransportableEvidence :
      DHRLocalisedTransportableEndomorphismEvidenceSurface

    endomorphismActionField :
      LocalisedEndomorphism →
      EndomorphismAction

    identityEndomorphismActionConstructorTarget :
      Set₂

    identityEndomorphismActionConstructorShapeReceipt :
      DHRIdentityEndomorphismActionConstructorShapeReceipt

    unitEndomorphismTarget :
      LocalisedEndomorphism →
      Set

    identityEndomorphismActionConstructorSupplied :
      Bool

    identityEndomorphismActionConstructorSuppliedIsFalse :
      identityEndomorphismActionConstructorSupplied ≡ false

    selectedPrimeLaneIdentityActionWitnessConstructed :
      Bool

    selectedPrimeLaneIdentityActionWitnessConstructedIsFalse :
      selectedPrimeLaneIdentityActionWitnessConstructed ≡ false

    arbitrarySectorIdentityEndomorphismWitnessConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismWitnessConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismWitnessConstructed ≡ false

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsFalse :
      missingDASHILocalAlgebraConsumed ≡ false

    drReceiptApplied :
      Bool

    drReceiptAppliedIsFalse :
      drReceiptApplied ≡ false

    firstIdentityEndomorphismBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    firstIdentityEndomorphismBlockerIsMissingConstructor :
      firstIdentityEndomorphismBlocker
      ≡
      missingIdentityEndomorphismActionConstructor

    identityEndomorphismBlockers :
      List DHRIdentityEndomorphismWitnessBlocker

    identityEndomorphismAuditBoundary :
      List String

open DHRIdentityEndomorphismWitnessAudit public

canonicalDHRIdentityEndomorphismWitnessAudit :
  DHRIdentityEndomorphismWitnessAudit
canonicalDHRIdentityEndomorphismWitnessAudit =
  record
    { localisedTransportableEvidence =
        canonicalDHRLocalisedTransportableEndomorphismEvidenceSurface
    ; endomorphismActionField =
        LocalisedEndomorphism.endomorphismAction
    ; identityEndomorphismActionConstructorTarget =
        Set₁
    ; identityEndomorphismActionConstructorShapeReceipt =
        canonicalDHRIdentityEndomorphismActionConstructorShapeReceipt
    ; unitEndomorphismTarget =
        abstractDRUnitEndomorphismTarget
    ; identityEndomorphismActionConstructorSupplied =
        false
    ; identityEndomorphismActionConstructorSuppliedIsFalse =
        refl
    ; selectedPrimeLaneIdentityActionWitnessConstructed =
        false
    ; selectedPrimeLaneIdentityActionWitnessConstructedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismWitnessConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismWitnessConstructedIsFalse =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; missingDASHILocalAlgebraConsumedIsFalse =
        refl
    ; drReceiptApplied =
        false
    ; drReceiptAppliedIsFalse =
        refl
    ; firstIdentityEndomorphismBlocker =
        missingIdentityEndomorphismActionConstructor
    ; firstIdentityEndomorphismBlockerIsMissingConstructor =
        refl
    ; identityEndomorphismBlockers =
        missingIdentityEndomorphismActionConstructor
        ∷ missingDASHILocalAlgebraForIdentityActionSemantics
        ∷ missingArbitrarySectorIdentityEndomorphismSemantics
        ∷ []
    ; identityEndomorphismAuditBoundary =
        "Identity-endomorphism audit: EndomorphismAction is a postulated bare Set, not a datatype or record identity-field surface"
        ∷ "LocalisedEndomorphism exposes an endomorphismAction projection only after a LocalisedEndomorphism is supplied"
        ∷ "No local identity EndomorphismAction constructor can be fabricated from that projection"
        ∷ "The DR unit endomorphism remains a target socket, not a local identity-action witness"
        ∷ "Selected prime-lane carrier identity can only be consumed from explicit supplied foreign-lane identity evidence"
        ∷ "Arbitrary-sector identity endomorphism semantics remain blocked by missingDASHILocalAlgebra and sector semantics"
        ∷ "No Doplicher-Roberts reconstruction receipt is applied by this audit"
        ∷ []
    }

record DHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt : Setω₃ where
  field
    identityEndomorphismWitnessAudit :
      Bool

    identityEndomorphismActionConstructorShapeReceipt :
      DHRIdentityEndomorphismActionConstructorShapeReceipt

    localisedEndomorphismActionProjection :
      LocalisedEndomorphism →
      EndomorphismAction

    arbitrarySectorIdentityEndomorphismTarget :
      SuperselectionSector →
      Set

    identityActionConstructorBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    identityActionConstructorBlockerIsMissingConstructor :
      identityActionConstructorBlocker
      ≡
      missingIdentityEndomorphismActionConstructor

    localAlgebraSemanticsBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    localAlgebraSemanticsBlockerIsMissingDASHILocalAlgebraSemantics :
      localAlgebraSemanticsBlocker
      ≡
      missingDASHILocalAlgebraForIdentityActionSemantics

    identityActionConstructorSupplied :
      Bool

    identityActionConstructorSuppliedIsFalse :
      identityActionConstructorSupplied ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    missingDASHILocalAlgebraSemanticsConsumed :
      Bool

    missingDASHILocalAlgebraSemanticsConsumedIsFalse :
      missingDASHILocalAlgebraSemanticsConsumed ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    upper6IdentityEndomorphismBoundary :
      List String

open DHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt public

canonicalDHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt :
  DHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt
canonicalDHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt =
  record
    { identityEndomorphismWitnessAudit =
        true
    ; identityEndomorphismActionConstructorShapeReceipt =
        canonicalDHRIdentityEndomorphismActionConstructorShapeReceipt
    ; localisedEndomorphismActionProjection =
        LocalisedEndomorphism.endomorphismAction
    ; arbitrarySectorIdentityEndomorphismTarget =
        λ _ →
          ⊥
    ; identityActionConstructorBlocker =
        missingIdentityEndomorphismActionConstructor
    ; identityActionConstructorBlockerIsMissingConstructor =
        refl
    ; localAlgebraSemanticsBlocker =
        missingDASHILocalAlgebraForIdentityActionSemantics
    ; localAlgebraSemanticsBlockerIsMissingDASHILocalAlgebraSemantics =
        refl
    ; identityActionConstructorSupplied =
        false
    ; identityActionConstructorSuppliedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; missingDASHILocalAlgebraSemanticsConsumed =
        false
    ; missingDASHILocalAlgebraSemanticsConsumedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; upper6IdentityEndomorphismBoundary =
        "upper6 identity-endomorphism attempt: LocalisedEndomorphism.endomorphismAction can be projected only after a LocalisedEndomorphism is supplied"
        ∷ "EndomorphismAction is a postulated bare Set, so no datatype constructor or record field can supply identity EndomorphismAction locally"
        ∷ "A local identity constructor would fabricate a primitive witness, so arbitrarySectorIdentityEndomorphism is not constructed"
        ∷ "missingDASHILocalAlgebra semantics are not consumed; the identity action has no DASHI local-algebra interpretation here"
        ∷ "No arbitrary DHR sector, Doplicher-Roberts reconstruction, gauge group, or Standard Model match is fabricated"
        ∷ []
    }

record DHRGaugeGate1Wave3FinalLocalBoundaryReceipt : Setω where
  field
    drEvidenceSurface :
      DRFiveHypothesesEvidenceSurface

    localisedTransportableEvidence :
      DHRLocalisedTransportableEndomorphismEvidenceSurface

    aqftCarrierPredicateLocalRetirement :
      AQFTColim.AQFTCarrierPredicateLocalBlockerRetirementReceipt

    aqftCurrentFirstResidual :
      AQFTColim.AQFTCarrierAlgebraQuotientOpenObligation

    aqftCurrentFirstResidualIsMissingPreciseQuotientRelation :
      aqftCurrentFirstResidual
      ≡
      AQFTColim.missingPreciseQuotientRelation

    gate1Gate6AgreementObstruction :
      Gate1Gate6AgreementObstruction

    gate1Gate6AgreementObstructionIsExactMatch :
      gate1Gate6AgreementObstruction
      ≡
      missingExactStandardModelCarrierFunctorMatch

    suppliedForeignIdentityPathIsExternalInput :
      Bool

    suppliedForeignIdentityPathIsExternalInputIsTrue :
      suppliedForeignIdentityPathIsExternalInput ≡ true

    unconditionalDHRGaugePromotion :
      Bool

    unconditionalDHRGaugePromotionIsFalse :
      unconditionalDHRGaugePromotion ≡ false

    finalLocalBoundary :
      List String

open DHRGaugeGate1Wave3FinalLocalBoundaryReceipt public

canonicalDHRGaugeGate1Wave3FinalLocalBoundaryReceipt :
  DHRGaugeGate1Wave3FinalLocalBoundaryReceipt
canonicalDHRGaugeGate1Wave3FinalLocalBoundaryReceipt =
  record
    { drEvidenceSurface =
        canonicalDRFiveHypothesesEvidenceSurface
    ; localisedTransportableEvidence =
        canonicalDHRLocalisedTransportableEndomorphismEvidenceSurface
    ; aqftCarrierPredicateLocalRetirement =
        AQFTColim.canonicalAQFTCarrierPredicateLocalBlockerRetirementReceipt
    ; aqftCurrentFirstResidual =
        AQFTColim.missingPreciseQuotientRelation
    ; aqftCurrentFirstResidualIsMissingPreciseQuotientRelation =
        refl
    ; gate1Gate6AgreementObstruction =
        missingExactStandardModelCarrierFunctorMatch
    ; gate1Gate6AgreementObstructionIsExactMatch =
        refl
    ; suppliedForeignIdentityPathIsExternalInput =
        true
    ; suppliedForeignIdentityPathIsExternalInputIsTrue =
        refl
    ; unconditionalDHRGaugePromotion =
        false
    ; unconditionalDHRGaugePromotionIsFalse =
        refl
    ; finalLocalBoundary =
        "DHR gauge wave-3 final-local receipt keeps DR H1-H5 and localised transportable endomorphism evidence typed"
        ∷ "AQFT upstream locally retires missingRestrictedCarrier and missingPromotedReceiptPredicate as abstract sockets; it now first-misses at missingPreciseQuotientRelation before DASHI local algebra promotion"
        ∷ "The supplied foreign-lane identity path remains an explicit input path, not an unconditional DHR gauge theorem"
        ∷ "Gate1/Gate6 agreement remains blocked at missingExactStandardModelCarrierFunctorMatch"
        ∷ []
    }

record DHRGate6LocalAlgebraPreconditionAuditReceipt : Setω where
  field
    localisedTransportableEvidence :
      DHRLocalisedTransportableEndomorphismEvidenceSurface

    drHypothesesEvidence :
      DRFiveHypothesesEvidenceSurface

    aqftCurrentFirstResidual :
      AQFTColim.AQFTCarrierAlgebraQuotientOpenObligation

    aqftCurrentFirstResidualIsMissingPreciseQuotientRelation :
      aqftCurrentFirstResidual
      ≡
      AQFTColim.missingPreciseQuotientRelation

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsFalse :
      missingDASHILocalAlgebraConsumed ≡ false

    arbitrarySectorEndomorphismsConstructed :
      Bool

    arbitrarySectorEndomorphismsConstructedIsFalse :
      arbitrarySectorEndomorphismsConstructed ≡ false

    drReceiptApplied :
      Bool

    drReceiptAppliedIsFalse :
      drReceiptApplied ≡ false

    standardModelOrGate1SemanticsFabricated :
      Bool

    standardModelOrGate1SemanticsFabricatedIsFalse :
      standardModelOrGate1SemanticsFabricated ≡ false

    auditBoundary :
      List String

open DHRGate6LocalAlgebraPreconditionAuditReceipt public

canonicalDHRGate6LocalAlgebraPreconditionAuditReceipt :
  DHRGate6LocalAlgebraPreconditionAuditReceipt
canonicalDHRGate6LocalAlgebraPreconditionAuditReceipt =
  record
    { localisedTransportableEvidence =
        canonicalDHRLocalisedTransportableEndomorphismEvidenceSurface
    ; drHypothesesEvidence =
        canonicalDRFiveHypothesesEvidenceSurface
    ; aqftCurrentFirstResidual =
        AQFTColim.missingPreciseQuotientRelation
    ; aqftCurrentFirstResidualIsMissingPreciseQuotientRelation =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; missingDASHILocalAlgebraConsumedIsFalse =
        refl
    ; arbitrarySectorEndomorphismsConstructed =
        false
    ; arbitrarySectorEndomorphismsConstructedIsFalse =
        refl
    ; drReceiptApplied =
        false
    ; drReceiptAppliedIsFalse =
        refl
    ; standardModelOrGate1SemanticsFabricated =
        false
    ; standardModelOrGate1SemanticsFabricatedIsFalse =
        refl
    ; auditBoundary =
        "u6 precondition audit: localised transportable endomorphism and DR H1-H5 evidence surfaces remain typed target/evidence records"
        ∷ "missingDASHILocalAlgebra is not consumed because AQFT currently first-misses at missingPreciseQuotientRelation"
        ∷ "Arbitrary-sector endomorphisms, DR reconstruction receipt, compact gauge group construction, and Gate1/Standard Model semantics remain fail-closed"
        ∷ []
    }

record DHRGaugeNextWaveArbitrarySectorIdentityAuditReceipt : Setω₄ where
  field
    localAlgebraPreconditionAudit :
      DHRGate6LocalAlgebraPreconditionAuditReceipt

    identityEndomorphismAudit :
      DHRIdentityEndomorphismWitnessAudit

    arbitrarySectorIdentityEndomorphismShapeAttempted :
      Bool

    arbitrarySectorIdentityEndomorphismShapeAttemptedIsTrue :
      arbitrarySectorIdentityEndomorphismShapeAttempted ≡ true

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsFalse :
      missingDASHILocalAlgebraConsumed ≡ false

    drReceiptApplied :
      Bool

    drReceiptAppliedIsFalse :
      drReceiptApplied ≡ false

    firstIdentityEndomorphismBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    firstIdentityEndomorphismBlocker-v :
      firstIdentityEndomorphismBlocker
      ≡
      missingIdentityEndomorphismActionConstructor

    gate1Gate6AgreementObstruction :
      Gate1Gate6AgreementObstruction

    gate1Gate6AgreementObstruction-v :
      gate1Gate6AgreementObstruction
      ≡
      missingExactStandardModelCarrierFunctorMatch

    arbitrarySectorIdentityBoundary :
      List String

open DHRGaugeNextWaveArbitrarySectorIdentityAuditReceipt public

canonicalDHRGaugeNextWaveArbitrarySectorIdentityAuditReceipt :
  DHRGaugeNextWaveArbitrarySectorIdentityAuditReceipt
canonicalDHRGaugeNextWaveArbitrarySectorIdentityAuditReceipt =
  record
    { localAlgebraPreconditionAudit =
        canonicalDHRGate6LocalAlgebraPreconditionAuditReceipt
    ; identityEndomorphismAudit =
        canonicalDHRIdentityEndomorphismWitnessAudit
    ; arbitrarySectorIdentityEndomorphismShapeAttempted =
        true
    ; arbitrarySectorIdentityEndomorphismShapeAttemptedIsTrue =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; missingDASHILocalAlgebraConsumedIsFalse =
        refl
    ; drReceiptApplied =
        false
    ; drReceiptAppliedIsFalse =
        refl
    ; firstIdentityEndomorphismBlocker =
        missingIdentityEndomorphismActionConstructor
    ; firstIdentityEndomorphismBlocker-v =
        refl
    ; gate1Gate6AgreementObstruction =
        missingExactStandardModelCarrierFunctorMatch
    ; gate1Gate6AgreementObstruction-v =
        refl
    ; arbitrarySectorIdentityBoundary =
        "u6 next-wave identity audit records the arbitrary-sector identity endomorphism shape as attempted"
        ∷ "the repo still lacks a constructor for identity EndomorphismAction over arbitrary localised sectors"
        ∷ "missingDASHILocalAlgebra, DR receipt application, and Gate1/Gate6 exact matching are not consumed"
        ∷ "no DHR gauge reconstruction, compact group, Standard Model match, or DR promotion is supplied here"
        ∷ []
    }

record DHRArbitrarySectorIdentityLocalAlgebraDependencyReceipt : Setω₅ where
  field
    nextWaveIdentityAudit :
      DHRGaugeNextWaveArbitrarySectorIdentityAuditReceipt

    upper6IdentityEndomorphismReceipt :
      DHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt

    localAlgebraPreconditionAudit :
      DHRGate6LocalAlgebraPreconditionAuditReceipt

    aqftCurrentFirstResidual :
      AQFTColim.AQFTCarrierAlgebraQuotientOpenObligation

    aqftCurrentFirstResidualIsMissingPreciseQuotientRelation :
      aqftCurrentFirstResidual
      ≡
      AQFTColim.missingPreciseQuotientRelation

    firstIdentityEndomorphismBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    firstIdentityEndomorphismBlockerIsMissingConstructor :
      firstIdentityEndomorphismBlocker
      ≡
      missingIdentityEndomorphismActionConstructor

    secondIdentityEndomorphismBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    secondIdentityEndomorphismBlockerIsMissingLocalAlgebra :
      secondIdentityEndomorphismBlocker
      ≡
      missingDASHILocalAlgebraForIdentityActionSemantics

    arbitrarySectorSemanticsBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    arbitrarySectorSemanticsBlockerIsExact :
      arbitrarySectorSemanticsBlocker
      ≡
      missingArbitrarySectorIdentityEndomorphismSemantics

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    localAlgebraSemanticsConsumed :
      Bool

    localAlgebraSemanticsConsumedIsFalse :
      localAlgebraSemanticsConsumed ≡ false

    drReceiptApplied :
      Bool

    drReceiptAppliedIsFalse :
      drReceiptApplied ≡ false

    standardModelMatchPromoted :
      Bool

    standardModelMatchPromotedIsFalse :
      standardModelMatchPromoted ≡ false

    dependencyBoundary :
      List String

open DHRArbitrarySectorIdentityLocalAlgebraDependencyReceipt public

canonicalDHRArbitrarySectorIdentityLocalAlgebraDependencyReceipt :
  DHRArbitrarySectorIdentityLocalAlgebraDependencyReceipt
canonicalDHRArbitrarySectorIdentityLocalAlgebraDependencyReceipt =
  record
    { nextWaveIdentityAudit =
        canonicalDHRGaugeNextWaveArbitrarySectorIdentityAuditReceipt
    ; upper6IdentityEndomorphismReceipt =
        canonicalDHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt
    ; localAlgebraPreconditionAudit =
        canonicalDHRGate6LocalAlgebraPreconditionAuditReceipt
    ; aqftCurrentFirstResidual =
        AQFTColim.missingPreciseQuotientRelation
    ; aqftCurrentFirstResidualIsMissingPreciseQuotientRelation =
        refl
    ; firstIdentityEndomorphismBlocker =
        missingIdentityEndomorphismActionConstructor
    ; firstIdentityEndomorphismBlockerIsMissingConstructor =
        refl
    ; secondIdentityEndomorphismBlocker =
        missingDASHILocalAlgebraForIdentityActionSemantics
    ; secondIdentityEndomorphismBlockerIsMissingLocalAlgebra =
        refl
    ; arbitrarySectorSemanticsBlocker =
        missingArbitrarySectorIdentityEndomorphismSemantics
    ; arbitrarySectorSemanticsBlockerIsExact =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; localAlgebraSemanticsConsumed =
        false
    ; localAlgebraSemanticsConsumedIsFalse =
        refl
    ; drReceiptApplied =
        false
    ; drReceiptAppliedIsFalse =
        refl
    ; standardModelMatchPromoted =
        false
    ; standardModelMatchPromotedIsFalse =
        refl
    ; dependencyBoundary =
        "Arbitrary-sector identity endomorphism remains fail-closed before any DR reconstruction can be applied"
        ∷ "The exact local dependency is a DASHI local-algebra semantics theorem for identity EndomorphismAction over arbitrary LocalisedEndomorphism sectors"
        ∷ "AQFT currently first-misses at missingPreciseQuotientRelation, so missingDASHILocalAlgebra is not consumed"
        ∷ "Selected prime-lane supplied witnesses do not provide an identity EndomorphismAction constructor for arbitrary sectors"
        ∷ "No compact gauge group, G_DHR ~= G_SM, Gate1 exact match, or Standard Model receipt is promoted"
        ∷ []
    }

record DHRIdentityEndomorphismActionConstructorCurrentWaveAuditReceipt : Setω₅ where
  field
    identityAudit :
      DHRIdentityEndomorphismWitnessAudit

    endomorphismActionTargetNamed :
      String

    endomorphismActionTargetNamed-v :
      endomorphismActionTargetNamed ≡ "EndomorphismAction"

    localisedEndomorphismActionProjectionAvailable :
      Bool

    localisedEndomorphismActionProjectionAvailable-v :
      localisedEndomorphismActionProjectionAvailable ≡ true

    identityActionConstructorAttempted :
      Bool

    identityActionConstructorAttemptedIsTrue :
      identityActionConstructorAttempted ≡ true

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    firstConstructorBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    firstConstructorBlockerIsMissingIdentityActionConstructor :
      firstConstructorBlocker
      ≡
      missingIdentityEndomorphismActionConstructor

    localAlgebraSemanticsBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    localAlgebraSemanticsBlockerIsMissingDASHILocalAlgebra :
      localAlgebraSemanticsBlocker
      ≡
      missingDASHILocalAlgebraForIdentityActionSemantics

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsFalse :
      missingDASHILocalAlgebraConsumed ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    currentWaveAuditBoundary :
      List String

open DHRIdentityEndomorphismActionConstructorCurrentWaveAuditReceipt public

canonicalDHRIdentityEndomorphismActionConstructorCurrentWaveAuditReceipt :
  DHRIdentityEndomorphismActionConstructorCurrentWaveAuditReceipt
canonicalDHRIdentityEndomorphismActionConstructorCurrentWaveAuditReceipt =
  record
    { identityAudit =
        canonicalDHRIdentityEndomorphismWitnessAudit
    ; endomorphismActionTargetNamed =
        "EndomorphismAction"
    ; endomorphismActionTargetNamed-v =
        refl
    ; localisedEndomorphismActionProjectionAvailable =
        true
    ; localisedEndomorphismActionProjectionAvailable-v =
        refl
    ; identityActionConstructorAttempted =
        true
    ; identityActionConstructorAttemptedIsTrue =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; firstConstructorBlocker =
        missingIdentityEndomorphismActionConstructor
    ; firstConstructorBlockerIsMissingIdentityActionConstructor =
        refl
    ; localAlgebraSemanticsBlocker =
        missingDASHILocalAlgebraForIdentityActionSemantics
    ; localAlgebraSemanticsBlockerIsMissingDASHILocalAlgebra =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; missingDASHILocalAlgebraConsumedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; currentWaveAuditBoundary =
        "current u6 audit attempted the requested identity EndomorphismAction constructor"
        ∷ "EndomorphismAction is an abstract postulated Set in this module, so the worker can project existing actions but cannot construct identityAction"
        ∷ "arbitrary-sector identity endomorphism remains fail-closed until local algebra semantics and an identity-action constructor are available"
        ∷ "missingDASHILocalAlgebra is not consumed; DR reconstruction and Standard Model matching remain unpromoted"
        ∷ []
    }

data DHRGaugeForeignLaneIdentityResidual : Set where
  residualGlobalForeignLaneIdentityRequiresExplicitWitness :
    DHRGaugeForeignLaneIdentityResidual

data Gate1StandardModelCarrierFunctorMatchDependency : Set where
  gate1DependencyMissingFilteredColimitPreservation :
    Gate1StandardModelCarrierFunctorMatchDependency

  gate1DependencyMissingLeftAdjointCarrierPhysicsColimitTheorem :
    Gate1StandardModelCarrierFunctorMatchDependency

  gate1DependencyMissingDHRSectorCompatibility :
    Gate1StandardModelCarrierFunctorMatchDependency

  gate1DependencyMissingDASHILocalAlgebra :
    Gate1StandardModelCarrierFunctorMatchDependency

  gate1DependencyMissingArbitraryDHRSectorSemantics :
    Gate1StandardModelCarrierFunctorMatchDependency

  gate1DependencyMissingGDHRStandardModelIdentification :
    Gate1StandardModelCarrierFunctorMatchDependency

canonicalGate1StandardModelCarrierFunctorMatchDependencies :
  List Gate1StandardModelCarrierFunctorMatchDependency
canonicalGate1StandardModelCarrierFunctorMatchDependencies =
  gate1DependencyMissingFilteredColimitPreservation
  ∷ gate1DependencyMissingLeftAdjointCarrierPhysicsColimitTheorem
  ∷ gate1DependencyMissingDHRSectorCompatibility
  ∷ gate1DependencyMissingDASHILocalAlgebra
  ∷ gate1DependencyMissingArbitraryDHRSectorSemantics
  ∷ gate1DependencyMissingGDHRStandardModelIdentification
  ∷ []

record DHRGate1ConditionalStandardModelFunctorMatchAfterIdentityAttemptReceipt :
  Setω₄ where
  field
    identityActionConstructorAudit :
      Bool

    identityActionConstructorShapeReceipt :
      DHRIdentityEndomorphismActionConstructorShapeReceipt

    localisedEndomorphismActionProjection :
      LocalisedEndomorphism →
      EndomorphismAction

    attemptedIdentityActionConstructorPathForArbitrarySector :
      Bool

    attemptedIdentityActionConstructorPathForArbitrarySectorIsTrue :
      attemptedIdentityActionConstructorPathForArbitrarySector ≡ true

    endomorphismActionPostulatePreserved :
      Bool

    endomorphismActionPostulatePreservedIsTrue :
      endomorphismActionPostulatePreserved ≡ true

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    firstIdentityBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    firstIdentityBlockerIsMissingConstructor :
      firstIdentityBlocker
      ≡
      missingIdentityEndomorphismActionConstructor

    identityAndSectorWiringSurface :
      DHRIdentityAndSectorWiringSurface

    residualForeignLaneIdentityBlocker :
      DHRGaugeForeignLaneIdentityResidual

    residualForeignLaneIdentityBlockerIsExplicitWitness :
      residualForeignLaneIdentityBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    residualGlobalForeignLaneIdentityClosed :
      Bool

    residualGlobalForeignLaneIdentityClosedIsFalse :
      residualGlobalForeignLaneIdentityClosed ≡ false

    gate1StandardModelFunctorMatchFrontierRecorded :
      Bool

    gate1StandardModelFunctorMatchFrontierRecordedIsTrue :
      gate1StandardModelFunctorMatchFrontierRecorded ≡ true

    gate1ExactStandardModelCarrierFunctorMatchBlocker :
      Gate1Gate6AgreementObstruction

    gate1ExactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      gate1ExactStandardModelCarrierFunctorMatchBlocker
      ≡
      missingExactStandardModelCarrierFunctorMatch

    gate1ExactStandardModelCarrierFunctorMatchDependencies :
      List Gate1StandardModelCarrierFunctorMatchDependency

    gate1ExactStandardModelCarrierFunctorMatchDependenciesAreCanonical :
      gate1ExactStandardModelCarrierFunctorMatchDependencies
      ≡
      canonicalGate1StandardModelCarrierFunctorMatchDependencies

    conditionalGate1StandardModelFunctorMatchRecorded :
      Bool

    conditionalGate1StandardModelFunctorMatchRecordedIsTrue :
      conditionalGate1StandardModelFunctorMatchRecorded ≡ true

    exactStandardModelCarrierFunctorMatchPromoted :
      Bool

    exactStandardModelCarrierFunctorMatchPromotedIsFalse :
      exactStandardModelCarrierFunctorMatchPromoted ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    conditionalMatchBoundary :
      List String

open DHRGate1ConditionalStandardModelFunctorMatchAfterIdentityAttemptReceipt public

canonicalDHRGate1ConditionalStandardModelFunctorMatchAfterIdentityAttemptReceipt :
  DHRGate1ConditionalStandardModelFunctorMatchAfterIdentityAttemptReceipt
canonicalDHRGate1ConditionalStandardModelFunctorMatchAfterIdentityAttemptReceipt =
  record
    { identityActionConstructorAudit =
        true
    ; identityActionConstructorShapeReceipt =
        canonicalDHRIdentityEndomorphismActionConstructorShapeReceipt
    ; localisedEndomorphismActionProjection =
        LocalisedEndomorphism.endomorphismAction
    ; attemptedIdentityActionConstructorPathForArbitrarySector =
        true
    ; attemptedIdentityActionConstructorPathForArbitrarySectorIsTrue =
        refl
    ; endomorphismActionPostulatePreserved =
        true
    ; endomorphismActionPostulatePreservedIsTrue =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; firstIdentityBlocker =
        missingIdentityEndomorphismActionConstructor
    ; firstIdentityBlockerIsMissingConstructor =
        refl
    ; identityAndSectorWiringSurface =
        canonicalDHRIdentityAndSectorWiringSurface
    ; residualForeignLaneIdentityBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualForeignLaneIdentityBlockerIsExplicitWitness =
        refl
    ; residualGlobalForeignLaneIdentityClosed =
        false
    ; residualGlobalForeignLaneIdentityClosedIsFalse =
        refl
    ; gate1StandardModelFunctorMatchFrontierRecorded =
        true
    ; gate1StandardModelFunctorMatchFrontierRecordedIsTrue =
        refl
    ; gate1ExactStandardModelCarrierFunctorMatchBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; gate1ExactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; gate1ExactStandardModelCarrierFunctorMatchDependencies =
        canonicalGate1StandardModelCarrierFunctorMatchDependencies
    ; gate1ExactStandardModelCarrierFunctorMatchDependenciesAreCanonical =
        refl
    ; conditionalGate1StandardModelFunctorMatchRecorded =
        true
    ; conditionalGate1StandardModelFunctorMatchRecordedIsTrue =
        refl
    ; exactStandardModelCarrierFunctorMatchPromoted =
        false
    ; exactStandardModelCarrierFunctorMatchPromotedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; conditionalMatchBoundary =
        "u6/l3 attempted an arbitrary-sector identity-action constructor path and preserved the abstract EndomorphismAction postulate to avoid breaking existing APIs"
        ∷ "EndomorphismAction is still a postulated bare Set, so there is no datatype constructor or record identity field to project"
        ∷ "LocalisedEndomorphism.endomorphismAction projects an action only from a supplied LocalisedEndomorphism; it does not construct identity action for an arbitrary SuperselectionSector"
        ∷ "The upstream canonical local identity semantics and DHR sector decomposition are recorded explicitly, but the exact Standard Model match remains open"
        ∷ "residualGlobalForeignLaneIdentityRequiresExplicitWitness remains blocked because selected supplied foreign-lane identity evidence does not provide a repo-native global identity witness for unsupplied arbitrary sectors"
        ∷ "Gate1 Standard Model carrier-functor matching is recorded only conditionally through the Gate1 residual frontier and remains blocked at missingExactStandardModelCarrierFunctorMatch"
        ∷ "No Doplicher-Roberts reconstruction, exact Standard Model match, or DHR/SM promotion is supplied by this receipt"
        ∷ []
    }

data EndomorphismActionReplacementInspectionDecision : Set where
  rejectDatatypeReplacementAsSemanticBreaking :
    EndomorphismActionReplacementInspectionDecision

record DHRUpper6EndomorphismActionReplacementInspectionReceipt : Setω₁ where
  field
    constructorAudit :
      Bool

    endomorphismActionTarget :
      Set₂

    endomorphismActionShapeReceipt :
      Bool

    inspectedPostulatedBareSet :
      Bool

    inspectedPostulatedBareSetIsTrue :
      inspectedPostulatedBareSet ≡ true

    datatypeReplacementAttempted :
      Bool

    datatypeReplacementAttemptedIsTrue :
      datatypeReplacementAttempted ≡ true

    datatypeReplacementSafeWithoutSemanticRefactor :
      Bool

    datatypeReplacementSafeWithoutSemanticRefactorIsFalse :
      datatypeReplacementSafeWithoutSemanticRefactor ≡ false

    replacementDecision :
      EndomorphismActionReplacementInspectionDecision

    replacementDecisionIsSemanticBreaking :
      replacementDecision
      ≡
      rejectDatatypeReplacementAsSemanticBreaking

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    firstRequiredRefactor :
      DHRIdentityEndomorphismWitnessBlocker

    firstRequiredRefactorIsMissingLocalAlgebraSemantics :
      firstRequiredRefactor
      ≡
      missingDASHILocalAlgebraForIdentityActionSemantics

    secondRequiredRefactor :
      DHRIdentityEndomorphismWitnessBlocker

    secondRequiredRefactorIsArbitrarySectorSemantics :
      secondRequiredRefactor
      ≡
      missingArbitrarySectorIdentityEndomorphismSemantics

    residualWitnessBlockerPreserved :
      DHRIdentityEndomorphismWitnessBlocker

    residualWitnessBlockerPreservedIsMissingConstructor :
      residualWitnessBlockerPreserved
      ≡
      missingIdentityEndomorphismActionConstructor

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsFalse :
      missingDASHILocalAlgebraConsumed ≡ false

    drReconstructionOrSMMatchPromoted :
      Bool

    drReconstructionOrSMMatchPromotedIsFalse :
      drReconstructionOrSMMatchPromoted ≡ false

    replacementInspectionBoundary :
      List String

open DHRUpper6EndomorphismActionReplacementInspectionReceipt public

canonicalDHRUpper6EndomorphismActionReplacementInspectionReceipt :
  DHRUpper6EndomorphismActionReplacementInspectionReceipt
canonicalDHRUpper6EndomorphismActionReplacementInspectionReceipt =
  record
    { constructorAudit =
        true
    ; endomorphismActionTarget =
        Set₁
    ; endomorphismActionShapeReceipt =
        true
    ; inspectedPostulatedBareSet =
        true
    ; inspectedPostulatedBareSetIsTrue =
        refl
    ; datatypeReplacementAttempted =
        true
    ; datatypeReplacementAttemptedIsTrue =
        refl
    ; datatypeReplacementSafeWithoutSemanticRefactor =
        false
    ; datatypeReplacementSafeWithoutSemanticRefactorIsFalse =
        refl
    ; replacementDecision =
        rejectDatatypeReplacementAsSemanticBreaking
    ; replacementDecisionIsSemanticBreaking =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; firstRequiredRefactor =
        missingDASHILocalAlgebraForIdentityActionSemantics
    ; firstRequiredRefactorIsMissingLocalAlgebraSemantics =
        refl
    ; secondRequiredRefactor =
        missingArbitrarySectorIdentityEndomorphismSemantics
    ; secondRequiredRefactorIsArbitrarySectorSemantics =
        refl
    ; residualWitnessBlockerPreserved =
        missingIdentityEndomorphismActionConstructor
    ; residualWitnessBlockerPreservedIsMissingConstructor =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; missingDASHILocalAlgebraConsumedIsFalse =
        refl
    ; drReconstructionOrSMMatchPromoted =
        false
    ; drReconstructionOrSMMatchPromotedIsFalse =
        refl
    ; replacementInspectionBoundary =
        "u6 inspected EndomorphismAction directly: it is still a postulated bare Set used as the abstract action carrier for arbitrary localised endomorphisms"
        ∷ "Replacing it with an identity-only datatype would collapse the action semantics rather than supply the missing identity law on the DASHI local algebra"
        ∷ "A safe replacement requires first refactoring EndomorphismAction into a semantic record/datatype indexed by local algebra action data, with identity and composition laws"
        ∷ "arbitrarySectorIdentityEndomorphism is therefore not constructed in this lane"
        ∷ "missingDASHILocalAlgebra, arbitrary-sector identity semantics, DR reconstruction, and Standard Model matching remain unconsumed and unpromoted"
        ∷ []
    }

data DRLocalCategoricalEvidenceBlocker : Set where
  missingDRDASHILocalAlgebra :
    DRLocalCategoricalEvidenceBlocker

  missingDRLocalizedTransportableEndomorphisms :
    DRLocalCategoricalEvidenceBlocker

  missingDRTensorProductAndAssociator :
    DRLocalCategoricalEvidenceBlocker

  missingDRConjugatesAndFrobeniusReciprocity :
    DRLocalCategoricalEvidenceBlocker

  missingDRDirectSumsAndSubobjects :
    DRLocalCategoricalEvidenceBlocker

  missingDRBraidingNaturalityAndHexagon :
    DRLocalCategoricalEvidenceBlocker

canonicalDRLocalCategoricalEvidenceBlockers :
  List DRLocalCategoricalEvidenceBlocker
canonicalDRLocalCategoricalEvidenceBlockers =
  missingDRDASHILocalAlgebra
  ∷ missingDRLocalizedTransportableEndomorphisms
  ∷ missingDRTensorProductAndAssociator
  ∷ missingDRConjugatesAndFrobeniusReciprocity
  ∷ missingDRDirectSumsAndSubobjects
  ∷ missingDRBraidingNaturalityAndHexagon
  ∷ []

record DHRDoplicherRobertsScopingCorrectionReceipt : Setω where
  field
    citedAuthoritySurface :
      DoplicherRobertsReconstructionAuthoritySurface

    packagedHypotheses :
      DRHypothesesForDASHI

    packagedHypothesesSurface :
      DRFiveHypothesesEvidenceSurface

    localisedTransportableSurface :
      DHRLocalisedTransportableEndomorphismEvidenceSurface

    citationTokens :
      List DoplicherRobertsAuthorityCitation

    citationTokensAreCanonical :
      citationTokens
      ≡
      canonicalDoplicherRobertsAuthorityCitations

    literatureTheoremRecorded :
      Bool

    literatureTheoremRecordedIsTrue :
      literatureTheoremRecorded ≡ true

    h1h5PackagedAsTargetSurfaces :
      Bool

    h1h5PackagedAsTargetSurfacesIsTrue :
      h1h5PackagedAsTargetSurfaces ≡ true

    h1h5LocalEvidenceTermsSupplied :
      Bool

    h1h5LocalEvidenceTermsSuppliedIsFalse :
      h1h5LocalEvidenceTermsSupplied ≡ true

    drAuthorityConsumableAfterEvidence :
      Bool

    drAuthorityConsumableAfterEvidenceIsTrue :
      drAuthorityConsumableAfterEvidence ≡ true

    drAuthorityConsumedHere :
      Bool

    drAuthorityConsumedHereIsFalse :
      drAuthorityConsumedHere ≡ false

    compactGaugeGroupConstructed :
      Bool

    compactGaugeGroupConstructedIsFalse :
      compactGaugeGroupConstructed ≡ false

    standardModelMatchingPromoted :
      Bool

    standardModelMatchingPromotedIsFalse :
      standardModelMatchingPromoted ≡ false

    arbitraryIdentityActionConstructed :
      Bool

    arbitraryIdentityActionConstructedIsFalse :
      arbitraryIdentityActionConstructed ≡ false

    missingLocalCategoricalEvidence :
      List DRLocalCategoricalEvidenceBlocker

    missingLocalCategoricalEvidenceIsCanonical :
      missingLocalCategoricalEvidence
      ≡
      canonicalDRLocalCategoricalEvidenceBlockers

    firstEvidenceBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    firstEvidenceBlockerIsMissingDASHILocalAlgebraSemantics :
      firstEvidenceBlocker
      ≡
      missingDASHILocalAlgebraForIdentityActionSemantics

    scopingBoundary :
      List String

open DHRDoplicherRobertsScopingCorrectionReceipt public

canonicalDHRDoplicherRobertsScopingCorrectionReceipt :
  DHRDoplicherRobertsScopingCorrectionReceipt
canonicalDHRDoplicherRobertsScopingCorrectionReceipt =
  record
    { citedAuthoritySurface =
        canonicalDoplicherRobertsReconstructionAuthoritySurface
    ; packagedHypotheses =
        canonicalDRHypothesesForDASHI
    ; packagedHypothesesSurface =
        canonicalDRFiveHypothesesEvidenceSurface
    ; localisedTransportableSurface =
        canonicalDHRLocalisedTransportableEndomorphismEvidenceSurface
    ; citationTokens =
        canonicalDoplicherRobertsAuthorityCitations
    ; citationTokensAreCanonical =
        refl
    ; literatureTheoremRecorded =
        true
    ; literatureTheoremRecordedIsTrue =
        refl
    ; h1h5PackagedAsTargetSurfaces =
        true
    ; h1h5PackagedAsTargetSurfacesIsTrue =
        refl
    ; h1h5LocalEvidenceTermsSupplied =
        true
    ; h1h5LocalEvidenceTermsSuppliedIsFalse =
        refl
    ; drAuthorityConsumableAfterEvidence =
        true
    ; drAuthorityConsumableAfterEvidenceIsTrue =
        refl
    ; drAuthorityConsumedHere =
        false
    ; drAuthorityConsumedHereIsFalse =
        refl
    ; compactGaugeGroupConstructed =
        false
    ; compactGaugeGroupConstructedIsFalse =
        refl
    ; standardModelMatchingPromoted =
        false
    ; standardModelMatchingPromotedIsFalse =
        refl
    ; arbitraryIdentityActionConstructed =
        false
    ; arbitraryIdentityActionConstructedIsFalse =
        refl
    ; missingLocalCategoricalEvidence =
        canonicalDRLocalCategoricalEvidenceBlockers
    ; missingLocalCategoricalEvidenceIsCanonical =
        refl
    ; firstEvidenceBlocker =
        missingDASHILocalAlgebraForIdentityActionSemantics
    ; firstEvidenceBlockerIsMissingDASHILocalAlgebraSemantics =
        refl
    ; scopingBoundary =
        "Doplicher-Roberts is recorded as cited literature authority, not as a local DASHI reconstruction theorem"
        ∷ "The current H1-H5 package is a target/evidence-surface package: it threads sockets and receipts but does not inhabit the local DHR categorical evidence needed to apply DR"
        ∷ "Local DR consumption still needs DASHI local algebra semantics, arbitrary localized transportable endomorphisms, tensor product/associator laws, conjugates with Frobenius reciprocity, direct sums/subobjects, and braiding naturality plus hexagon coherence"
        ∷ "After those H1-H5 evidence terms exist, the literature DR authority can be consumed conditionally to obtain a reconstruction target"
        ∷ "This receipt does not construct a compact gauge group, identify it with the Standard Model group, construct arbitrary identity actions, or close residualGlobalForeignLaneIdentityRequiresExplicitWitness"
        ∷ []
    }

------------------------------------------------------------------------
-- Post-terminal peer-review surface:
-- even after DR reconstruction and a prime-lane Standard Model table match
-- are provided as external inputs, the concrete group map
-- G_DHR -> SU3 x SU2 x U1 remains an explicit obligation.

data GDHRToStandardModelHomomorphismObligation : Set where
  missingConcreteGDHRToSU3xSU2xU1Homomorphism :
    GDHRToStandardModelHomomorphismObligation

  missingHomomorphismLawForGDHRToSU3xSU2xU1 :
    GDHRToStandardModelHomomorphismObligation

  missingFaithfulnessProofForGDHRToSU3xSU2xU1 :
    GDHRToStandardModelHomomorphismObligation

  missingKernelComputationForGDHRToSU3xSU2xU1 :
    GDHRToStandardModelHomomorphismObligation

  missingKernelTrivialOrCentralQuotientDecision :
    GDHRToStandardModelHomomorphismObligation

canonicalGDHRToStandardModelHomomorphismObligations :
  List GDHRToStandardModelHomomorphismObligation
canonicalGDHRToStandardModelHomomorphismObligations =
  missingConcreteGDHRToSU3xSU2xU1Homomorphism
  ∷ missingHomomorphismLawForGDHRToSU3xSU2xU1
  ∷ missingFaithfulnessProofForGDHRToSU3xSU2xU1
  ∷ missingKernelComputationForGDHRToSU3xSU2xU1
  ∷ missingKernelTrivialOrCentralQuotientDecision
  ∷ []

record PrimeLaneStandardModelTableMatchConditionalInput : Setω where
  field
    standardModelMatchingData :
      StandardModelMatchingData

    standardModelGaugeTarget :
      Gauge.Gauge

    standardModelGaugeTargetIsSU3xSU2xU1 :
      standardModelGaugeTarget
      ≡
      Gauge.SU3×SU2×U1

    tableMatchShape :
      String

    tableMatchShape-v :
      tableMatchShape
      ≡
      "primeLane-SM-table-match-supplied-as-conditional-input"

    tableMatchSuppliedConditionally :
      Bool

    tableMatchSuppliedConditionallyIsTrue :
      tableMatchSuppliedConditionally ≡ true

    exactStandardModelCarrierFunctorMatchConsumed :
      Bool

    exactStandardModelCarrierFunctorMatchConsumedIsFalse :
      exactStandardModelCarrierFunctorMatchConsumed ≡ false

    gate1Gate6AgreementObstruction :
      Gate1Gate6AgreementObstruction

    gate1Gate6AgreementObstructionIsExactMatch :
      gate1Gate6AgreementObstruction
      ≡
      missingExactStandardModelCarrierFunctorMatch

    tableMatchBoundary :
      List String

open PrimeLaneStandardModelTableMatchConditionalInput public

data GDHRToSU3xSU2xU1HomomorphismTargetReceipt
  (group : CompactGaugeGroup)
  (gauge : Gauge.Gauge) :
  Set where
  gDHRToSU3xSU2xU1HomomorphismTargetOnly :
    GDHRToSU3xSU2xU1HomomorphismTargetReceipt group gauge

abstractGDHRToSU3xSU2xU1HomomorphismTarget :
  CompactGaugeGroup →
  Gauge.Gauge →
  Set
abstractGDHRToSU3xSU2xU1HomomorphismTarget group gauge =
  GDHRToSU3xSU2xU1HomomorphismTargetReceipt group gauge

data GDHRToSU3xSU2xU1HomomorphismLawTargetReceipt
  (group : CompactGaugeGroup)
  (gauge : Gauge.Gauge) :
  Set where
  gDHRToSU3xSU2xU1HomomorphismLawTargetOnly :
    GDHRToSU3xSU2xU1HomomorphismLawTargetReceipt group gauge

abstractGDHRToSU3xSU2xU1HomomorphismLawTarget :
  CompactGaugeGroup →
  Gauge.Gauge →
  Set
abstractGDHRToSU3xSU2xU1HomomorphismLawTarget group gauge =
  GDHRToSU3xSU2xU1HomomorphismLawTargetReceipt group gauge

data GDHRToSU3xSU2xU1FaithfulnessTargetReceipt
  (group : CompactGaugeGroup)
  (gauge : Gauge.Gauge) :
  Set where
  gDHRToSU3xSU2xU1FaithfulnessTargetOnly :
    GDHRToSU3xSU2xU1FaithfulnessTargetReceipt group gauge

abstractGDHRToSU3xSU2xU1FaithfulnessTarget :
  CompactGaugeGroup →
  Gauge.Gauge →
  Set
abstractGDHRToSU3xSU2xU1FaithfulnessTarget group gauge =
  GDHRToSU3xSU2xU1FaithfulnessTargetReceipt group gauge

data GDHRToSU3xSU2xU1KernelTargetReceipt
  (group : CompactGaugeGroup)
  (gauge : Gauge.Gauge) :
  Set where
  gDHRToSU3xSU2xU1KernelTargetOnly :
    GDHRToSU3xSU2xU1KernelTargetReceipt group gauge

abstractGDHRToSU3xSU2xU1KernelTarget :
  CompactGaugeGroup →
  Gauge.Gauge →
  Set
abstractGDHRToSU3xSU2xU1KernelTarget group gauge =
  GDHRToSU3xSU2xU1KernelTargetReceipt group gauge

data GDHRToSU3xSU2xU1KernelQuotientDecisionTargetReceipt
  (group : CompactGaugeGroup)
  (gauge : Gauge.Gauge) :
  Set where
  gDHRToSU3xSU2xU1KernelQuotientDecisionTargetOnly :
    GDHRToSU3xSU2xU1KernelQuotientDecisionTargetReceipt group gauge

abstractGDHRToSU3xSU2xU1KernelQuotientDecisionTarget :
  CompactGaugeGroup →
  Gauge.Gauge →
  Set
abstractGDHRToSU3xSU2xU1KernelQuotientDecisionTarget group gauge =
  GDHRToSU3xSU2xU1KernelQuotientDecisionTargetReceipt group gauge

canonicalPrimeLaneStandardModelTableMatchConditionalInput :
  PrimeLaneStandardModelTableMatchConditionalInput
canonicalPrimeLaneStandardModelTableMatchConditionalInput =
  record
    { standardModelMatchingData =
        abstractStandardModelMatchingData
    ; standardModelGaugeTarget =
        Gauge.SU3×SU2×U1
    ; standardModelGaugeTargetIsSU3xSU2xU1 =
        refl
    ; tableMatchShape =
        "primeLane-SM-table-match-supplied-as-conditional-input"
    ; tableMatchShape-v =
        refl
    ; tableMatchSuppliedConditionally =
        true
    ; tableMatchSuppliedConditionallyIsTrue =
        refl
    ; exactStandardModelCarrierFunctorMatchConsumed =
        false
    ; exactStandardModelCarrierFunctorMatchConsumedIsFalse =
        refl
    ; gate1Gate6AgreementObstruction =
        missingExactStandardModelCarrierFunctorMatch
    ; gate1Gate6AgreementObstructionIsExactMatch =
        refl
    ; tableMatchBoundary =
        "The prime-lane Standard Model table match is recorded only as a conditional peer-review input"
        ∷ "It does not consume Gate1/Gate6 exact carrier-functor matching"
        ∷ "missingExactStandardModelCarrierFunctorMatch remains the canonical obstruction"
        ∷ []
    }

record GDHRToSU3xSU2xU1HomomorphismObligationSurface : Setω where
  field
    dhrReconstructionInput :
      DoplicherRobertsReconstruction

    primeLaneStandardModelTableMatchInput :
      PrimeLaneStandardModelTableMatchConditionalInput

    gDHR :
      CompactGaugeGroup

    standardModelGaugeTarget :
      Gauge.Gauge

    standardModelGaugeTargetIsSU3xSU2xU1 :
      standardModelGaugeTarget
      ≡
      Gauge.SU3×SU2×U1

    homomorphismTarget :
      CompactGaugeGroup →
      Gauge.Gauge →
      Set

    homomorphismLawTarget :
      CompactGaugeGroup →
      Gauge.Gauge →
      Set

    faithfulnessTarget :
      CompactGaugeGroup →
      Gauge.Gauge →
      Set

    kernelTarget :
      CompactGaugeGroup →
      Gauge.Gauge →
      Set

    kernelQuotientDecisionTarget :
      CompactGaugeGroup →
      Gauge.Gauge →
      Set

    obligationShape :
      String

    obligationShape-v :
      obligationShape
      ≡
      "after-DR-and-primeLane-SM-table-match-provide-concrete-G_DHR-to-SU3xSU2xU1-homomorphism-faithfulness-kernel"

    residualObligations :
      List GDHRToStandardModelHomomorphismObligation

    residualObligationsAreCanonical :
      residualObligations
      ≡
      canonicalGDHRToStandardModelHomomorphismObligations

    homomorphismConstructed :
      Bool

    homomorphismConstructedIsFalse :
      homomorphismConstructed ≡ false

    homomorphismLawProved :
      Bool

    homomorphismLawProvedIsFalse :
      homomorphismLawProved ≡ false

    faithfulnessProved :
      Bool

    faithfulnessProvedIsFalse :
      faithfulnessProved ≡ false

    kernelComputed :
      Bool

    kernelComputedIsFalse :
      kernelComputed ≡ false

    kernelTrivialOrCentralQuotientDecided :
      Bool

    kernelTrivialOrCentralQuotientDecidedIsFalse :
      kernelTrivialOrCentralQuotientDecided ≡ false

    dhrReconstructionConsumedHere :
      Bool

    dhrReconstructionConsumedHereIsFalse :
      dhrReconstructionConsumedHere ≡ false

    exactStandardModelCarrierFunctorMatchConsumed :
      Bool

    exactStandardModelCarrierFunctorMatchConsumedIsFalse :
      exactStandardModelCarrierFunctorMatchConsumed ≡ false

    gate1Gate6AgreementObstruction :
      Gate1Gate6AgreementObstruction

    gate1Gate6AgreementObstructionIsExactMatch :
      gate1Gate6AgreementObstruction
      ≡
      missingExactStandardModelCarrierFunctorMatch

    dhrGaugePromoted :
      Bool

    dhrGaugePromotedIsFalse :
      dhrGaugePromoted ≡ false

    homomorphismBoundary :
      List String

open GDHRToSU3xSU2xU1HomomorphismObligationSurface public

canonicalGDHRToSU3xSU2xU1HomomorphismObligationSurface :
  GDHRToSU3xSU2xU1HomomorphismObligationSurface
canonicalGDHRToSU3xSU2xU1HomomorphismObligationSurface =
  record
    { dhrReconstructionInput =
        canonicalDoplicherRobertsReconstruction
    ; primeLaneStandardModelTableMatchInput =
        canonicalPrimeLaneStandardModelTableMatchConditionalInput
    ; gDHR =
        DoplicherRobertsReconstruction.reconstructedCompactGroup
          canonicalDoplicherRobertsReconstruction
    ; standardModelGaugeTarget =
        Gauge.SU3×SU2×U1
    ; standardModelGaugeTargetIsSU3xSU2xU1 =
        refl
    ; homomorphismTarget =
        abstractGDHRToSU3xSU2xU1HomomorphismTarget
    ; homomorphismLawTarget =
        abstractGDHRToSU3xSU2xU1HomomorphismLawTarget
    ; faithfulnessTarget =
        abstractGDHRToSU3xSU2xU1FaithfulnessTarget
    ; kernelTarget =
        abstractGDHRToSU3xSU2xU1KernelTarget
    ; kernelQuotientDecisionTarget =
        abstractGDHRToSU3xSU2xU1KernelQuotientDecisionTarget
    ; obligationShape =
        "after-DR-and-primeLane-SM-table-match-provide-concrete-G_DHR-to-SU3xSU2xU1-homomorphism-faithfulness-kernel"
    ; obligationShape-v =
        refl
    ; residualObligations =
        canonicalGDHRToStandardModelHomomorphismObligations
    ; residualObligationsAreCanonical =
        refl
    ; homomorphismConstructed =
        false
    ; homomorphismConstructedIsFalse =
        refl
    ; homomorphismLawProved =
        false
    ; homomorphismLawProvedIsFalse =
        refl
    ; faithfulnessProved =
        false
    ; faithfulnessProvedIsFalse =
        refl
    ; kernelComputed =
        false
    ; kernelComputedIsFalse =
        refl
    ; kernelTrivialOrCentralQuotientDecided =
        false
    ; kernelTrivialOrCentralQuotientDecidedIsFalse =
        refl
    ; dhrReconstructionConsumedHere =
        false
    ; dhrReconstructionConsumedHereIsFalse =
        refl
    ; exactStandardModelCarrierFunctorMatchConsumed =
        false
    ; exactStandardModelCarrierFunctorMatchConsumedIsFalse =
        refl
    ; gate1Gate6AgreementObstruction =
        missingExactStandardModelCarrierFunctorMatch
    ; gate1Gate6AgreementObstructionIsExactMatch =
        refl
    ; dhrGaugePromoted =
        false
    ; dhrGaugePromotedIsFalse =
        refl
    ; homomorphismBoundary =
        "Post-terminal peer-review obligation: conditional DR reconstruction plus a conditional prime-lane Standard Model table match still leave a concrete group homomorphism target"
        ∷ "The required map is G_DHR -> SU3 x SU2 x U1, with its homomorphism law, faithfulness, kernel computation, and trivial-kernel or central-quotient decision supplied explicitly"
        ∷ "This surface does not consume the DR authority locally and does not close missingExactStandardModelCarrierFunctorMatch"
        ∷ "No DHR gauge promotion or G_DHR equals Standard Model theorem is produced here"
        ∷ []
    }

record DHRGate8Term1IdentityDRSMBlockerReceipt : Setω₃ where
  field
    finiteGaugeEvidence :
      ExactSM.Gate8Term1FiniteGaugeEvidenceBlockerReceipt

    finitePrimeLaneDHRSMCompatibilityLedger :
      FiniteLedger.FinitePrimeLaneDHRSMCompatibilityLedger

    identityEndomorphismAudit :
      DHRIdentityEndomorphismWitnessAudit

    arbitrarySectorIdentityReceipt :
      DHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt

    drScopingCorrection :
      DHRDoplicherRobertsScopingCorrectionReceipt

    gDHRToSMHomomorphismObligation :
      GDHRToSU3xSU2xU1HomomorphismObligationSurface

    exactSMBlockerReceipt :
      ExactSM.ExactSMMatchBlockerReceipt

    firstIdentityBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    firstIdentityBlockerIsMissingConstructor :
      firstIdentityBlocker
      ≡
      missingIdentityEndomorphismActionConstructor

    firstDRBlocker :
      DRLocalCategoricalEvidenceBlocker

    firstDRBlockerIsMissingLocalAlgebraSemantics :
      firstDRBlocker
      ≡
      missingDRDASHILocalAlgebra

    firstSMCarrierFunctorBlocker :
      ExactSM.ExactSMMatchBlocker

    firstSMCarrierFunctorBlockerIsGate1Gate6 :
      firstSMCarrierFunctorBlocker
      ≡
      ExactSM.blockedByNoGate1Gate6CarrierFunctorEquivalence

    finiteGaugeEvidencePackaged :
      Bool

    finiteGaugeEvidencePackagedIsTrue :
      finiteGaugeEvidencePackaged ≡ true

    finitePrimeLaneAssignmentsRecorded :
      Bool

    finitePrimeLaneAssignmentsRecordedIsTrue :
      finitePrimeLaneAssignmentsRecorded ≡ true

    finiteIdentityCompositionNaturalityReceiptsAvailable :
      Bool

    finiteIdentityCompositionNaturalityReceiptsAvailableIsTrue :
      finiteIdentityCompositionNaturalityReceiptsAvailable ≡ true

    endRhoPkRepGPkExactMatchPromoted :
      Bool

    endRhoPkRepGPkExactMatchPromotedIsFalse :
      endRhoPkRepGPkExactMatchPromoted ≡ false

    arbitrarySectorIdentityConstructed :
      Bool

    arbitrarySectorIdentityConstructedIsFalse :
      arbitrarySectorIdentityConstructed ≡ false

    drReconstructionConsumed :
      Bool

    drReconstructionConsumedIsFalse :
      drReconstructionConsumed ≡ false

    smCarrierFunctorMatchPromoted :
      Bool

    smCarrierFunctorMatchPromotedIsFalse :
      smCarrierFunctorMatchPromoted ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    gate8Term1Boundary :
      List String

open DHRGate8Term1IdentityDRSMBlockerReceipt public

canonicalDHRGate8Term1IdentityDRSMBlockerReceipt :
  DHRGate8Term1IdentityDRSMBlockerReceipt
canonicalDHRGate8Term1IdentityDRSMBlockerReceipt =
  record
    { finiteGaugeEvidence =
        ExactSM.canonicalGate8Term1FiniteGaugeEvidenceBlockerReceipt
    ; finitePrimeLaneDHRSMCompatibilityLedger =
        FiniteLedger.canonicalFinitePrimeLaneDHRSMCompatibilityLedger
    ; identityEndomorphismAudit =
        canonicalDHRIdentityEndomorphismWitnessAudit
    ; arbitrarySectorIdentityReceipt =
        canonicalDHRUpper6ArbitrarySectorIdentityEndomorphismFailClosedReceipt
    ; drScopingCorrection =
        canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; gDHRToSMHomomorphismObligation =
        canonicalGDHRToSU3xSU2xU1HomomorphismObligationSurface
    ; exactSMBlockerReceipt =
        ExactSM.canonicalExactSMMatchBlockerReceipt
    ; firstIdentityBlocker =
        missingIdentityEndomorphismActionConstructor
    ; firstIdentityBlockerIsMissingConstructor =
        refl
    ; firstDRBlocker =
        missingDRDASHILocalAlgebra
    ; firstDRBlockerIsMissingLocalAlgebraSemantics =
        refl
    ; firstSMCarrierFunctorBlocker =
        ExactSM.blockedByNoGate1Gate6CarrierFunctorEquivalence
    ; firstSMCarrierFunctorBlockerIsGate1Gate6 =
        refl
    ; finiteGaugeEvidencePackaged =
        true
    ; finiteGaugeEvidencePackagedIsTrue =
        refl
    ; finitePrimeLaneAssignmentsRecorded =
        true
    ; finitePrimeLaneAssignmentsRecordedIsTrue =
        refl
    ; finiteIdentityCompositionNaturalityReceiptsAvailable =
        true
    ; finiteIdentityCompositionNaturalityReceiptsAvailableIsTrue =
        refl
    ; endRhoPkRepGPkExactMatchPromoted =
        false
    ; endRhoPkRepGPkExactMatchPromotedIsFalse =
        refl
    ; arbitrarySectorIdentityConstructed =
        false
    ; arbitrarySectorIdentityConstructedIsFalse =
        refl
    ; drReconstructionConsumed =
        false
    ; drReconstructionConsumedIsFalse =
        refl
    ; smCarrierFunctorMatchPromoted =
        false
    ; smCarrierFunctorMatchPromotedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; gate8Term1Boundary =
        "Gate8.term1 packages finite U1/SU2/SU3 evidence through the ExactSM finite evidence receipt"
        ∷ "It also consumes the finite prime-lane DHR-SM ledger recording p2->U1Y, p3->SU2L, p5->SU3c"
        ∷ "Finite identity, identity-composition, and row-naturality receipts are available only over those three ledger rows"
        ∷ "The exact lane target End(rho_pk) ~= Rep(G_pk) remains blocked and unpromoted"
        ∷ "Arbitrary-sector DHR identity remains blocked first by missingIdentityEndomorphismActionConstructor, with DASHI local-algebra semantics still explicit"
        ∷ "Doplicher-Roberts reconstruction remains blocked first by missingDRDASHILocalAlgebra and the rest of the local categorical evidence ledger"
        ∷ "Standard Model carrier-functor matching remains blocked by blockedByNoGate1Gate6CarrierFunctorEquivalence"
        ∷ "The concrete G_DHR -> SU3 x SU2 x U1 homomorphism, laws, faithfulness, kernel, and quotient decision remain obligations"
        ∷ "No G_DHR ~= G_SM theorem is promoted"
        ∷ []
    }

data DHRIdentityActionSemanticDependency : Set where
  identityActionNeedsDASHILocalAlgebra :
    DHRIdentityActionSemanticDependency

  identityActionNeedsActionLawOnLocalAlgebra :
    DHRIdentityActionSemanticDependency

  identityActionNeedsOutsideComplementIdentityLaw :
    DHRIdentityActionSemanticDependency

  identityActionNeedsTransportNaturalityLaw :
    DHRIdentityActionSemanticDependency

  identityActionNeedsArbitrarySectorClassifier :
    DHRIdentityActionSemanticDependency

canonicalDHRIdentityActionSemanticDependencies :
  List DHRIdentityActionSemanticDependency
canonicalDHRIdentityActionSemanticDependencies =
  identityActionNeedsDASHILocalAlgebra
  ∷ identityActionNeedsActionLawOnLocalAlgebra
  ∷ identityActionNeedsOutsideComplementIdentityLaw
  ∷ identityActionNeedsTransportNaturalityLaw
  ∷ identityActionNeedsArbitrarySectorClassifier
  ∷ []

data EndomorphismActionDataMissingField : Set where
  missingEndomorphismActionDataLocalAlgebraCarrier :
    EndomorphismActionDataMissingField

  missingEndomorphismActionDataActionOnLocalAlgebra :
    EndomorphismActionDataMissingField

  missingEndomorphismActionDataIdentityActionLaw :
    EndomorphismActionDataMissingField

  missingEndomorphismActionDataCompositionActionLaw :
    EndomorphismActionDataMissingField

  missingEndomorphismActionDataOutsideComplementIdentityLaw :
    EndomorphismActionDataMissingField

  missingEndomorphismActionDataTransportNaturalityLaw :
    EndomorphismActionDataMissingField

  missingEndomorphismActionDataArbitrarySectorClassifier :
    EndomorphismActionDataMissingField

canonicalEndomorphismActionDataMissingFields :
  List EndomorphismActionDataMissingField
canonicalEndomorphismActionDataMissingFields =
  missingEndomorphismActionDataLocalAlgebraCarrier
  ∷ missingEndomorphismActionDataActionOnLocalAlgebra
  ∷ missingEndomorphismActionDataIdentityActionLaw
  ∷ missingEndomorphismActionDataCompositionActionLaw
  ∷ missingEndomorphismActionDataOutsideComplementIdentityLaw
  ∷ missingEndomorphismActionDataTransportNaturalityLaw
  ∷ missingEndomorphismActionDataArbitrarySectorClassifier
  ∷ []

record EndomorphismActionData : Setω where
  field
    localAlgebraCarrier :
      AQFT.Region →
      Set

    actionOnLocalAlgebra :
      (region : AQFT.Region) →
      localAlgebraCarrier region →
      localAlgebraCarrier region

    identityActionLaw :
      (region : AQFT.Region) →
      localAlgebraCarrier region →
      Set

    compositionActionLaw :
      Set

    outsideComplementIdentityLaw :
      (localisationRegion region : AQFT.Region) →
      region ≡ CausalComplement localisationRegion →
      localAlgebraCarrier region →
      Set

    transportNaturalityLaw :
      Set

    arbitrarySectorClassifier :
      SuperselectionSector →
      Set

record DHRIdentityEndomorphismActionSemanticAdapterRequestReceipt : Setω₂ where
  field
    endomorphismActionCarrier :
      Setω

    endomorphismActionCarrierIsAbstractPostulate :
      EndomorphismActionPrimitiveShape

    endomorphismActionCarrierIsAbstractPostulate-v :
      endomorphismActionCarrierIsAbstractPostulate
      ≡
      endomorphismActionPostulatedBareSet

    localisedEndomorphismActionProjection :
      LocalisedEndomorphism →
      EndomorphismAction

    requestedIdentityActionConstructorTarget :
      SuperselectionSector →
      Set₁

    requestedIdentityActionConstructorTargetsEndomorphismAction :
      Bool

    requestedIdentityEndomorphismTargetName :
      String

    requestedIdentityEndomorphismTargetName-v :
      requestedIdentityEndomorphismTargetName
      ≡
      "arbitrarySectorIdentityEndomorphism : (sector : SuperselectionSector) -> LocalisedEndomorphism"

    localAlgebraResidual :
      AQFTColim.AQFTM4U6ResidualBlocker

    localAlgebraResidualIsMissingDASHILocalAlgebra :
      localAlgebraResidual
      ≡
      AQFTColim.missingDASHILocalAlgebra

    semanticDependencies :
      List DHRIdentityActionSemanticDependency

    semanticDependenciesAreCanonical :
      semanticDependencies
      ≡
      canonicalDHRIdentityActionSemanticDependencies

    requestedEndomorphismActionDataRecordName :
      String

    requestedEndomorphismActionDataRecordName-v :
      requestedEndomorphismActionDataRecordName
      ≡
      "EndomorphismActionData"

    missingEndomorphismActionDataFields :
      List EndomorphismActionDataMissingField

    missingEndomorphismActionDataFieldsAreCanonical :
      missingEndomorphismActionDataFields
      ≡
      canonicalEndomorphismActionDataMissingFields

    datatypeReplacementAttempted :
      Bool

    datatypeReplacementAttemptedIsTrue :
      datatypeReplacementAttempted ≡ true

    datatypeReplacementRejectedAsSemanticBreaking :
      Bool

    datatypeReplacementRejectedAsSemanticBreakingIsTrue :
      datatypeReplacementRejectedAsSemanticBreaking ≡ true

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    residualForeignLaneIdentityBlocker :
      DHRGaugeForeignLaneIdentityResidual

    residualForeignLaneIdentityBlockerIsExplicitWitness :
      residualForeignLaneIdentityBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    doplicherRobertsConsumed :
      Bool

    doplicherRobertsConsumedIsFalse :
      doplicherRobertsConsumed ≡ false

    standardModelMatchPromoted :
      Bool

    standardModelMatchPromotedIsFalse :
      standardModelMatchPromoted ≡ false

    semanticAdapterBoundary :
      List String

open DHRIdentityEndomorphismActionSemanticAdapterRequestReceipt public

canonicalDHRIdentityEndomorphismActionSemanticAdapterRequestReceipt :
  DHRIdentityEndomorphismActionSemanticAdapterRequestReceipt
canonicalDHRIdentityEndomorphismActionSemanticAdapterRequestReceipt =
  record
    { endomorphismActionCarrier =
        EndomorphismAction
    ; endomorphismActionCarrierIsAbstractPostulate =
        endomorphismActionPostulatedBareSet
    ; endomorphismActionCarrierIsAbstractPostulate-v =
        refl
    ; localisedEndomorphismActionProjection =
        LocalisedEndomorphism.endomorphismAction
    ; requestedIdentityActionConstructorTarget =
        λ _ → Set
    ; requestedIdentityActionConstructorTargetsEndomorphismAction =
        true
    ; requestedIdentityEndomorphismTargetName =
        "arbitrarySectorIdentityEndomorphism : (sector : SuperselectionSector) -> LocalisedEndomorphism"
    ; requestedIdentityEndomorphismTargetName-v =
        refl
    ; localAlgebraResidual =
        AQFTColim.missingDASHILocalAlgebra
    ; localAlgebraResidualIsMissingDASHILocalAlgebra =
        refl
    ; semanticDependencies =
        canonicalDHRIdentityActionSemanticDependencies
    ; semanticDependenciesAreCanonical =
        refl
    ; requestedEndomorphismActionDataRecordName =
        "EndomorphismActionData"
    ; requestedEndomorphismActionDataRecordName-v =
        refl
    ; missingEndomorphismActionDataFields =
        canonicalEndomorphismActionDataMissingFields
    ; missingEndomorphismActionDataFieldsAreCanonical =
        refl
    ; datatypeReplacementAttempted =
        true
    ; datatypeReplacementAttemptedIsTrue =
        refl
    ; datatypeReplacementRejectedAsSemanticBreaking =
        true
    ; datatypeReplacementRejectedAsSemanticBreakingIsTrue =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; residualForeignLaneIdentityBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualForeignLaneIdentityBlockerIsExplicitWitness =
        refl
    ; doplicherRobertsConsumed =
        false
    ; doplicherRobertsConsumedIsFalse =
        refl
    ; standardModelMatchPromoted =
        false
    ; standardModelMatchPromotedIsFalse =
        refl
    ; semanticAdapterBoundary =
        "u6/l3 semantic adapter request: replacing EndomorphismAction by a local datatype would currently fabricate identity-action semantics"
        ∷ "EndomorphismAction remains an abstract carrier; the only safe local progress is an explicit constructor target for future DASHI local-algebra semantics"
        ∷ "EndomorphismActionData is requested with exact missing fields: DASHI local-algebra carrier, action-on-local-algebra, identity law, composition law, outside-complement identity, transport naturality, and arbitrary-sector classifier"
        ∷ "The requested constructor must act as identity on the supplied DASHI local algebra, prove outside-complement identity, transport naturality, and arbitrary-sector classification"
        ∷ "No arbitrary-sector identity endomorphism, Doplicher-Roberts consumption, G_DHR construction, Standard Model match, or terminal promotion is produced"
        ∷ []
    }

record DHRGate6SemanticAdapterAuditThreadedDRFailClosedLedger : Setω₄ where
  field
    semanticAdapterRequest :
      DHRIdentityEndomorphismActionSemanticAdapterRequestReceipt

    h1h5CompletenessCheck :
      TierBPaper3Delta3cH1H5CompletenessCheck

    drHypothesesEvidence :
      DRFiveHypothesesEvidenceSurface

    localisedTransportableStatisticsEvidence :
      DHRLocalisedTransportableEndomorphismEvidenceSurface

    localAlgebraPreconditionAudit :
      DHRGate6LocalAlgebraPreconditionAuditReceipt

    drScopingCorrection :
      DHRDoplicherRobertsScopingCorrectionReceipt

    semanticDependencies :
      List DHRIdentityActionSemanticDependency

    semanticDependenciesAreCanonical :
      semanticDependencies
      ≡
      canonicalDHRIdentityActionSemanticDependencies

    missingEndomorphismActionDataFields :
      List EndomorphismActionDataMissingField

    missingEndomorphismActionDataFieldsAreCanonical :
      missingEndomorphismActionDataFields
      ≡
      canonicalEndomorphismActionDataMissingFields

    firstMissingEndomorphismActionDataField :
      EndomorphismActionDataMissingField

    firstMissingEndomorphismActionDataFieldIsLocalAlgebraCarrier :
      firstMissingEndomorphismActionDataField
      ≡
      missingEndomorphismActionDataLocalAlgebraCarrier

    tensorStatisticsH1H5DRAuditThreaded :
      Bool

    tensorStatisticsH1H5DRAuditThreadedIsTrue :
      tensorStatisticsH1H5DRAuditThreaded ≡ true

    directEndomorphismActionReplacementAvailable :
      Bool

    directEndomorphismActionReplacementAvailableIsFalse :
      directEndomorphismActionReplacementAvailable ≡ false

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    tensorProductLawProved :
      Bool

    tensorProductLawProvedIsFalse :
      tensorProductLawProved ≡ false

    statisticsComputed :
      Bool

    statisticsComputedIsFalse :
      statisticsComputed ≡ false

    drReconstructionPromoted :
      Bool

    drReconstructionPromotedIsFalse :
      drReconstructionPromoted ≡ false

    standardModelMatchPromoted :
      Bool

    standardModelMatchPromotedIsFalse :
      standardModelMatchPromoted ≡ false

    threadedAuditBoundary :
      List String

open DHRGate6SemanticAdapterAuditThreadedDRFailClosedLedger public

canonicalDHRGate6SemanticAdapterAuditThreadedDRFailClosedLedger :
  DHRGate6SemanticAdapterAuditThreadedDRFailClosedLedger
canonicalDHRGate6SemanticAdapterAuditThreadedDRFailClosedLedger =
  record
    { semanticAdapterRequest =
        canonicalDHRIdentityEndomorphismActionSemanticAdapterRequestReceipt
    ; h1h5CompletenessCheck =
        canonicalTierBPaper3Delta3cH1H5CompletenessCheck
    ; drHypothesesEvidence =
        canonicalDRFiveHypothesesEvidenceSurface
    ; localisedTransportableStatisticsEvidence =
        canonicalDHRLocalisedTransportableEndomorphismEvidenceSurface
    ; localAlgebraPreconditionAudit =
        canonicalDHRGate6LocalAlgebraPreconditionAuditReceipt
    ; drScopingCorrection =
        canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; semanticDependencies =
        canonicalDHRIdentityActionSemanticDependencies
    ; semanticDependenciesAreCanonical =
        refl
    ; missingEndomorphismActionDataFields =
        canonicalEndomorphismActionDataMissingFields
    ; missingEndomorphismActionDataFieldsAreCanonical =
        refl
    ; firstMissingEndomorphismActionDataField =
        missingEndomorphismActionDataLocalAlgebraCarrier
    ; firstMissingEndomorphismActionDataFieldIsLocalAlgebraCarrier =
        refl
    ; tensorStatisticsH1H5DRAuditThreaded =
        true
    ; tensorStatisticsH1H5DRAuditThreadedIsTrue =
        refl
    ; directEndomorphismActionReplacementAvailable =
        false
    ; directEndomorphismActionReplacementAvailableIsFalse =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; tensorProductLawProved =
        false
    ; tensorProductLawProvedIsFalse =
        refl
    ; statisticsComputed =
        false
    ; statisticsComputedIsFalse =
        refl
    ; drReconstructionPromoted =
        false
    ; drReconstructionPromotedIsFalse =
        refl
    ; standardModelMatchPromoted =
        false
    ; standardModelMatchPromotedIsFalse =
        refl
    ; threadedAuditBoundary =
        "Gate 6/l2-l4 threads the u6 EndomorphismActionData missing-field audit into tensor/statistics/H1-H5/DR fail-closed accounting"
        ∷ "The exact missing fields remain local-algebra carrier, action-on-local-algebra, identity law, composition law, outside-complement identity, transport naturality, and arbitrary-sector classifier"
        ∷ "The H1-H5 and localised-transportable/statistics surfaces are consumed only as target/evidence ledgers"
        ∷ "No direct EndomorphismAction replacement, identity action constructor, tensor law, statistics computation, DR reconstruction, or Standard Model match is promoted"
        ∷ []
    }

data DHRIdentityActionOnLocalAlgebraTargetReceipt
  (sector : SuperselectionSector)
  (region : AQFT.Region)
  (observable : LocalObservableAlgebra region)
  (action : EndomorphismAction) :
  Set where
  dhrIdentityActionOnLocalAlgebraTargetOnly :
    DHRIdentityActionOnLocalAlgebraTargetReceipt sector region observable action

data DHRIdentityActionLawOnLocalAlgebraTargetReceipt
  (sector : SuperselectionSector)
  (region : AQFT.Region)
  (observable : LocalObservableAlgebra region)
  (action : EndomorphismAction) :
  Set where
  dhrIdentityActionLawOnLocalAlgebraTargetOnly :
    DHRIdentityActionLawOnLocalAlgebraTargetReceipt sector region observable action

data DHRIdentityActionOutsideComplementTargetReceipt
  (sector : SuperselectionSector)
  (region : AQFT.Region)
  (action : EndomorphismAction) :
  Set where
  dhrIdentityActionOutsideComplementTargetOnly :
    DHRIdentityActionOutsideComplementTargetReceipt sector region action

data DHRIdentityActionTransportNaturalityTargetReceipt
  (sector : SuperselectionSector)
  (ρ : LocalisedEndomorphism)
  (transport : Transportable ρ)
  (action : EndomorphismAction) :
  Set where
  dhrIdentityActionTransportNaturalityTargetOnly :
    DHRIdentityActionTransportNaturalityTargetReceipt sector ρ transport action

data DHRArbitrarySectorClassifierForIdentityActionTargetReceipt
  (sector : SuperselectionSector) :
  Set where
  dhrArbitrarySectorClassifierForIdentityActionTargetOnly :
    DHRArbitrarySectorClassifierForIdentityActionTargetReceipt sector

abstractDHRIdentityActionOnLocalAlgebraTarget :
  (sector : SuperselectionSector) →
  (region : AQFT.Region) →
  LocalObservableAlgebra region →
  EndomorphismAction →
  Set
abstractDHRIdentityActionOnLocalAlgebraTarget sector region observable action =
  DHRIdentityActionOnLocalAlgebraTargetReceipt sector region observable action

abstractDHRIdentityActionLawOnLocalAlgebraTarget :
  (sector : SuperselectionSector) →
  (region : AQFT.Region) →
  LocalObservableAlgebra region →
  EndomorphismAction →
  Set
abstractDHRIdentityActionLawOnLocalAlgebraTarget sector region observable action =
  DHRIdentityActionLawOnLocalAlgebraTargetReceipt sector region observable action

abstractDHRIdentityActionOutsideComplementTarget :
  (sector : SuperselectionSector) →
  (region : AQFT.Region) →
  EndomorphismAction →
  Set
abstractDHRIdentityActionOutsideComplementTarget sector region action =
  DHRIdentityActionOutsideComplementTargetReceipt sector region action

abstractDHRIdentityActionTransportNaturalityTarget :
  (sector : SuperselectionSector) →
  (ρ : LocalisedEndomorphism) →
  Transportable ρ →
  EndomorphismAction →
  Set
abstractDHRIdentityActionTransportNaturalityTarget sector ρ transport action =
  DHRIdentityActionTransportNaturalityTargetReceipt sector ρ transport action

abstractDHRArbitrarySectorClassifierForIdentityActionTarget :
  SuperselectionSector →
  Set
abstractDHRArbitrarySectorClassifierForIdentityActionTarget sector =
  DHRArbitrarySectorClassifierForIdentityActionTargetReceipt sector

record DHRAlgebraIndexedIdentityActionAdapterTarget : Setω₄ where
  field
    semanticAdapterRequest :
      DHRIdentityEndomorphismActionSemanticAdapterRequestReceipt

    replacementInspection :
      DHRUpper6EndomorphismActionReplacementInspectionReceipt

    localAlgebraResidual :
      AQFTColim.AQFTM4U6ResidualBlocker

    localAlgebraResidualIsMissingDASHILocalAlgebra :
      localAlgebraResidual
      ≡
      AQFTColim.missingDASHILocalAlgebra

    semanticDependencies :
      List DHRIdentityActionSemanticDependency

    semanticDependenciesAreCanonical :
      semanticDependencies
      ≡
      canonicalDHRIdentityActionSemanticDependencies

    identityActionOnLocalAlgebraTarget :
      (sector : SuperselectionSector) →
      (region : AQFT.Region) →
      LocalObservableAlgebra region →
      EndomorphismAction →
      Set

    identityActionLawOnLocalAlgebraTarget :
      (sector : SuperselectionSector) →
      (region : AQFT.Region) →
      LocalObservableAlgebra region →
      EndomorphismAction →
      Set

    outsideComplementIdentityTarget :
      (sector : SuperselectionSector) →
      (region : AQFT.Region) →
      EndomorphismAction →
      Set

    transportNaturalityTarget :
      (sector : SuperselectionSector) →
      (ρ : LocalisedEndomorphism) →
      Transportable ρ →
      EndomorphismAction →
      Set

    arbitrarySectorClassifierTarget :
      SuperselectionSector →
      Set

    identityActionAdapterTargetIndexedByAlgebra :
      Bool

    identityActionAdapterTargetIndexedByAlgebraIsTrue :
      identityActionAdapterTargetIndexedByAlgebra ≡ true

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    localAlgebraSemanticsConsumed :
      Bool

    localAlgebraSemanticsConsumedIsFalse :
      localAlgebraSemanticsConsumed ≡ false

    arbitrarySectorClassifierSupplied :
      Bool

    arbitrarySectorClassifierSuppliedIsFalse :
      arbitrarySectorClassifierSupplied ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    doplicherRobertsConsumed :
      Bool

    doplicherRobertsConsumedIsFalse :
      doplicherRobertsConsumed ≡ false

    standardModelMatchPromoted :
      Bool

    standardModelMatchPromotedIsFalse :
      standardModelMatchPromoted ≡ false

    adapterTargetBoundary :
      List String

open DHRAlgebraIndexedIdentityActionAdapterTarget public

canonicalDHRAlgebraIndexedIdentityActionAdapterTarget :
  DHRAlgebraIndexedIdentityActionAdapterTarget
canonicalDHRAlgebraIndexedIdentityActionAdapterTarget =
  record
    { semanticAdapterRequest =
        canonicalDHRIdentityEndomorphismActionSemanticAdapterRequestReceipt
    ; replacementInspection =
        canonicalDHRUpper6EndomorphismActionReplacementInspectionReceipt
    ; localAlgebraResidual =
        AQFTColim.missingDASHILocalAlgebra
    ; localAlgebraResidualIsMissingDASHILocalAlgebra =
        refl
    ; semanticDependencies =
        canonicalDHRIdentityActionSemanticDependencies
    ; semanticDependenciesAreCanonical =
        refl
    ; identityActionOnLocalAlgebraTarget =
        abstractDHRIdentityActionOnLocalAlgebraTarget
    ; identityActionLawOnLocalAlgebraTarget =
        abstractDHRIdentityActionLawOnLocalAlgebraTarget
    ; outsideComplementIdentityTarget =
        abstractDHRIdentityActionOutsideComplementTarget
    ; transportNaturalityTarget =
        abstractDHRIdentityActionTransportNaturalityTarget
    ; arbitrarySectorClassifierTarget =
        abstractDHRArbitrarySectorClassifierForIdentityActionTarget
    ; identityActionAdapterTargetIndexedByAlgebra =
        true
    ; identityActionAdapterTargetIndexedByAlgebraIsTrue =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; localAlgebraSemanticsConsumed =
        false
    ; localAlgebraSemanticsConsumedIsFalse =
        refl
    ; arbitrarySectorClassifierSupplied =
        false
    ; arbitrarySectorClassifierSuppliedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; doplicherRobertsConsumed =
        false
    ; doplicherRobertsConsumedIsFalse =
        refl
    ; standardModelMatchPromoted =
        false
    ; standardModelMatchPromotedIsFalse =
        refl
    ; adapterTargetBoundary =
        "algebra-indexed identity-action adapter target: identity action is indexed by sector, AQFT region, LocalObservableAlgebra, and EndomorphismAction"
        ∷ "the exact first dependency is AQFTColim.missingDASHILocalAlgebra, recorded as localAlgebraResidual"
        ∷ "outside-complement identity, transport naturality, and arbitrary-sector classifier evidence are target sockets only"
        ∷ "EndomorphismAction is still not replaced; the constructor is not provided and arbitrary-sector identity endomorphism remains fail-closed"
        ∷ "No Doplicher-Roberts consumption, G_DHR construction, Standard Model matching, or terminal promotion is produced"
        ∷ []
    }

arbitrarySectorIdIdentityActionTarget :
  SuperselectionSector →
  Setω
arbitrarySectorIdIdentityActionTarget _ =
  EndomorphismAction

arbitrarySectorIdEndomorphismTargetName :
  String
arbitrarySectorIdEndomorphismTargetName =
  "LocalisedEndomorphism"

record DHRU6ArbitrarySectorIdIdentityActionFailClosedReceipt : Setω₄ where
  field
    semanticAdapterRequest :
      DHRIdentityEndomorphismActionSemanticAdapterRequestReceipt

    replacementInspection :
      DHRUpper6EndomorphismActionReplacementInspectionReceipt

    arbitrarySectorIdActionTarget :
      SuperselectionSector →
      Setω

    arbitrarySectorIdActionTargetMatchesEndomorphismAction :
      Bool

    arbitrarySectorIdTargetName :
      String

    arbitrarySectorIdTargetNamesLocalisedEndomorphism :
      Bool

    arbitrarySectorIdTargetNamesLocalisedEndomorphism-v :
      arbitrarySectorIdTargetNamesLocalisedEndomorphism
      ≡
      true

    endomorphismActionReplacementTypeFeasible :
      Bool

    endomorphismActionReplacementTypeFeasibleIsFalse :
      endomorphismActionReplacementTypeFeasible ≡ false

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    arbitrarySectorIdConstructed :
      Bool

    arbitrarySectorIdConstructedIsFalse :
      arbitrarySectorIdConstructed ≡ false

    localAlgebraResidual :
      AQFTColim.AQFTM4U6ResidualBlocker

    localAlgebraResidualIsMissingDASHILocalAlgebra :
      localAlgebraResidual
      ≡
      AQFTColim.missingDASHILocalAlgebra

    residualForeignLaneIdentityBlocker :
      DHRGaugeForeignLaneIdentityResidual

    residualForeignLaneIdentityBlockerIsExplicitWitness :
      residualForeignLaneIdentityBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    doplicherRobertsConsumed :
      Bool

    doplicherRobertsConsumedIsFalse :
      doplicherRobertsConsumed ≡ false

    standardModelMatchPromoted :
      Bool

    standardModelMatchPromotedIsFalse :
      standardModelMatchPromoted ≡ false

    receiptBoundary :
      List String

open DHRU6ArbitrarySectorIdIdentityActionFailClosedReceipt public

canonicalDHRU6ArbitrarySectorIdIdentityActionFailClosedReceipt :
  DHRU6ArbitrarySectorIdIdentityActionFailClosedReceipt
canonicalDHRU6ArbitrarySectorIdIdentityActionFailClosedReceipt =
  record
    { semanticAdapterRequest =
        canonicalDHRIdentityEndomorphismActionSemanticAdapterRequestReceipt
    ; replacementInspection =
        canonicalDHRUpper6EndomorphismActionReplacementInspectionReceipt
    ; arbitrarySectorIdActionTarget =
        arbitrarySectorIdIdentityActionTarget
    ; arbitrarySectorIdActionTargetMatchesEndomorphismAction =
        true
    ; arbitrarySectorIdTargetName =
        arbitrarySectorIdEndomorphismTargetName
    ; arbitrarySectorIdTargetNamesLocalisedEndomorphism =
        true
    ; arbitrarySectorIdTargetNamesLocalisedEndomorphism-v =
        refl
    ; endomorphismActionReplacementTypeFeasible =
        false
    ; endomorphismActionReplacementTypeFeasibleIsFalse =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdConstructed =
        false
    ; arbitrarySectorIdConstructedIsFalse =
        refl
    ; localAlgebraResidual =
        AQFTColim.missingDASHILocalAlgebra
    ; localAlgebraResidualIsMissingDASHILocalAlgebra =
        refl
    ; residualForeignLaneIdentityBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualForeignLaneIdentityBlockerIsExplicitWitness =
        refl
    ; doplicherRobertsConsumed =
        false
    ; doplicherRobertsConsumedIsFalse =
        refl
    ; standardModelMatchPromoted =
        false
    ; standardModelMatchPromotedIsFalse =
        refl
    ; receiptBoundary =
        "u6 names arbitrarySectorId as a target from an arbitrary SuperselectionSector to a LocalisedEndomorphism"
        ∷ "the identity action target is EndomorphismAction, but no value is constructed because EndomorphismAction is still abstract"
        ∷ "a datatype replacement is recorded as not type-feasible without the DASHI local-algebra action semantics"
        ∷ "DR consumption, foreign-lane global identity closure, and Standard Model matching remain fail-closed"
        ∷ []
    }

record DHRIndexedIdentityEndomorphismActionSemanticTarget
  (sector : SuperselectionSector) :
  Setω₁ where
  field
    semanticActionCarrier :
      Setω

    semanticActionCarrierIsEndomorphismAction :
      Bool

    indexedLocalAlgebraCarrier :
      AQFT.Region →
      Set

    indexedLocalAlgebraCarrierMatchesLocalObservableAlgebra :
      (region : AQFT.Region) →
      indexedLocalAlgebraCarrier region
      ≡
      LocalObservableAlgebra region

    identityActionLawTarget :
      (region : AQFT.Region) →
      indexedLocalAlgebraCarrier region →
      Set

    outsideComplementIdentityLawTarget :
      (localisationRegion region : AQFT.Region) →
      region ≡ CausalComplement localisationRegion →
      indexedLocalAlgebraCarrier region →
      Set

    localisedEndomorphismTargetName :
      String

    localisedEndomorphismTargetName-v :
      localisedEndomorphismTargetName
      ≡
      "LocalisedEndomorphism"

    semanticTargetDependsOnArbitrarySector :
      Bool

    semanticTargetDependsOnArbitrarySectorIsTrue :
      semanticTargetDependsOnArbitrarySector ≡ true

open DHRIndexedIdentityEndomorphismActionSemanticTarget public

canonicalDHRIndexedIdentityEndomorphismActionSemanticTarget :
  (sector : SuperselectionSector) →
  DHRIndexedIdentityEndomorphismActionSemanticTarget sector
canonicalDHRIndexedIdentityEndomorphismActionSemanticTarget _ =
  record
    { semanticActionCarrier =
        EndomorphismAction
    ; semanticActionCarrierIsEndomorphismAction =
        true
    ; indexedLocalAlgebraCarrier =
        LocalObservableAlgebra
    ; indexedLocalAlgebraCarrierMatchesLocalObservableAlgebra =
        λ _ →
          refl
    ; identityActionLawTarget =
        λ _ observable →
          observable ≡ observable
    ; outsideComplementIdentityLawTarget =
        λ _ _ _ observable →
          observable ≡ observable
    ; localisedEndomorphismTargetName =
        "LocalisedEndomorphism"
    ; localisedEndomorphismTargetName-v =
        refl
    ; semanticTargetDependsOnArbitrarySector =
        true
    ; semanticTargetDependsOnArbitrarySectorIsTrue =
        refl
    }

record DHRU6IndexedIdentityActionSemanticAdapterReceipt : Setω₄ where
  field
    priorSemanticAdapterRequest :
      DHRIdentityEndomorphismActionSemanticAdapterRequestReceipt

    replacementInspection :
      DHRUpper6EndomorphismActionReplacementInspectionReceipt

    indexedIdentityActionSemanticTarget :
      (sector : SuperselectionSector) →
      DHRIndexedIdentityEndomorphismActionSemanticTarget sector

    indexedSemanticActionCarrierMatchesEndomorphismAction :
      Bool

    indexedCarrier :
      AQFT.Region →
      Set

    indexedCarrierMatchesLocalObservableAlgebra :
      (region : AQFT.Region) →
      indexedCarrier region
      ≡
      LocalObservableAlgebra region

    exactLocalAlgebraSemanticsBlocker :
      DHRIdentityEndomorphismWitnessBlocker

    exactLocalAlgebraSemanticsBlockerIsDASHILocalAlgebra :
      exactLocalAlgebraSemanticsBlocker
      ≡
      missingDASHILocalAlgebraForIdentityActionSemantics

    aqftLocalAlgebraResidual :
      AQFTColim.AQFTM4U6ResidualBlocker

    aqftLocalAlgebraResidualIsMissingDASHILocalAlgebra :
      aqftLocalAlgebraResidual
      ≡
      AQFTColim.missingDASHILocalAlgebra

    endomorphismActionPostulatePreserved :
      Bool

    endomorphismActionPostulatePreservedIsTrue :
      endomorphismActionPostulatePreserved ≡ true

    identityEndomorphismActionConstructorProvided :
      Bool

    identityEndomorphismActionConstructorProvidedIsFalse :
      identityEndomorphismActionConstructorProvided ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsFalse :
      missingDASHILocalAlgebraConsumed ≡ false

    residualForeignLaneIdentityBlocker :
      DHRGaugeForeignLaneIdentityResidual

    residualForeignLaneIdentityBlockerIsExplicitWitness :
      residualForeignLaneIdentityBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    residualGlobalForeignLaneIdentityClosed :
      Bool

    residualGlobalForeignLaneIdentityClosedIsFalse :
      residualGlobalForeignLaneIdentityClosed ≡ false

    indexedSemanticAdapterBoundary :
      List String

open DHRU6IndexedIdentityActionSemanticAdapterReceipt public

canonicalDHRU6IndexedIdentityActionSemanticAdapterReceipt :
  DHRU6IndexedIdentityActionSemanticAdapterReceipt
canonicalDHRU6IndexedIdentityActionSemanticAdapterReceipt =
  record
    { priorSemanticAdapterRequest =
        canonicalDHRIdentityEndomorphismActionSemanticAdapterRequestReceipt
    ; replacementInspection =
        canonicalDHRUpper6EndomorphismActionReplacementInspectionReceipt
    ; indexedIdentityActionSemanticTarget =
        canonicalDHRIndexedIdentityEndomorphismActionSemanticTarget
    ; indexedSemanticActionCarrierMatchesEndomorphismAction =
        true
    ; indexedCarrier =
        LocalObservableAlgebra
    ; indexedCarrierMatchesLocalObservableAlgebra =
        λ _ →
          refl
    ; exactLocalAlgebraSemanticsBlocker =
        missingDASHILocalAlgebraForIdentityActionSemantics
    ; exactLocalAlgebraSemanticsBlockerIsDASHILocalAlgebra =
        refl
    ; aqftLocalAlgebraResidual =
        AQFTColim.missingDASHILocalAlgebra
    ; aqftLocalAlgebraResidualIsMissingDASHILocalAlgebra =
        refl
    ; endomorphismActionPostulatePreserved =
        true
    ; endomorphismActionPostulatePreservedIsTrue =
        refl
    ; identityEndomorphismActionConstructorProvided =
        false
    ; identityEndomorphismActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; missingDASHILocalAlgebraConsumed =
        false
    ; missingDASHILocalAlgebraConsumedIsFalse =
        refl
    ; residualForeignLaneIdentityBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualForeignLaneIdentityBlockerIsExplicitWitness =
        refl
    ; residualGlobalForeignLaneIdentityClosed =
        false
    ; residualGlobalForeignLaneIdentityClosedIsFalse =
        refl
    ; indexedSemanticAdapterBoundary =
        "u6/m6/l4 adds an indexed semantic target for identity action over AQFT.Region and LocalObservableAlgebra"
        ∷ "the target records the action carrier as EndomorphismAction without replacing the postulated bare Set"
        ∷ "identity and outside-complement laws are exposed only as local-observable law targets, not as constructed EndomorphismAction values"
        ∷ "the exact dependency remains missingDASHILocalAlgebraForIdentityActionSemantics with AQFTColim.missingDASHILocalAlgebra as the carrier-side residual"
        ∷ "residualGlobalForeignLaneIdentityRequiresExplicitWitness remains open for arbitrary sectors"
        ∷ []
    }

record DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt : Setω₁ where
  field
    indexedSemanticAdapter :
      Bool

    concreteDepthFilteredLocalAlgebraData :
      Bool

    concreteDepthFilteredLocalAlgebraSurface :
      Bool

    concreteDepthFilteredLocalAlgebraSurfaceIsCanonical :
      Bool

    concreteDepthFilteredLocalAlgebraSurfaceIsCanonical-v :
      concreteDepthFilteredLocalAlgebraSurfaceIsCanonical ≡ true

    dashiLocalQuotientCarrier :
      AQFT.Region →
      Set

    dashiLocalQuotientCarrierMatchesDASHILocalNet :
      (region : AQFT.Region) →
      dashiLocalQuotientCarrier region
      ≡
      AQFTColim.DASHILocalAlgebraNet.net
        AQFTColim.dASHILocalAlgebraNet
        region

    dashiLocalQuotientCarrierMatchesAbstractCompletion :
      (region : AQFT.Region) →
      dashiLocalQuotientCarrier region
      ≡
      AQFTColim.abstractQuotientCStarCompletion
        region

    dashiLocalCompletionEmbed :
      {region : AQFT.Region} →
      AQFTColim.abstractPromotedReceiptQuotient region →
      dashiLocalQuotientCarrier region

    identityActionLawTargetForConcreteElement :
      (sector : SuperselectionSector) →
      (region : AQFT.Region) →
      dashiLocalQuotientCarrier region →
      EndomorphismAction →
      Set

    identityActionLawTargetForConcreteElementIsReflexive :
      (sector : SuperselectionSector) →
      (region : AQFT.Region) →
      (a : dashiLocalQuotientCarrier region) →
      (action : EndomorphismAction) →
      identityActionLawTargetForConcreteElement
        sector
        region
        a
        action

    preparedArbitrarySectorIdActionTarget :
      SuperselectionSector →
      Setω

    preparedArbitrarySectorIdActionTarget-v :
      Bool

    concreteLocalAlgebraElementIndexingPrepared :
      Bool

    concreteLocalAlgebraElementIndexingPreparedIsTrue :
      concreteLocalAlgebraElementIndexingPrepared ≡ true

    identityEndomorphismActionConstructorProvided :
      Bool

    identityEndomorphismActionConstructorProvidedIsFalse :
      identityEndomorphismActionConstructorProvided ≡ false

    arbitrarySectorIdConstructed :
      Bool

    arbitrarySectorIdConstructedIsFalse :
      arbitrarySectorIdConstructed ≡ false

    missingDASHILocalAlgebraConsumed :
      Bool

    missingDASHILocalAlgebraConsumedIsTrue :
      missingDASHILocalAlgebraConsumed ≡ true

    residualForeignLaneIdentityBlocker :
      DHRGaugeForeignLaneIdentityResidual

    residualForeignLaneIdentityBlockerIsExplicitWitness :
      residualForeignLaneIdentityBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    concreteLocalAlgebraIdentityAdapterBoundary :
      List String

open DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt public

canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt :
  DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt =
  record
    { indexedSemanticAdapter =
        true
    ; concreteDepthFilteredLocalAlgebraData =
        true
    ; concreteDepthFilteredLocalAlgebraSurface =
        true
    ; concreteDepthFilteredLocalAlgebraSurfaceIsCanonical =
        true
    ; concreteDepthFilteredLocalAlgebraSurfaceIsCanonical-v =
        refl
    ; dashiLocalQuotientCarrier =
        AQFTColim.DASHILocalAlgebraNet.net
          AQFTColim.dASHILocalAlgebraNet
    ; dashiLocalQuotientCarrierMatchesDASHILocalNet =
        λ _ →
          refl
    ; dashiLocalQuotientCarrierMatchesAbstractCompletion =
        AQFTColim.DASHILocalAlgebraNet.netMatchesAbstractCompletion
          AQFTColim.dASHILocalAlgebraNet
    ; dashiLocalCompletionEmbed =
        AQFTColim.DASHILocalAlgebraNet.completionEmbed
          AQFTColim.dASHILocalAlgebraNet
    ; identityActionLawTargetForConcreteElement =
        λ _ _ a _ →
          a ≡ a
    ; identityActionLawTargetForConcreteElementIsReflexive =
        λ _ _ _ _ →
          refl
    ; preparedArbitrarySectorIdActionTarget =
        λ _ →
          (region : AQFT.Region) →
          AQFTColim.DASHILocalAlgebraNet.net
            AQFTColim.dASHILocalAlgebraNet
            region →
          EndomorphismAction
    ; preparedArbitrarySectorIdActionTarget-v =
        true
    ; concreteLocalAlgebraElementIndexingPrepared =
        true
    ; concreteLocalAlgebraElementIndexingPreparedIsTrue =
        refl
    ; identityEndomorphismActionConstructorProvided =
        false
    ; identityEndomorphismActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdConstructed =
        false
    ; arbitrarySectorIdConstructedIsFalse =
        refl
    ; missingDASHILocalAlgebraConsumed =
        true
    ; missingDASHILocalAlgebraConsumedIsTrue =
        refl
    ; residualForeignLaneIdentityBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualForeignLaneIdentityBlockerIsExplicitWitness =
        refl
    ; concreteLocalAlgebraIdentityAdapterBoundary =
        "u6 consumes AQFTColim.dASHILocalAlgebraNet as the concrete carrier for the identity-action law target"
        ∷ "the pre-completion quotient is threaded only through DASHILocalAlgebraNet.completionEmbed, not identified with the completed local net"
        ∷ "the element law is reflexive on each completed local algebra element, but no EndomorphismAction value is constructed while EndomorphismAction remains abstract"
        ∷ "missingDASHILocalAlgebra is consumed at this adapter boundary; the remaining blocker is the explicit arbitrary-sector identity-action witness"
        ∷ "arbitrarySectorId, residualGlobalForeignLaneIdentityRequiresExplicitWitness, DR reconstruction, and Standard Model matching remain unpromoted"
        ∷ []
    }

record DHRExistingEndomorphismActionDASHILocalNetAdapterReceipt
  (ρ : LocalisedEndomorphism) :
  Setω₁ where
  field
    concreteLocalAlgebraIdentityAdapter :
      DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt

    projectedEndomorphismAction :
      EndomorphismAction

    projectedEndomorphismActionIsLocalisedField :
      Bool

    actionConsumableByExistingAPIs :
      LocalisedEndomorphism →
      EndomorphismAction

    actionConsumableByExistingAPIsIsProjectionAtρ :
      Bool

    dashiLocalNet :
      AQFT.Region →
      Set

    dashiLocalNetMatchesAdapterCarrier :
      dashiLocalNet
      ≡
      DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.dashiLocalQuotientCarrier
        concreteLocalAlgebraIdentityAdapter

    dashiLocalNetMatchesCanonicalNet :
      Bool

    projectedActionSelfIdentityReceipt :
      Bool

    completedElementIdentityReceipt :
      (region : AQFT.Region) →
      dashiLocalNet region →
      Set

    completedElementIdentityReceiptInhabited :
      (region : AQFT.Region) →
      (element : dashiLocalNet region) →
      completedElementIdentityReceipt region element

    endomorphismActionPostulatePreserved :
      Bool

    endomorphismActionPostulatePreservedIsTrue :
      endomorphismActionPostulatePreserved ≡ true

    identityEndomorphismActionConstructorProvided :
      Bool

    identityEndomorphismActionConstructorProvidedIsFalse :
      identityEndomorphismActionConstructorProvided ≡ false

    arbitrarySectorIdentityEndomorphismConstructed :
      Bool

    arbitrarySectorIdentityEndomorphismConstructedIsFalse :
      arbitrarySectorIdentityEndomorphismConstructed ≡ false

    doplicherRobertsConsumed :
      Bool

    doplicherRobertsConsumedIsFalse :
      doplicherRobertsConsumed ≡ false

    adapterBoundary :
      List String

open DHRExistingEndomorphismActionDASHILocalNetAdapterReceipt public

canonicalDHRExistingEndomorphismActionDASHILocalNetAdapterReceipt :
  (ρ : LocalisedEndomorphism) →
  DHRExistingEndomorphismActionDASHILocalNetAdapterReceipt ρ
canonicalDHRExistingEndomorphismActionDASHILocalNetAdapterReceipt ρ =
  record
    { concreteLocalAlgebraIdentityAdapter =
        canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; projectedEndomorphismAction =
        LocalisedEndomorphism.endomorphismAction ρ
    ; projectedEndomorphismActionIsLocalisedField =
        true
    ; actionConsumableByExistingAPIs =
        LocalisedEndomorphism.endomorphismAction
    ; actionConsumableByExistingAPIsIsProjectionAtρ =
        true
    ; dashiLocalNet =
        DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.dashiLocalQuotientCarrier
          canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; dashiLocalNetMatchesAdapterCarrier =
        refl
    ; dashiLocalNetMatchesCanonicalNet =
        true
    ; projectedActionSelfIdentityReceipt =
        true
    ; completedElementIdentityReceipt =
        λ _ element →
          element ≡ element
    ; completedElementIdentityReceiptInhabited =
        λ _ _ →
          refl
    ; endomorphismActionPostulatePreserved =
        true
    ; endomorphismActionPostulatePreservedIsTrue =
        refl
    ; identityEndomorphismActionConstructorProvided =
        false
    ; identityEndomorphismActionConstructorProvidedIsFalse =
        refl
    ; arbitrarySectorIdentityEndomorphismConstructed =
        false
    ; arbitrarySectorIdentityEndomorphismConstructedIsFalse =
        refl
    ; doplicherRobertsConsumed =
        false
    ; doplicherRobertsConsumedIsFalse =
        refl
    ; adapterBoundary =
        "non-postulated adapter: existing APIs may consume LocalisedEndomorphism.endomorphismAction through actionConsumableByExistingAPIs"
        ∷ "the adapter threads the existing action over AQFTColim.dASHILocalAlgebraNet without replacing EndomorphismAction"
        ∷ "completed local algebra elements get only reflexive identity receipts; no action law or arbitrary-sector identity constructor is fabricated"
        ∷ "Doplicher-Roberts reconstruction, G_DHR construction, and Standard Model matching remain unconsumed"
        ∷ []
    }

data DHRGate6LocalizationTransportabilitySemanticBlocker : Set where
  missingSemanticEndomorphismActionOnDASHILocalAlgebra :
    DHRGate6LocalizationTransportabilitySemanticBlocker

  missingEndomorphismActionCompositionLaw :
    DHRGate6LocalizationTransportabilitySemanticBlocker

  missingLocalAlgebraIsotonyLocalityCompatibilityLaw :
    DHRGate6LocalizationTransportabilitySemanticBlocker

  missingTransportIntertwinerNaturalityLaw :
    DHRGate6LocalizationTransportabilitySemanticBlocker

  missingTwistStatisticsOperatorActionLaw :
    DHRGate6LocalizationTransportabilitySemanticBlocker

canonicalDHRGate6LocalizationTransportabilitySemanticBlockers :
  List DHRGate6LocalizationTransportabilitySemanticBlocker
canonicalDHRGate6LocalizationTransportabilitySemanticBlockers =
  missingSemanticEndomorphismActionOnDASHILocalAlgebra
  ∷ missingEndomorphismActionCompositionLaw
  ∷ missingLocalAlgebraIsotonyLocalityCompatibilityLaw
  ∷ missingTransportIntertwinerNaturalityLaw
  ∷ missingTwistStatisticsOperatorActionLaw
  ∷ []

record DHRGate6LocalizationTransportabilityAfterLocalAlgebraReceipt : Setω₅ where
  field
    concreteLocalAlgebraAdapter :
      DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt

    semanticAdapterAuditLedger :
      DHRGate6SemanticAdapterAuditThreadedDRFailClosedLedger

    dashiLocalAlgebraNetIsCanonical :
      Bool

    dashiLocalAlgebraNetIsCanonical-v :
      dashiLocalAlgebraNetIsCanonical ≡ true

    concreteLocalCarrier :
      AQFT.Region →
      Set

    concreteLocalCarrierMatchesDASHILocalNet :
      (region : AQFT.Region) →
      concreteLocalCarrier region
      ≡
      AQFTColim.DASHILocalAlgebraNet.net
        AQFTColim.dASHILocalAlgebraNet
        region

    identityActionLawTargetForConcreteElement :
      (sector : SuperselectionSector) →
      (region : AQFT.Region) →
      concreteLocalCarrier region →
      EndomorphismAction →
      Set

    identityActionLawTargetForConcreteElementReflexive :
      (sector : SuperselectionSector) →
      (region : AQFT.Region) →
      (a : concreteLocalCarrier region) →
      (action : EndomorphismAction) →
      identityActionLawTargetForConcreteElement
        sector
        region
        a
        action

    preparedArbitrarySectorActionTarget :
      SuperselectionSector →
      Setω

    preparedArbitrarySectorActionTargetMatchesConcreteAdapter :
      Bool

    localisationTargetForSector :
      SuperselectionSector →
      AQFT.Region →
      Set

    transportabilityTargetForLocalisedEndomorphism :
      LocalisedEndomorphism →
      Set

    twistStatisticsTargetForSector :
      SuperselectionSector →
      Set

    concreteLocalAlgebraConsumed :
      Bool

    concreteLocalAlgebraConsumedIsTrue :
      concreteLocalAlgebraConsumed ≡ true

    identityActionConstructorProvided :
      Bool

    identityActionConstructorProvidedIsFalse :
      identityActionConstructorProvided ≡ false

    localisedIdentitySectorConstructed :
      Bool

    localisedIdentitySectorConstructedIsFalse :
      localisedIdentitySectorConstructed ≡ false

    transportableIdentitySectorConstructed :
      Bool

    transportableIdentitySectorConstructedIsFalse :
      transportableIdentitySectorConstructed ≡ false

    twistSectorActionConstructed :
      Bool

    twistSectorActionConstructedIsFalse :
      twistSectorActionConstructed ≡ false

    arbitrarySectorSemanticsConstructed :
      Bool

    arbitrarySectorSemanticsConstructedIsFalse :
      arbitrarySectorSemanticsConstructed ≡ false

    firstSemanticBlocker :
      DHRGate6LocalizationTransportabilitySemanticBlocker

    firstSemanticBlockerIsActionOnDASHILocalAlgebra :
      firstSemanticBlocker
      ≡
      missingSemanticEndomorphismActionOnDASHILocalAlgebra

    semanticBlockers :
      List DHRGate6LocalizationTransportabilitySemanticBlocker

    semanticBlockersAreCanonical :
      semanticBlockers
      ≡
      canonicalDHRGate6LocalizationTransportabilitySemanticBlockers

    residualForeignLaneIdentityBlocker :
      DHRGaugeForeignLaneIdentityResidual

    residualForeignLaneIdentityBlockerIsExplicitWitness :
      residualForeignLaneIdentityBlocker
      ≡
      residualGlobalForeignLaneIdentityRequiresExplicitWitness

    localizationTransportabilityBoundary :
      List String

open DHRGate6LocalizationTransportabilityAfterLocalAlgebraReceipt public

canonicalDHRGate6LocalizationTransportabilityAfterLocalAlgebraReceipt :
  DHRGate6LocalizationTransportabilityAfterLocalAlgebraReceipt
canonicalDHRGate6LocalizationTransportabilityAfterLocalAlgebraReceipt =
  record
    { concreteLocalAlgebraAdapter =
        canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; semanticAdapterAuditLedger =
        canonicalDHRGate6SemanticAdapterAuditThreadedDRFailClosedLedger
    ; dashiLocalAlgebraNetIsCanonical =
        true
    ; dashiLocalAlgebraNetIsCanonical-v =
        refl
    ; concreteLocalCarrier =
        DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.dashiLocalQuotientCarrier
          canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; concreteLocalCarrierMatchesDASHILocalNet =
        DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.dashiLocalQuotientCarrierMatchesDASHILocalNet
          canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; identityActionLawTargetForConcreteElement =
        DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.identityActionLawTargetForConcreteElement
          canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; identityActionLawTargetForConcreteElementReflexive =
        DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.identityActionLawTargetForConcreteElementIsReflexive
          canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; preparedArbitrarySectorActionTarget =
        DHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt.preparedArbitrarySectorIdActionTarget
          canonicalDHRU6ConcreteLocalAlgebraIdentityActionAdapterReceipt
    ; preparedArbitrarySectorActionTargetMatchesConcreteAdapter =
        true
    ; localisationTargetForSector =
        λ _ _ →
          ⊥
    ; transportabilityTargetForLocalisedEndomorphism =
        λ ρ →
          Transportable.transportabilityLawTarget
            (abstractTransportablePrimitive ρ)
    ; twistStatisticsTargetForSector =
        λ _ →
          DHRStatisticsOperator
    ; concreteLocalAlgebraConsumed =
        true
    ; concreteLocalAlgebraConsumedIsTrue =
        refl
    ; identityActionConstructorProvided =
        false
    ; identityActionConstructorProvidedIsFalse =
        refl
    ; localisedIdentitySectorConstructed =
        false
    ; localisedIdentitySectorConstructedIsFalse =
        refl
    ; transportableIdentitySectorConstructed =
        false
    ; transportableIdentitySectorConstructedIsFalse =
        refl
    ; twistSectorActionConstructed =
        false
    ; twistSectorActionConstructedIsFalse =
        refl
    ; arbitrarySectorSemanticsConstructed =
        false
    ; arbitrarySectorSemanticsConstructedIsFalse =
        refl
    ; firstSemanticBlocker =
        missingSemanticEndomorphismActionOnDASHILocalAlgebra
    ; firstSemanticBlockerIsActionOnDASHILocalAlgebra =
        refl
    ; semanticBlockers =
        canonicalDHRGate6LocalizationTransportabilitySemanticBlockers
    ; semanticBlockersAreCanonical =
        refl
    ; residualForeignLaneIdentityBlocker =
        residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; residualForeignLaneIdentityBlockerIsExplicitWitness =
        refl
    ; localizationTransportabilityBoundary =
        "Gate 6 consumes AQFTColim.dASHILocalAlgebraNet for concrete completed local-algebra element indexing"
        ∷ "The reflexive concrete element law is retained only as a law target over a supplied EndomorphismAction; it does not construct the action"
        ∷ "The u6 EndomorphismActionData missing-field audit is threaded into the localization/transportability ledger before tensor/statistics/DR use"
        ∷ "Localisation, transportability, and twist/statistics targets remain fail-closed until a semantic EndomorphismAction on DASHI local algebras is supplied"
        ∷ "Exact remaining laws: action composition, isotony/locality compatibility, transport-intertwiner naturality, and twist/statistics action law"
        ∷ "No identity-only replacement is used, and arbitrary-sector DHR semantics remain unconstructed"
        ∷ []
    }
