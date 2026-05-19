module DASHI.Physics.QFT.DHRGaugeReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT

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
  CausalComplement :
    AQFT.Region →
    AQFT.Region

  DoubleComplement :
    AQFT.Region →
    AQFT.Region

  LocalObservableAlgebra :
    AQFT.Region →
    Set

  CommutantAlgebra :
    AQFT.Region →
    Set

  SuperselectionSector :
    Set

  EndomorphismAction :
    Set

  DHRStatisticsOperator :
    Set

  TensorCStarCategory :
    Set

  CompactGaugeGroup :
    Set

  StandardModelMatchingData :
    Set

  PrimeLaneCondensationData :
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

record HaagDualityReceiptTarget : Setω where
  field
    status :
      HaagDualityStatus

    netSurface :
      AQFT.AQFTTypedNetSurface

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

postulate
  abstractHaagInclusionTarget :
    (region : AQFT.Region) →
    LocalObservableAlgebra region →
    CommutantAlgebra (CausalComplement region) →
    Set

  abstractHaagEqualityTarget :
    (region : AQFT.Region) →
    LocalObservableAlgebra region
    ≡
    CommutantAlgebra (CausalComplement region)

  abstractDoubleComplementCaveat :
    (region : AQFT.Region) →
    (double : AQFT.Region) →
    double ≡ DoubleComplement region →
    Set

canonicalHaagDualityReceiptTarget :
  HaagDualityReceiptTarget
canonicalHaagDualityReceiptTarget =
  record
    { status =
        haagDualityEqualityTargetOnly
    ; netSurface =
        AQFT.canonicalAQFTTypedNetSurface
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

postulate
  abstractSuperselectionSectorTarget :
    SuperselectionSector →
    Set

  abstractDHRLocalizedEndomorphismTarget :
    SuperselectionSector →
    Set

  abstractDHRTransportableLocalisationTarget :
    SuperselectionSector →
    Set

  abstractDHRFiniteStatisticsTarget :
    SuperselectionSector →
    Set

  abstractLocalisedEndomorphismPrimitive :
    SuperselectionSector →
    LocalisedEndomorphism

  abstractTransportablePrimitive :
    (ρ : LocalisedEndomorphism) →
    Transportable ρ

  abstractIntertwinerPrimitiveTarget :
    (ρ σ : LocalisedEndomorphism) →
    Intertwiner ρ σ →
    Set

  abstractDHRStatisticsOperator :
    SuperselectionSector →
    SuperselectionSector →
    DHRStatisticsOperator

  abstractDHRStatisticsFormulaSocket :
    (ρ σ : LocalisedEndomorphism) →
    DHRStatisticsFormulaSocket ρ σ

  abstractDHRStatisticsOperatorFormulaAgreesTarget :
    (ρ σ : LocalisedEndomorphism) →
    DHRStatisticsFormulaSocket.statisticsOperatorCarrier
      (abstractDHRStatisticsFormulaSocket ρ σ)
    ≡
    abstractDHRStatisticsOperator
      (LocalisedEndomorphism.localisedSector ρ)
      (LocalisedEndomorphism.localisedSector σ)

  abstractDHRStatisticsOperatorTarget :
    DHRStatisticsOperator →
    Set

canonicalDHRFormalismPrimitiveReceipt :
  DHRFormalismPrimitiveReceipt
canonicalDHRFormalismPrimitiveReceipt =
  record
    { formalismLocalisedEndomorphismPrimitive =
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
        "LocalisedEndomorphism and Transportable are typed DHR primitives over the AQFT net surface"
        ∷ "The statistics operator epsilon-rho-sigma is typed with a formula socket, but no computation is promoted"
        ∷ "Doplicher-Roberts reconstruction authority cannot be invoked until the symmetric tensor C*-category hypotheses are supplied"
        ∷ []
    }

canonicalDHRSelectionCriterionTarget :
  DHRSelectionCriterionTarget
canonicalDHRSelectionCriterionTarget =
  record
    { sector =
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
        ∷ "LocalisedEndomorphism, Transportable, and Intertwiner are explicit constructive primitives, but their AQFT laws remain target sockets"
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

postulate
  abstractDHRCategoryObjectTarget :
    LocalisedEndomorphism →
    Set

  abstractDHRCategoryMorphismTarget :
    (ρ σ : LocalisedEndomorphism) →
    Intertwiner ρ σ →
    Set

  abstractDHRCategoryTensorObjectTarget :
    LocalisedEndomorphism →
    LocalisedEndomorphism →
    Set

  abstractDHRCategoryTensorMorphismTarget :
    (ρ σ τ υ : LocalisedEndomorphism) →
    Intertwiner ρ σ →
    Intertwiner τ υ →
    Set

  abstractDHRCategoryUnitObjectTarget :
    LocalisedEndomorphism →
    Set

  abstractDHRCategorySymmetryFromStatisticsTarget :
    (ρ σ : LocalisedEndomorphism) →
    DHRStatisticsFormulaSocket ρ σ →
    Set

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

postulate
  abstractTensorCStarCategory :
    TensorCStarCategory

  abstractTensorProductTarget :
    TensorCStarCategory →
    Set

  abstractSymmetryTarget :
    TensorCStarCategory →
    Set

  abstractCStarStructureTarget :
    TensorCStarCategory →
    Set

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

postulate
  abstractDoplicherRobertsTheoremHypothesesTarget :
    TensorCStarCategory →
    Set

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

postulate
  abstractDRStatisticsOperatorSymmetryTarget :
    (ρ σ : LocalisedEndomorphism) →
    DHRStatisticsFormulaSocket ρ σ →
    Set

  abstractDRBraidInvolutiveTarget :
    (ρ σ : LocalisedEndomorphism) →
    Set

  abstractDRSpacetimeDimensionAtLeastThreeTarget :
    Set

  abstractDRConjugateEndomorphismTarget :
    LocalisedEndomorphism →
    LocalisedEndomorphism →
    Set

  abstractDRReehSchliederInputTarget :
    Set

  abstractDRCoevaluationIntertwinerTarget :
    (ρ ρbar : LocalisedEndomorphism) →
    Set

  abstractDREvaluationIntertwinerTarget :
    (ρ ρbar : LocalisedEndomorphism) →
    Set

  abstractDRConjugateEquationsTarget :
    (ρ ρbar : LocalisedEndomorphism) →
    Set

  abstractDRTypeIIIProjectionSupplyTarget :
    AQFT.Region →
    Set

  abstractDRDirectSumProjectionTarget :
    (ρ σ : LocalisedEndomorphism) →
    Set

  abstractDRDirectSumEndomorphismTarget :
    (ρ σ : LocalisedEndomorphism) →
    LocalisedEndomorphism →
    Set

  abstractDREndomorphismProjectionTarget :
    LocalisedEndomorphism →
    Set

  abstractDRSubobjectSplitTarget :
    (ρ : LocalisedEndomorphism) →
    Set

  abstractDRSubEndomorphismTransportableTarget :
    (ρ : LocalisedEndomorphism) →
    Set

  abstractDRUnitEndomorphismTarget :
    LocalisedEndomorphism →
    Set

  abstractDREndUnitIntertwinerTarget :
    Set

  abstractDRIrreducibilityInputTarget :
    Set

  abstractDRScalarCentreTarget :
    Set

  abstractDREndUnitComplexScalarsTarget :
    Set

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
        abstractDRReehSchliederInputTarget
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
        abstractDRReehSchliederInputTarget
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
        ∷ "Haag duality plus Reeh-Schlieder cyclicity and irreducibility reduces the centre to scalars"
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
        abstractDRReehSchliederInputTarget
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
        ∷ "H5 End(1) ~= C is explicitly dependent on Haag duality plus Reeh-Schlieder cyclicity, with Reeh-Schlieder 1961 cited or targeted from AQFT axioms"
        ∷ "The checklist does not supply the local H5 proof and does not promote Doplicher-Roberts reconstruction"
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

    laneDimensionRemainsOpen :
      Bool

    laneDimensionRemainsOpenIsTrue :
      laneDimensionRemainsOpen ≡ true

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

postulate
  abstractDoplicherRobertsReconstructionPostulate :
    TensorCStarCategory →
    CompactGaugeGroup →
    Set

  abstractDoplicherRobertsCompactGroup :
    CompactGaugeGroup

  abstractCompactGroupRepresentationCategory :
    CompactGaugeGroup →
    Set

  abstractDoplicherRobertsCategoryEquivalenceToRepG :
    TensorCStarCategory →
    CompactGaugeGroup →
    Set

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
    ; laneDimensionRemainsOpen =
        true
    ; laneDimensionRemainsOpenIsTrue =
        refl
    ; dhrEqualsStandardModelPromoted =
        false
    ; dhrEqualsStandardModelPromotedIsFalse =
        refl
    ; boundary =
        "Doplicher-Roberts reconstruction is safe authority for reconstructing a compact group from a symmetric tensor C*-category"
        ∷ "The authority also records the target category equivalence to Rep(G)"
        ∷ "Standard Model matching and laneDimension remain open downstream obligations"
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
        ∷ "laneDimension remains open and is not closed by this authority item"
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
-- Serre-Tate lane-group theorem supplies the lane groups.
--
-- It deliberately does not prove laneDimension, Serre-Tate ST3, or the
-- low-energy Standard Model breaking.  Those remain explicit hypotheses.

postulate
  PrimeLane :
    Set

  PrimeLaneAlgebra :
    PrimeLane →
    AQFT.Region →
    Set

  PrimeLaneDHRCategory :
    PrimeLane →
    Set

  ProductPrimeLaneGaugeGroup :
    Set

  HighEnergyPatiSalamGroup :
    Set

  LowEnergyStandardModelGroup :
    Set

  SerreTateLaneGroupTheorem :
    PrimeLane →
    CompactGaugeGroup →
    Set

  G4PrimeLaneIndependenceReceipt :
    Set

  SU2RSeesawBreakingReceipt :
    Set

  abstractG4PrimeLaneIndependenceReceipt :
    G4PrimeLaneIndependenceReceipt

  abstractProductPrimeLaneGaugeGroup :
    ProductPrimeLaneGaugeGroup

  abstractHighEnergyPatiSalamGroup :
    HighEnergyPatiSalamGroup

  abstractLowEnergyStandardModelGroup :
    LowEnergyStandardModelGroup

  abstractPrimeLaneTensorFactorisationTarget :
    (region : AQFT.Region) →
    LocalObservableAlgebra region →
    Set

  abstractPrimeLaneAlgebraComponentTarget :
    (lane : PrimeLane) →
    (region : AQFT.Region) →
    PrimeLaneAlgebra lane region →
    Set

  abstractLaneDHRRepClassificationTarget :
    (lane : PrimeLane) →
    (group : CompactGaugeGroup) →
    PrimeLaneDHRCategory lane →
    Set

  abstractFullDHRBoxtimesTarget :
    TensorCStarCategory →
    Set

  abstractFullDHRRepProductEquivalenceTarget :
    TensorCStarCategory →
    ProductPrimeLaneGaugeGroup →
    Set

  abstractProductGroupIsHighEnergyPatiSalamTarget :
    ProductPrimeLaneGaugeGroup →
    HighEnergyPatiSalamGroup →
    Set

  abstractDRHighEnergyPatiSalamReconstructionTarget :
    DoplicherRobertsReconstruction →
    ProductPrimeLaneGaugeGroup →
    HighEnergyPatiSalamGroup →
    Set

  abstractLowEnergySMFromSU2RBreakingTarget :
    HighEnergyPatiSalamGroup →
    SU2RSeesawBreakingReceipt →
    LowEnergyStandardModelGroup →
    Set

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
    ; serreTateLaneGroupTheorem =
        SerreTateLaneGroupTheorem
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
        ∷ "The group G_p is supplied by the Serre-Tate lane-group theorem, not computed in this module"
        ∷ "This receipt records the DHR computation shape without proving laneDimension"
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
        ∷ "After lane classification, boxtimes_p Rep(G_p) is targeted as Rep(product_p G_p)"
        ∷ "This is conditional on the lane groups supplied by the Serre-Tate laneDimension theorem"
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
        "Conditional on the Serre-Tate laneDimension theorem, DR reconstructs product_p G_p"
        ∷ "With lane groups U1, SU2L, SU3c, and SU2R, the high-energy output is the Pati-Salam-side group U1 x SU2L x SU3c x SU2R"
        ∷ "The low-energy Standard Model requires an additional SU2R breaking receipt at the seesaw scale"
        ∷ "This conditional receipt does not prove laneDimension and does not flip the DHR gauge promotion authority token"
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

postulate
  abstractCompactGaugeGroup :
    CompactGaugeGroup

  abstractFibreFunctorTarget :
    TensorCStarCategory →
    Set

  abstractReconstructionTheoremTarget :
    TensorCStarCategory →
    CompactGaugeGroup →
    Set

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

postulate
  abstractStandardModelMatchingData :
    StandardModelMatchingData

  abstractPrimeLaneCondensationData :
    PrimeLaneCondensationData

  abstractStandardModelMatchingTarget :
    StandardModelMatchingData →
    Set

  abstractPrimeLaneCondensationTarget :
    PrimeLaneCondensationData →
    Set

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

    openObligations :
      List DHRGaugeOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalDHRGaugeOpenObligations

    dhrPrimitivesTyped :
      Bool

    dhrPrimitivesTypedIsTrue :
      dhrPrimitivesTyped ≡ true

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
    ; openObligations =
        canonicalDHRGaugeOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; dhrPrimitivesTyped =
        true
    ; dhrPrimitivesTypedIsTrue =
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
        ∷ "Tranche 1B records the conditional computation A(O) ~= tensor_p A_p(O), Delta_DHR ~= boxtimes_p Delta_DHR^(p), and DR reconstruction of product_p G_p"
        ∷ "Delta 3c records H1-H5 completeness and keeps H5 End(1) ~= C dependent on Haag duality plus Reeh-Schlieder cyclicity"
        ∷ "The conditional high-energy Pati-Salam output depends on the Serre-Tate laneDimension theorem and does not prove low-energy Standard Model matching without SU2R seesaw breaking"
        ∷ "Haag duality inclusion/equality, DHR law proofs, statistics computation, tensor C*-category construction, and Tannaka reconstruction remain open"
        ∷ "Standard Model matching and prime-lane condensation are downstream open obligations"
        ∷ "No gauge group, Standard Model, interacting QFT, GRQFT, or TOE promotion follows from this surface"
        ∷ []
    }
