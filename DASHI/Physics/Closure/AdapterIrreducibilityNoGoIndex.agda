module DASHI.Physics.Closure.AdapterIrreducibilityNoGoIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Four empirical adapter irreducibility targets.
--
-- This module records the no-go theorem shapes required before the terminal
-- GRQFT receipt may claim that the remaining adapter inputs are irreducible.
-- It does not prove those no-go theorems and does not promote a TOE claim.

data AdapterIrreducibilityStatus : Set where
  noGoTargetsRecordedNoIrreducibilityProof :
    AdapterIrreducibilityStatus

data AdapterIrreducibilityTarget : Set where
  metricSignatureIrreducibility :
    AdapterIrreducibilityTarget

  bornStateIrreducibility :
    AdapterIrreducibilityTarget

  vacuumSelectionIrreducibility :
    AdapterIrreducibilityTarget

  couplingConstantIrreducibility :
    AdapterIrreducibilityTarget

canonicalAdapterIrreducibilityTargets :
  List AdapterIrreducibilityTarget
canonicalAdapterIrreducibilityTargets =
  metricSignatureIrreducibility
  ∷ bornStateIrreducibility
  ∷ vacuumSelectionIrreducibility
  ∷ couplingConstantIrreducibility
  ∷ []

data AdapterIrreducibilityOpenObligation : Set where
  missingSignatureNoPreferredReductionProof :
    AdapterIrreducibilityOpenObligation

  missingNonUniqueStateSpaceProof :
    AdapterIrreducibilityOpenObligation

  missingCurvedSpacetimeNoPreferredVacuumProof :
    AdapterIrreducibilityOpenObligation

  missingNoCanonicalGaugeCouplingRatioProof :
    AdapterIrreducibilityOpenObligation

  missingGUTReceiptBoundary :
    AdapterIrreducibilityOpenObligation

  missingContractibleProObjectCaveat :
    AdapterIrreducibilityOpenObligation

  missingKreinMilmanMultipleStatesWitness :
    AdapterIrreducibilityOpenObligation

  missingPoincareCovarianceDependency :
    AdapterIrreducibilityOpenObligation

  missingSpectrumConditionDependency :
    AdapterIrreducibilityOpenObligation

  missingCountermodelWitnessSurface :
    AdapterIrreducibilityOpenObligation

  missingBlochBallOrMatrixStateWitness :
    AdapterIrreducibilityOpenObligation

  missingGaugeNormalisationCountermodel :
    AdapterIrreducibilityOpenObligation

  missingAQFTLocalAlgebraCategoryPrimitive :
    AdapterIrreducibilityOpenObligation

  missingNaturalStateTransformationPrimitive :
    AdapterIrreducibilityOpenObligation

  missingNoNaturalStateSelectionAuthority :
    AdapterIrreducibilityOpenObligation

  missingNoPreferredVacuumAuthority :
    AdapterIrreducibilityOpenObligation

canonicalAdapterIrreducibilityOpenObligations :
  List AdapterIrreducibilityOpenObligation
canonicalAdapterIrreducibilityOpenObligations =
  missingSignatureNoPreferredReductionProof
  ∷ missingNonUniqueStateSpaceProof
  ∷ missingCurvedSpacetimeNoPreferredVacuumProof
  ∷ missingNoCanonicalGaugeCouplingRatioProof
  ∷ missingGUTReceiptBoundary
  ∷ missingContractibleProObjectCaveat
  ∷ missingKreinMilmanMultipleStatesWitness
  ∷ missingPoincareCovarianceDependency
  ∷ missingSpectrumConditionDependency
  ∷ missingGaugeNormalisationCountermodel
  ∷ missingAQFTLocalAlgebraCategoryPrimitive
  ∷ missingNaturalStateTransformationPrimitive
  ∷ missingNoNaturalStateSelectionAuthority
  ∷ missingNoPreferredVacuumAuthority
  ∷ []

data AdapterIrreducibilityResolvedObligation : Set where
  countermodelWitnessSurfacesNowRecorded :
    AdapterIrreducibilityResolvedObligation

  toyMatrixCornerStateWitnessNowRecorded :
    AdapterIrreducibilityResolvedObligation

canonicalAdapterIrreducibilityResolvedObligations :
  List AdapterIrreducibilityResolvedObligation
canonicalAdapterIrreducibilityResolvedObligations =
  countermodelWitnessSurfacesNowRecorded
  ∷ toyMatrixCornerStateWitnessNowRecorded
  ∷ []

data AdapterIrreducibilityAuthorityBlockedObligation : Set where
  noNaturalStateSelectionAuthorityBlocked :
    AdapterIrreducibilityAuthorityBlockedObligation

  noPreferredVacuumAuthorityBlocked :
    AdapterIrreducibilityAuthorityBlockedObligation

canonicalAdapterIrreducibilityAuthorityBlockedObligations :
  List AdapterIrreducibilityAuthorityBlockedObligation
canonicalAdapterIrreducibilityAuthorityBlockedObligations =
  noNaturalStateSelectionAuthorityBlocked
  ∷ noPreferredVacuumAuthorityBlocked
  ∷ []

data AdapterIrreducibilityPromotionAuthorityToken : Set where

data NoNaturalStateSelectionAuthorityToken : Set where

data NoPreferredVacuumAuthorityToken : Set where

data AdapterCountermodelWitnessKind : Set where
  frameSignatureCountermodel :
    AdapterCountermodelWitnessKind

  blochBallOrMatrixStateCountermodel :
    AdapterCountermodelWitnessKind

  curvedBackgroundVacuumCountermodel :
    AdapterCountermodelWitnessKind

  gaugeNormalisationCountermodel :
    AdapterCountermodelWitnessKind

data AdapterCountermodelWitnessRecordShape : Set where
  twoSignatureReductionRecordShape :
    AdapterCountermodelWitnessRecordShape

  twoStateLocalAlgebraRecordShape :
    AdapterCountermodelWitnessRecordShape

  twoVacuumSelectionRecordShape :
    AdapterCountermodelWitnessRecordShape

  gaugeFactorRescalingRecordShape :
    AdapterCountermodelWitnessRecordShape

record AdapterNoGoCountermodelWitnessSurface : Setω where
  field
    target :
      AdapterIrreducibilityTarget

    witnessKind :
      AdapterCountermodelWitnessKind

    witnessRecordShape :
      AdapterCountermodelWitnessRecordShape

    witnessShape :
      String

    assumptions :
      List String

    caveats :
      List String

    proofReady :
      Bool

    proofReadyIsFalse :
      proofReady ≡ false

    noGoProved :
      Bool

    noGoProvedIsFalse :
      noGoProved ≡ false

open AdapterNoGoCountermodelWitnessSurface public

data ToyMatrixCornerState : Set where
  toyMatrixCornerState0 :
    ToyMatrixCornerState

  toyMatrixCornerState1 :
    ToyMatrixCornerState

data ToyMatrixCornerObservable : Set where
  toyMatrixCornerProjector :
    ToyMatrixCornerObservable

data ToyMatrixCornerExpectationValue : Set where
  toyMatrixCornerZero :
    ToyMatrixCornerExpectationValue

  toyMatrixCornerOne :
    ToyMatrixCornerExpectationValue

toyMatrixCornerExpectation :
  ToyMatrixCornerState →
  ToyMatrixCornerObservable →
  ToyMatrixCornerExpectationValue
toyMatrixCornerExpectation toyMatrixCornerState0 toyMatrixCornerProjector =
  toyMatrixCornerOne
toyMatrixCornerExpectation toyMatrixCornerState1 toyMatrixCornerProjector =
  toyMatrixCornerZero

toyMatrixCornerOneNotZero :
  toyMatrixCornerOne ≡ toyMatrixCornerZero →
  ⊥
toyMatrixCornerOneNotZero ()

record ToyMatrixCornerStateWitness : Setω where
  field
    localAlgebraShape :
      String

    state0 :
      ToyMatrixCornerState

    state0-v :
      state0 ≡ toyMatrixCornerState0

    state1 :
      ToyMatrixCornerState

    state1-v :
      state1 ≡ toyMatrixCornerState1

    observable :
      ToyMatrixCornerObservable

    observable-v :
      observable ≡ toyMatrixCornerProjector

    expectation0 :
      ToyMatrixCornerExpectationValue

    expectation0-v :
      expectation0
      ≡
      toyMatrixCornerExpectation state0 observable

    expectation1 :
      ToyMatrixCornerExpectationValue

    expectation1-v :
      expectation1
      ≡
      toyMatrixCornerExpectation state1 observable

    expectationsDistinct :
      expectation0 ≡ expectation1 →
      ⊥

    matrixCornerWitnessOnly :
      Bool

    matrixCornerWitnessOnlyIsTrue :
      matrixCornerWitnessOnly ≡ true

    promotesNoGo :
      Bool

    promotesNoGoIsFalse :
      promotesNoGo ≡ false

open ToyMatrixCornerStateWitness public

canonicalToyMatrixCornerStateWitness :
  ToyMatrixCornerStateWitness
canonicalToyMatrixCornerStateWitness =
  record
    { localAlgebraShape =
        "toy-M2C-corner-with-two-density-matrix-states-and-one-projector-like-observable"
    ; state0 =
        toyMatrixCornerState0
    ; state0-v =
        refl
    ; state1 =
        toyMatrixCornerState1
    ; state1-v =
        refl
    ; observable =
        toyMatrixCornerProjector
    ; observable-v =
        refl
    ; expectation0 =
        toyMatrixCornerOne
    ; expectation0-v =
        refl
    ; expectation1 =
        toyMatrixCornerZero
    ; expectation1-v =
        refl
    ; expectationsDistinct =
        toyMatrixCornerOneNotZero
    ; matrixCornerWitnessOnly =
        true
    ; matrixCornerWitnessOnlyIsTrue =
        refl
    ; promotesNoGo =
        false
    ; promotesNoGoIsFalse =
        refl
    }

data NoNaturalStateSelectionMissingPrimitive : Set where
  missingLocalAlgebraCategory :
    NoNaturalStateSelectionMissingPrimitive

  missingAdmissibleMorphismClass :
    NoNaturalStateSelectionMissingPrimitive

  missingStateSpaceFunctor :
    NoNaturalStateSelectionMissingPrimitive

  missingNaturalitySquare :
    NoNaturalStateSelectionMissingPrimitive

  missingGlobalNonexistenceProof :
    NoNaturalStateSelectionMissingPrimitive

  missingCornerEmbeddingLiftsToAQFTCategory :
    NoNaturalStateSelectionMissingPrimitive

canonicalNoNaturalStateSelectionMissingPrimitives :
  List NoNaturalStateSelectionMissingPrimitive
canonicalNoNaturalStateSelectionMissingPrimitives =
  missingLocalAlgebraCategory
  ∷ missingAdmissibleMorphismClass
  ∷ missingStateSpaceFunctor
  ∷ missingNaturalitySquare
  ∷ missingGlobalNonexistenceProof
  ∷ missingCornerEmbeddingLiftsToAQFTCategory
  ∷ []

data CornerEmbeddingArgumentStep : Set where
  finiteMatrixCornerSelected :
    CornerEmbeddingArgumentStep

  cornerEmbeddingIntoLocalAlgebraRequired :
    CornerEmbeddingArgumentStep

  embeddedStatesExtendAlongAdmissibleMorphisms :
    CornerEmbeddingArgumentStep

  observableSeparationSurvivesEmbedding :
    CornerEmbeddingArgumentStep

  naturalitySquareForEveryEmbeddingRequired :
    CornerEmbeddingArgumentStep

canonicalCornerEmbeddingArgumentSteps :
  List CornerEmbeddingArgumentStep
canonicalCornerEmbeddingArgumentSteps =
  finiteMatrixCornerSelected
  ∷ cornerEmbeddingIntoLocalAlgebraRequired
  ∷ embeddedStatesExtendAlongAdmissibleMorphisms
  ∷ observableSeparationSurvivesEmbedding
  ∷ naturalitySquareForEveryEmbeddingRequired
  ∷ []

record CornerEmbeddingNoNaturalStateArgumentSurface : Setω where
  field
    status :
      AdapterIrreducibilityStatus

    target :
      AdapterIrreducibilityTarget

    targetIsBornState :
      target ≡ bornStateIrreducibility

    toyCornerWitness :
      ToyMatrixCornerStateWitness

    argumentSteps :
      List CornerEmbeddingArgumentStep

    argumentStepsAreCanonical :
      argumentSteps
      ≡
      canonicalCornerEmbeddingArgumentSteps

    cornerEmbeddingShape :
      String

    cornerEmbeddingShape-v :
      cornerEmbeddingShape
      ≡
      "embed-a-finite-M2C-corner-into-each-admissible-local-algebra-and-use-separated-states-to-obstruct-a-natural-canonical-state"

    completeArgumentSurfaceRecorded :
      Bool

    completeArgumentSurfaceRecordedIsTrue :
      completeArgumentSurfaceRecorded ≡ true

    liftsToGlobalAQFTTheorem :
      Bool

    liftsToGlobalAQFTTheoremIsFalse :
      liftsToGlobalAQFTTheorem ≡ false

    noNaturalStateTheoremPromoted :
      Bool

    noNaturalStateTheoremPromotedIsFalse :
      noNaturalStateTheoremPromoted ≡ false

    authorityStillBlocked :
      NoNaturalStateSelectionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open CornerEmbeddingNoNaturalStateArgumentSurface public

canonicalCornerEmbeddingNoNaturalStateArgumentSurface :
  CornerEmbeddingNoNaturalStateArgumentSurface
canonicalCornerEmbeddingNoNaturalStateArgumentSurface =
  record
    { status =
        noGoTargetsRecordedNoIrreducibilityProof
    ; target =
        bornStateIrreducibility
    ; targetIsBornState =
        refl
    ; toyCornerWitness =
        canonicalToyMatrixCornerStateWitness
    ; argumentSteps =
        canonicalCornerEmbeddingArgumentSteps
    ; argumentStepsAreCanonical =
        refl
    ; cornerEmbeddingShape =
        "embed-a-finite-M2C-corner-into-each-admissible-local-algebra-and-use-separated-states-to-obstruct-a-natural-canonical-state"
    ; cornerEmbeddingShape-v =
        refl
    ; completeArgumentSurfaceRecorded =
        true
    ; completeArgumentSurfaceRecordedIsTrue =
        refl
    ; liftsToGlobalAQFTTheorem =
        false
    ; liftsToGlobalAQFTTheoremIsFalse =
        refl
    ; noNaturalStateTheoremPromoted =
        false
    ; noNaturalStateTheoremPromotedIsFalse =
        refl
    ; authorityStillBlocked =
        λ ()
    ; receiptBoundary =
        "corner-embedding argument surface is now complete as a target recipe"
        ∷ "the finite M2C corner supplies separated states and an observable"
        ∷ "promotion still requires an embedding theorem for every admissible AQFT local algebra and naturality-square contradiction"
        ∷ "NoNaturalStateSelectionAuthorityToken remains constructorless"
        ∷ []
    }

record NoNaturalStateSelectionPrimitiveWitness : Setω where
  field
    target :
      AdapterIrreducibilityTarget

    targetIsBornState :
      target ≡ bornStateIrreducibility

    authorityRequired :
      String

    toyMatrixCornerWitness :
      ToyMatrixCornerStateWitness

    cornerEmbeddingArgumentSurface :
      CornerEmbeddingNoNaturalStateArgumentSurface

    missingPrimitives :
      List NoNaturalStateSelectionMissingPrimitive

    missingPrimitivesAreCanonical :
      missingPrimitives
      ≡
      canonicalNoNaturalStateSelectionMissingPrimitives

    naturalStateSelectionProvedImpossible :
      Bool

    naturalStateSelectionProvedImpossibleIsFalse :
      naturalStateSelectionProvedImpossible ≡ false

    proofAuthorityBlocked :
      NoNaturalStateSelectionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open NoNaturalStateSelectionPrimitiveWitness public

canonicalNoNaturalStateSelectionPrimitiveWitness :
  NoNaturalStateSelectionPrimitiveWitness
canonicalNoNaturalStateSelectionPrimitiveWitness =
  record
    { target =
        bornStateIrreducibility
    ; targetIsBornState =
        refl
    ; authorityRequired =
        "NoNaturalStateSelectionAuthorityToken is constructorless until the AQFT algebra category and naturality no-go proof are supplied"
    ; toyMatrixCornerWitness =
        canonicalToyMatrixCornerStateWitness
    ; cornerEmbeddingArgumentSurface =
        canonicalCornerEmbeddingNoNaturalStateArgumentSurface
    ; missingPrimitives =
        canonicalNoNaturalStateSelectionMissingPrimitives
    ; missingPrimitivesAreCanonical =
        refl
    ; naturalStateSelectionProvedImpossible =
        false
    ; naturalStateSelectionProvedImpossibleIsFalse =
        refl
    ; proofAuthorityBlocked =
        λ ()
    ; receiptBoundary =
        "toy matrix corner shows two states can disagree on one observable"
        ∷ "the toy witness is not the categorical theorem that no natural state selection exists"
        ∷ "promotion remains blocked on category, functor, naturality, and global nonexistence primitives"
        ∷ []
    }

data NoPreferredVacuumMissingPrimitive : Set where
  missingBackgroundCategory :
    NoPreferredVacuumMissingPrimitive

  missingVacuumCandidateFunctor :
    NoPreferredVacuumMissingPrimitive

  missingSymmetryReplacementLaw :
    NoPreferredVacuumMissingPrimitive

  missingSpectrumConditionSubstitute :
    NoPreferredVacuumMissingPrimitive

  missingCurvedBackgroundCountermodel :
    NoPreferredVacuumMissingPrimitive

  missingKillingVectorAnalysisSurface :
    NoPreferredVacuumMissingPrimitive

canonicalNoPreferredVacuumMissingPrimitives :
  List NoPreferredVacuumMissingPrimitive
canonicalNoPreferredVacuumMissingPrimitives =
  missingBackgroundCategory
  ∷ missingVacuumCandidateFunctor
  ∷ missingSymmetryReplacementLaw
  ∷ missingSpectrumConditionSubstitute
  ∷ missingCurvedBackgroundCountermodel
  ∷ missingKillingVectorAnalysisSurface
  ∷ []

data KillingVectorVacuumArgumentStep : Set where
  timelikeKillingVectorRequiredForFrequencySplit :
    KillingVectorVacuumArgumentStep

  noGlobalTimelikeKillingVectorOnGenericBackground :
    KillingVectorVacuumArgumentStep

  positiveFrequencyDecompositionNotFunctorial :
    KillingVectorVacuumArgumentStep

  hadamardOrGNSConditionStillSelectionData :
    KillingVectorVacuumArgumentStep

  minkowskiUniquenessDoesNotTransport :
    KillingVectorVacuumArgumentStep

canonicalKillingVectorVacuumArgumentSteps :
  List KillingVectorVacuumArgumentStep
canonicalKillingVectorVacuumArgumentSteps =
  timelikeKillingVectorRequiredForFrequencySplit
  ∷ noGlobalTimelikeKillingVectorOnGenericBackground
  ∷ positiveFrequencyDecompositionNotFunctorial
  ∷ hadamardOrGNSConditionStillSelectionData
  ∷ minkowskiUniquenessDoesNotTransport
  ∷ []

record KillingVectorNoPreferredVacuumArgumentSurface : Setω where
  field
    status :
      AdapterIrreducibilityStatus

    target :
      AdapterIrreducibilityTarget

    targetIsVacuum :
      target ≡ vacuumSelectionIrreducibility

    vacuumCountermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    argumentSteps :
      List KillingVectorVacuumArgumentStep

    argumentStepsAreCanonical :
      argumentSteps
      ≡
      canonicalKillingVectorVacuumArgumentSteps

    killingVectorShape :
      String

    killingVectorShape-v :
      killingVectorShape
      ≡
      "preferred-vacuum-selection-needs-a-global-timelike-Killing-vector-or-replacement-positive-frequency-structure-not-present-functorially-on-background-varying-QFT"

    completeArgumentSurfaceRecorded :
      Bool

    completeArgumentSurfaceRecordedIsTrue :
      completeArgumentSurfaceRecorded ≡ true

    globalVacuumNoGoTheoremProved :
      Bool

    globalVacuumNoGoTheoremProvedIsFalse :
      globalVacuumNoGoTheoremProved ≡ false

    noPreferredVacuumTheoremPromoted :
      Bool

    noPreferredVacuumTheoremPromotedIsFalse :
      noPreferredVacuumTheoremPromoted ≡ false

    authorityStillBlocked :
      NoPreferredVacuumAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open KillingVectorNoPreferredVacuumArgumentSurface public

record NoPreferredVacuumPrimitiveWitness : Setω where
  field
    target :
      AdapterIrreducibilityTarget

    targetIsVacuum :
      target ≡ vacuumSelectionIrreducibility

    authorityRequired :
      String

    vacuumCountermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    killingVectorArgumentSurface :
      KillingVectorNoPreferredVacuumArgumentSurface

    missingPrimitives :
      List NoPreferredVacuumMissingPrimitive

    missingPrimitivesAreCanonical :
      missingPrimitives
      ≡
      canonicalNoPreferredVacuumMissingPrimitives

    preferredVacuumProvedImpossible :
      Bool

    preferredVacuumProvedImpossibleIsFalse :
      preferredVacuumProvedImpossible ≡ false

    proofAuthorityBlocked :
      NoPreferredVacuumAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open NoPreferredVacuumPrimitiveWitness public

canonicalSignatureCountermodelWitnessSurface :
  AdapterNoGoCountermodelWitnessSurface
canonicalSignatureCountermodelWitnessSurface =
  record
    { target =
        metricSignatureIrreducibility
    ; witnessKind =
        frameSignatureCountermodel
    ; witnessRecordShape =
        twoSignatureReductionRecordShape
    ; witnessShape =
        "two-frame-or-two-metric-signature-reductions-over-same-carrier-data-with-no-internal-preference"
    ; assumptions =
        "same restricted carrier data admits distinct non-equivalent signature reductions"
        ∷ "candidate reductions preserve the currently exposed frame/metric interface"
        ∷ []
    ; caveats =
        "contractible pro-object carrier may collapse the countermodel and must be checked before using this witness"
        ∷ "this witness surface does not replace the B0 formal-disk or G-structure proof"
        ∷ []
    ; proofReady =
        false
    ; proofReadyIsFalse =
        refl
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

canonicalBornStateCountermodelWitnessSurface :
  AdapterNoGoCountermodelWitnessSurface
canonicalBornStateCountermodelWitnessSurface =
  record
    { target =
        bornStateIrreducibility
    ; witnessKind =
        blochBallOrMatrixStateCountermodel
    ; witnessRecordShape =
        twoStateLocalAlgebraRecordShape
    ; witnessShape =
        "Bloch-ball-or-M2C-density-matrix-pair-showing-at-least-two-states-on-one-local-algebra"
    ; assumptions =
        "local algebra admits a simple two-level matrix-state model or equivalent state-space witness"
        ∷ "two selected states yield distinct expectation/Born weights for some observable"
        ∷ []
    ; caveats =
        "simple matrix witnesses are countermodel targets only and do not construct the DASHI AQFT local algebra"
        ∷ "Krein-Milman or extreme-state language requires a locally supplied compact-convex state-space surface"
        ∷ []
    ; proofReady =
        false
    ; proofReadyIsFalse =
        refl
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

canonicalVacuumCountermodelWitnessSurface :
  AdapterNoGoCountermodelWitnessSurface
canonicalVacuumCountermodelWitnessSurface =
  record
    { target =
        vacuumSelectionIrreducibility
    ; witnessKind =
        curvedBackgroundVacuumCountermodel
    ; witnessRecordShape =
        twoVacuumSelectionRecordShape
    ; witnessShape =
        "two-background-or-two-state-vacuum-selection-witness-without-shared-Poincare-spectrum-data"
    ; assumptions =
        "vacuum comparison is made after specifying background geometry or replacement symmetry"
        ∷ "Poincare covariance and positive spectrum are named dependencies, not implicit defaults"
        ∷ []
    ; caveats =
        "Minkowski vacuum uniqueness cannot be transported to curved or background-free settings without an explicit substitute"
        ∷ "this witness surface does not supply Poincare covariance, spectrum condition, or Hadamard/GNS selection"
        ∷ []
    ; proofReady =
        false
    ; proofReadyIsFalse =
        refl
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

canonicalKillingVectorNoPreferredVacuumArgumentSurface :
  KillingVectorNoPreferredVacuumArgumentSurface
canonicalKillingVectorNoPreferredVacuumArgumentSurface =
  record
    { status =
        noGoTargetsRecordedNoIrreducibilityProof
    ; target =
        vacuumSelectionIrreducibility
    ; targetIsVacuum =
        refl
    ; vacuumCountermodelWitness =
        canonicalVacuumCountermodelWitnessSurface
    ; argumentSteps =
        canonicalKillingVectorVacuumArgumentSteps
    ; argumentStepsAreCanonical =
        refl
    ; killingVectorShape =
        "preferred-vacuum-selection-needs-a-global-timelike-Killing-vector-or-replacement-positive-frequency-structure-not-present-functorially-on-background-varying-QFT"
    ; killingVectorShape-v =
        refl
    ; completeArgumentSurfaceRecorded =
        true
    ; completeArgumentSurfaceRecordedIsTrue =
        refl
    ; globalVacuumNoGoTheoremProved =
        false
    ; globalVacuumNoGoTheoremProvedIsFalse =
        refl
    ; noPreferredVacuumTheoremPromoted =
        false
    ; noPreferredVacuumTheoremPromotedIsFalse =
        refl
    ; authorityStillBlocked =
        λ ()
    ; receiptBoundary =
        "Killing-vector argument surface is now complete as a target recipe"
        ∷ "Minkowski uniqueness depends on a global timelike symmetry and positive-frequency split"
        ∷ "generic curved/background-varying QFT lacks a functorial replacement with the required spectrum condition"
        ∷ "Hadamard or GNS choices remain selection data rather than a canonical vacuum theorem"
        ∷ "NoPreferredVacuumAuthorityToken remains constructorless"
        ∷ []
    }

canonicalNoPreferredVacuumPrimitiveWitness :
  NoPreferredVacuumPrimitiveWitness
canonicalNoPreferredVacuumPrimitiveWitness =
  record
    { target =
        vacuumSelectionIrreducibility
    ; targetIsVacuum =
        refl
    ; authorityRequired =
        "NoPreferredVacuumAuthorityToken is constructorless until background, symmetry, spectrum, and countermodel primitives are supplied"
    ; vacuumCountermodelWitness =
        canonicalVacuumCountermodelWitnessSurface
    ; killingVectorArgumentSurface =
        canonicalKillingVectorNoPreferredVacuumArgumentSurface
    ; missingPrimitives =
        canonicalNoPreferredVacuumMissingPrimitives
    ; missingPrimitivesAreCanonical =
        refl
    ; preferredVacuumProvedImpossible =
        false
    ; preferredVacuumProvedImpossibleIsFalse =
        refl
    ; proofAuthorityBlocked =
        λ ()
    ; receiptBoundary =
        "vacuum uniqueness is not transported outside its symmetry and spectrum hypotheses"
        ∷ "this surface records the no-preferred-vacuum theorem shape but does not prove it"
        ∷ "promotion remains blocked on explicit background category, vacuum functor, replacement symmetry, and spectrum-condition substitute"
        ∷ []
    }

canonicalCouplingCountermodelWitnessSurface :
  AdapterNoGoCountermodelWitnessSurface
canonicalCouplingCountermodelWitnessSurface =
  record
    { target =
        couplingConstantIrreducibility
    ; witnessKind =
        gaugeNormalisationCountermodel
    ; witnessRecordShape =
        gaugeFactorRescalingRecordShape
    ; witnessShape =
        "independent-gauge-factor-normalisation-rescaling-witness-with-no-canonical-coupling-ratio"
    ; assumptions =
        "gauge factors are compared before a unified embedding and normalisation receipt is supplied"
        ∷ "scale running and threshold conventions are not fixed by the local carrier alone"
        ∷ []
    ; caveats =
        "a GUTEmbeddingReceipt can change the boundary by supplying unified group embedding and normalisation data"
        ∷ "this witness surface does not disprove any specific GUT model or construct coupling unification"
        ∷ []
    ; proofReady =
        false
    ; proofReadyIsFalse =
        refl
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

record NoNaturalStateSelectionTheoremTarget : Setω where
  field
    target :
      AdapterIrreducibilityTarget

    targetIsBornState :
      target ≡ bornStateIrreducibility

    theoremShape :
      String

    theoremShape-v :
      theoremShape
      ≡
      "target-no-star-algebraically-natural-canonical-state-assignment-for-AQFT-local-algebras"

    formalisationBoundary :
      List String

    countermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    primitiveWitness :
      NoNaturalStateSelectionPrimitiveWitness

    cornerEmbeddingArgumentSurface :
      CornerEmbeddingNoNaturalStateArgumentSurface

    theoremFormalized :
      Bool

    theoremFormalizedIsFalse :
      theoremFormalized ≡ false

    noGoProved :
      Bool

    noGoProvedIsFalse :
      noGoProved ≡ false

open NoNaturalStateSelectionTheoremTarget public

canonicalNoNaturalStateSelectionTheoremTarget :
  NoNaturalStateSelectionTheoremTarget
canonicalNoNaturalStateSelectionTheoremTarget =
  record
    { target =
        bornStateIrreducibility
    ; targetIsBornState =
        refl
    ; theoremShape =
        "target-no-star-algebraically-natural-canonical-state-assignment-for-AQFT-local-algebras"
    ; theoremShape-v =
        refl
    ; formalisationBoundary =
        "define the category of AQFT local algebras and admissible embeddings"
        ∷ "define natural state assignment as a natural transformation into state spaces"
        ∷ "prove nonexistence or supply a typed counterexample within that category"
        ∷ []
    ; countermodelWitness =
        canonicalBornStateCountermodelWitnessSurface
    ; primitiveWitness =
        canonicalNoNaturalStateSelectionPrimitiveWitness
    ; cornerEmbeddingArgumentSurface =
        canonicalCornerEmbeddingNoNaturalStateArgumentSurface
    ; theoremFormalized =
        false
    ; theoremFormalizedIsFalse =
        refl
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

record NoPreferredVacuumTheoremTarget : Setω where
  field
    target :
      AdapterIrreducibilityTarget

    targetIsVacuum :
      target ≡ vacuumSelectionIrreducibility

    theoremShape :
      String

    theoremShape-v :
      theoremShape
      ≡
      "target-no-canonical-vacuum-selection-for-background-varying-locally-covariant-QFT"

    formalisationBoundary :
      List String

    countermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    primitiveWitness :
      NoPreferredVacuumPrimitiveWitness

    killingVectorArgumentSurface :
      KillingVectorNoPreferredVacuumArgumentSurface

    theoremFormalized :
      Bool

    theoremFormalizedIsFalse :
      theoremFormalized ≡ false

    noGoProved :
      Bool

    noGoProvedIsFalse :
      noGoProved ≡ false

open NoPreferredVacuumTheoremTarget public

canonicalNoPreferredVacuumTheoremTarget :
  NoPreferredVacuumTheoremTarget
canonicalNoPreferredVacuumTheoremTarget =
  record
    { target =
        vacuumSelectionIrreducibility
    ; targetIsVacuum =
        refl
    ; theoremShape =
        "target-no-canonical-vacuum-selection-for-background-varying-locally-covariant-QFT"
    ; theoremShape-v =
        refl
    ; formalisationBoundary =
        "define the background category and admissible spacetime morphisms"
        ∷ "define vacuum candidates as a functor or section over background-dependent state spaces"
        ∷ "prove no preferred section exists without extra symmetry, spectrum, or Hadamard/GNS authority"
        ∷ []
    ; countermodelWitness =
        canonicalVacuumCountermodelWitnessSurface
    ; primitiveWitness =
        canonicalNoPreferredVacuumPrimitiveWitness
    ; killingVectorArgumentSurface =
        canonicalKillingVectorNoPreferredVacuumArgumentSurface
    ; theoremFormalized =
        false
    ; theoremFormalizedIsFalse =
        refl
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

data AdapterSelectionNoGoReceiptStatus : Set where
  selectionNoGoReceiptSurfaceRecordedNoAuthority :
    AdapterSelectionNoGoReceiptStatus

  selectionNoGoReceiptCompleteModuloAuthorityBoundary :
    AdapterSelectionNoGoReceiptStatus

data MatrixCornerEmbeddingWitness : Set where
  upperLeftCornerEmbeddingMnToM2n :
    MatrixCornerEmbeddingWitness

  lowerRightCornerEmbeddingMnToM2n :
    MatrixCornerEmbeddingWitness

data MatrixCornerProjectionWitness : Set where
  upperLeftComplementaryProjection :
    MatrixCornerProjectionWitness

  lowerRightComplementaryProjection :
    MatrixCornerProjectionWitness

data FaithfulStateContradictionWitness : Set where
  faithfulStateCannotVanishOnBothComplementaryCorners :
    FaithfulStateContradictionWitness

data StrengthenedNoNaturalStateSelectionStep : Set where
  chooseSimpleFiniteMatrixAlgebraMn :
    StrengthenedNoNaturalStateSelectionStep

  compareUpperAndLowerCornerEmbeddingsIntoM2n :
    StrengthenedNoNaturalStateSelectionStep

  naturalityForcesSameStateOnM2n :
    StrengthenedNoNaturalStateSelectionStep

  pushedStatesAreSupportedOnComplementaryCorners :
    StrengthenedNoNaturalStateSelectionStep

  faithfulnessContradictsVanishingOnComplementaryProjection :
    StrengthenedNoNaturalStateSelectionStep

canonicalStrengthenedNoNaturalStateSelectionSteps :
  List StrengthenedNoNaturalStateSelectionStep
canonicalStrengthenedNoNaturalStateSelectionSteps =
  chooseSimpleFiniteMatrixAlgebraMn
  ∷ compareUpperAndLowerCornerEmbeddingsIntoM2n
  ∷ naturalityForcesSameStateOnM2n
  ∷ pushedStatesAreSupportedOnComplementaryCorners
  ∷ faithfulnessContradictsVanishingOnComplementaryProjection
  ∷ []

record StrengthenedNoNaturalStateSelectionCategoricalReceipt : Setω where
  field
    status :
      AdapterSelectionNoGoReceiptStatus

    target :
      AdapterIrreducibilityTarget

    targetIsBornState :
      target ≡ bornStateIrreducibility

    upperCornerEmbedding :
      MatrixCornerEmbeddingWitness

    upperCornerEmbedding-v :
      upperCornerEmbedding ≡ upperLeftCornerEmbeddingMnToM2n

    lowerCornerEmbedding :
      MatrixCornerEmbeddingWitness

    lowerCornerEmbedding-v :
      lowerCornerEmbedding ≡ lowerRightCornerEmbeddingMnToM2n

    upperProjection :
      MatrixCornerProjectionWitness

    upperProjection-v :
      upperProjection ≡ upperLeftComplementaryProjection

    lowerProjection :
      MatrixCornerProjectionWitness

    lowerProjection-v :
      lowerProjection ≡ lowerRightComplementaryProjection

    contradictionWitness :
      FaithfulStateContradictionWitness

    contradictionWitness-v :
      contradictionWitness
      ≡
      faithfulStateCannotVanishOnBothComplementaryCorners

    proofSteps :
      List StrengthenedNoNaturalStateSelectionStep

    proofStepsAreCanonical :
      proofSteps
      ≡
      canonicalStrengthenedNoNaturalStateSelectionSteps

    theoremShape :
      String

    theoremShape-v :
      theoremShape
      ≡
      "no-functorial-faithful-state-selection-natural-for-all-unital-injective-star-monomorphisms-by-upper-lower-corner-embedding-contradiction"

    receiptSurfaceComplete :
      Bool

    receiptSurfaceCompleteIsTrue :
      receiptSurfaceComplete ≡ true

    authorityBoundaryStillHonest :
      NoNaturalStateSelectionAuthorityToken →
      ⊥

    fullyInternalAQFTCategoryTheoremPromoted :
      Bool

    fullyInternalAQFTCategoryTheoremPromotedIsFalse :
      fullyInternalAQFTCategoryTheoremPromoted ≡ false

    receiptBoundary :
      List String

open StrengthenedNoNaturalStateSelectionCategoricalReceipt public

canonicalStrengthenedNoNaturalStateSelectionCategoricalReceipt :
  StrengthenedNoNaturalStateSelectionCategoricalReceipt
canonicalStrengthenedNoNaturalStateSelectionCategoricalReceipt =
  record
    { status =
        selectionNoGoReceiptCompleteModuloAuthorityBoundary
    ; target =
        bornStateIrreducibility
    ; targetIsBornState =
        refl
    ; upperCornerEmbedding =
        upperLeftCornerEmbeddingMnToM2n
    ; upperCornerEmbedding-v =
        refl
    ; lowerCornerEmbedding =
        lowerRightCornerEmbeddingMnToM2n
    ; lowerCornerEmbedding-v =
        refl
    ; upperProjection =
        upperLeftComplementaryProjection
    ; upperProjection-v =
        refl
    ; lowerProjection =
        lowerRightComplementaryProjection
    ; lowerProjection-v =
        refl
    ; contradictionWitness =
        faithfulStateCannotVanishOnBothComplementaryCorners
    ; contradictionWitness-v =
        refl
    ; proofSteps =
        canonicalStrengthenedNoNaturalStateSelectionSteps
    ; proofStepsAreCanonical =
        refl
    ; theoremShape =
        "no-functorial-faithful-state-selection-natural-for-all-unital-injective-star-monomorphisms-by-upper-lower-corner-embedding-contradiction"
    ; theoremShape-v =
        refl
    ; receiptSurfaceComplete =
        true
    ; receiptSurfaceCompleteIsTrue =
        refl
    ; authorityBoundaryStillHonest =
        λ ()
    ; fullyInternalAQFTCategoryTheoremPromoted =
        false
    ; fullyInternalAQFTCategoryTheoremPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Assume a natural faithful state assignment on unital injective C*-algebra morphisms"
        ∷ "upper-left and lower-right embeddings Mn(C) -> M2n(C) force the same selected state on M2n(C)"
        ∷ "the two pushforwards are supported on complementary matrix corners"
        ∷ "faithfulness forbids a state from vanishing on both complementary nonzero projections"
        ∷ "the categorical no-go receipt is complete at surface level; the project-local AQFT category theorem remains guarded by the constructorless authority token"
        ∷ []
    }

data ExplicitVacuumCountermodel : Set where
  unruhRindlerMinkowskiCountermodel :
    ExplicitVacuumCountermodel

  deSitterAlphaVacuaMultiplicityCountermodel :
    ExplicitVacuumCountermodel

data ExplicitNoPreferredVacuumStep : Set where
  compareMinkowskiAndRindlerGroundStates :
    ExplicitNoPreferredVacuumStep

  unruhKMSRelationShowsObserverDependence :
    ExplicitNoPreferredVacuumStep

  deSitterHasBunchDaviesAndAlphaVacua :
    ExplicitNoPreferredVacuumStep

  invariantVacuaCanStillBeMultiple :
    ExplicitNoPreferredVacuumStep

  canonicalVacuumRequiresExtraEmpiricalSelection :
    ExplicitNoPreferredVacuumStep

canonicalExplicitNoPreferredVacuumSteps :
  List ExplicitNoPreferredVacuumStep
canonicalExplicitNoPreferredVacuumSteps =
  compareMinkowskiAndRindlerGroundStates
  ∷ unruhKMSRelationShowsObserverDependence
  ∷ deSitterHasBunchDaviesAndAlphaVacua
  ∷ invariantVacuaCanStillBeMultiple
  ∷ canonicalVacuumRequiresExtraEmpiricalSelection
  ∷ []

record ExplicitNoPreferredVacuumCountermodelReceipt : Setω where
  field
    status :
      AdapterSelectionNoGoReceiptStatus

    target :
      AdapterIrreducibilityTarget

    targetIsVacuum :
      target ≡ vacuumSelectionIrreducibility

    unruhCountermodel :
      ExplicitVacuumCountermodel

    unruhCountermodel-v :
      unruhCountermodel ≡ unruhRindlerMinkowskiCountermodel

    alphaVacuaCountermodel :
      ExplicitVacuumCountermodel

    alphaVacuaCountermodel-v :
      alphaVacuaCountermodel
      ≡
      deSitterAlphaVacuaMultiplicityCountermodel

    proofSteps :
      List ExplicitNoPreferredVacuumStep

    proofStepsAreCanonical :
      proofSteps
      ≡
      canonicalExplicitNoPreferredVacuumSteps

    theoremShape :
      String

    theoremShape-v :
      theoremShape
      ≡
      "no-background-independent-preferred-vacuum-selection-because-Unruh-Rindler-and-de-Sitter-alpha-vacua-give-explicit-nonunique-natural-candidates"

    receiptSurfaceComplete :
      Bool

    receiptSurfaceCompleteIsTrue :
      receiptSurfaceComplete ≡ true

    authorityBoundaryStillHonest :
      NoPreferredVacuumAuthorityToken →
      ⊥

    fullyInternalBackgroundCategoryTheoremPromoted :
      Bool

    fullyInternalBackgroundCategoryTheoremPromotedIsFalse :
      fullyInternalBackgroundCategoryTheoremPromoted ≡ false

    receiptBoundary :
      List String

open ExplicitNoPreferredVacuumCountermodelReceipt public

canonicalExplicitNoPreferredVacuumCountermodelReceipt :
  ExplicitNoPreferredVacuumCountermodelReceipt
canonicalExplicitNoPreferredVacuumCountermodelReceipt =
  record
    { status =
        selectionNoGoReceiptCompleteModuloAuthorityBoundary
    ; target =
        vacuumSelectionIrreducibility
    ; targetIsVacuum =
        refl
    ; unruhCountermodel =
        unruhRindlerMinkowskiCountermodel
    ; unruhCountermodel-v =
        refl
    ; alphaVacuaCountermodel =
        deSitterAlphaVacuaMultiplicityCountermodel
    ; alphaVacuaCountermodel-v =
        refl
    ; proofSteps =
        canonicalExplicitNoPreferredVacuumSteps
    ; proofStepsAreCanonical =
        refl
    ; theoremShape =
        "no-background-independent-preferred-vacuum-selection-because-Unruh-Rindler-and-de-Sitter-alpha-vacua-give-explicit-nonunique-natural-candidates"
    ; theoremShape-v =
        refl
    ; receiptSurfaceComplete =
        true
    ; receiptSurfaceCompleteIsTrue =
        refl
    ; authorityBoundaryStillHonest =
        λ ()
    ; fullyInternalBackgroundCategoryTheoremPromoted =
        false
    ; fullyInternalBackgroundCategoryTheoremPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Minkowski and Rindler observers induce inequivalent ground/KMS descriptions on the same field algebra"
        ∷ "the Unruh relation makes vacuum selection observer- and dynamics-dependent rather than algebraically canonical"
        ∷ "de Sitter alpha-vacua give multiple invariant candidate vacua, so symmetry invariance alone does not select one"
        ∷ "the no-preferred-vacuum receipt is complete at countermodel-surface level; the local background-category theorem remains guarded by the constructorless authority token"
        ∷ []
    }

record Adapter2IrreducibilityCompletedReceiptSurface : Setω where
  field
    status :
      AdapterSelectionNoGoReceiptStatus

    noNaturalStateSelectionReceipt :
      StrengthenedNoNaturalStateSelectionCategoricalReceipt

    noPreferredVacuumReceipt :
      ExplicitNoPreferredVacuumCountermodelReceipt

    bornStateTarget :
      AdapterIrreducibilityTarget

    bornStateTargetIsBornState :
      bornStateTarget ≡ bornStateIrreducibility

    vacuumTarget :
      AdapterIrreducibilityTarget

    vacuumTargetIsVacuum :
      vacuumTarget ≡ vacuumSelectionIrreducibility

    adapter2IrreducibilityCompleteAtReceiptSurface :
      Bool

    adapter2IrreducibilityCompleteAtReceiptSurfaceIsTrue :
      adapter2IrreducibilityCompleteAtReceiptSurface ≡ true

    fullyInternalPromotionClaimed :
      Bool

    fullyInternalPromotionClaimedIsFalse :
      fullyInternalPromotionClaimed ≡ false

    receiptBoundary :
      List String

open Adapter2IrreducibilityCompletedReceiptSurface public

canonicalAdapter2IrreducibilityCompletedReceiptSurface :
  Adapter2IrreducibilityCompletedReceiptSurface
canonicalAdapter2IrreducibilityCompletedReceiptSurface =
  record
    { status =
        selectionNoGoReceiptCompleteModuloAuthorityBoundary
    ; noNaturalStateSelectionReceipt =
        canonicalStrengthenedNoNaturalStateSelectionCategoricalReceipt
    ; noPreferredVacuumReceipt =
        canonicalExplicitNoPreferredVacuumCountermodelReceipt
    ; bornStateTarget =
        bornStateIrreducibility
    ; bornStateTargetIsBornState =
        refl
    ; vacuumTarget =
        vacuumSelectionIrreducibility
    ; vacuumTargetIsVacuum =
        refl
    ; adapter2IrreducibilityCompleteAtReceiptSurface =
        true
    ; adapter2IrreducibilityCompleteAtReceiptSurfaceIsTrue =
        refl
    ; fullyInternalPromotionClaimed =
        false
    ; fullyInternalPromotionClaimedIsFalse =
        refl
    ; receiptBoundary =
        "Adapter2 irreducibility is complete at receipt-surface level: selected states and selected vacua are not naturally determined by the algebra/background interface alone"
        ∷ "the no-natural-state part uses the Mn -> M2n upper/lower corner contradiction for faithful natural selections"
        ∷ "the no-preferred-vacuum part uses Unruh/Rindler and de Sitter alpha-vacua countermodels"
        ∷ "project-local authority tokens remain constructorless, so this does not pretend that every category primitive has been formalised internally"
        ∷ []
    }

record NoNaturalStateSelectionReceiptSurface : Setω where
  field
    status :
      AdapterSelectionNoGoReceiptStatus

    theoremTarget :
      NoNaturalStateSelectionTheoremTarget

    primitiveWitness :
      NoNaturalStateSelectionPrimitiveWitness

    cornerEmbeddingArgumentSurface :
      CornerEmbeddingNoNaturalStateArgumentSurface

    strengthenedCategoricalReceipt :
      StrengthenedNoNaturalStateSelectionCategoricalReceipt

    authorityBoundary :
      String

    authorityBoundary-v :
      authorityBoundary
      ≡
      "NoNaturalStateSelectionAuthorityToken-remains-constructorless-until-AQFT-local-algebra-category-state-functor-naturality-and-global-nonexistence-proof-are-supplied"

    toyWitnessBoundary :
      String

    toyWitnessBoundary-v :
      toyWitnessBoundary
      ≡
      "ToyMatrixCornerStateWitness-separates-two-states-but-does-not-prove-categorical-no-natural-state-selection"

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    receiptSurfaceComplete :
      Bool

    receiptSurfaceCompleteIsTrue :
      receiptSurfaceComplete ≡ true

    noPromotionWithoutAuthority :
      NoNaturalStateSelectionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open NoNaturalStateSelectionReceiptSurface public

canonicalNoNaturalStateSelectionReceiptSurface :
  NoNaturalStateSelectionReceiptSurface
canonicalNoNaturalStateSelectionReceiptSurface =
  record
    { status =
        selectionNoGoReceiptSurfaceRecordedNoAuthority
    ; theoremTarget =
        canonicalNoNaturalStateSelectionTheoremTarget
    ; primitiveWitness =
        canonicalNoNaturalStateSelectionPrimitiveWitness
    ; cornerEmbeddingArgumentSurface =
        canonicalCornerEmbeddingNoNaturalStateArgumentSurface
    ; strengthenedCategoricalReceipt =
        canonicalStrengthenedNoNaturalStateSelectionCategoricalReceipt
    ; authorityBoundary =
        "NoNaturalStateSelectionAuthorityToken-remains-constructorless-until-AQFT-local-algebra-category-state-functor-naturality-and-global-nonexistence-proof-are-supplied"
    ; authorityBoundary-v =
        refl
    ; toyWitnessBoundary =
        "ToyMatrixCornerStateWitness-separates-two-states-but-does-not-prove-categorical-no-natural-state-selection"
    ; toyWitnessBoundary-v =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; receiptSurfaceComplete =
        true
    ; receiptSurfaceCompleteIsTrue =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "no-natural-state-selection now has a completed categorical receipt using upper/lower corner embeddings Mn(C) -> M2n(C)"
        ∷ "naturality forces identical pushforward states while complementary supports and faithfulness force contradiction"
        ∷ "the project-local AQFT category theorem remains authority-token guarded even though the receipt surface is complete"
        ∷ []
    }

record NoPreferredVacuumReceiptSurface : Setω where
  field
    status :
      AdapterSelectionNoGoReceiptStatus

    theoremTarget :
      NoPreferredVacuumTheoremTarget

    primitiveWitness :
      NoPreferredVacuumPrimitiveWitness

    killingVectorArgumentSurface :
      KillingVectorNoPreferredVacuumArgumentSurface

    explicitCountermodelReceipt :
      ExplicitNoPreferredVacuumCountermodelReceipt

    authorityBoundary :
      String

    authorityBoundary-v :
      authorityBoundary
      ≡
      "NoPreferredVacuumAuthorityToken-remains-constructorless-until-background-category-vacuum-functor-replacement-symmetry-spectrum-substitute-and-countermodel-proof-are-supplied"

    minkowskiBoundary :
      String

    minkowskiBoundary-v :
      minkowskiBoundary
      ≡
      "Minkowski-vacuum-uniqueness-does-not-select-a-preferred-vacuum-across-background-varying-or-curved-spacetime-QFT"

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    receiptSurfaceComplete :
      Bool

    receiptSurfaceCompleteIsTrue :
      receiptSurfaceComplete ≡ true

    noPromotionWithoutAuthority :
      NoPreferredVacuumAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open NoPreferredVacuumReceiptSurface public

canonicalNoPreferredVacuumReceiptSurface :
  NoPreferredVacuumReceiptSurface
canonicalNoPreferredVacuumReceiptSurface =
  record
    { status =
        selectionNoGoReceiptSurfaceRecordedNoAuthority
    ; theoremTarget =
        canonicalNoPreferredVacuumTheoremTarget
    ; primitiveWitness =
        canonicalNoPreferredVacuumPrimitiveWitness
    ; killingVectorArgumentSurface =
        canonicalKillingVectorNoPreferredVacuumArgumentSurface
    ; explicitCountermodelReceipt =
        canonicalExplicitNoPreferredVacuumCountermodelReceipt
    ; authorityBoundary =
        "NoPreferredVacuumAuthorityToken-remains-constructorless-until-background-category-vacuum-functor-replacement-symmetry-spectrum-substitute-and-countermodel-proof-are-supplied"
    ; authorityBoundary-v =
        refl
    ; minkowskiBoundary =
        "Minkowski-vacuum-uniqueness-does-not-select-a-preferred-vacuum-across-background-varying-or-curved-spacetime-QFT"
    ; minkowskiBoundary-v =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; receiptSurfaceComplete =
        true
    ; receiptSurfaceCompleteIsTrue =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "no-preferred-vacuum now has explicit Unruh/Rindler and de Sitter alpha-vacua countermodel receipts"
        ∷ "symmetry and ground-state language do not functorially select one vacuum across observer/background changes"
        ∷ "the local background-category theorem remains authority-token guarded even though the countermodel receipt surface is complete"
        ∷ []
    }

record SignatureIrreducibilityNoGoTarget : Setω where
  field
    target :
      AdapterIrreducibilityTarget

    targetIsSignature :
      target ≡ metricSignatureIrreducibility

    noGoShape :
      String

    noGoShape-v :
      noGoShape
      ≡
      "carrier-frame-data-admits-multiple-signature-reductions-no-structural-preference"

    contractibleProObjectCaveat :
      String

    contractibleProObjectCaveat-v :
      contractibleProObjectCaveat
      ≡
      "if-the-pro-object-carrier-is-contractible-the-signature-choice-may-collapse-and-the-no-go-target-must-be-rechecked"

    openObligations :
      List AdapterIrreducibilityOpenObligation

    countermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    noGoProved :
      Bool

    noGoProvedIsFalse :
      noGoProved ≡ false

open SignatureIrreducibilityNoGoTarget public

canonicalSignatureIrreducibilityNoGoTarget :
  SignatureIrreducibilityNoGoTarget
canonicalSignatureIrreducibilityNoGoTarget =
  record
    { target =
        metricSignatureIrreducibility
    ; targetIsSignature =
        refl
    ; noGoShape =
        "carrier-frame-data-admits-multiple-signature-reductions-no-structural-preference"
    ; noGoShape-v =
        refl
    ; contractibleProObjectCaveat =
        "if-the-pro-object-carrier-is-contractible-the-signature-choice-may-collapse-and-the-no-go-target-must-be-rechecked"
    ; contractibleProObjectCaveat-v =
        refl
    ; openObligations =
        missingSignatureNoPreferredReductionProof
        ∷ missingContractibleProObjectCaveat
        ∷ []
    ; countermodelWitness =
        canonicalSignatureCountermodelWitnessSurface
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

record BornStateIrreducibilityNoGoTarget : Setω where
  field
    target :
      AdapterIrreducibilityTarget

    targetIsBornState :
      target ≡ bornStateIrreducibility

    noGoShape :
      String

    noGoShape-v :
      noGoShape
      ≡
      "state-space-of-local-algebra-is-nonunique-Born-rule-needs-selected-state"

    multipleStatesWitnessTarget :
      String

    multipleStatesWitnessTarget-v :
      multipleStatesWitnessTarget
      ≡
      "construct-at-least-two-states-or-a-nontrivial-extreme-state-space-witness-Krein-Milman-style-before-claiming-nonunique-Born-adapter"

    gleasonNoSelectionBoundary :
      String

    gleasonNoSelectionBoundary-v :
      gleasonNoSelectionBoundary
      ≡
      "Gleason-Busch-fixes-trace-form-from-probability-measure-but-does-not-select-density-matrix-rho"

    noNaturalStateSelectionTarget :
      String

    noNaturalStateSelectionTarget-v :
      noNaturalStateSelectionTarget
      ≡
      "target-no-star-algebraically-natural-canonical-state-assignment-for-AQFT-local-algebras"

    noNaturalStateSelectionTheorem :
      NoNaturalStateSelectionTheoremTarget

    noNaturalStateSelectionPrimitiveWitness :
      NoNaturalStateSelectionPrimitiveWitness

    cornerEmbeddingArgumentSurface :
      CornerEmbeddingNoNaturalStateArgumentSurface

    noNaturalStateSelectionReceipt :
      NoNaturalStateSelectionReceiptSurface

    strengthenedNoNaturalStateSelectionReceipt :
      StrengthenedNoNaturalStateSelectionCategoricalReceipt

    selectedStateAdapterRequired :
      Bool

    selectedStateAdapterRequiredIsTrue :
      selectedStateAdapterRequired ≡ true

    openObligations :
      List AdapterIrreducibilityOpenObligation

    countermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    noGoProved :
      Bool

    noGoProvedIsFalse :
      noGoProved ≡ false

open BornStateIrreducibilityNoGoTarget public

canonicalBornStateIrreducibilityNoGoTarget :
  BornStateIrreducibilityNoGoTarget
canonicalBornStateIrreducibilityNoGoTarget =
  record
    { target =
        bornStateIrreducibility
    ; targetIsBornState =
        refl
    ; noGoShape =
        "state-space-of-local-algebra-is-nonunique-Born-rule-needs-selected-state"
    ; noGoShape-v =
        refl
    ; multipleStatesWitnessTarget =
        "construct-at-least-two-states-or-a-nontrivial-extreme-state-space-witness-Krein-Milman-style-before-claiming-nonunique-Born-adapter"
    ; multipleStatesWitnessTarget-v =
        refl
    ; gleasonNoSelectionBoundary =
        "Gleason-Busch-fixes-trace-form-from-probability-measure-but-does-not-select-density-matrix-rho"
    ; gleasonNoSelectionBoundary-v =
        refl
    ; noNaturalStateSelectionTarget =
        "target-no-star-algebraically-natural-canonical-state-assignment-for-AQFT-local-algebras"
    ; noNaturalStateSelectionTarget-v =
        refl
    ; noNaturalStateSelectionTheorem =
        canonicalNoNaturalStateSelectionTheoremTarget
    ; noNaturalStateSelectionPrimitiveWitness =
        canonicalNoNaturalStateSelectionPrimitiveWitness
    ; cornerEmbeddingArgumentSurface =
        canonicalCornerEmbeddingNoNaturalStateArgumentSurface
    ; noNaturalStateSelectionReceipt =
        canonicalNoNaturalStateSelectionReceiptSurface
    ; strengthenedNoNaturalStateSelectionReceipt =
        canonicalStrengthenedNoNaturalStateSelectionCategoricalReceipt
    ; selectedStateAdapterRequired =
        true
    ; selectedStateAdapterRequiredIsTrue =
        refl
    ; openObligations =
        missingNonUniqueStateSpaceProof
        ∷ missingKreinMilmanMultipleStatesWitness
        ∷ missingAQFTLocalAlgebraCategoryPrimitive
        ∷ missingNaturalStateTransformationPrimitive
        ∷ missingNoNaturalStateSelectionAuthority
        ∷ []
    ; countermodelWitness =
        canonicalBornStateCountermodelWitnessSurface
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

record VacuumIrreducibilityNoGoTarget : Setω where
  field
    target :
      AdapterIrreducibilityTarget

    targetIsVacuum :
      target ≡ vacuumSelectionIrreducibility

    noGoShape :
      String

    noGoShape-v :
      noGoShape
      ≡
      "vacuum-selection-is-conditional-on-metric-symmetry-spectrum-and-spacetime-background"

    poincareDependency :
      String

    poincareDependency-v :
      poincareDependency
      ≡
      "Minkowski-vacuum-uniqueness-requires-Poincare-invariance-or-an-explicit-replacement-symmetry"

    spectrumConditionDependency :
      String

    spectrumConditionDependency-v :
      spectrumConditionDependency
      ≡
      "vacuum-selection-requires-positive-energy-spectrum-condition-or-an-explicit-substitute"

    openObligations :
      List AdapterIrreducibilityOpenObligation

    countermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    noPreferredVacuumPrimitiveWitness :
      NoPreferredVacuumPrimitiveWitness

    noPreferredVacuumTheorem :
      NoPreferredVacuumTheoremTarget

    killingVectorArgumentSurface :
      KillingVectorNoPreferredVacuumArgumentSurface

    noPreferredVacuumReceipt :
      NoPreferredVacuumReceiptSurface

    explicitNoPreferredVacuumCountermodelReceipt :
      ExplicitNoPreferredVacuumCountermodelReceipt

    noGoProved :
      Bool

    noGoProvedIsFalse :
      noGoProved ≡ false

open VacuumIrreducibilityNoGoTarget public

canonicalVacuumIrreducibilityNoGoTarget :
  VacuumIrreducibilityNoGoTarget
canonicalVacuumIrreducibilityNoGoTarget =
  record
    { target =
        vacuumSelectionIrreducibility
    ; targetIsVacuum =
        refl
    ; noGoShape =
        "vacuum-selection-is-conditional-on-metric-symmetry-spectrum-and-spacetime-background"
    ; noGoShape-v =
        refl
    ; poincareDependency =
        "Minkowski-vacuum-uniqueness-requires-Poincare-invariance-or-an-explicit-replacement-symmetry"
    ; poincareDependency-v =
        refl
    ; spectrumConditionDependency =
        "vacuum-selection-requires-positive-energy-spectrum-condition-or-an-explicit-substitute"
    ; spectrumConditionDependency-v =
        refl
    ; openObligations =
        missingCurvedSpacetimeNoPreferredVacuumProof
        ∷ missingPoincareCovarianceDependency
        ∷ missingSpectrumConditionDependency
        ∷ missingNoPreferredVacuumAuthority
        ∷ []
    ; countermodelWitness =
        canonicalVacuumCountermodelWitnessSurface
    ; noPreferredVacuumPrimitiveWitness =
        canonicalNoPreferredVacuumPrimitiveWitness
    ; noPreferredVacuumTheorem =
        canonicalNoPreferredVacuumTheoremTarget
    ; killingVectorArgumentSurface =
        canonicalKillingVectorNoPreferredVacuumArgumentSurface
    ; noPreferredVacuumReceipt =
        canonicalNoPreferredVacuumReceiptSurface
    ; explicitNoPreferredVacuumCountermodelReceipt =
        canonicalExplicitNoPreferredVacuumCountermodelReceipt
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

data YukawaSectorGrammarClassification : Set where
  representationPatternPartiallyDerived :
    YukawaSectorGrammarClassification

  generationCountingStillAdapterBoundary :
    YukawaSectorGrammarClassification

  yukawaMatrixTextureStillEmpirical :
    YukawaSectorGrammarClassification

  absoluteMassScaleIrreducibleAdapterInput :
    YukawaSectorGrammarClassification

data YukawaSectorGrammarObligation : Set where
  missingPrimeLaneRepresentationDerivation :
    YukawaSectorGrammarObligation

  missingThreeGenerationTheorem :
    YukawaSectorGrammarObligation

  missingYukawaTextureDerivation :
    YukawaSectorGrammarObligation

  missingCKMPMNSMixingDerivation :
    YukawaSectorGrammarObligation

  missingHiggsVEVOrAbsoluteScaleAuthority :
    YukawaSectorGrammarObligation

canonicalYukawaSectorGrammarObligations :
  List YukawaSectorGrammarObligation
canonicalYukawaSectorGrammarObligations =
  missingPrimeLaneRepresentationDerivation
  ∷ missingThreeGenerationTheorem
  ∷ missingYukawaTextureDerivation
  ∷ missingCKMPMNSMixingDerivation
  ∷ missingHiggsVEVOrAbsoluteScaleAuthority
  ∷ []

record YukawaSectorPartialDerivationGrammar : Setω where
  field
    status :
      AdapterIrreducibilityStatus

    partialClassification :
      YukawaSectorGrammarClassification

    partialClassificationIsRepresentationPattern :
      partialClassification ≡ representationPatternPartiallyDerived

    absoluteScaleClassification :
      YukawaSectorGrammarClassification

    absoluteScaleClassificationIsIrreducible :
      absoluteScaleClassification ≡ absoluteMassScaleIrreducibleAdapterInput

    grammarShape :
      String

    grammarShape-v :
      grammarShape
      ≡
      "Yukawa-sector-may-partially-derive-representation-texture-patterns-but-absolute-mass-scale-remains-irreducible-until-Higgs-VEV-calibration-and-running-authority-are-supplied"

    openObligations :
      List YukawaSectorGrammarObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalYukawaSectorGrammarObligations

    partialDerivationSurfaceRecorded :
      Bool

    partialDerivationSurfaceRecordedIsTrue :
      partialDerivationSurfaceRecorded ≡ true

    absoluteScaleDerived :
      Bool

    absoluteScaleDerivedIsFalse :
      absoluteScaleDerived ≡ false

    adapter4Promoted :
      Bool

    adapter4PromotedIsFalse :
      adapter4Promoted ≡ false

    receiptBoundary :
      List String

open YukawaSectorPartialDerivationGrammar public

canonicalYukawaSectorPartialDerivationGrammar :
  YukawaSectorPartialDerivationGrammar
canonicalYukawaSectorPartialDerivationGrammar =
  record
    { status =
        noGoTargetsRecordedNoIrreducibilityProof
    ; partialClassification =
        representationPatternPartiallyDerived
    ; partialClassificationIsRepresentationPattern =
        refl
    ; absoluteScaleClassification =
        absoluteMassScaleIrreducibleAdapterInput
    ; absoluteScaleClassificationIsIrreducible =
        refl
    ; grammarShape =
        "Yukawa-sector-may-partially-derive-representation-texture-patterns-but-absolute-mass-scale-remains-irreducible-until-Higgs-VEV-calibration-and-running-authority-are-supplied"
    ; grammarShape-v =
        refl
    ; openObligations =
        canonicalYukawaSectorGrammarObligations
    ; openObligationsAreCanonical =
        refl
    ; partialDerivationSurfaceRecorded =
        true
    ; partialDerivationSurfaceRecordedIsTrue =
        refl
    ; absoluteScaleDerived =
        false
    ; absoluteScaleDerivedIsFalse =
        refl
    ; adapter4Promoted =
        false
    ; adapter4PromotedIsFalse =
        refl
    ; receiptBoundary =
        "Yukawa grammar separates partial representation-pattern derivation from physical absolute-scale selection"
        ∷ "textures, CKM/PMNS angles, neutrino sector, and running remain adapter targets"
        ∷ "absolute fermion mass scale requires Higgs VEV, renormalisation scale, threshold, and calibration authority"
        ∷ "no Adapter4, Standard Model, GRQFT, or TOE promotion follows"
        ∷ []
    }

record CouplingIrreducibilityNoGoTarget : Setω where
  field
    target :
      AdapterIrreducibilityTarget

    targetIsCoupling :
      target ≡ couplingConstantIrreducibility

    noGoShape :
      String

    noGoShape-v :
      noGoShape
      ≡
      "independent-gauge-holonomy-normalisations-have-no-canonical-ratio-without-GUT-receipt"

    gutEmbeddingReceiptBoundary :
      String

    gutEmbeddingReceiptBoundary-v :
      gutEmbeddingReceiptBoundary
      ≡
      "GUTEmbeddingReceipt-must-supply-unified-group-embedding-normalisation-scale-running-and-threshold-boundaries-before-coupling-ratios-can-be-promoted"

    betaFunctionMatterBoundary :
      String

    betaFunctionMatterBoundary-v :
      betaFunctionMatterBoundary
      ≡
      "coupling-ratios-run-by-beta-coefficients-determined-by-gauge-group-and-matter-representation-content"

    matterRepresentationDerivationBoundary :
      String

    matterRepresentationDerivationBoundary-v :
      matterRepresentationDerivationBoundary
      ≡
      "Adapter4-remains-unreduced-until-prime-lane-gauge-assignment-also-derives-SM-matter-representations-Yukawas-and-mixing-data"

    yukawaSectorGrammar :
      YukawaSectorPartialDerivationGrammar

    openObligations :
      List AdapterIrreducibilityOpenObligation

    countermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    noGoProved :
      Bool

    noGoProvedIsFalse :
      noGoProved ≡ false

open CouplingIrreducibilityNoGoTarget public

canonicalCouplingIrreducibilityNoGoTarget :
  CouplingIrreducibilityNoGoTarget
canonicalCouplingIrreducibilityNoGoTarget =
  record
    { target =
        couplingConstantIrreducibility
    ; targetIsCoupling =
        refl
    ; noGoShape =
        "independent-gauge-holonomy-normalisations-have-no-canonical-ratio-without-GUT-receipt"
    ; noGoShape-v =
        refl
    ; gutEmbeddingReceiptBoundary =
        "GUTEmbeddingReceipt-must-supply-unified-group-embedding-normalisation-scale-running-and-threshold-boundaries-before-coupling-ratios-can-be-promoted"
    ; gutEmbeddingReceiptBoundary-v =
        refl
    ; betaFunctionMatterBoundary =
        "coupling-ratios-run-by-beta-coefficients-determined-by-gauge-group-and-matter-representation-content"
    ; betaFunctionMatterBoundary-v =
        refl
    ; matterRepresentationDerivationBoundary =
        "Adapter4-remains-unreduced-until-prime-lane-gauge-assignment-also-derives-SM-matter-representations-Yukawas-and-mixing-data"
    ; matterRepresentationDerivationBoundary-v =
        refl
    ; yukawaSectorGrammar =
        canonicalYukawaSectorPartialDerivationGrammar
    ; openObligations =
        missingNoCanonicalGaugeCouplingRatioProof
        ∷ missingGUTReceiptBoundary
        ∷ missingGaugeNormalisationCountermodel
        ∷ []
    ; countermodelWitness =
        canonicalCouplingCountermodelWitnessSurface
    ; noGoProved =
        false
    ; noGoProvedIsFalse =
        refl
    }

record AdapterIrreducibilityNoGoIndex : Setω where
  field
    status :
      AdapterIrreducibilityStatus

    targets :
      List AdapterIrreducibilityTarget

    targetsAreCanonical :
      targets
      ≡
      canonicalAdapterIrreducibilityTargets

    openObligations :
      List AdapterIrreducibilityOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalAdapterIrreducibilityOpenObligations

    resolvedObligations :
      List AdapterIrreducibilityResolvedObligation

    resolvedObligationsAreCanonical :
      resolvedObligations
      ≡
      canonicalAdapterIrreducibilityResolvedObligations

    authorityBlockedObligations :
      List AdapterIrreducibilityAuthorityBlockedObligation

    authorityBlockedObligationsAreCanonical :
      authorityBlockedObligations
      ≡
      canonicalAdapterIrreducibilityAuthorityBlockedObligations

    signatureTargetSurface :
      SignatureIrreducibilityNoGoTarget

    bornStateTargetSurface :
      BornStateIrreducibilityNoGoTarget

    vacuumTargetSurface :
      VacuumIrreducibilityNoGoTarget

    couplingTargetSurface :
      CouplingIrreducibilityNoGoTarget

    signatureCountermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    bornStateCountermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    noNaturalStateSelectionTheorem :
      NoNaturalStateSelectionTheoremTarget

    noNaturalStateSelectionPrimitiveWitness :
      NoNaturalStateSelectionPrimitiveWitness

    cornerEmbeddingNoNaturalStateArgumentSurface :
      CornerEmbeddingNoNaturalStateArgumentSurface

    noNaturalStateSelectionReceipt :
      NoNaturalStateSelectionReceiptSurface

    strengthenedNoNaturalStateSelectionReceipt :
      StrengthenedNoNaturalStateSelectionCategoricalReceipt

    vacuumCountermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    noPreferredVacuumPrimitiveWitness :
      NoPreferredVacuumPrimitiveWitness

    noPreferredVacuumTheorem :
      NoPreferredVacuumTheoremTarget

    killingVectorNoPreferredVacuumArgumentSurface :
      KillingVectorNoPreferredVacuumArgumentSurface

    noPreferredVacuumReceipt :
      NoPreferredVacuumReceiptSurface

    explicitNoPreferredVacuumCountermodelReceipt :
      ExplicitNoPreferredVacuumCountermodelReceipt

    adapter2CompletedReceiptSurface :
      Adapter2IrreducibilityCompletedReceiptSurface

    couplingCountermodelWitness :
      AdapterNoGoCountermodelWitnessSurface

    yukawaSectorPartialDerivationGrammar :
      YukawaSectorPartialDerivationGrammar

    signatureNoGoShape :
      String

    signatureNoGoShape-v :
      signatureNoGoShape
      ≡
      "carrier-frame-data-admits-multiple-signature-reductions-no-structural-preference"

    bornRuleNoGoShape :
      String

    bornRuleNoGoShape-v :
      bornRuleNoGoShape
      ≡
      "state-space-of-local-algebra-is-nonunique-Born-rule-needs-selected-state"

    vacuumNoGoShape :
      String

    vacuumNoGoShape-v :
      vacuumNoGoShape
      ≡
      "vacuum-selection-is-conditional-on-metric-symmetry-spectrum-and-spacetime-background"

    couplingNoGoShape :
      String

    couplingNoGoShape-v :
      couplingNoGoShape
      ≡
      "independent-gauge-holonomy-normalisations-have-no-canonical-ratio-without-GUT-receipt"

    irreducibilityProved :
      Bool

    irreducibilityProvedIsFalse :
      irreducibilityProved ≡ false

    adapter2IrreducibilityCompleteAtReceiptSurface :
      Bool

    adapter2IrreducibilityCompleteAtReceiptSurfaceIsTrue :
      adapter2IrreducibilityCompleteAtReceiptSurface ≡ true

    noPromotionWithoutAuthority :
      AdapterIrreducibilityPromotionAuthorityToken →
      ⊥

    noGoBoundary :
      List String

open AdapterIrreducibilityNoGoIndex public

canonicalAdapterIrreducibilityNoGoIndex :
  AdapterIrreducibilityNoGoIndex
canonicalAdapterIrreducibilityNoGoIndex =
  record
    { status =
        noGoTargetsRecordedNoIrreducibilityProof
    ; targets =
        canonicalAdapterIrreducibilityTargets
    ; targetsAreCanonical =
        refl
    ; openObligations =
        canonicalAdapterIrreducibilityOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; resolvedObligations =
        canonicalAdapterIrreducibilityResolvedObligations
    ; resolvedObligationsAreCanonical =
        refl
    ; authorityBlockedObligations =
        canonicalAdapterIrreducibilityAuthorityBlockedObligations
    ; authorityBlockedObligationsAreCanonical =
        refl
    ; signatureTargetSurface =
        canonicalSignatureIrreducibilityNoGoTarget
    ; bornStateTargetSurface =
        canonicalBornStateIrreducibilityNoGoTarget
    ; vacuumTargetSurface =
        canonicalVacuumIrreducibilityNoGoTarget
    ; couplingTargetSurface =
        canonicalCouplingIrreducibilityNoGoTarget
    ; signatureCountermodelWitness =
        canonicalSignatureCountermodelWitnessSurface
    ; bornStateCountermodelWitness =
        canonicalBornStateCountermodelWitnessSurface
    ; noNaturalStateSelectionTheorem =
        canonicalNoNaturalStateSelectionTheoremTarget
    ; noNaturalStateSelectionPrimitiveWitness =
        canonicalNoNaturalStateSelectionPrimitiveWitness
    ; cornerEmbeddingNoNaturalStateArgumentSurface =
        canonicalCornerEmbeddingNoNaturalStateArgumentSurface
    ; noNaturalStateSelectionReceipt =
        canonicalNoNaturalStateSelectionReceiptSurface
    ; strengthenedNoNaturalStateSelectionReceipt =
        canonicalStrengthenedNoNaturalStateSelectionCategoricalReceipt
    ; vacuumCountermodelWitness =
        canonicalVacuumCountermodelWitnessSurface
    ; noPreferredVacuumPrimitiveWitness =
        canonicalNoPreferredVacuumPrimitiveWitness
    ; noPreferredVacuumTheorem =
        canonicalNoPreferredVacuumTheoremTarget
    ; killingVectorNoPreferredVacuumArgumentSurface =
        canonicalKillingVectorNoPreferredVacuumArgumentSurface
    ; noPreferredVacuumReceipt =
        canonicalNoPreferredVacuumReceiptSurface
    ; explicitNoPreferredVacuumCountermodelReceipt =
        canonicalExplicitNoPreferredVacuumCountermodelReceipt
    ; adapter2CompletedReceiptSurface =
        canonicalAdapter2IrreducibilityCompletedReceiptSurface
    ; couplingCountermodelWitness =
        canonicalCouplingCountermodelWitnessSurface
    ; yukawaSectorPartialDerivationGrammar =
        canonicalYukawaSectorPartialDerivationGrammar
    ; signatureNoGoShape =
        "carrier-frame-data-admits-multiple-signature-reductions-no-structural-preference"
    ; signatureNoGoShape-v =
        refl
    ; bornRuleNoGoShape =
        "state-space-of-local-algebra-is-nonunique-Born-rule-needs-selected-state"
    ; bornRuleNoGoShape-v =
        refl
    ; vacuumNoGoShape =
        "vacuum-selection-is-conditional-on-metric-symmetry-spectrum-and-spacetime-background"
    ; vacuumNoGoShape-v =
        refl
    ; couplingNoGoShape =
        "independent-gauge-holonomy-normalisations-have-no-canonical-ratio-without-GUT-receipt"
    ; couplingNoGoShape-v =
        refl
    ; irreducibilityProved =
        false
    ; irreducibilityProvedIsFalse =
        refl
    ; adapter2IrreducibilityCompleteAtReceiptSurface =
        true
    ; adapter2IrreducibilityCompleteAtReceiptSurfaceIsTrue =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; noGoBoundary =
        "adapter irreducibility is recorded as four no-go theorem targets, not as proved"
        ∷ "signature requires a no-preferred-reduction proof over possible metric signatures"
        ∷ "signature no-go has a contractible pro-object caveat: if the carrier limit is contractible, the target must be rechecked"
        ∷ "Born rule requires a nonunique-state-space proof plus selected-state adapter"
        ∷ "no-natural-state selection is now complete at receipt-surface level by the strengthened Mn -> M2n upper/lower corner contradiction"
        ∷ "missingBlochBallOrMatrixStateWitness is no longer an active blocker because ToyMatrixCornerStateWitness records the finite corner shape"
        ∷ "no-natural-state selection now has a primitive witness record with a toy matrix corner and a categorical faithful-state contradiction receipt, but remains authority-token-blocked for project-local formalisation"
        ∷ "no-natural-state selection now has an explicit non-promoting receipt surface linking the theorem target, primitive witness, and constructorless authority token"
        ∷ "the strengthened corner-embedding argument records upper/lower Mn-to-M2n embeddings, complementary projections, and the faithful-state contradiction"
        ∷ "Born/state no-go requires a multiple-states or Krein-Milman-style extreme-state witness target"
        ∷ "Gleason/Busch fixes the trace-form of a probability assignment but does not select the density matrix"
        ∷ "vacuum selection requires the curved-spacetime no-preferred-vacuum boundary"
        ∷ "missingCountermodelWitnessSurface is no longer an active blocker because signature/Born/vacuum/coupling countermodel surfaces are recorded"
        ∷ "no-preferred-vacuum now has a primitive witness record and explicit Unruh/Rindler plus de Sitter alpha-vacua countermodel receipts, but remains authority-token-blocked on background category, replacement symmetry, and spectrum substitute"
        ∷ "no-preferred-vacuum now has an explicit theorem target and non-promoting receipt surface for background-varying locally covariant QFT"
        ∷ "Adapter2 irreducibility is complete at receipt-surface level while the fully internal background/category authority tokens stay constructorless"
        ∷ "Minkowski vacuum uniqueness depends on Poincare covariance plus a spectrum-condition or explicit substitute"
        ∷ "couplings require a no-canonical-ratio proof unless a GUT receipt is supplied"
        ∷ "coupling ratios also depend on beta-function coefficients and therefore on matter representations, not carrier topology alone"
        ∷ "Yukawa grammar separates partial representation-pattern derivation from irreducible absolute-scale input"
        ∷ "Yukawa, CKM, neutrino-mixing, and axion-scale data remain Adapter4 sub-problems unless prime-lane matter representations and physical scales are derived"
        ∷ "GUTEmbeddingReceipt remains a boundary for unified embedding, normalisation, scale running, and thresholds"
        ∷ "proof-ready countermodel witnesses are now named for signature, Born/state, vacuum, and coupling targets, but each remains unproved"
        ∷ "Born/state witness target may use a Bloch-ball or simple matrix-state pair only as a countermodel surface, not as the constructed DASHI AQFT algebra"
        ∷ "no terminal GRQFT or TOE promotion follows from this index"
        ∷ []
    }
