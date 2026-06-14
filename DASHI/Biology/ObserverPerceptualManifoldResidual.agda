module DASHI.Biology.ObserverPerceptualManifoldResidual where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Observer fibres over a shared latent transport manifold.
------------------------------------------------------------------------

data ObserverSpecies : Set where
  humanObserver : ObserverSpecies
  birdObserver : ObserverSpecies
  batObserver : ObserverSpecies
  octopusObserver : ObserverSpecies
  beeObserver : ObserverSpecies

data PerceptualFibre : Set where
  humanVisionLanguageFibre : PerceptualFibre
  birdMagnetoreceptionFibre : PerceptualFibre
  batEcholocationFibre : PerceptualFibre
  octopusDistributedBodyFibre : PerceptualFibre
  beePolarizedUvMagneticFibre : PerceptualFibre

fibreFor :
  ObserverSpecies →
  PerceptualFibre
fibreFor humanObserver = humanVisionLanguageFibre
fibreFor birdObserver = birdMagnetoreceptionFibre
fibreFor batObserver = batEcholocationFibre
fibreFor octopusObserver = octopusDistributedBodyFibre
fibreFor beeObserver = beePolarizedUvMagneticFibre

allObserverFibres : List PerceptualFibre
allObserverFibres =
  humanVisionLanguageFibre
  ∷ birdMagnetoreceptionFibre
  ∷ batEcholocationFibre
  ∷ octopusDistributedBodyFibre
  ∷ beePolarizedUvMagneticFibre
  ∷ []

data LatentTransportLayer : Set where
  sharedWorldStateLayer : LatentTransportLayer
  physicalSignalTransportLayer : LatentTransportLayer
  receptorInterfaceLayer : LatentTransportLayer
  embodiedSensorimotorLayer : LatentTransportLayer
  behaviorQuotientLayer : LatentTransportLayer

data PerceptualQuotientLayer : Set where
  observerFibreSelectionLayer : PerceptualQuotientLayer
  modalityProjectionLayer : PerceptualQuotientLayer
  embodiedPolicyLayer : PerceptualQuotientLayer
  communicableReportLayer : PerceptualQuotientLayer
  nonPhenomenalBoundaryLayer : PerceptualQuotientLayer

data ProjectionResidualKind : Set where
  sourceFibreLoss : ProjectionResidualKind
  targetFibreOverload : ProjectionResidualKind
  modalityNonCommensurability : ProjectionResidualKind
  behaviorClassUnderdetermination : ProjectionResidualKind
  reportChannelMismatch : ProjectionResidualKind
  noSharedPhenomenalCoordinate : ProjectionResidualKind

data ProjectionDefectKind : Set where
  noFibreIsomorphism : ProjectionDefectKind
  noProjectionRetraction : ProjectionDefectKind
  noCrossSpeciesIdentityMap : ProjectionDefectKind
  noQualiaPreservingFunctor : ProjectionDefectKind
  noFirstPersonTransportWitness : ProjectionDefectKind

data PhenomenalBoundary : Set where
  noFirstPersonInhabitantBoundary : PhenomenalBoundary
  noQualiaClosureBoundary : PhenomenalBoundary
  noPhenomenalIdentityBoundary : PhenomenalBoundary
  noObserverExperienceTransferBoundary : PhenomenalBoundary
  noBehaviorToExperiencePromotionBoundary : PhenomenalBoundary

canonicalTransportLayers : List LatentTransportLayer
canonicalTransportLayers =
  sharedWorldStateLayer
  ∷ physicalSignalTransportLayer
  ∷ receptorInterfaceLayer
  ∷ embodiedSensorimotorLayer
  ∷ behaviorQuotientLayer
  ∷ []

canonicalQuotientLayers : List PerceptualQuotientLayer
canonicalQuotientLayers =
  observerFibreSelectionLayer
  ∷ modalityProjectionLayer
  ∷ embodiedPolicyLayer
  ∷ communicableReportLayer
  ∷ nonPhenomenalBoundaryLayer
  ∷ []

canonicalProjectionResiduals : List ProjectionResidualKind
canonicalProjectionResiduals =
  sourceFibreLoss
  ∷ targetFibreOverload
  ∷ modalityNonCommensurability
  ∷ behaviorClassUnderdetermination
  ∷ reportChannelMismatch
  ∷ noSharedPhenomenalCoordinate
  ∷ []

canonicalProjectionDefects : List ProjectionDefectKind
canonicalProjectionDefects =
  noFibreIsomorphism
  ∷ noProjectionRetraction
  ∷ noCrossSpeciesIdentityMap
  ∷ noQualiaPreservingFunctor
  ∷ noFirstPersonTransportWitness
  ∷ []

canonicalPhenomenalBoundaries : List PhenomenalBoundary
canonicalPhenomenalBoundaries =
  noFirstPersonInhabitantBoundary
  ∷ noQualiaClosureBoundary
  ∷ noPhenomenalIdentityBoundary
  ∷ noObserverExperienceTransferBoundary
  ∷ noBehaviorToExperiencePromotionBoundary
  ∷ []

------------------------------------------------------------------------
-- Transcript and projection-defect boundary aliases.
--
-- These small carriers give the qualitative-transcript PNF lane a stable
-- vocabulary for multi-speaker residuals and blocked phenomenal closure while
-- leaving the richer observer quotient records below as the main structure.

record MultiSpeakerResidual : Set where
  field
    multiSpeakerResidual :
      List ProjectionResidualKind

    multiSpeakerResiduals :
      List ProjectionResidualKind

    multiSpeakerResidualsAreCanonical :
      multiSpeakerResiduals ≡ canonicalProjectionResiduals

    multiSpeakerResidualsPromoted :
      Bool

    multiSpeakerResidualsPromotedIsFalse :
      multiSpeakerResidualsPromoted ≡ false

    multiSpeakerResidualReading :
      String

open MultiSpeakerResidual public

canonicalMultiSpeakerResidual : MultiSpeakerResidual
canonicalMultiSpeakerResidual =
  record
    { multiSpeakerResidual =
        canonicalProjectionResiduals
    ; multiSpeakerResiduals =
        canonicalProjectionResiduals
    ; multiSpeakerResidualsAreCanonical =
        refl
    ; multiSpeakerResidualsPromoted =
        false
    ; multiSpeakerResidualsPromotedIsFalse =
        refl
    ; multiSpeakerResidualReading =
        "Multi-speaker qualitative reports expose comparable residual structure without promoting shared phenomenal identity."
    }

record PerceptualManifoldProjectionDefect : Set where
  field
    perceptualManifoldProjectionDefect :
      List ProjectionDefectKind

    projectionDefectPromoted :
      Bool

    projectionDefectPromotedIsFalse :
      projectionDefectPromoted ≡ false

    projectionDefectReading :
      String

open PerceptualManifoldProjectionDefect public

canonicalPerceptualManifoldProjectionDefect :
  PerceptualManifoldProjectionDefect
canonicalPerceptualManifoldProjectionDefect =
  record
    { perceptualManifoldProjectionDefect =
        canonicalProjectionDefects
    ; projectionDefectPromoted =
        false
    ; projectionDefectPromotedIsFalse =
        refl
    ; projectionDefectReading =
        "Cross-observer translation retains a projection defect instead of promoting a fibre isomorphism or qualia-preserving map."
    }

record BlockedPhenomenalClosure : Set where
  field
    blockedPhenomenalClosure :
      List PhenomenalBoundary

    blockedPhenomenalClosureIsFalse :
      false ≡ false

    phenomenalClosureBlocked :
      Bool

    phenomenalClosureBlockedIsTrue :
      phenomenalClosureBlocked ≡ true

    closureRecoveryPromoted :
      Bool

    closureRecoveryPromotedIsFalse :
      closureRecoveryPromoted ≡ false

    blockedPhenomenalClosureReading :
      String

open BlockedPhenomenalClosure public

canonicalBlockedPhenomenalClosure : BlockedPhenomenalClosure
canonicalBlockedPhenomenalClosure =
  record
    { blockedPhenomenalClosure =
        canonicalPhenomenalBoundaries
    ; blockedPhenomenalClosureIsFalse =
        refl
    ; phenomenalClosureBlocked =
        true
    ; phenomenalClosureBlockedIsTrue =
        refl
    ; closureRecoveryPromoted =
        false
    ; closureRecoveryPromotedIsFalse =
        refl
    ; blockedPhenomenalClosureReading =
        "The observer-manifold quotient can constrain projection structure while phenomenal closure remains blocked."
    }

------------------------------------------------------------------------
-- Shared manifold and observer quotient.
------------------------------------------------------------------------

record SharedLatentTransportManifold : Set₁ where
  field
    LatentState : Set
    PhysicalTrace : Set
    ReceptorState : Set
    SensorimotorState : Set
    BehaviorClass : Set
    TransportReceipt : Set

    latentToPhysicalTrace :
      LatentState →
      PhysicalTrace

    physicalTraceToReceptor :
      PhysicalTrace →
      ReceptorState

    receptorToSensorimotor :
      ReceptorState →
      SensorimotorState

    sensorimotorToBehavior :
      SensorimotorState →
      BehaviorClass

    receiptFor :
      LatentState →
      TransportReceipt

    receiptAdmissible :
      TransportReceipt →
      Set

    transportLayers :
      List LatentTransportLayer

    transportLayersAreCanonical :
      transportLayers ≡ canonicalTransportLayers

    manifoldReading : String

open SharedLatentTransportManifold public

record ObserverPerceptualQuotient
    (manifold : SharedLatentTransportManifold)
    (observer : ObserverSpecies) : Set₁ where
  field
    fibre :
      PerceptualFibre

    fibreMatchesObserver :
      fibre ≡ fibreFor observer

    QuotientState :
      Set

    projectBehavior :
      BehaviorClass manifold →
      QuotientState

    identifyInQuotient :
      QuotientState →
      QuotientState →
      Set

    quotientReceipt :
      QuotientState →
      TransportReceipt manifold

    quotientLayers :
      List PerceptualQuotientLayer

    quotientLayersAreCanonical :
      quotientLayers ≡ canonicalQuotientLayers

    observerProjectionPromoted :
      Bool

    observerProjectionPromotedIsTrue :
      observerProjectionPromoted ≡ true

    directPhenomenalInhabitant :
      Bool

    directPhenomenalInhabitantIsFalse :
      directPhenomenalInhabitant ≡ false

    qualiaClosure :
      Bool

    qualiaClosureIsFalse :
      qualiaClosure ≡ false

    quotientReading :
      String

open ObserverPerceptualQuotient public

canonicalObserverPerceptualQuotient :
  (manifold : SharedLatentTransportManifold) →
  (observer : ObserverSpecies) →
  (QuotientState : Set) →
  (projectBehavior : BehaviorClass manifold → QuotientState) →
  (identifyInQuotient : QuotientState → QuotientState → Set) →
  (quotientReceipt : QuotientState → TransportReceipt manifold) →
  ObserverPerceptualQuotient manifold observer
canonicalObserverPerceptualQuotient
  manifold
  observer
  QuotientState
  projectBehavior
  identifyInQuotient
  quotientReceipt =
  record
    { fibre = fibreFor observer
    ; fibreMatchesObserver = refl
    ; QuotientState = QuotientState
    ; projectBehavior = projectBehavior
    ; identifyInQuotient = identifyInQuotient
    ; quotientReceipt = quotientReceipt
    ; quotientLayers = canonicalQuotientLayers
    ; quotientLayersAreCanonical = refl
    ; observerProjectionPromoted = true
    ; observerProjectionPromotedIsTrue = refl
    ; directPhenomenalInhabitant = false
    ; directPhenomenalInhabitantIsFalse = refl
    ; qualiaClosure = false
    ; qualiaClosureIsFalse = refl
    ; quotientReading =
        "An observer-specific fibre projects shared latent transport into a perceptual-behavior quotient, not into first-person inhabitation."
    }

record PhenomenalInhabitationBlocked
    {manifold : SharedLatentTransportManifold}
    {observer : ObserverSpecies}
    (quotient : ObserverPerceptualQuotient manifold observer) : Set where
  field
    boundaries :
      List PhenomenalBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalPhenomenalBoundaries

    projectionPromoted :
      observerProjectionPromoted quotient ≡ true

    noDirectInhabitant :
      directPhenomenalInhabitant quotient ≡ false

    noQualiaClosure :
      qualiaClosure quotient ≡ false

    blockReading :
      String

open PhenomenalInhabitationBlocked public

canonicalPhenomenalInhabitationBlocked :
  {manifold : SharedLatentTransportManifold} →
  {observer : ObserverSpecies} →
  (quotient : ObserverPerceptualQuotient manifold observer) →
  PhenomenalInhabitationBlocked quotient
canonicalPhenomenalInhabitationBlocked quotient =
  record
    { boundaries = canonicalPhenomenalBoundaries
    ; boundariesAreCanonical = refl
    ; projectionPromoted =
        observerProjectionPromotedIsTrue quotient
    ; noDirectInhabitant =
        directPhenomenalInhabitantIsFalse quotient
    ; noQualiaClosure =
        qualiaClosureIsFalse quotient
    ; blockReading =
        "The quotient carries observer-relative constraints while phenomenal inhabitation and qualia closure remain blocked."
    }

------------------------------------------------------------------------
-- Cross-species translation and projection defect.
------------------------------------------------------------------------

record CrossSpeciesProjectionDefect
    {manifold : SharedLatentTransportManifold}
    {sourceObserver targetObserver : ObserverSpecies}
    (sourceQuotient :
      ObserverPerceptualQuotient manifold sourceObserver)
    (targetQuotient :
      ObserverPerceptualQuotient manifold targetObserver) : Set₁ where
  field
    sourceFibre :
      PerceptualFibre

    sourceFibreMatches :
      sourceFibre ≡ fibre sourceQuotient

    targetFibre :
      PerceptualFibre

    targetFibreMatches :
      targetFibre ≡ fibre targetQuotient

    TranslatedCandidate :
      Set

    translateSourceProjection :
      QuotientState sourceQuotient →
      TranslatedCandidate

    compareWithTargetProjection :
      TranslatedCandidate →
      QuotientState targetQuotient →
      Set

    residualKinds :
      List ProjectionResidualKind

    residualKindsAreCanonical :
      residualKinds ≡ canonicalProjectionResiduals

    projectionDefects :
      List ProjectionDefectKind

    projectionDefectsAreCanonical :
      projectionDefects ≡ canonicalProjectionDefects

    phenomenalBoundaries :
      List PhenomenalBoundary

    phenomenalBoundariesAreCanonical :
      phenomenalBoundaries ≡ canonicalPhenomenalBoundaries

    crossSpeciesTranslationPromoted :
      Bool

    crossSpeciesTranslationPromotedIsTrue :
      crossSpeciesTranslationPromoted ≡ true

    projectionDefectPresent :
      Bool

    projectionDefectPresentIsTrue :
      projectionDefectPresent ≡ true

    fibreIsomorphismClaim :
      Bool

    fibreIsomorphismClaimIsFalse :
      fibreIsomorphismClaim ≡ false

    projectionRetractionClaim :
      Bool

    projectionRetractionClaimIsFalse :
      projectionRetractionClaim ≡ false

    phenomenalIdentityClaim :
      Bool

    phenomenalIdentityClaimIsFalse :
      phenomenalIdentityClaim ≡ false

    qualiaClosureClaim :
      Bool

    qualiaClosureClaimIsFalse :
      qualiaClosureClaim ≡ false

    defectReading :
      String

open CrossSpeciesProjectionDefect public

canonicalCrossSpeciesProjectionDefect :
  {manifold : SharedLatentTransportManifold} →
  {sourceObserver targetObserver : ObserverSpecies} →
  (sourceQuotient :
    ObserverPerceptualQuotient manifold sourceObserver) →
  (targetQuotient :
    ObserverPerceptualQuotient manifold targetObserver) →
  (TranslatedCandidate : Set) →
  (translateSourceProjection :
    QuotientState sourceQuotient → TranslatedCandidate) →
  (compareWithTargetProjection :
    TranslatedCandidate →
    QuotientState targetQuotient →
    Set) →
  CrossSpeciesProjectionDefect sourceQuotient targetQuotient
canonicalCrossSpeciesProjectionDefect
  sourceQuotient
  targetQuotient
  TranslatedCandidate
  translateSourceProjection
  compareWithTargetProjection =
  record
    { sourceFibre = fibre sourceQuotient
    ; sourceFibreMatches = refl
    ; targetFibre = fibre targetQuotient
    ; targetFibreMatches = refl
    ; TranslatedCandidate = TranslatedCandidate
    ; translateSourceProjection = translateSourceProjection
    ; compareWithTargetProjection = compareWithTargetProjection
    ; residualKinds = canonicalProjectionResiduals
    ; residualKindsAreCanonical = refl
    ; projectionDefects = canonicalProjectionDefects
    ; projectionDefectsAreCanonical = refl
    ; phenomenalBoundaries = canonicalPhenomenalBoundaries
    ; phenomenalBoundariesAreCanonical = refl
    ; crossSpeciesTranslationPromoted = true
    ; crossSpeciesTranslationPromotedIsTrue = refl
    ; projectionDefectPresent = true
    ; projectionDefectPresentIsTrue = refl
    ; fibreIsomorphismClaim = false
    ; fibreIsomorphismClaimIsFalse = refl
    ; projectionRetractionClaim = false
    ; projectionRetractionClaimIsFalse = refl
    ; phenomenalIdentityClaim = false
    ; phenomenalIdentityClaimIsFalse = refl
    ; qualiaClosureClaim = false
    ; qualiaClosureClaimIsFalse = refl
    ; defectReading =
        "Cross-species translation compares quotient projections across fibres while recording the residual projection defect and blocking phenomenal identity."
    }

record ObserverPerceptualManifoldResidual
    (manifold : SharedLatentTransportManifold) : Set₁ where
  field
    humanQuotient :
      ObserverPerceptualQuotient manifold humanObserver

    birdQuotient :
      ObserverPerceptualQuotient manifold birdObserver

    batQuotient :
      ObserverPerceptualQuotient manifold batObserver

    octopusQuotient :
      ObserverPerceptualQuotient manifold octopusObserver

    beeQuotient :
      ObserverPerceptualQuotient manifold beeObserver

    fibres :
      List PerceptualFibre

    fibresAreAllObserverFibres :
      fibres ≡ allObserverFibres

    humanBlock :
      PhenomenalInhabitationBlocked humanQuotient

    birdBlock :
      PhenomenalInhabitationBlocked birdQuotient

    batBlock :
      PhenomenalInhabitationBlocked batQuotient

    octopusBlock :
      PhenomenalInhabitationBlocked octopusQuotient

    beeBlock :
      PhenomenalInhabitationBlocked beeQuotient

    humanBirdDefect :
      CrossSpeciesProjectionDefect humanQuotient birdQuotient

    humanBatDefect :
      CrossSpeciesProjectionDefect humanQuotient batQuotient

    humanOctopusDefect :
      CrossSpeciesProjectionDefect humanQuotient octopusQuotient

    humanBeeDefect :
      CrossSpeciesProjectionDefect humanQuotient beeQuotient

    observerProjectionPromoted :
      Bool

    observerProjectionPromotedIsTrue :
      observerProjectionPromoted ≡ true

    crossSpeciesProjectionDefectRetained :
      Bool

    crossSpeciesProjectionDefectRetainedIsTrue :
      crossSpeciesProjectionDefectRetained ≡ true

    phenomenalInhabitationRecovered :
      Bool

    phenomenalInhabitationRecoveredIsFalse :
      phenomenalInhabitationRecovered ≡ false

    qualiaClosureRecovered :
      Bool

    qualiaClosureRecoveredIsFalse :
      qualiaClosureRecovered ≡ false

    residualReading :
      String

open ObserverPerceptualManifoldResidual public
