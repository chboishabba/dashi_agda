module DASHI.Biology.GenomeSensorimotorConnectomeBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Safe genome -> development -> sensorimotor-connectome vocabulary
------------------------------------------------------------------------

data DevelopmentalConstraintKind : Set where
  genomeSequenceBoundary : DevelopmentalConstraintKind
  cisRegulatoryTiming : DevelopmentalConstraintKind
  chromatinAccessibility : DevelopmentalConstraintKind
  morphogenGradient : DevelopmentalConstraintKind
  tissuePatterning : DevelopmentalConstraintKind
  axonGuidance : DevelopmentalConstraintKind
  pruningAndRefinement : DevelopmentalConstraintKind
  bodyBiomechanics : DevelopmentalConstraintKind

data SensorimotorTarget : Set where
  retinalSheet : SensorimotorTarget
  opticNerveBundle : SensorimotorTarget
  brainRelay : SensorimotorTarget
  brainBodyLoop : SensorimotorTarget
  bodyEffectorMap : SensorimotorTarget

data GenomeSensorimotorBoundary : Set where
  boundaryConstraintOnly : GenomeSensorimotorBoundary
  boundaryNoDNAEncodesMeaningClaim : GenomeSensorimotorBoundary
  boundaryNoDNAEncodesQualiaClaim : GenomeSensorimotorBoundary
  boundaryNoGenomeToConnectomeClosure : GenomeSensorimotorBoundary
  boundaryNoPerceptionClosure : GenomeSensorimotorBoundary
  boundaryNoEmpiricalValidationClaim : GenomeSensorimotorBoundary

------------------------------------------------------------------------
-- Developmental genome constraint surface
------------------------------------------------------------------------

record DevelopmentalGenomeConstraintSurface : Set₁ where
  field
    Genome : Set
    RegulatoryState : Set
    RegulatoryElement : Set
    MorphogeneticState : Set
    TissueGeometry : Set
    CellLineage : Set
    Environment : Set

    regulationFromGenome :
      Genome →
      Environment →
      RegulatoryState

    regulatoryConstraint :
      RegulatoryState →
      RegulatoryElement →
      DevelopmentalConstraintKind

    morphogenesisFromRegulation :
      RegulatoryState →
      MorphogeneticState

    tissueGeometry :
      MorphogeneticState →
      TissueGeometry

    lineageFromMorphogenesis :
      MorphogeneticState →
      CellLineage

    genomeReading : String
    genomeIsConstraintSource : Bool
    genomeIsConstraintSourceIsTrue :
      genomeIsConstraintSource ≡ true

    genomeBlueprintClaim : Bool
    genomeBlueprintClaimIsFalse :
      genomeBlueprintClaim ≡ false

open DevelopmentalGenomeConstraintSurface public

------------------------------------------------------------------------
-- Sensorimotor connectome surface
------------------------------------------------------------------------

record SensorimotorConnectomeSurface
    (dev : DevelopmentalGenomeConstraintSurface) : Set₁ where
  field
    Retina : Set
    OpticNerve : Set
    BrainRegion : Set
    BodySegment : Set
    BodyEffector : Set
    SensoryBodyConnectome : Set
    ConnectomeEdge : Set
    ConnectomeWeight : Set
    SensorimotorPolicy : Set

    retinaFromTissue :
      TissueGeometry dev →
      Retina

    opticNerveFromLineage :
      CellLineage dev →
      Retina →
      OpticNerve

    brainRegionFromLineage :
      CellLineage dev →
      BrainRegion

    bodySegmentFromMorphogenesis :
      MorphogeneticState dev →
      BodySegment

    bodyEffectorFromSegment :
      BodySegment →
      BodyEffector

    connectomeFromDevelopment :
      RegulatoryState dev →
      MorphogeneticState dev →
      CellLineage dev →
      Retina →
      OpticNerve →
      BrainRegion →
      BodyEffector →
      SensoryBodyConnectome

    admittedEdge :
      SensoryBodyConnectome →
      ConnectomeEdge →
      Set

    edgeWeight :
      SensoryBodyConnectome →
      ConnectomeEdge →
      ConnectomeWeight

    policyConstrainedByConnectome :
      SensoryBodyConnectome →
      SensorimotorPolicy →
      Set

    targetKind :
      SensorimotorTarget →
      DevelopmentalConstraintKind

    connectomeReading : String
    connectomeConstrainsButDoesNotDetermineFunction : Bool
    connectomeConstrainsButDoesNotDetermineFunctionIsTrue :
      connectomeConstrainsButDoesNotDetermineFunction ≡ true

open SensorimotorConnectomeSurface public

------------------------------------------------------------------------
-- Bridge: DNA/regulation/morphogenesis constrain sensorimotor wiring.
------------------------------------------------------------------------

record GenomeSensorimotorConnectomeBridge : Set₁ where
  field
    developmentalSurface :
      DevelopmentalGenomeConstraintSurface

    sensorimotorSurface :
      SensorimotorConnectomeSurface developmentalSurface

    environment :
      Environment developmentalSurface

    genome :
      Genome developmentalSurface

    regulatoryState :
      RegulatoryState developmentalSurface

    morphogeneticState :
      MorphogeneticState developmentalSurface

    tissue :
      TissueGeometry developmentalSurface

    lineage :
      CellLineage developmentalSurface

    retina :
      Retina sensorimotorSurface

    opticNerve :
      OpticNerve sensorimotorSurface

    brainRegion :
      BrainRegion sensorimotorSurface

    bodySegment :
      BodySegment sensorimotorSurface

    bodyEffector :
      BodyEffector sensorimotorSurface

    sensoryBodyConnectome :
      SensoryBodyConnectome sensorimotorSurface

    developmentalChain :
      List String

    constraintTargets :
      List SensorimotorTarget

    boundaries :
      List GenomeSensorimotorBoundary

    nonPromoting : Bool
    nonPromotingIsTrue :
      nonPromoting ≡ true

    dnaEncodesMeaningClaim : Bool
    dnaEncodesMeaningClaimIsFalse :
      dnaEncodesMeaningClaim ≡ false

    dnaEncodesQualiaClaim : Bool
    dnaEncodesQualiaClaimIsFalse :
      dnaEncodesQualiaClaim ≡ false

    genomeToConnectomeClosureClaim : Bool
    genomeToConnectomeClosureClaimIsFalse :
      genomeToConnectomeClosureClaim ≡ false

    safeReading : String

open GenomeSensorimotorConnectomeBridge public

record GenomeSensorimotorNonPromotionCertificate
    (bridge : GenomeSensorimotorConnectomeBridge) : Set where
  field
    nonPromotionHeld :
      nonPromoting bridge ≡ true

    meaningEncodingBlocked :
      dnaEncodesMeaningClaim bridge ≡ false

    qualiaEncodingBlocked :
      dnaEncodesQualiaClaim bridge ≡ false

    connectomeClosureBlocked :
      genomeToConnectomeClosureClaim bridge ≡ false

    certificateReading : String

open GenomeSensorimotorNonPromotionCertificate public

------------------------------------------------------------------------
-- Canonical proof-light token witness.
------------------------------------------------------------------------

data GenomeSensorimotorToken : Set where
  genomeToken : GenomeSensorimotorToken
  environmentToken : GenomeSensorimotorToken
  regulatoryStateToken : GenomeSensorimotorToken
  regulatoryElementToken : GenomeSensorimotorToken
  morphogeneticStateToken : GenomeSensorimotorToken
  tissueGeometryToken : GenomeSensorimotorToken
  lineageToken : GenomeSensorimotorToken
  retinaToken : GenomeSensorimotorToken
  opticNerveToken : GenomeSensorimotorToken
  brainRegionToken : GenomeSensorimotorToken
  bodySegmentToken : GenomeSensorimotorToken
  bodyEffectorToken : GenomeSensorimotorToken
  connectomeToken : GenomeSensorimotorToken
  edgeToken : GenomeSensorimotorToken
  weightToken : GenomeSensorimotorToken
  policyToken : GenomeSensorimotorToken
  witnessToken : GenomeSensorimotorToken

canonicalDevelopmentalGenomeConstraintSurface :
  DevelopmentalGenomeConstraintSurface
canonicalDevelopmentalGenomeConstraintSurface =
  record
    { Genome = GenomeSensorimotorToken
    ; RegulatoryState = GenomeSensorimotorToken
    ; RegulatoryElement = GenomeSensorimotorToken
    ; MorphogeneticState = GenomeSensorimotorToken
    ; TissueGeometry = GenomeSensorimotorToken
    ; CellLineage = GenomeSensorimotorToken
    ; Environment = GenomeSensorimotorToken
    ; regulationFromGenome = λ _ _ → regulatoryStateToken
    ; regulatoryConstraint = λ _ _ → cisRegulatoryTiming
    ; morphogenesisFromRegulation = λ _ → morphogeneticStateToken
    ; tissueGeometry = λ _ → tissueGeometryToken
    ; lineageFromMorphogenesis = λ _ → lineageToken
    ; genomeReading =
        "Genome and regulation supply developmental constraints, not a phenotype or percept blueprint."
    ; genomeIsConstraintSource = true
    ; genomeIsConstraintSourceIsTrue = refl
    ; genomeBlueprintClaim = false
    ; genomeBlueprintClaimIsFalse = refl
    }

canonicalSensorimotorConnectomeSurface :
  SensorimotorConnectomeSurface
    canonicalDevelopmentalGenomeConstraintSurface
canonicalSensorimotorConnectomeSurface =
  record
    { Retina = GenomeSensorimotorToken
    ; OpticNerve = GenomeSensorimotorToken
    ; BrainRegion = GenomeSensorimotorToken
    ; BodySegment = GenomeSensorimotorToken
    ; BodyEffector = GenomeSensorimotorToken
    ; SensoryBodyConnectome = GenomeSensorimotorToken
    ; ConnectomeEdge = GenomeSensorimotorToken
    ; ConnectomeWeight = GenomeSensorimotorToken
    ; SensorimotorPolicy = GenomeSensorimotorToken
    ; retinaFromTissue = λ _ → retinaToken
    ; opticNerveFromLineage = λ _ _ → opticNerveToken
    ; brainRegionFromLineage = λ _ → brainRegionToken
    ; bodySegmentFromMorphogenesis = λ _ → bodySegmentToken
    ; bodyEffectorFromSegment = λ _ → bodyEffectorToken
    ; connectomeFromDevelopment =
        λ _ _ _ _ _ _ _ → connectomeToken
    ; admittedEdge = λ _ _ → GenomeSensorimotorToken
    ; edgeWeight = λ _ _ → weightToken
    ; policyConstrainedByConnectome = λ _ _ → GenomeSensorimotorToken
    ; targetKind =
        λ { retinalSheet → tissuePatterning
          ; opticNerveBundle → axonGuidance
          ; brainRelay → pruningAndRefinement
          ; brainBodyLoop → pruningAndRefinement
          ; bodyEffectorMap → bodyBiomechanics
          }
    ; connectomeReading =
        "Retina, optic nerve, brain relay, and body-effector wiring are constrained by developmental history."
    ; connectomeConstrainsButDoesNotDetermineFunction = true
    ; connectomeConstrainsButDoesNotDetermineFunctionIsTrue = refl
    }

canonicalGenomeSensorimotorConnectomeBridge :
  GenomeSensorimotorConnectomeBridge
canonicalGenomeSensorimotorConnectomeBridge =
  record
    { developmentalSurface =
        canonicalDevelopmentalGenomeConstraintSurface
    ; sensorimotorSurface =
        canonicalSensorimotorConnectomeSurface
    ; environment =
        environmentToken
    ; genome =
        genomeToken
    ; regulatoryState =
        regulatoryStateToken
    ; morphogeneticState =
        morphogeneticStateToken
    ; tissue =
        tissueGeometryToken
    ; lineage =
        lineageToken
    ; retina =
        retinaToken
    ; opticNerve =
        opticNerveToken
    ; brainRegion =
        brainRegionToken
    ; bodySegment =
        bodySegmentToken
    ; bodyEffector =
        bodyEffectorToken
    ; sensoryBodyConnectome =
        connectomeToken
    ; developmentalChain =
        "DNA / genome carrier"
        ∷ "regulatory activation"
        ∷ "morphogenesis and tissue geometry"
        ∷ "neural lineage and retinal sheet formation"
        ∷ "optic nerve bundle"
        ∷ "brain relay and brain-body loop"
        ∷ "body effector map"
        ∷ "sensory-body connectome constraint"
        ∷ []
    ; constraintTargets =
        retinalSheet
        ∷ opticNerveBundle
        ∷ brainRelay
        ∷ brainBodyLoop
        ∷ bodyEffectorMap
        ∷ []
    ; boundaries =
        boundaryConstraintOnly
        ∷ boundaryNoDNAEncodesMeaningClaim
        ∷ boundaryNoDNAEncodesQualiaClaim
        ∷ boundaryNoGenomeToConnectomeClosure
        ∷ boundaryNoPerceptionClosure
        ∷ boundaryNoEmpiricalValidationClaim
        ∷ []
    ; nonPromoting =
        true
    ; nonPromotingIsTrue =
        refl
    ; dnaEncodesMeaningClaim =
        false
    ; dnaEncodesMeaningClaimIsFalse =
        refl
    ; dnaEncodesQualiaClaim =
        false
    ; dnaEncodesQualiaClaimIsFalse =
        refl
    ; genomeToConnectomeClosureClaim =
        false
    ; genomeToConnectomeClosureClaimIsFalse =
        refl
    ; safeReading =
        "DNA, regulation, and morphogenesis constrain sensorimotor connectome formation; they do not encode meaning, qualia, or a closed brain/body state."
    }

canonicalGenomeSensorimotorNonPromotionCertificate :
  GenomeSensorimotorNonPromotionCertificate
    canonicalGenomeSensorimotorConnectomeBridge
canonicalGenomeSensorimotorNonPromotionCertificate =
  record
    { nonPromotionHeld =
        refl
    ; meaningEncodingBlocked =
        refl
    ; qualiaEncodingBlocked =
        refl
    ; connectomeClosureBlocked =
        refl
    ; certificateReading =
        "The bridge is a developmental constraint surface only."
    }
