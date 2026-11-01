module DASHI.Physics.Closure.QuantumPathFibreObservationQuotient where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Quantum optics as phase-sensitive transport over admissible path fibres.
--
-- This is a theorem-thin observation surface for the fetched thread tail.
-- It records the shared carrier behind double-slit, Feynman/Fermat mirrors,
-- gratings/masks, and quantum eraser experiments:
--
--   admissible path fibres
--     -> amplitude/action/phase contribution
--     -> quotient-dependent observable
--
-- The module deliberately does not promote a hidden classical path, a
-- retrocausal update, a collapse theorem, global QED completeness, or an
-- O(1) rendering theorem.

data PathFibreLayer : Set where
  sourceBoundaryLayer : PathFibreLayer
  admissibleFibreLayer : PathFibreLayer
  amplitudeLayer : PathFibreLayer
  actionLayer : PathFibreLayer
  phaseContributionLayer : PathFibreLayer
  interferenceLayer : PathFibreLayer
  observationQuotientLayer : PathFibreLayer
  coincidenceSelectionLayer : PathFibreLayer

canonicalQuantumPathLayers : List PathFibreLayer
canonicalQuantumPathLayers =
  sourceBoundaryLayer
  ∷ admissibleFibreLayer
  ∷ amplitudeLayer
  ∷ actionLayer
  ∷ phaseContributionLayer
  ∷ interferenceLayer
  ∷ observationQuotientLayer
  ∷ coincidenceSelectionLayer
  ∷ []

data SlitBranch : Set where
  leftBranch : SlitBranch
  rightBranch : SlitBranch
  whichPathDistinguishedBranch : SlitBranch

data PhaseCouplingMode : Set where
  coherentCrossCoupling : PhaseCouplingMode
  constructiveInterference : PhaseCouplingMode
  destructiveInterference : PhaseCouplingMode
  decoheredWhichPathCoupling : PhaseCouplingMode

data PathIntegralTopology : Set where
  allAdmissibleFibres : PathIntegralTopology
  stationaryActionAttractor : PathIntegralTopology
  stationaryPhaseAttractor : PathIntegralTopology
  mirrorFermatAttractor : PathIntegralTopology
  gratingMaskRetopologized : PathIntegralTopology

data ObservationQuotientKind : Set where
  coherentScreenQuotient : ObservationQuotientKind
  whichPathQuotient : ObservationQuotientKind
  oneParticleSmudgeQuotient : ObservationQuotientKind
  jointCoincidenceQuotient : ObservationQuotientKind
  correlatedSubFibreQuotient : ObservationQuotientKind

data QuantumPathNonPromotionBoundary : Set where
  noFutureChangesPastClaim : QuantumPathNonPromotionBoundary
  noClassicalHiddenPathClaim : QuantumPathNonPromotionBoundary
  noGlobalQEDCompletenessClaim : QuantumPathNonPromotionBoundary
  noO1RendererTheorem : QuantumPathNonPromotionBoundary
  noMeasurementCollapseTheorem : QuantumPathNonPromotionBoundary
  noRetrocausalEraserClaim : QuantumPathNonPromotionBoundary

canonicalQuantumPathBoundaries :
  List QuantumPathNonPromotionBoundary
canonicalQuantumPathBoundaries =
  noFutureChangesPastClaim
  ∷ noClassicalHiddenPathClaim
  ∷ noGlobalQEDCompletenessClaim
  ∷ noO1RendererTheorem
  ∷ noMeasurementCollapseTheorem
  ∷ noRetrocausalEraserClaim
  ∷ []

------------------------------------------------------------------------
-- Common carrier: admissible path fibres with amplitude/action/phase data.

record AdmissiblePathFibreCarrier : Set₁ where
  field
    SourceBoundary : Set
    DetectorBoundary : Set
    PathFibre : Set
    Amplitude : Set
    Action : Set
    PhaseContribution : Set
    AdmissibilityReceipt : Set

    admissibleFibre :
      SourceBoundary →
      DetectorBoundary →
      PathFibre →
      AdmissibilityReceipt →
      Set

    amplitudeOf :
      PathFibre →
      Amplitude

    actionOf :
      PathFibre →
      Action

    phaseContributionOf :
      PathFibre →
      PhaseContribution

    combineAmplitudes :
      List PathFibre →
      Amplitude

    phaseCoupling :
      PathFibre →
      PathFibre →
      PhaseCouplingMode

    carrierReading :
      String

open AdmissiblePathFibreCarrier public

------------------------------------------------------------------------
-- Double slit: coherent branch split and which-path quotient.

record DoubleSlitPhaseSurface
    (carrier : AdmissiblePathFibreCarrier) : Set₁ where
  field
    ScreenObservation : Set
    BranchQuotient : Set

    leftFibre :
      PathFibre carrier

    rightFibre :
      PathFibre carrier

    coherentSplit :
      PathFibre carrier →
      List (PathFibre carrier)

    branchOf :
      PathFibre carrier →
      SlitBranch

    crossFibrePhaseCoupling :
      PathFibre carrier →
      PathFibre carrier →
      PhaseCouplingMode

    interferenceAtScreen :
      PathFibre carrier →
      PathFibre carrier →
      ScreenObservation

    whichPathObservation :
      PathFibre carrier →
      BranchQuotient

    branchDistinguished :
      BranchQuotient →
      Set

    quotientKind :
      BranchQuotient →
      ObservationQuotientKind

    doubleSlitReading :
      String

open DoubleSlitPhaseSurface public

------------------------------------------------------------------------
-- Feynman/Fermat mirror: path integral and stationary-phase attractor.

record FeynmanFermatPathSurface
    (carrier : AdmissiblePathFibreCarrier) : Set₁ where
  field
    PathIntegralObservable : Set
    GratingMask : Set
    CancellationTopology : Set

    admissibleFibresBetween :
      SourceBoundary carrier →
      DetectorBoundary carrier →
      List (PathFibre carrier)

    pathIntegralOver :
      List (PathFibre carrier) →
      PathIntegralObservable

    stationaryAction :
      PathFibre carrier →
      Set

    stationaryPhase :
      PathFibre carrier →
      Set

    attractorTopology :
      PathFibre carrier →
      PathIntegralTopology

    mirrorFermatPath :
      SourceBoundary carrier →
      DetectorBoundary carrier →
      PathFibre carrier

    retopologizeByMask :
      GratingMask →
      List (PathFibre carrier) →
      List (PathFibre carrier)

    cancellationTopology :
      GratingMask →
      CancellationTopology

    feynmanFermatReading :
      String

open FeynmanFermatPathSurface public

------------------------------------------------------------------------
-- Quantum eraser: one-particle quotient vs joint coincidence quotient.

record QuantumEraserQuotient
    (carrier : AdmissiblePathFibreCarrier) : Set₁ where
  field
    Signal : Set
    Idler : Set
    EntangledPair : Set
    OneParticleObservation : Set
    CoincidenceObservation : Set
    CorrelatedSubFibre : Set

    entangle :
      Signal →
      Idler →
      EntangledPair

    signalFibre :
      EntangledPair →
      PathFibre carrier

    idlerFibre :
      EntangledPair →
      PathFibre carrier

    oneParticleQuotient :
      EntangledPair →
      OneParticleObservation

    oneParticleQuotientKind :
      OneParticleObservation →
      ObservationQuotientKind

    smudgedByIdlerTrace :
      OneParticleObservation →
      Set

    coincidenceQuotient :
      EntangledPair →
      CoincidenceObservation

    coincidenceQuotientKind :
      CoincidenceObservation →
      ObservationQuotientKind

    selectCorrelatedSubFibre :
      CoincidenceObservation →
      CorrelatedSubFibre

    subFibreIsSelectedByJointData :
      CorrelatedSubFibre →
      Set

    eraserReading :
      String

open QuantumEraserQuotient public

------------------------------------------------------------------------
-- Aggregate observation quotient and non-promotion certificate.

record QuantumPathFibreObservationQuotient : Set₁ where
  field
    carrier :
      AdmissiblePathFibreCarrier

    doubleSlitSurface :
      DoubleSlitPhaseSurface carrier

    feynmanFermatSurface :
      FeynmanFermatPathSurface carrier

    quantumEraserSurface :
      QuantumEraserQuotient carrier

    layers :
      List PathFibreLayer

    layersAreCanonical :
      layers ≡ canonicalQuantumPathLayers

    boundaries :
      List QuantumPathNonPromotionBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalQuantumPathBoundaries

    observationReading :
      String

open QuantumPathFibreObservationQuotient public

record QuantumPathNonPromotionCertificate
    (surface : QuantumPathFibreObservationQuotient) : Set where
  field
    boundariesHeld :
      boundaries surface ≡ canonicalQuantumPathBoundaries

    futureChangesPastPromoted :
      Bool

    futureChangesPastPromotedIsFalse :
      futureChangesPastPromoted ≡ false

    classicalHiddenPathPromoted :
      Bool

    classicalHiddenPathPromotedIsFalse :
      classicalHiddenPathPromoted ≡ false

    globalQEDCompletenessPromoted :
      Bool

    globalQEDCompletenessPromotedIsFalse :
      globalQEDCompletenessPromoted ≡ false

    o1RendererTheoremPromoted :
      Bool

    o1RendererTheoremPromotedIsFalse :
      o1RendererTheoremPromoted ≡ false

    measurementCollapseTheoremPromoted :
      Bool

    measurementCollapseTheoremPromotedIsFalse :
      measurementCollapseTheoremPromoted ≡ false

    retrocausalEraserPromoted :
      Bool

    retrocausalEraserPromotedIsFalse :
      retrocausalEraserPromoted ≡ false

    certificateReading :
      String

open QuantumPathNonPromotionCertificate public

------------------------------------------------------------------------
-- Toy inhabitants.

data QuantumPathToken : Set where
  sourceToken : QuantumPathToken
  detectorToken : QuantumPathToken
  genericFibreToken : QuantumPathToken
  leftFibreToken : QuantumPathToken
  rightFibreToken : QuantumPathToken
  signalToken : QuantumPathToken
  idlerToken : QuantumPathToken
  pairToken : QuantumPathToken
  maskToken : QuantumPathToken
  observationToken : QuantumPathToken
  subFibreToken : QuantumPathToken

canonicalAdmissiblePathFibreCarrier :
  AdmissiblePathFibreCarrier
canonicalAdmissiblePathFibreCarrier =
  record
    { SourceBoundary =
        QuantumPathToken
    ; DetectorBoundary =
        QuantumPathToken
    ; PathFibre =
        QuantumPathToken
    ; Amplitude =
        QuantumPathToken
    ; Action =
        QuantumPathToken
    ; PhaseContribution =
        QuantumPathToken
    ; AdmissibilityReceipt =
        ⊤
    ; admissibleFibre =
        λ _ _ _ _ → ⊤
    ; amplitudeOf =
        λ _ → observationToken
    ; actionOf =
        λ _ → observationToken
    ; phaseContributionOf =
        λ _ → observationToken
    ; combineAmplitudes =
        λ _ → observationToken
    ; phaseCoupling =
        λ _ _ → coherentCrossCoupling
    ; carrierReading =
        "Toy path carrier: every admissible fibre carries amplitude, action, and phase contribution slots."
    }

canonicalDoubleSlitPhaseSurface :
  DoubleSlitPhaseSurface canonicalAdmissiblePathFibreCarrier
canonicalDoubleSlitPhaseSurface =
  record
    { ScreenObservation =
        QuantumPathToken
    ; BranchQuotient =
        QuantumPathToken
    ; leftFibre =
        leftFibreToken
    ; rightFibre =
        rightFibreToken
    ; coherentSplit =
        λ _ → leftFibreToken ∷ rightFibreToken ∷ []
    ; branchOf =
        λ fibre →
          leftBranch
    ; crossFibrePhaseCoupling =
        λ _ _ → coherentCrossCoupling
    ; interferenceAtScreen =
        λ _ _ → observationToken
    ; whichPathObservation =
        λ _ → observationToken
    ; branchDistinguished =
        λ _ → ⊤
    ; quotientKind =
        λ _ → whichPathQuotient
    ; doubleSlitReading =
        "Double slit transport splits coherently into branch fibres; a which-path quotient distinguishes branch data and changes the observation quotient."
    }

canonicalFeynmanFermatPathSurface :
  FeynmanFermatPathSurface canonicalAdmissiblePathFibreCarrier
canonicalFeynmanFermatPathSurface =
  record
    { PathIntegralObservable =
        QuantumPathToken
    ; GratingMask =
        QuantumPathToken
    ; CancellationTopology =
        QuantumPathToken
    ; admissibleFibresBetween =
        λ _ _ → genericFibreToken ∷ leftFibreToken ∷ rightFibreToken ∷ []
    ; pathIntegralOver =
        λ _ → observationToken
    ; stationaryAction =
        λ _ → ⊤
    ; stationaryPhase =
        λ _ → ⊤
    ; attractorTopology =
        λ _ → stationaryPhaseAttractor
    ; mirrorFermatPath =
        λ _ _ → genericFibreToken
    ; retopologizeByMask =
        λ _ fibres → fibres
    ; cancellationTopology =
        λ _ → observationToken
    ; feynmanFermatReading =
        "Feynman/Fermat transport sums admissible fibres while stationary action/phase acts as an attractor; gratings and masks alter cancellation topology."
    }

canonicalQuantumEraserQuotient :
  QuantumEraserQuotient canonicalAdmissiblePathFibreCarrier
canonicalQuantumEraserQuotient =
  record
    { Signal =
        QuantumPathToken
    ; Idler =
        QuantumPathToken
    ; EntangledPair =
        QuantumPathToken
    ; OneParticleObservation =
        QuantumPathToken
    ; CoincidenceObservation =
        QuantumPathToken
    ; CorrelatedSubFibre =
        QuantumPathToken
    ; entangle =
        λ _ _ → pairToken
    ; signalFibre =
        λ _ → signalToken
    ; idlerFibre =
        λ _ → idlerToken
    ; oneParticleQuotient =
        λ _ → observationToken
    ; oneParticleQuotientKind =
        λ _ → oneParticleSmudgeQuotient
    ; smudgedByIdlerTrace =
        λ _ → ⊤
    ; coincidenceQuotient =
        λ _ → observationToken
    ; coincidenceQuotientKind =
        λ _ → jointCoincidenceQuotient
    ; selectCorrelatedSubFibre =
        λ _ → subFibreToken
    ; subFibreIsSelectedByJointData =
        λ _ → ⊤
    ; eraserReading =
        "Quantum eraser transport keeps the one-particle quotient smudged while a joint coincidence quotient may select a correlated sub-fibre without retrocausal promotion."
    }

canonicalQuantumPathFibreObservationQuotient :
  QuantumPathFibreObservationQuotient
canonicalQuantumPathFibreObservationQuotient =
  record
    { carrier =
        canonicalAdmissiblePathFibreCarrier
    ; doubleSlitSurface =
        canonicalDoubleSlitPhaseSurface
    ; feynmanFermatSurface =
        canonicalFeynmanFermatPathSurface
    ; quantumEraserSurface =
        canonicalQuantumEraserQuotient
    ; layers =
        canonicalQuantumPathLayers
    ; layersAreCanonical =
        refl
    ; boundaries =
        canonicalQuantumPathBoundaries
    ; boundariesAreCanonical =
        refl
    ; observationReading =
        "Quantum optics is recorded here as phase-sensitive transport over admissible path fibres, observed through explicit quotients."
    }

canonicalQuantumPathNonPromotionCertificate :
  QuantumPathNonPromotionCertificate
    canonicalQuantumPathFibreObservationQuotient
canonicalQuantumPathNonPromotionCertificate =
  record
    { boundariesHeld =
        refl
    ; futureChangesPastPromoted =
        false
    ; futureChangesPastPromotedIsFalse =
        refl
    ; classicalHiddenPathPromoted =
        false
    ; classicalHiddenPathPromotedIsFalse =
        refl
    ; globalQEDCompletenessPromoted =
        false
    ; globalQEDCompletenessPromotedIsFalse =
        refl
    ; o1RendererTheoremPromoted =
        false
    ; o1RendererTheoremPromotedIsFalse =
        refl
    ; measurementCollapseTheoremPromoted =
        false
    ; measurementCollapseTheoremPromotedIsFalse =
        refl
    ; retrocausalEraserPromoted =
        false
    ; retrocausalEraserPromotedIsFalse =
        refl
    ; certificateReading =
        "The quotient is observation-only: it blocks retrocausal, hidden-path, global-QED, O(1)-renderer, and measurement-collapse promotion."
    }
