module DASHI.Biology.AvianHepaticMacrophageMagnetoreception where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.MagnetoreceptionSurface as Generic
import DASHI.Biology.AvianMagnetoreceptionSourceRegistry as Sources

------------------------------------------------------------------------
-- Lisowski et al. 2026 evidence surface.
--
-- Source:
--   C. Lisowski et al.,
--   "Homing pigeon navigation relies on superparamagnetic macrophages under
--   overcast conditions", Science 392 (6801), 985-991 (2026).
--   DOI 10.1126/science.ady2486; PMID 42207892.
--
-- The causal intervention receipt is restricted to the measured behavioural
-- result.  The receptor-to-autonomic-to-brain transduction chain remains a
-- candidate mechanism until direct neural evidence is supplied.
------------------------------------------------------------------------

data HepaticMacrophageLayer : Set where
  hepaticMacrophagePopulation : HepaticMacrophageLayer
  intracellularIronCarrier : HepaticMacrophageLayer
  superparamagneticMaterialState : HepaticMacrophageLayer
  localAutonomicFibreProximity : HepaticMacrophageLayer
  afferentEncodingResidual : HepaticMacrophageLayer
  centralNavigationIntegrationResidual : HepaticMacrophageLayer

data MacrophageEvidenceClass : Set where
  directlyObservedCellularMaterial : MacrophageEvidenceClass
  depletionInterventionBehaviorReceipt : MacrophageEvidenceClass
  intactSolarCueControlReceipt : MacrophageEvidenceClass
  anatomicalProximityReceipt : MacrophageEvidenceClass
  proposedAfferentMechanism : MacrophageEvidenceClass
  unresolvedCentralRepresentation : MacrophageEvidenceClass

data MacrophageMagnetoreceptionBoundary : Set where
  noVagusTransductionTheorem : MacrophageMagnetoreceptionBoundary
  noSympatheticTransductionTheorem : MacrophageMagnetoreceptionBoundary
  noMacrophageSpikeCodeTheorem : MacrophageMagnetoreceptionBoundary
  noCentralMagneticMapTheorem : MacrophageMagnetoreceptionBoundary
  noPhenomenologyFromBehavior : MacrophageMagnetoreceptionBoundary
  noCryptochromeFalsificationClaim : MacrophageMagnetoreceptionBoundary
  noIronAloneSufficiencyClaim : MacrophageMagnetoreceptionBoundary

record HepaticMacrophageMagnetoreceptionReceipt : Set₁ where
  field
    MagneticField : Set
    HepaticMacrophage : Set
    IronMaterialState : Set
    MagneticMaterialResponse : Set
    AutonomicFibreContext : Set
    CandidateAfferentSignal : Set
    NavigationContext : Set
    OrientationBehavior : Set

    ironMaterial :
      HepaticMacrophage -> IronMaterialState

    magneticResponse :
      MagneticField ->
      IronMaterialState ->
      MagneticMaterialResponse

    autonomicProximityContext :
      HepaticMacrophage ->
      AutonomicFibreContext

    candidateAfferent :
      MagneticMaterialResponse ->
      AutonomicFibreContext ->
      CandidateAfferentSignal

    behaviorUnderContext :
      NavigationContext ->
      OrientationBehavior

    macrophagePopulationObserved :
      Bool
    macrophagePopulationObservedIsTrue :
      macrophagePopulationObserved ≡ true

    superparamagneticMaterialObserved :
      Bool
    superparamagneticMaterialObservedIsTrue :
      superparamagneticMaterialObserved ≡ true

    depletionDisruptsOvercastOrientation :
      Bool
    depletionDisruptsOvercastOrientationIsTrue :
      depletionDisruptsOvercastOrientation ≡ true

    visibleSunControlRetainsOrientation :
      Bool
    visibleSunControlRetainsOrientationIsTrue :
      visibleSunControlRetainsOrientation ≡ true

    afferentMechanismDirectlyEstablished :
      Bool
    afferentMechanismDirectlyEstablishedIsFalse :
      afferentMechanismDirectlyEstablished ≡ false

    brainRepresentationEstablished :
      Bool
    brainRepresentationEstablishedIsFalse :
      brainRepresentationEstablished ≡ false

    phenomenalContentRecovered :
      Bool
    phenomenalContentRecoveredIsFalse :
      phenomenalContentRecovered ≡ false

    layers :
      List HepaticMacrophageLayer

    evidenceClasses :
      List MacrophageEvidenceClass

    boundaries :
      List MacrophageMagnetoreceptionBoundary

    sourceReceipt :
      Sources.AvianMagnetoreceptionSource

    sourceReceiptIsLisowski2026 :
      sourceReceipt ≡ Sources.lisowskiEtAl2026

    sourceReference :
      String

    plainReading :
      String

open HepaticMacrophageMagnetoreceptionReceipt public

data HepaticToken : Set where
  fieldToken : HepaticToken
  macrophageToken : HepaticToken
  ironToken : HepaticToken
  magneticResponseToken : HepaticToken
  autonomicContextToken : HepaticToken
  candidateAfferentToken : HepaticToken
  overcastContextToken : HepaticToken
  sunnyContextToken : HepaticToken
  orientationToken : HepaticToken

canonicalHepaticLayers : List HepaticMacrophageLayer
canonicalHepaticLayers =
  hepaticMacrophagePopulation
  ∷ intracellularIronCarrier
  ∷ superparamagneticMaterialState
  ∷ localAutonomicFibreProximity
  ∷ afferentEncodingResidual
  ∷ centralNavigationIntegrationResidual
  ∷ []

canonicalMacrophageEvidenceClasses : List MacrophageEvidenceClass
canonicalMacrophageEvidenceClasses =
  directlyObservedCellularMaterial
  ∷ depletionInterventionBehaviorReceipt
  ∷ intactSolarCueControlReceipt
  ∷ anatomicalProximityReceipt
  ∷ proposedAfferentMechanism
  ∷ unresolvedCentralRepresentation
  ∷ []

canonicalMacrophageBoundaries : List MacrophageMagnetoreceptionBoundary
canonicalMacrophageBoundaries =
  noVagusTransductionTheorem
  ∷ noSympatheticTransductionTheorem
  ∷ noMacrophageSpikeCodeTheorem
  ∷ noCentralMagneticMapTheorem
  ∷ noPhenomenologyFromBehavior
  ∷ noCryptochromeFalsificationClaim
  ∷ noIronAloneSufficiencyClaim
  ∷ []

canonicalHepaticMacrophageMagnetoreceptionReceipt :
  HepaticMacrophageMagnetoreceptionReceipt
canonicalHepaticMacrophageMagnetoreceptionReceipt =
  record
    { MagneticField = HepaticToken
    ; HepaticMacrophage = HepaticToken
    ; IronMaterialState = HepaticToken
    ; MagneticMaterialResponse = HepaticToken
    ; AutonomicFibreContext = HepaticToken
    ; CandidateAfferentSignal = HepaticToken
    ; NavigationContext = HepaticToken
    ; OrientationBehavior = HepaticToken
    ; ironMaterial = λ _ -> ironToken
    ; magneticResponse = λ _ _ -> magneticResponseToken
    ; autonomicProximityContext = λ _ -> autonomicContextToken
    ; candidateAfferent = λ _ _ -> candidateAfferentToken
    ; behaviorUnderContext = λ _ -> orientationToken
    ; macrophagePopulationObserved = true
    ; macrophagePopulationObservedIsTrue = refl
    ; superparamagneticMaterialObserved = true
    ; superparamagneticMaterialObservedIsTrue = refl
    ; depletionDisruptsOvercastOrientation = true
    ; depletionDisruptsOvercastOrientationIsTrue = refl
    ; visibleSunControlRetainsOrientation = true
    ; visibleSunControlRetainsOrientationIsTrue = refl
    ; afferentMechanismDirectlyEstablished = false
    ; afferentMechanismDirectlyEstablishedIsFalse = refl
    ; brainRepresentationEstablished = false
    ; brainRepresentationEstablishedIsFalse = refl
    ; phenomenalContentRecovered = false
    ; phenomenalContentRecoveredIsFalse = refl
    ; layers = canonicalHepaticLayers
    ; evidenceClasses = canonicalMacrophageEvidenceClasses
    ; boundaries = canonicalMacrophageBoundaries
    ; sourceReceipt = Sources.lisowskiEtAl2026
    ; sourceReceiptIsLisowski2026 = refl
    ; sourceReference =
        Sources.identifier Sources.lisowskiEtAl2026
    ; plainReading =
        "Hepatic superparamagnetic macrophages and the depletion-overcast behavioural effect are promoted as source-attributed evidence; autonomic transduction, central representation, and phenomenal content remain residual."
    }

hepaticMacrophageGenericSurface : Generic.MagnetoreceptionSurface
hepaticMacrophageGenericSurface =
  record
    { MagneticStimulus = HepaticToken
    ; ReceptorState = HepaticToken
    ; TransductionState = HepaticToken
    ; AfferentSignal = HepaticToken
    ; NavigationCue = HepaticToken
    ; NavigationContext = HepaticToken
    ; NavigationPolicy = HepaticToken
    ; OrientationOutput = HepaticToken
    ; receptorResponse = λ _ _ -> magneticResponseToken
    ; afferentEncode = λ _ -> candidateAfferentToken
    ; cueFromAfference = λ _ _ -> orientationToken
    ; navigationUse = λ _ _ -> orientationToken
    ; channel = Generic.hepaticMacrophageChannel
    ; afferentRoute = Generic.autonomicAfferentCandidateRoute
    ; receptorEvidence = Generic.causalInterventionReceipt
    ; afferentEvidence = Generic.structuralHypothesis
    ; navigationEvidence = Generic.causalInterventionReceipt
    ; boundaries = Generic.canonicalMechanismNeutralBoundaries
    ; surfaceReading =
        "Hepatic macrophage inhabitant: strong intervention evidence at receptor/behaviour level, candidate-only autonomic afference."
    }
