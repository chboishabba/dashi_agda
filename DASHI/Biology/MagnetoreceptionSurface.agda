module DASHI.Biology.MagnetoreceptionSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Mechanism-neutral magnetoreception vocabulary.
--
-- This owner intentionally does not privilege a retinal, hepatic, vestibular,
-- trigeminal, or other receptor.  Particular biological mechanisms inhabit the
-- same stimulus -> receptor -> transduction -> afferent -> cue -> policy chain.
------------------------------------------------------------------------

data MagnetoreceptorChannel : Set where
  radicalPairRetinalChannel : MagnetoreceptorChannel
  hepaticMacrophageChannel : MagnetoreceptorChannel
  vestibularCandidateChannel : MagnetoreceptorChannel
  trigeminalCandidateChannel : MagnetoreceptorChannel
  unresolvedMagnetoreceptorChannel : MagnetoreceptorChannel

data AfferentRouteClass : Set where
  retinalNeuralRoute : AfferentRouteClass
  autonomicAfferentCandidateRoute : AfferentRouteClass
  trigeminalCandidateRoute : AfferentRouteClass
  vestibularCandidateRoute : AfferentRouteClass
  unresolvedAfferentRoute : AfferentRouteClass

data EvidenceStrength : Set where
  structuralHypothesis : EvidenceStrength
  correlationalReceipt : EvidenceStrength
  perturbationReceipt : EvidenceStrength
  causalInterventionReceipt : EvidenceStrength
  directMechanismReceipt : EvidenceStrength

data MagnetoreceptionBoundary : Set where
  noSingleMechanismExclusivityClaim : MagnetoreceptionBoundary
  noReceptorToBrainClosureClaim : MagnetoreceptionBoundary
  noCueToQualiaIdentityClaim : MagnetoreceptionBoundary
  noBehaviorToPhenomenologyPromotion : MagnetoreceptionBoundary
  noIronPresenceToMagnetoreceptorPromotion : MagnetoreceptionBoundary
  noRetinalOverlayUniversalityClaim : MagnetoreceptionBoundary

record MagnetoreceptionSurface : Set₁ where
  field
    MagneticStimulus : Set
    ReceptorState : Set
    TransductionState : Set
    AfferentSignal : Set
    NavigationCue : Set
    NavigationContext : Set
    NavigationPolicy : Set
    OrientationOutput : Set

    receptorResponse :
      MagneticStimulus -> ReceptorState -> TransductionState

    afferentEncode :
      TransductionState -> AfferentSignal

    cueFromAfference :
      AfferentSignal -> NavigationContext -> NavigationCue

    navigationUse :
      NavigationCue -> NavigationPolicy -> OrientationOutput

    channel :
      MagnetoreceptorChannel

    afferentRoute :
      AfferentRouteClass

    receptorEvidence :
      EvidenceStrength

    afferentEvidence :
      EvidenceStrength

    navigationEvidence :
      EvidenceStrength

    boundaries :
      List MagnetoreceptionBoundary

    surfaceReading :
      String

open MagnetoreceptionSurface public

record MagnetoreceptionEvidenceReceipt
    (surface : MagnetoreceptionSurface) : Set where
  field
    receptorEvidenceCarried :
      EvidenceStrength
    receptorEvidenceMatches :
      receptorEvidenceCarried ≡ receptorEvidence surface

    afferentEvidenceCarried :
      EvidenceStrength
    afferentEvidenceMatches :
      afferentEvidenceCarried ≡ afferentEvidence surface

    navigationEvidenceCarried :
      EvidenceStrength
    navigationEvidenceMatches :
      navigationEvidenceCarried ≡ navigationEvidence surface

    mechanismExclusive :
      Bool
    mechanismExclusiveIsFalse :
      mechanismExclusive ≡ false

    phenomenalContentRecovered :
      Bool
    phenomenalContentRecoveredIsFalse :
      phenomenalContentRecovered ≡ false

    receiptReading :
      String

open MagnetoreceptionEvidenceReceipt public

data MagnetoToken : Set where
  magneticStimulusToken : MagnetoToken
  receptorStateToken : MagnetoToken
  transductionStateToken : MagnetoToken
  afferentSignalToken : MagnetoToken
  navigationCueToken : MagnetoToken
  navigationContextToken : MagnetoToken
  navigationPolicyToken : MagnetoToken
  orientationOutputToken : MagnetoToken

canonicalMechanismNeutralBoundaries : List MagnetoreceptionBoundary
canonicalMechanismNeutralBoundaries =
  noSingleMechanismExclusivityClaim
  ∷ noReceptorToBrainClosureClaim
  ∷ noCueToQualiaIdentityClaim
  ∷ noBehaviorToPhenomenologyPromotion
  ∷ noIronPresenceToMagnetoreceptorPromotion
  ∷ noRetinalOverlayUniversalityClaim
  ∷ []

canonicalMechanismNeutralMagnetoreceptionSurface : MagnetoreceptionSurface
canonicalMechanismNeutralMagnetoreceptionSurface =
  record
    { MagneticStimulus = MagnetoToken
    ; ReceptorState = MagnetoToken
    ; TransductionState = MagnetoToken
    ; AfferentSignal = MagnetoToken
    ; NavigationCue = MagnetoToken
    ; NavigationContext = MagnetoToken
    ; NavigationPolicy = MagnetoToken
    ; OrientationOutput = MagnetoToken
    ; receptorResponse = λ _ _ -> transductionStateToken
    ; afferentEncode = λ _ -> afferentSignalToken
    ; cueFromAfference = λ _ _ -> navigationCueToken
    ; navigationUse = λ _ _ -> orientationOutputToken
    ; channel = unresolvedMagnetoreceptorChannel
    ; afferentRoute = unresolvedAfferentRoute
    ; receptorEvidence = structuralHypothesis
    ; afferentEvidence = structuralHypothesis
    ; navigationEvidence = perturbationReceipt
    ; boundaries = canonicalMechanismNeutralBoundaries
    ; surfaceReading =
        "Mechanism-neutral magnetic stimulus to receptor/transduction/afferent/cue/policy surface; no receptor exclusivity, brain closure, or phenomenal identity is promoted."
    }

canonicalMechanismNeutralEvidenceReceipt :
  MagnetoreceptionEvidenceReceipt canonicalMechanismNeutralMagnetoreceptionSurface
canonicalMechanismNeutralEvidenceReceipt =
  record
    { receptorEvidenceCarried = structuralHypothesis
    ; receptorEvidenceMatches = refl
    ; afferentEvidenceCarried = structuralHypothesis
    ; afferentEvidenceMatches = refl
    ; navigationEvidenceCarried = perturbationReceipt
    ; navigationEvidenceMatches = refl
    ; mechanismExclusive = false
    ; mechanismExclusiveIsFalse = refl
    ; phenomenalContentRecovered = false
    ; phenomenalContentRecoveredIsFalse = refl
    ; receiptReading =
        "The generic carrier records evidence strength separately at receptor, afferent, and navigation layers."
    }
