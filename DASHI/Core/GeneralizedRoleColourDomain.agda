module DASHI.Core.GeneralizedRoleColourDomain where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.ProofLens

-- Continuous-first candidate colour carrier.  Device and design surfaces are
-- projections; none recover spectrum or qualia.
record OpponentFieldSample : Set where
  constructor opponentSample
  field
    redGreen blueYellow lightDark : Nat

record WaveContact : Set where
  constructor waveContact
  field
    wavelengthBin amplitudeBin phaseBin : Nat

data ColourSurface : Set where
  opponentSurface pccsSurface rgbaSurface cmykaSurface semioticSurface : ColourSurface

data ColourOperation : Set where
  receptorProject opponentProject quantizePCCS emitRGBA printCMYKA interpretSign : ColourOperation

data ColourResidual : Set where
  observerVariance deviceVariance contextVariance spectrumLoss qualiaUnrecoverable : ColourResidual

data ColourEvidence : Set where
  calibrated measured reported candidateModel : ColourEvidence

ColourRole : FormalRole → Set
ColourRole carrierSpaceRole    = WaveContact
ColourRole stateRole           = OpponentFieldSample
ColourRole operatorRole        = ColourOperation
ColourRole observableRole      = ColourSurface
ColourRole spectrumToolRole    = WaveContact → OpponentFieldSample
ColourRole boundaryGateRole    = ColourSurface → Bool
ColourRole obstructionRole     = ColourResidual
ColourRole algebraRole         = ColourOperation → ColourOperation → ColourOperation
ColourRole proofObligationRole = ColourSurface → Set
ColourRole decompositionRole   = WaveContact → List OpponentFieldSample
ColourRole hamiltonianRole     = OpponentFieldSample → Nat
ColourRole metricRole          = OpponentFieldSample → OpponentFieldSample → Nat
ColourRole projectionRole      = OpponentFieldSample → ColourSurface
ColourRole residualRole        = List ColourResidual
ColourRole receiptRole         = ColourEvidence
ColourRole functorRole         = ColourOperation → ColourOperation
ColourRole transitionRole      = OpponentFieldSample → ColourOperation → OpponentFieldSample
ColourRole invariantRole       = OpponentFieldSample → Set
ColourRole symmetryRole        = OpponentFieldSample → OpponentFieldSample
ColourRole modeRole            = ColourSurface
ColourRole sourceRole          = WaveContact
ColourRole sinkRole            = ColourSurface
ColourRole flowRole            = OpponentFieldSample → OpponentFieldSample
ColourRole constraintRole      = OpponentFieldSample → Set
ColourRole remedyRole          = ColourOperation

colourDomain : RoleFamily
colourDomain = record { Carrier = WaveContact ; RoleType = ColourRole }

data ColourLensWitness :
  ProofLens → (r : FormalRole) → ColourRole r → Set where
  waveContactWitness :
    (contact : WaveContact) →
    ColourLensWitness waveLens carrierSpaceRole contact

  opponentSpectrumWitness :
    (tool : WaveContact → OpponentFieldSample) →
    ColourLensWitness spectralLens spectrumToolRole tool

  balancedTernaryRefinementWitness :
    (residuals : List ColourResidual) →
    ColourLensWitness btBraidLens residualRole residuals

  semioticGraphWitness :
    ColourLensWitness graphLens observableRole semioticSurface

colourLenses : LensFamily colourDomain
colourLenses = record { LensWitness = ColourLensWitness }

-- Typed guards: the target propositions are intentionally uninhabited here.
data QualiaRecovery : Set where
data ExactSpectrumRecovery : Set where
data CrossSurfaceIdentity : Set where

noQualiaRecovery : QualiaRecovery → ⊥
noQualiaRecovery ()

noExactSpectrumRecovery : ExactSpectrumRecovery → ⊥
noExactSpectrumRecovery ()

noCrossSurfaceIdentity : CrossSurfaceIdentity → ⊥
noCrossSurfaceIdentity ()
