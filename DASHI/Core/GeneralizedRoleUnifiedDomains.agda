module DASHI.Core.GeneralizedRoleUnifiedDomains where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.ProofLens

------------------------------------------------------------------------
-- Ramsey / correlated-colouring domain.

data RamseyState : Set where
  latentGeometry binaryColouring cliqueSurface : RamseyState

data RamseyOperator : Set where
  sampleEmbedding thresholdDistance countCliques restrictFibre : RamseyOperator

data RamseyObservable : Set where
  redClique blueClique expectedCliqueCount lowerBound : RamseyObservable

data RamseyResidual : Set where
  monochromaticCliqueRisk diagonalGap constructionGap : RamseyResidual

RamseyRole : FormalRole → Set
RamseyRole carrierSpaceRole    = RamseyState
RamseyRole stateRole           = RamseyState
RamseyRole operatorRole        = RamseyOperator
RamseyRole observableRole      = RamseyObservable
RamseyRole spectrumToolRole    = List RamseyObservable → List RamseyObservable
RamseyRole boundaryGateRole    = RamseyState → Bool
RamseyRole obstructionRole     = RamseyResidual
RamseyRole algebraRole         = RamseyOperator → RamseyOperator → RamseyOperator
RamseyRole proofObligationRole = RamseyObservable → Set
RamseyRole decompositionRole   = RamseyState → List RamseyObservable
RamseyRole hamiltonianRole     = RamseyState → Nat
RamseyRole metricRole          = RamseyState → RamseyState → Nat
RamseyRole projectionRole      = RamseyState → RamseyObservable
RamseyRole residualRole        = List RamseyResidual
RamseyRole receiptRole         = RamseyObservable
RamseyRole functorRole         = RamseyOperator → RamseyOperator
RamseyRole transitionRole      = RamseyState → RamseyOperator → RamseyState
RamseyRole invariantRole       = RamseyState → Set
RamseyRole symmetryRole        = RamseyState → RamseyState
RamseyRole modeRole            = RamseyState
RamseyRole sourceRole          = RamseyState
RamseyRole sinkRole            = RamseyState
RamseyRole flowRole            = RamseyState → RamseyState
RamseyRole constraintRole      = RamseyState → Set
RamseyRole remedyRole          = RamseyOperator

ramseyDomain : RoleFamily
ramseyDomain = record { Carrier = RamseyState ; RoleType = RamseyRole }

------------------------------------------------------------------------
-- Cross-jurisdiction regulation domain.

data RegulatoryState : Set where
  hiddenActivity documentedPolicy auditedActivity promotedCompliance : RegulatoryState

data RegulatoryOperator : Set where
  projectJurisdiction compareObligations auditEvidence computeConflict : RegulatoryOperator

data RegulatoryObservable : Set where
  obligation permission prohibition reportingRequirement : RegulatoryObservable

data RegulatoryResidual : Set where
  jurisdictionConflict missingEvidence implementationUnknown : RegulatoryResidual

RegulatoryRole : FormalRole → Set
RegulatoryRole carrierSpaceRole    = RegulatoryState
RegulatoryRole stateRole           = RegulatoryState
RegulatoryRole operatorRole        = RegulatoryOperator
RegulatoryRole observableRole      = RegulatoryObservable
RegulatoryRole spectrumToolRole    = List RegulatoryObservable → List RegulatoryObservable
RegulatoryRole boundaryGateRole    = RegulatoryState → Bool
RegulatoryRole obstructionRole     = RegulatoryResidual
RegulatoryRole algebraRole         = RegulatoryOperator → RegulatoryOperator → RegulatoryOperator
RegulatoryRole proofObligationRole = RegulatoryObservable → Set
RegulatoryRole decompositionRole   = RegulatoryState → List RegulatoryObservable
RegulatoryRole hamiltonianRole     = RegulatoryState → Nat
RegulatoryRole metricRole          = RegulatoryState → RegulatoryState → Nat
RegulatoryRole projectionRole      = RegulatoryState → List RegulatoryObservable
RegulatoryRole residualRole        = List RegulatoryResidual
RegulatoryRole receiptRole         = RegulatoryObservable
RegulatoryRole functorRole         = RegulatoryOperator → RegulatoryOperator
RegulatoryRole transitionRole      = RegulatoryState → RegulatoryOperator → RegulatoryState
RegulatoryRole invariantRole       = RegulatoryState → Set
RegulatoryRole symmetryRole        = RegulatoryState → RegulatoryState
RegulatoryRole modeRole            = RegulatoryState
RegulatoryRole sourceRole          = RegulatoryState
RegulatoryRole sinkRole            = RegulatoryState
RegulatoryRole flowRole            = RegulatoryState → RegulatoryState
RegulatoryRole constraintRole      = RegulatoryState → Set
RegulatoryRole remedyRole          = RegulatoryOperator

regulatoryDomain : RoleFamily
regulatoryDomain = record { Carrier = RegulatoryState ; RoleType = RegulatoryRole }

------------------------------------------------------------------------
-- Physical/perceptual/semiotic colour domain.

data ColourLayer : Set where
  physicalColour perceptualColour coordinateColour semioticColour : ColourLayer

data ColourOperator : Set where
  spectralResponse opponentProjection coordinateEncode interpretSign : ColourOperator

data ColourObservable : Set where
  wavelength opponentCoordinate colourLabel signAssociation : ColourObservable

data ColourResidual : Set where
  metamerism observerVariance culturalVariance hiddenSpectrum : ColourResidual

ColourRole : FormalRole → Set
ColourRole carrierSpaceRole    = ColourLayer
ColourRole stateRole           = ColourLayer
ColourRole operatorRole        = ColourOperator
ColourRole observableRole      = ColourObservable
ColourRole spectrumToolRole    = ColourObservable → Nat
ColourRole boundaryGateRole    = ColourLayer → Bool
ColourRole obstructionRole     = ColourResidual
ColourRole algebraRole         = ColourOperator → ColourOperator → ColourOperator
ColourRole proofObligationRole = ColourObservable → Set
ColourRole decompositionRole   = ColourLayer → List ColourObservable
ColourRole hamiltonianRole     = ColourLayer → Nat
ColourRole metricRole          = ColourLayer → ColourLayer → Nat
ColourRole projectionRole      = ColourLayer → ColourObservable
ColourRole residualRole        = List ColourResidual
ColourRole receiptRole         = ColourObservable
ColourRole functorRole         = ColourOperator → ColourOperator
ColourRole transitionRole      = ColourLayer → ColourOperator → ColourLayer
ColourRole invariantRole       = ColourLayer → Set
ColourRole symmetryRole        = ColourLayer → ColourLayer
ColourRole modeRole            = ColourLayer
ColourRole sourceRole          = ColourLayer
ColourRole sinkRole            = ColourLayer
ColourRole flowRole            = ColourLayer → ColourLayer
ColourRole constraintRole      = ColourLayer → Set
ColourRole remedyRole          = ColourOperator

colourUnifiedDomain : RoleFamily
colourUnifiedDomain = record { Carrier = ColourLayer ; RoleType = ColourRole }

------------------------------------------------------------------------
-- Cybersyn / viable feedback governance domain.

data CyberneticState : Set where
  realActivity sensedState modelState decisionState updatedState : CyberneticState

data CyberneticOperator : Set where
  sense normalize simulate decide intervene feedback : CyberneticOperator

data CyberneticObservable : Set where
  productionSignal wellbeingSignal anomalySignal modelPrediction : CyberneticObservable

data CyberneticResidual : Set where
  unmeasuredVariable sabotageSignal modelError legitimacyGap : CyberneticResidual

CyberneticRole : FormalRole → Set
CyberneticRole carrierSpaceRole    = CyberneticState
CyberneticRole stateRole           = CyberneticState
CyberneticRole operatorRole        = CyberneticOperator
CyberneticRole observableRole      = CyberneticObservable
CyberneticRole spectrumToolRole    = List CyberneticObservable → List CyberneticObservable
CyberneticRole boundaryGateRole    = CyberneticState → Bool
CyberneticRole obstructionRole     = CyberneticResidual
CyberneticRole algebraRole         = CyberneticOperator → CyberneticOperator → CyberneticOperator
CyberneticRole proofObligationRole = CyberneticObservable → Set
CyberneticRole decompositionRole   = CyberneticState → List CyberneticObservable
CyberneticRole hamiltonianRole     = CyberneticState → Nat
CyberneticRole metricRole          = CyberneticState → CyberneticState → Nat
CyberneticRole projectionRole      = CyberneticState → List CyberneticObservable
CyberneticRole residualRole        = List CyberneticResidual
CyberneticRole receiptRole         = CyberneticObservable
CyberneticRole functorRole         = CyberneticOperator → CyberneticOperator
CyberneticRole transitionRole      = CyberneticState → CyberneticOperator → CyberneticState
CyberneticRole invariantRole       = CyberneticState → Set
CyberneticRole symmetryRole        = CyberneticState → CyberneticState
CyberneticRole modeRole            = CyberneticState
CyberneticRole sourceRole          = CyberneticState
CyberneticRole sinkRole            = CyberneticState
CyberneticRole flowRole            = CyberneticState → CyberneticState
CyberneticRole constraintRole      = CyberneticState → Set
CyberneticRole remedyRole          = CyberneticOperator

cyberneticDomain : RoleFamily
cyberneticDomain = record { Carrier = CyberneticState ; RoleType = CyberneticRole }
