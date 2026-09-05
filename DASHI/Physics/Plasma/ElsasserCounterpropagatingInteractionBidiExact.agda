module DASHI.Physics.Plasma.ElsasserCounterpropagatingInteractionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ElsasserMHDChartExact as Elsasser

------------------------------------------------------------------------
-- COUNTERPROPAGATING ELSASSER INTERACTION
--
-- In incompressible ideal MHD the nonlinear transport has the shape
--
--   d_t z+ + (z- . grad) z+ = -grad P
--   d_t z- + (z+ . grad) z- = -grad P.
--
-- Thus a nonlinear z+ transfer needs a z- advector and vice versa.  A pure
-- one-direction Elsasser state is an exact nonlinear-depletion boundary in the
-- ideal homogeneous model, not an NS-like self-advection channel.
------------------------------------------------------------------------

data ElsasserOrientation : Set where
  plusOrientation
  minusOrientation
  : ElsasserOrientation

opposite : ElsasserOrientation → ElsasserOrientation
opposite plusOrientation = minusOrientation
opposite minusOrientation = plusOrientation

oppositeInvolutive : (s : ElsasserOrientation) → opposite (opposite s) ≡ s
oppositeInvolutive plusOrientation = refl
oppositeInvolutive minusOrientation = refl

record CounterpropagatingInteraction : Set₁ where
  constructor counterpropagating-interaction
  field
    Mode : Set
    Amplitude : Set
    targetOrientation : ElsasserOrientation
    targetMode advectingMode : Mode
    targetAmplitude advectingAmplitude : Amplitude
    advectorHasOppositeOrientation : Set
    triadOrGradientCoupling : Set
    incompressibilityReceipt : Set
    interactionReference : String

open CounterpropagatingInteraction public

record PureElsasserState : Set₁ where
  constructor pure-elsasser-state
  field
    Mode : Set
    NonzeroAmplitude : Set
    survivingOrientation : ElsasserOrientation
    mode : Mode
    amplitude : NonzeroAmplitude
    oppositeFieldVanishes : Set
    stateReference : String

open PureElsasserState public

record PureStateNonlinearDepletion
    (state : PureElsasserState) : Set where
  constructor pure-state-nonlinear-depletion
  field
    oppositeAdvectorAbsent : Set
    idealQuadraticTransferVanishes : Set
    depletionReference : String

open PureStateNonlinearDepletion public

------------------------------------------------------------------------
-- BIDI boundary / acquisition logic.
------------------------------------------------------------------------

record CounterpropagationBoundary : Set where
  constructor counterpropagation-boundary
  field
    plusNonlinearityNeedsMinusField : Bool
    plusNonlinearityNeedsMinusFieldIsTrue :
      plusNonlinearityNeedsMinusField ≡ true

    minusNonlinearityNeedsPlusField : Bool
    minusNonlinearityNeedsPlusFieldIsTrue :
      minusNonlinearityNeedsPlusField ≡ true

    pureElsasserWaveSelfInteractsAsNavierStokesMode : Bool
    pureElsasserWaveSelfInteractsAsNavierStokesModeIsFalse :
      pureElsasserWaveSelfInteractsAsNavierStokesMode ≡ false

    observedMHDTransferNeedsCounterpropagatingChannelAudit : Bool
    observedMHDTransferNeedsCounterpropagatingChannelAuditIsTrue :
      observedMHDTransferNeedsCounterpropagatingChannelAudit ≡ true

    nsHelicalTriadSignAloneDeterminesMHDTransfer : Bool
    nsHelicalTriadSignAloneDeterminesMHDTransferIsFalse :
      nsHelicalTriadSignAloneDeterminesMHDTransfer ≡ false

canonicalCounterpropagationBoundary : CounterpropagationBoundary
canonicalCounterpropagationBoundary =
  counterpropagation-boundary true refl true refl false refl true refl false refl

elsasserChartDonorReference : String
elsasserChartDonorReference = "DASHI.Physics.Plasma.ElsasserMHDChartExact"
