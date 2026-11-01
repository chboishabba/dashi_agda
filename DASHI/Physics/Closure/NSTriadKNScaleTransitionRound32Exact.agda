module DASHI.Physics.Closure.NSTriadKNScaleTransitionRound32Exact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Package the exact HH-bad repair as a typed transition between the raw
-- Bernstein sheet and the viscous sheet.  The transition certificate carries
-- the physical occupation inequality; consuming it yields the already-proved
-- exact absorption theorem.  No producer is fabricated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _≤_)

import DASHI.Physics.Closure.NSTriadKNHHBadTimeScaleGainRound31Exact as HHBad

record InverseScaleTransport : Set where
  constructor inverse-scale-transport
  field
    cell : HHBad.HHBadTimeScaleCell
    sourceScalePower : ℚ
    targetScalePower : ℚ
    exactlyOnePowerRepaired :
      sourceScalePower ≡ targetScalePower + 1ℚ

open InverseScaleTransport public

transportedRawCost : InverseScaleTransport → ℚ
transportedRawCost transport =
  HHBad.rawBernsteinBadCost (cell transport)

transportTarget : InverseScaleTransport → ℚ
transportTarget transport =
  HHBad.etaShellDiffusionCost (cell transport)

inverseScaleTransportAbsorbs :
  ∀ transport → transportedRawCost transport ≤ transportTarget transport
inverseScaleTransportAbsorbs transport =
  HHBad.timeScaleGainAbsorbsRawBernstein (cell transport)

record PhysicalInverseScaleProducer : Set where
  field
    atShell : ℚ → InverseScaleTransport

open PhysicalInverseScaleProducer public

physicalProducerGivesAbsorption :
  PhysicalInverseScaleProducer →
  ∀ shell →
  transportedRawCost (atShell shell) ≤ transportTarget (atShell shell)
physicalProducerGivesAbsorption producer shell =
  inverseScaleTransportAbsorbs (atShell producer shell)

inverseScaleTransportInterfaceClosed : Bool
inverseScaleTransportInterfaceClosed = true

physicalInverseScaleProducerConstructed : Bool
physicalInverseScaleProducerConstructed = false

inverseScaleTransportInterfaceClosedIsTrue :
  inverseScaleTransportInterfaceClosed ≡ true
inverseScaleTransportInterfaceClosedIsTrue = refl

physicalInverseScaleProducerConstructedIsFalse :
  physicalInverseScaleProducerConstructed ≡ false
physicalInverseScaleProducerConstructedIsFalse = refl
