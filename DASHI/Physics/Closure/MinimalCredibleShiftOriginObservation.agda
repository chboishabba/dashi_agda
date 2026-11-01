module DASHI.Physics.Closure.MinimalCredibleShiftOriginObservation where

open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_)

import CRTJFixedPointBridge as CRTJ
import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
import DASHI.Physics.Closure.ObservablePredictionPackage as OPP
import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
import DASHI.Physics.Closure.PhysicsClosureFull as PCF

------------------------------------------------------------------------
-- W8b: concrete origin-observation receipt for the minimal-credible shift
-- path.
--
-- The generic `OriginObservationReceipt` is deliberately Set-level for its
-- carrier slots, so this module uses small tokens and exposes separate
-- projections back to the actual minimal-credible closure path.  This gives
-- W3 a typed consumer surface without promoting empirical adequacy.

data MinimalCredibleShiftOriginSource : Set where
  minimalCredibleShiftPath : MinimalCredibleShiftOriginSource

data MinimalCredibleShiftOriginCarrier : Set where
  minimalCredibleShiftCarrier : MinimalCredibleShiftOriginCarrier

data MinimalCredibleShiftOriginObs : Set where
  minimalCredibleShiftObservation : MinimalCredibleShiftOriginObs

sourceClosure :
  MinimalCredibleShiftOriginSource →
  MCPC.MinimalCrediblePhysicsClosure
sourceClosure minimalCredibleShiftPath =
  MCCSI.minimumCredibleClosureShift

carrierClosure :
  MinimalCredibleShiftOriginCarrier →
  MCPC.MinimalCrediblePhysicsClosure
carrierClosure minimalCredibleShiftCarrier =
  MCCSI.minimumCredibleClosureShift

observationPackage :
  MinimalCredibleShiftOriginObs →
  OPP.ObservablePredictionPackage
observationPackage minimalCredibleShiftObservation =
  MCPC.observables MCCSI.minimumCredibleClosureShift

mapToMinimalCredibleShiftCarrier :
  MinimalCredibleShiftOriginSource →
  MinimalCredibleShiftOriginCarrier
mapToMinimalCredibleShiftCarrier minimalCredibleShiftPath =
  minimalCredibleShiftCarrier

transportMinimalCredibleShiftCarrier :
  MinimalCredibleShiftOriginCarrier →
  MinimalCredibleShiftOriginCarrier
transportMinimalCredibleShiftCarrier minimalCredibleShiftCarrier =
  minimalCredibleShiftCarrier

originObservationMapMinimalCredibleShift :
  MinimalCredibleShiftOriginCarrier →
  MinimalCredibleShiftOriginObs
originObservationMapMinimalCredibleShift minimalCredibleShiftCarrier =
  minimalCredibleShiftObservation

record MinimalCredibleShiftSignatureOwner : Set where
  constructor minimalCredibleShiftSignatureOwner
  field
    signatureMatch :
      PCF.PhysicsClosureFull.signature31
        (MCPC.full MCCSI.minimumCredibleClosureShift)
      ≡
      OPP.ObservablePredictionPackage.provedSignature
        (MCPC.observables MCCSI.minimumCredibleClosureShift)

minimalCredibleShiftSignatureOwnerValue :
  MinimalCredibleShiftSignatureOwner
minimalCredibleShiftSignatureOwnerValue =
  minimalCredibleShiftSignatureOwner
    (MCPC.closureSignatureMatchesPrediction
      MCCSI.minimumCredibleClosureShift)

data MinimalCredibleShiftDynamicsWitnessToken : Set where
  minimalCredibleShiftDynamicsWitnessToken :
    MinimalCredibleShiftDynamicsWitnessToken

minimalCredibleShiftDynamicsWitness :
  DCW.DynamicalClosureWitness
minimalCredibleShiftDynamicsWitness =
  MCPC.authoritativeDynamicsWitness MCCSI.minimumCredibleClosureShift

data MinimalCredibleShiftEmpiricalCaution : Set where
  empiricalAdequacyBridgeNotDischarged :
    MinimalCredibleShiftEmpiricalCaution

data MinimalCredibleShiftClosureBoundary : Set where
  originObservationReceiptDoesNotPromoteClosure :
    MinimalCredibleShiftClosureBoundary

minimalCredibleShiftOriginObservationReceipt :
  P0.OriginObservationReceipt
minimalCredibleShiftOriginObservationReceipt =
  record
    { Source = MinimalCredibleShiftOriginSource
    ; Carrier = MinimalCredibleShiftOriginCarrier
    ; Obs = MinimalCredibleShiftOriginObs
    ; SignatureOwner = MinimalCredibleShiftSignatureOwner
    ; DynamicsWitness = MinimalCredibleShiftDynamicsWitnessToken
    ; CRTJBridge = CRTJ.CRTJFixedPointBridge
    ; mapToCarrier = mapToMinimalCredibleShiftCarrier
    ; carrierTransport = transportMinimalCredibleShiftCarrier
    ; originObservationMap = originObservationMapMinimalCredibleShift
    ; signatureOwner = minimalCredibleShiftSignatureOwnerValue
    ; dynamicsWitness = minimalCredibleShiftDynamicsWitnessToken
    ; crtJBridge = CRTJ.crtJFixedPointBridgeSurface
    ; empiricalStatus = P0.empiricalBlocked
    ; empiricalCaution = MinimalCredibleShiftEmpiricalCaution
    ; closureClaimBoundary = MinimalCredibleShiftClosureBoundary
    }

------------------------------------------------------------------------
-- Typed diagnostic: the concrete receipt exists, but positive empirical
-- promotion is blocked until W3 supplies an adequacy bridge.

data MinimalCredibleShiftOriginMissingField : Set where
  missingEmpiricalAdequacyBridge :
    MinimalCredibleShiftOriginMissingField

record MinimalCredibleShiftBlockedOriginInstance : Setω where
  constructor minimalCredibleShiftBlockedOriginInstance
  field
    receipt : P0.OriginObservationReceipt
    missingField : MinimalCredibleShiftOriginMissingField
    empiricalCautionWitness : MinimalCredibleShiftEmpiricalCaution
    closureBoundaryWitness : MinimalCredibleShiftClosureBoundary

minimalCredibleShiftBlockedOriginInstanceValue :
  MinimalCredibleShiftBlockedOriginInstance
minimalCredibleShiftBlockedOriginInstanceValue =
  minimalCredibleShiftBlockedOriginInstance
    minimalCredibleShiftOriginObservationReceipt
    missingEmpiricalAdequacyBridge
    empiricalAdequacyBridgeNotDischarged
    originObservationReceiptDoesNotPromoteClosure
