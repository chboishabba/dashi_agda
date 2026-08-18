module DASHI.Physics.Closure.NSTriadKNPressureStretchingRotationJointTargetRound79Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.1017/jfm.2023.786.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Tosio Kato.
-- Title: "Perturbation Theory for Linear Operators".
-- DOI: 10.1007/978-3-642-66282-9.
--
-- ROUND79 / CORRECTED C3 SAME-EVENT TARGET
--
-- Round78 correctly reduced the AMPLITUDE side to a pressure-resolved scalar
-- stretching surplus. Round79 proves that scalar contraction does not determine
-- off-diagonal pressure injection, so the eigenframe/coherence side must remain
-- an independent coordinate on the SAME selected critical event.
--
-- A corrected C3 witness therefore carries simultaneously:
--
--   (A) the Round78 DefectResolvedB2Event;
--   (B) a division-free pressure-eigenframe rotation budget
--         |Pi_off| <= R * spectralGap;
--   (C) same-event identity/provenance evidence supplied by the physical
--       selected-trajectory producer.
--
-- From such a witness, strict frame-weighted supercriticality still gives the
-- Round78 scalar target, while the eigenframe rotation estimate is available
-- without a hidden reciprocal-gap assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNFrameWeightedSupercriticalPropagationRound77Exact as Propagation
import DASHI.Physics.Closure.NSTriadKNB2PressureSpectralTargetRound78Exact as Scalar
import DASHI.Physics.Closure.NSTriadKNPressureEigenframeRotationGapBudgetRound79Exact as Rotation

record JointPressureStretchingRotationEvent
    (row : Propagation.FrameWeightedSupercriticalRow) : Set where
  constructor joint-pressure-stretching-rotation-event
  field
    scalarEvent : Scalar.DefectResolvedB2Event row
    rotationInputs : Rotation.PressureRotationClosureInputs

    -- These proof-relevant same-event coordinates are deliberately abstract at
    -- this layer. The selected Galerkin trajectory must instantiate them from
    -- one physical time/packet/mode event; this module does not invent IDs.
    PhysicalEventIdentity : Set
    physicalEventWitness : PhysicalEventIdentity

open JointPressureStretchingRotationEvent public

jointEventForcesStrictStretchingTarget :
  ∀ {row} →
  (event : JointPressureStretchingRotationEvent row) →
  Scalar.additionalDepletion (scalarEvent event)
  <
  (let scalar = scalarEvent event in
   DASHI.Physics.Closure.NSTriadKNPressureAlignmentDefectSpectralBracketRound78Exact.inviscidAccelerationWithAlignmentDefect
     (Scalar.stretchingSquare scalar)
     (Scalar.enstrophy scalar)
     (Scalar.strainIntensity scalar)
     (Scalar.pressureAlignment scalar))
jointEventForcesStrictStretchingTarget event =
  Scalar.supercriticalEventForcesStrictSpectralTarget (scalarEvent event)

jointEventCarriesDivisionFreeRotationBound :
  ∀ {row} →
  (event : JointPressureStretchingRotationEvent row) →
  Rotation.injectionMagnitude (Rotation.gapBudget (rotationInputs event))
  ≤ Rotation.rotationBudget (Rotation.gapBudget (rotationInputs event))
      * Rotation.spectralGap (Rotation.gapBudget (rotationInputs event))
jointEventCarriesDivisionFreeRotationBound event =
  Rotation.divisionFreeRotationBound
    (Rotation.gapBudget (rotationInputs event))

round79CorrectC3NeedsPressureStretchingAndRotationCoordinates : Bool
round79CorrectC3NeedsPressureStretchingAndRotationCoordinates = true

round79SelectedCriticalEventsInstantiateJointPressureTarget : Bool
round79SelectedCriticalEventsInstantiateJointPressureTarget = false

round79CorrectC3NeedsPressureStretchingAndRotationCoordinatesIsTrue :
  round79CorrectC3NeedsPressureStretchingAndRotationCoordinates ≡ true
round79CorrectC3NeedsPressureStretchingAndRotationCoordinatesIsTrue = refl
