module DASHI.Physics.Closure.NSTriadKNB2PressureSpectralTargetRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND78 / DEFECT-RESOLVED B2 TARGET
--
-- This file combines Round77's positive frame-weighted excess with Round78's
-- exact pressure spectral bracket.  A selected event must identify its physical
-- excess with
--
--   epsilon
--     = W.W
--       + Omega [ -lambda3^D - D_align - (Omega-Sigma)/6 ]
--       - D_additional.
--
-- Since epsilon>0 on a supercritical row, B2 forces the strict scalar target
--
--   W.W + Omega * bracket > D_additional.
--
-- Conversely, on any event where bracket<=0 and W.W<=D_additional, the
-- supercritical row is impossible.  This is the sharp proof-or-kill reduction:
-- either the selected critical trajectory enters a quantitatively pressure-
-- enabling / sufficiently strong cross-mode stretching region, or the existing
-- depletion branch wins there.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNFrameWeightedSupercriticalPropagationRound77Exact as Propagation
import DASHI.Physics.Closure.NSTriadKNDeviatoricPressureAlignmentDefectRound78Exact as Defect
import DASHI.Physics.Closure.NSTriadKNPressureAlignmentDefectSpectralBracketRound78Exact as Spectral
import DASHI.Physics.Closure.NSTriadKNFrameWeightedStretchingDepletionGateRound78Exact as Gate

record DefectResolvedB2Event
    (row : Propagation.FrameWeightedSupercriticalRow) : Set where
  field
    stretchingSquare : ℚ
    enstrophy : ℚ
    strainIntensity : ℚ
    pressureAlignment : Defect.PressureEigenframeAlignment
    additionalDepletion : ℚ
    enstrophyNonnegative : 0ℚ ≤ enstrophy

    excessMeaning :
      Propagation.excess row
      ≡ Spectral.inviscidAccelerationWithAlignmentDefect
          stretchingSquare enstrophy strainIntensity pressureAlignment
          - additionalDepletion

open DefectResolvedB2Event public

supercriticalEventForcesStrictSpectralTarget :
  ∀ {row} (event : DefectResolvedB2Event row) →
  0ℚ <
    Spectral.inviscidAccelerationWithAlignmentDefect
      (stretchingSquare event)
      (enstrophy event)
      (strainIntensity event)
      (pressureAlignment event)
    - additionalDepletion event
supercriticalEventForcesStrictSpectralTarget {row} event =
  subst
    (0ℚ <_)
    (excessMeaning event)
    (Propagation.excessPositive row)

nonpositivePressureAndInsufficientQuadraticRefuteB2 :
  ∀ {row} (event : DefectResolvedB2Event row) →
  Spectral.pressureBracketWithAlignmentDefect
      (enstrophy event)
      (strainIntensity event)
      (pressureAlignment event)
    ≤ 0ℚ →
  stretchingSquare event ≤ additionalDepletion event →
  0ℚ < 0ℚ
nonpositivePressureAndInsufficientQuadraticRefuteB2 event bracket≤0 stretching≤cost =
  let
    acceleration≤stretching :
      Spectral.inviscidAccelerationWithAlignmentDefect
        (stretchingSquare event)
        (enstrophy event)
        (strainIntensity event)
        (pressureAlignment event)
      ≤ stretchingSquare event
    acceleration≤stretching =
      Spectral.nonpositiveDefectBracketCannotIncreaseQuadraticAcceleration
        (stretchingSquare event)
        (enstrophy event)
        (strainIntensity event)
        (pressureAlignment event)
        (enstrophyNonnegative event)
        bracket≤0

    acceleration≤cost :
      Spectral.inviscidAccelerationWithAlignmentDefect
        (stretchingSquare event)
        (enstrophy event)
        (strainIntensity event)
        (pressureAlignment event)
      ≤ additionalDepletion event
    acceleration≤cost = ℚP.≤-trans acceleration≤stretching stretching≤cost

    surplus≤0 :
      Spectral.inviscidAccelerationWithAlignmentDefect
        (stretchingSquare event)
        (enstrophy event)
        (strainIntensity event)
        (pressureAlignment event)
      - additionalDepletion event
      ≤ 0ℚ
    surplus≤0 =
      Gate.differenceNonpositiveFromDominance
        (Spectral.inviscidAccelerationWithAlignmentDefect
          (stretchingSquare event)
          (enstrophy event)
          (strainIntensity event)
          (pressureAlignment event))
        (additionalDepletion event)
        acceleration≤cost
  in
  ℚP.<-≤-trans
    (supercriticalEventForcesStrictSpectralTarget event)
    surplus≤0

round78B2ReducedToDefectResolvedPressureSpectralTarget : Bool
round78B2ReducedToDefectResolvedPressureSpectralTarget = true

round78NonpositivePressurePlusInsufficientQuadraticKillsB2 : Bool
round78NonpositivePressurePlusInsufficientQuadraticKillsB2 = true

round78SelectedCriticalEventsInstantiateDefectResolvedTarget : Bool
round78SelectedCriticalEventsInstantiateDefectResolvedTarget = false

round78B2ReducedToDefectResolvedPressureSpectralTargetIsTrue :
  round78B2ReducedToDefectResolvedPressureSpectralTarget ≡ true
round78B2ReducedToDefectResolvedPressureSpectralTargetIsTrue = refl
