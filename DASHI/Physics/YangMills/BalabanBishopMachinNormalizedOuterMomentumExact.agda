module DASHI.Physics.YangMills.BalabanBishopMachinNormalizedOuterMomentumExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Errett Bishop and Douglas Bridges, "Constructive Analysis", Springer 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
-- Instantiate the normalized Brillouin outer-angle theorem with the ACTUAL
-- Bishop Machin real constructed from convergent arctangent series.  Round57
-- proves 3 < pi_M < 22/7, so the old numeric pi-window input disappears.
--
-- This does NOT yet identify pi_M with the period used by the physical Fourier
-- convention.  That semantic period theorem remains the sole pi-facing YM leaf.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised using (_/_)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window
import DASHI.Physics.YangMills.BalabanBishopNormalizedOuterMomentumAngleExact as Angle
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Order
open import DASHI.Physics.YangMills.CompactLieProofLevel

threeNN : Bishop.NonNegative (Angle.embed Angle.three)
threeNN = Order.embeddedRationalNonnegative Angle.three nonNeg

machinPiNonnegative : Bishop.NonNegative Machin.bishopMachinPi
machinPiNonnegative =
  BishopP.0≤x⇒nonNegx
    (BishopP.≤-trans
      (BishopP.nonNegx⇒0≤x threeNN)
      Window.threeBelowMachinPiNonStrict)

record MachinNormalizedOuterCoordinateData : Set₁ where
  field
    qAbs angle : Bishop.ℝ
    qAbsNonnegative : Bishop.NonNegative qAbs
    qOuterLower : Bishop._≤_ (Angle.embed Angle.half) qAbs
    qOuterUpper : Bishop._≤_ qAbs (Angle.embed Angle.one)
    angleDefinition :
      Bishop._≃_ angle
        (Bishop._*_
          (Angle.embed Angle.half)
          (Bishop._*_ Machin.bishopMachinPi qAbs))

open MachinNormalizedOuterCoordinateData public

asNormalizedOuterMomentumAngleData :
  MachinNormalizedOuterCoordinateData →
  Angle.NormalizedOuterMomentumAngleData
asNormalizedOuterMomentumAngleData data = record
  { Angle.NormalizedOuterMomentumAngleData.piValue = Machin.bishopMachinPi
  ; Angle.NormalizedOuterMomentumAngleData.qAbs = qAbs data
  ; Angle.NormalizedOuterMomentumAngleData.angle = angle data
  ; Angle.NormalizedOuterMomentumAngleData.piNonnegative = machinPiNonnegative
  ; Angle.NormalizedOuterMomentumAngleData.qAbsNonnegative = qAbsNonnegative data
  ; Angle.NormalizedOuterMomentumAngleData.piLower =
      Window.threeBelowMachinPiNonStrict
  ; Angle.NormalizedOuterMomentumAngleData.piUpper =
      Window.machinPiBelowTwentyTwoSeventhsNonStrict
  ; Angle.NormalizedOuterMomentumAngleData.qOuterLower = qOuterLower data
  ; Angle.NormalizedOuterMomentumAngleData.qOuterUpper = qOuterUpper data
  ; Angle.NormalizedOuterMomentumAngleData.angleDefinition = angleDefinition data
  }

machinNormalizedAngleLower :
  (data : MachinNormalizedOuterCoordinateData) →
  Bishop._≤_ (Angle.embed Angle.threeQuarters) (angle data)
machinNormalizedAngleLower data =
  Angle.angleLower (asNormalizedOuterMomentumAngleData data)

machinNormalizedAngleUpper :
  (data : MachinNormalizedOuterCoordinateData) →
  Bishop._≤_ (angle data) (Angle.embed Angle.elevenSevenths)
machinNormalizedAngleUpper data =
  Angle.angleUpper (asNormalizedOuterMomentumAngleData data)

bishopMachinNormalizedOuterAngleWindowLevel : ProofLevel
bishopMachinNormalizedOuterAngleWindowLevel = machineChecked

-- Remaining source semantic leaf only: the normalized Fourier coordinate must
-- use this same Machin-constructed period.  No numerical pi bound remains.
literalWilsonFourierPeriodIsMachinPiLevel : ProofLevel
literalWilsonFourierPeriodIsMachinPiLevel = conditional
