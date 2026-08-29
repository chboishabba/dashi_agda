module DASHI.Physics.YangMills.BalabanWilsonFourierMachinPeriodCarrierExact where

------------------------------------------------------------------------
-- ROUND86: ONE CONSTRUCTIVE PERIOD CARRIER, NOT TWO INDEPENDENT PI OBJECTS
--
-- PRIMARY / CONSTRUCTIVE SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- MATHEMATICAL ROLE
--
-- Round57 constructed a literal Bishop real pi_M by Machin arctangent series and
-- proved 3 < pi_M < 22/7.  The remaining comment-level seam said the Wilson
-- Fourier period had to be "identified" with this same real.  That is an
-- avoidable duplication if the formal lattice Fourier convention is introduced
-- with pi_M as its period parameter from the start.
--
-- This module supplies that source-native carrier.  It does NOT claim a theorem
-- that an independently postulated transcendental constant equals pi_M; no such
-- second constant is introduced.  Any literal Fourier evaluator that consumes
-- `WilsonFourierPeriodCarrier` therefore uses the same constructive real
-- definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import Real as Bishop
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Physics.YangMills.BalabanBishopNormalizedOuterMomentumAngleExact as Angle
import DASHI.Physics.YangMills.BalabanBishopMachinNormalizedOuterMomentumExact as Outer
open import DASHI.Physics.YangMills.CompactLieProofLevel

record WilsonFourierPeriodCarrier : Set₁ where
  field
    periodPi : Bishop.ℝ
    periodPiIsMachin : periodPi ≡ Machin.bishopMachinPi

open WilsonFourierPeriodCarrier public

canonicalWilsonFourierPeriodCarrier : WilsonFourierPeriodCarrier
canonicalWilsonFourierPeriodCarrier = record
  { periodPi = Machin.bishopMachinPi
  ; periodPiIsMachin = refl
  }

canonicalWilsonPeriodIsMachin :
  periodPi canonicalWilsonFourierPeriodCarrier ≡ Machin.bishopMachinPi
canonicalWilsonPeriodIsMachin = refl

-- The actual normalized outer-coordinate data can now be built directly on the
-- canonical period carrier; no equality transport between two pi values occurs.
record CanonicalWilsonOuterCoordinate : Set₁ where
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

open CanonicalWilsonOuterCoordinate public

canonicalOuterAsMachinData :
  CanonicalWilsonOuterCoordinate → Outer.MachinNormalizedOuterCoordinateData
canonicalOuterAsMachinData dataSet = record
  { Outer.MachinNormalizedOuterCoordinateData.qAbs = qAbs dataSet
  ; Outer.MachinNormalizedOuterCoordinateData.angle = angle dataSet
  ; Outer.MachinNormalizedOuterCoordinateData.qAbsNonnegative =
      qAbsNonnegative dataSet
  ; Outer.MachinNormalizedOuterCoordinateData.qOuterLower =
      qOuterLower dataSet
  ; Outer.MachinNormalizedOuterCoordinateData.qOuterUpper =
      qOuterUpper dataSet
  ; Outer.MachinNormalizedOuterCoordinateData.angleDefinition =
      angleDefinition dataSet
  }

wilsonFourierMachinPeriodCarrierLevel : ProofLevel
wilsonFourierMachinPeriodCarrierLevel = machineChecked

-- Remaining implementation seam: the literal Wilson/Brillouin evaluator must
-- USE this carrier rather than introducing an unrelated period field.  That is a
-- same-object wiring obligation, not a new transcendental equality theorem.
literalEvaluatorUsesCanonicalWilsonPeriodLevel : ProofLevel
literalEvaluatorUsesCanonicalWilsonPeriodLevel = conditional
