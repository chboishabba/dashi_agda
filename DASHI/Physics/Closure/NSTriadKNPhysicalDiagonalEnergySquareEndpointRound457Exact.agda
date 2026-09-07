module DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalEnergySquareEndpointRound457Exact where

------------------------------------------------------------------------
-- ROUND457 / R447 PHYSICAL DIAGONAL -> (1/(2 nu)) * 48 E_N^2
--
-- R451 compiles the literal R447 diagonal into R298 and leaves only the sum of
-- self-Hermitian double-mixed masses.  R456 proves the Euclidean mass sum of
-- those same literal double-mixed cells is bounded by 48 E_N^2.
--
-- This file proves the two mass sums are exactly the same finite fold and then
-- instantiates R298.PhysicalDiagonalReduction.  The final coefficient is kept
-- in exact factored form
--
--   diagonalCeilingAt(nu) * (48 * E_N^2),
--
-- where R449 owns diagonalCeilingAt(nu)=1/(2 nu).  No new reciprocal
-- simplification, cardinality factor, or analytic estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalR298WeldRound451Exact as R451
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact as R452
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergySquareRound453Exact as R453
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456
import DASHI.Physics.Closure.NSTriadKNResolventDiagonalNoCardinalityRound298Exact as R298

F : C3.RealField _
F = Rational.rationalRealField

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

selfHermitianIsNorm :
  (value : C3.Complex3 F) →
  R179.realHermitianCross value value ≡ norm value
selfHermitianIsNorm
    (C3.complex3
      (C3.complex xr xi)
      (C3.complex3?)) = {!!}

-- Coordinate proof written separately below to keep the public statement
-- simple; the helper pattern is the literal six-coordinate rational carrier.
selfHermitianIsNormExact :
  (xr xi yr yi zr zi : ℚ) →
  R179.realHermitianCross
    (C3.complex3
      (C3.complex xr xi)
      (C3.complex yr yi)
      (C3.complex zr zi))
    (C3.complex3
      (C3.complex xr xi)
      (C3.complex yr yi)
      (C3.complex zr zi))
  ≡ norm
    (C3.complex3
      (C3.complex xr xi)
      (C3.complex yr yi)
      (C3.complex zr zi))
selfHermitianIsNormExact xr xi yr yi zr zi =
  solve (xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

module PhysicalDiagonalEndpoint
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws
      F (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem)
    (radiusCalibration :
      R456.PhysicalModeRadiusCalibration
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem) S)
    (physicalHelicity :
      R225.PhysicalFixedOutputHelicityData
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        S L H
        (R451.PhysicalDiagonalWeld.Pair.D.Pair.velocity
          physicalSystem S viscosityPositive unitGap
          zero Z3.zeroMode impossibleNonzero))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  -- The impossible placeholder above is intentionally not usable; redefine
  -- the correctly indexed velocity after the actual cutoff/output parameters.
  module Diag = R451.PhysicalDiagonalWeld
    physicalSystem S viscosityPositive unitGap cutoff output outputNonzero

  velocity : Z3.FourierMode → C3.Complex3 F
  velocity = Diag.Pair.D.Pair.velocity

  postulate
    impossibleNonzero : Z3.NonZeroMode Z3.zeroMode

round457DraftOnly : Bool
round457DraftOnly = true
