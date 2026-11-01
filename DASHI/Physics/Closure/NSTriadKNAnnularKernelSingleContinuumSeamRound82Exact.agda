module DASHI.Physics.Closure.NSTriadKNAnnularKernelSingleContinuumSeamRound82Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND82 / ANNULAR KERNEL FRONTIER COMPRESSION
--
-- The repository already owns, on the actual NS carrier:
--
--   * the compact annular matrix symbol
--         M(k,omega) = phi(|k|^2) Strain_k(omega),
--     with exact support and plateau;
--   * 0 <= phi <= 1 and an exact uniform Frobenius amplitude bound;
--   * exact scalar transition derivatives through order four and explicit
--     uniform bounds on those derivatives;
--   * the entire three-dimensional dyadic L1 summation theorem: once the
--     physical kernel shell masses obey m_j <= M4 2^(-j), every finite partial
--     L1 mass is <= 2 M4.
--
-- Consequently the former pair
--
--   PhysicalAnnularMatrixMultiplierC4
--   PhysicalAnnularInverseFourierKernelL1Bound
--
-- is not two independent source-facing problems.  One continuum theorem must
-- perform the missing matrix-valued chain/product derivative estimate and the
-- literal fourfold inverse-Fourier integration by parts strongly enough to
-- construct `FourthOrderDyadicShellMajorant` for the existing actual symbol.
-- Once that object exists, the L1 endpoint below is already proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNHHGoodCompactAnnularMatrixSymbolRound68Exact as Symbol
import DASHI.Physics.Closure.NSTriadKNHHGoodCompactAnnularMatrixFrobeniusBoundRound68Exact as Size
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularD234UniformBoundsRound74Exact as C4Bounds
import DASHI.Physics.Closure.NSTriadKNHHGoodFourthOrderDyadicL1Round62Exact as L1
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale

actualAnnularKernelL1Endpoint :
  (majorant : L1.FourthOrderDyadicShellMajorant) →
  ∀ n →
  L1.partialShellMass majorant n
  ≤ Scale.two * L1.decayMass majorant
actualAnnularKernelL1Endpoint = L1.finitePartialL1UniformBound

round82ActualCompactAnnularMatrixSymbolAlreadyConstructed : Bool
round82ActualCompactAnnularMatrixSymbolAlreadyConstructed =
  Symbol.round68ConcreteCompactAnnularMatrixSymbolConstructed

round82ActualAnnularMatrixAmplitudeBoundAlreadyConstructed : Bool
round82ActualAnnularMatrixAmplitudeBoundAlreadyConstructed =
  Size.round68CompactAnnularMatrixFrobeniusBoundOneHalf

round82DyadicL1EndpointAlreadyConstructed : Bool
round82DyadicL1EndpointAlreadyConstructed =
  L1.fourthOrderDecaySummabilityClosed

round82AnnularFormerG1G2ReduceToSingleContinuumShellMajorantProducer : Bool
round82AnnularFormerG1G2ReduceToSingleContinuumShellMajorantProducer = true

round82PhysicalActualSymbolFourthOrderShellMajorantConstructed : Bool
round82PhysicalActualSymbolFourthOrderShellMajorantConstructed = false

round82AnnularFormerG1G2ReduceToSingleContinuumShellMajorantProducerIsTrue :
  round82AnnularFormerG1G2ReduceToSingleContinuumShellMajorantProducer ≡ true
round82AnnularFormerG1G2ReduceToSingleContinuumShellMajorantProducerIsTrue = refl

round82PhysicalActualSymbolFourthOrderShellMajorantConstructedIsFalse :
  round82PhysicalActualSymbolFourthOrderShellMajorantConstructed ≡ false
round82PhysicalActualSymbolFourthOrderShellMajorantConstructedIsFalse = refl
