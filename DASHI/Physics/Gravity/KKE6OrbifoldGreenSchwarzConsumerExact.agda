module DASHI.Physics.Gravity.KKE6OrbifoldGreenSchwarzConsumerExact where

------------------------------------------------------------------------
-- 2026-10-25 E6-derived SU3^3 orbifold local anomaly FACTORISATION.
--
-- Original authors: Slansky 1981 (27); Arkani-Hamed/Cohen/Georgi 2001,
-- Scrucca et al 2002, von Gersdorff/Quiros PRD 68 (2003) 105002
-- (5D orbifold localized anomalies and GS forms). Repo donors:
-- E6 #1106 E32/E33, KK #1241 and the existing finite SM
-- AnomalyCancellationVerificationReceipt, NOT another invented SM.
--
-- Source-reconstructed ZERO-MODE anomaly in the selected generator basis:
-- cubic = (F_L - F_R)(40 F_L² + 64 F_L F_R + 40 F_R²).
-- gravitational U1 = 16(F_L-F_R).
-- each SU3c²U1, SU2L²U1, SU2R²U1 = 2(F_L-F_R)
-- in the exact script's NORMALIZATION. Python exhaustively enumerates
-- all 27 states. This Agda module proves only coefficient NAT
-- arithmetic and finite query-indexed BIDI. A local WZ variation
-- is NOT a globally well-defined 5D spin/quotient QFT.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_+_; _*_)
import DASHI.Physics.Closure.AnomalyCancellationVerificationReceipt as SM
import DASHI.Physics.Gravity.KKE6OrbifoldVEVAnomalyModelForkExact as Orb
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

priorFiniteSMAnomalyOwner : SM.AnomalyCancellationVerificationReceipt
priorFiniteSMAnomalyOwner = SM.canonicalAnomalyCancellationVerificationReceipt

uvCubicLLLFactor : 8 * 5 ≡ 40
uvCubicLLLFactor = refl

uvCubicLLRFactor : 8 * 8 ≡ 64
uvCubicLLRFactor = refl

uvSymmetrisedLLRMixedCoefficient : 3 * 8 ≡ 24
uvSymmetrisedLLRMixedCoefficient = refl

uvGravitationalFactor : 2 * 8 ≡ 16
uvGravitationalFactor = refl

uvAbelianBoundaryLLLCoefficient : 2 * 20 ≡ 40
uvAbelianBoundaryLLLCoefficient = refl

uvAbelianBoundaryLLRCoefficient : 2 * 32 ≡ 64
uvAbelianBoundaryLLRCoefficient = refl

uvGravitationalBoundaryCoefficient : 2 * 8 ≡ 16
uvGravitationalBoundaryCoefficient = refl

uvMixedNonabelianBoundaryCoefficient : 2 * 1 ≡ 2
uvMixedNonabelianBoundaryCoefficient = refl

-- The existing E32, E33 and candidate Chi E21 weights produce
-- Y = (U_L + U_R - 3 H_R)/6. Its gauge parameter projects equally
-- onto central U_L and U_R; the anomalous difference has zero shift.
data AbelianGaugeDirection : Set where
  finalHypercharge
  anomalousLeftMinusRight : AbelianGaugeDirection

localUnitAxionShifts : AbelianGaugeDirection → Bool
localUnitAxionShifts finalHypercharge = false
localUnitAxionShifts anomalousLeftMinusRight = true

hyperchargeDoesNotShiftCompensator :
  localUnitAxionShifts finalHypercharge ≡ false
hyperchargeDoesNotShiftCompensator = refl

-- In this selected 5D interval model, bulk CS inflow has OPPOSITE
-- endpoint variations. A symmetric pair of LOCALIZED WZ variations
-- can have the SAME sign and cancel a factorised LOCAL anomaly.
-- This is an admissible *infinitesimal variation ansatz*, not a
-- constructed globally periodic Goldstone/axion or a 5D eta action.
data OrbifoldAnomalyCounterterm : Set where
  oppositeBoundaryBulkCSOnly
  twoLocalFactorisedWZVariations : OrbifoldAnomalyCounterterm

sameAnomalySourceCubicMagnitude :
  OrbifoldAnomalyCounterterm → Nat
sameAnomalySourceCubicMagnitude _ = 40

formalInfinitesimalAnomalyCancellationAvailable :
  OrbifoldAnomalyCounterterm → Bool
formalInfinitesimalAnomalyCancellationAvailable
  oppositeBoundaryBulkCSOnly = false
formalInfinitesimalAnomalyCancellationAvailable
  twoLocalFactorisedWZVariations = true

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

bareAnomalyMagnitudeCannotChooseInflow :
  Transport.ClaimNonTransportWitness
    sameAnomalySourceCubicMagnitude
    formalInfinitesimalAnomalyCancellationAvailable
bareAnomalyMagnitudeCannotChooseInflow =
  Descent.consumerNonDescentWitness
    oppositeBoundaryBulkCSOnly
    twoLocalFactorisedWZVariations refl falseNotTrue

fullGlobalSpinCSOrAxionPeriodicityCertified :
  OrbifoldAnomalyCounterterm → Bool
fullGlobalSpinCSOrAxionPeriodicityCertified _ = false

sourceIsFullGaugedE6 : Bool
sourceIsFullGaugedE6 = false

orbifoldIRDoesNotPayUV :
  Transport.ClaimNonTransportWitness
    Orb.source27DimensionAtEitherStage
    Orb.allTestedPerturbativeGaugeCoefficientsZero
orbifoldIRDoesNotPayUV =
  Orb.IRAnomalyCancellationDoesNotPayUVOrbifoldGauge

-- Source-level symbolically checked experimental-free result:
-- a charge-2 Chi33 phase could shift along U_L-U_R, but its half
-- phase is not obviously globally 2pi-periodic. Fixed-point
-- quantization, original gamma5 mass parity, fermion eta/regulator,
-- one physical EW Higgs minimum and full E6 coset remain unproved.
