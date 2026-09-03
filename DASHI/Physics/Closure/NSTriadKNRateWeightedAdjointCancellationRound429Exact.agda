module DASHI.Physics.Closure.NSTriadKNRateWeightedAdjointCancellationRound429Exact where

------------------------------------------------------------------------
-- ROUND429 / RATE-DEPENDENT HEAT/RESOLVENT WEIGHTS PRESERVE ADJOINT BALANCE
--
-- R428 gives exact equality of the two partial-adjoint real pairings before
-- norms.  R295 proves that the physical damping rate
--
--   lambda_tau = rho(p_tau) + rho(q_tau)
--
-- is swap-invariant.  Heat/resolvent one-cell factors depend only on this
-- lambda.  Therefore multiplying BOTH adjoint channels by any rational
-- function psi(lambda_tau) preserves the exact cancellation.
--
-- No positivity, absolute value, Cauchy--Schwarz, shell count, or Wiener norm
-- appears here.  This is the signed algebraic invariant that a later analytic
-- heat realization is allowed to transport.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _-_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact as R295
import DASHI.Physics.Closure.NSTriadKNAdjointBalancedSignedCancellationRound428Exact as R428

F : C3.RealField _
F = Rational.rationalRealField

rateScalarWeight :
  (rho : Z3.FourierMode → ℚ) →
  (psi : ℚ → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
rateScalarWeight rho psi tau = psi (R295.cellRate rho tau)

weightedFirstAdjointPairing :
  (rho : Z3.FourierMode → ℚ) →
  (psi : ℚ → ℚ) →
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → ℚ
weightedFirstAdjointPairing rho psi E I tau uP uQ testK =
  rateScalarWeight rho psi tau
  * R428.firstAdjointRealPairing E I
      (Physical.p tau) (Physical.q tau) uP uQ testK

weightedSecondAdjointPairing :
  (rho : Z3.FourierMode → ℚ) →
  (psi : ℚ → ℚ) →
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → ℚ
weightedSecondAdjointPairing rho psi E I tau uP uQ testK =
  rateScalarWeight rho psi tau
  * R428.secondAdjointRealPairing E I
      (Physical.q tau) uP uQ testK

rateWeightPreservesLiteralAdjointBalance :
  (rho : Z3.FourierMode → ℚ) →
  (psi : ℚ → ℚ) →
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E (Physical.k tau) testK →
  Helical.Transverse E (Physical.p tau) uP →
  Helical.Transverse E (Physical.q tau) uQ →
  weightedFirstAdjointPairing rho psi E I tau uP uQ testK
  ≡ weightedSecondAdjointPairing rho psi E I tau uP uQ testK
rateWeightPreservesLiteralAdjointBalance rho psi E I tau uP uQ testK tk tp tq
  rewrite R428.literalPartialAdjointBalance E I
    (Physical.k tau) (Physical.p tau) (Physical.q tau)
    uP uQ testK tk tp tq = refl

rateWeightedSignedAdjointDifferenceZero :
  (rho : Z3.FourierMode → ℚ) →
  (psi : ℚ → ℚ) →
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E (Physical.k tau) testK →
  Helical.Transverse E (Physical.p tau) uP →
  Helical.Transverse E (Physical.q tau) uQ →
  weightedFirstAdjointPairing rho psi E I tau uP uQ testK
    - weightedSecondAdjointPairing rho psi E I tau uP uQ testK
  ≡ 0ℚ
rateWeightedSignedAdjointDifferenceZero rho psi E I tau uP uQ testK tk tp tq
  rewrite rateWeightPreservesLiteralAdjointBalance
    rho psi E I tau uP uQ testK tk tp tq = refl

round429AnyRationalFunctionOfCellRatePreservesAdjointCancellation : Bool
round429AnyRationalFunctionOfCellRatePreservesAdjointCancellation = true

round429HeatResolventSymmetryRequirementReducedToRateDependence : Bool
round429HeatResolventSymmetryRequirementReducedToRateDependence = true

round429AbsoluteValueIntroduced : Bool
round429AbsoluteValueIntroduced = false

round429WienerMajorizationIntroduced : Bool
round429WienerMajorizationIntroduced = false

round429AnyRationalFunctionOfCellRatePreservesAdjointCancellationIsTrue :
  round429AnyRationalFunctionOfCellRatePreservesAdjointCancellation ≡ true
round429AnyRationalFunctionOfCellRatePreservesAdjointCancellationIsTrue = refl
