module DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionProjectedPairingExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2a / LITERAL CRITICAL PRODUCTION -> R39/R98 PAIRING
--
-- S0 now defines the physical critical production directly from the live
-- projected nonlinearity,
--
--   N'_N(t) = 2 sum_k w(k) Re < N_k(u_N), u_N(k) >.
--
-- The packet-flux / layer-cake line uses the older literal projected pairing
--
--   Re < u_N(k), N_k(u_N) >.
--
-- On the rational Complex3 carrier these are exactly the same real scalar:
-- the real part of the Hermitian pairing is symmetric under argument swap.
-- This file proves that equality directly by finite rational algebra and then
-- folds it over the SAME live mode list and dyadic critical weight.
--
-- No estimate, packet selector, radial sorting, Abel inequality, remainder,
-- or positivity assumption is introduced here.  Consequently the remaining
-- S2 theorem is genuinely quantitative: transport this now-literal weighted
-- projected pairing through the existing packet/layer-cake machinery and pay
-- it by dissipation plus the literal R406 remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as R98
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as S0

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Local same-object equality.
------------------------------------------------------------------------

realHermitianSwap :
  (left right : C3.Complex3 F) →
  S0.realHermitianPairing left right
  ≡ R39.realHermitianPower right left
realHermitianSwap
    (C3.complex3
      (C3.complex lx lxi) (C3.complex ly lyi) (C3.complex lz lzi))
    (C3.complex3
      (C3.complex rx rxi) (C3.complex ry ryi) (C3.complex rz rzi)) =
  solve
    ( lx ∷ lxi ∷ ly ∷ lyi ∷ lz ∷ lzi
    ∷ rx ∷ rxi ∷ ry ∷ ryi ∷ rz ∷ rzi ∷ [] )

literalModeProductionPairingSameObject :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (mode : Z3.FourierMode) →
  S0.realHermitianPairing
      (Audit.projectedNonlinearity system mode)
      (Audit.velocity system mode)
  ≡
  R39.realHermitianPower
      (Audit.velocity system mode)
      (Audit.projectedNonlinearity system mode)
literalModeProductionPairingSameObject system mode =
  realHermitianSwap
    (Audit.projectedNonlinearity system mode)
    (Audit.velocity system mode)

------------------------------------------------------------------------
-- Weighted R39 carrier and finite same-object fold.
------------------------------------------------------------------------

weightedProjectedPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode →
  ℚ
weightedProjectedPairing system [] = 0ℚ
weightedProjectedPairing system (mode ∷ rest) =
  S0.dyadicCriticalWeight mode
    * R39.realHermitianPower
        (Audit.velocity system mode)
        (Audit.projectedNonlinearity system mode)
    + weightedProjectedPairing system rest

literalWeightedProductionIsWeightedProjectedPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (modes : List Z3.FourierMode) →
  S0.weightedProjectedNonlinearProduction system modes
  ≡ weightedProjectedPairing system modes
literalWeightedProductionIsWeightedProjectedPairing system [] = refl
literalWeightedProductionIsWeightedProjectedPairing system (mode ∷ rest) =
  cong₂ _+_
    (cong (S0.dyadicCriticalWeight mode *_)
      (literalModeProductionPairingSameObject system mode))
    (literalWeightedProductionIsWeightedProjectedPairing system rest)

literalCriticalProductionIsTwiceWeightedProjectedPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  S0.criticalProductionRate system
  ≡ S0.two * weightedProjectedPairing system (Audit.modes system)
literalCriticalProductionIsTwiceWeightedProjectedPairing system =
  cong (S0.two *_)
    (literalWeightedProductionIsWeightedProjectedPairing
      system (Audit.modes system))

------------------------------------------------------------------------
-- R98 compatibility marker.
--
-- `weightedProjectedPairing` uses R39's exact literal output pairing. R98's
-- selected packet theorem uses that same R39 pairing output-by-output, so the
-- next physical theorem is selector/radial-band realization + quantitative
-- layer-cake payment, not another production-scalar identification.
------------------------------------------------------------------------

literalCriticalProductionProjectedPairingSameObjectClosed : Bool
literalCriticalProductionProjectedPairingSameObjectClosed = true

r98LiteralProjectedPairingCarrierReused : Bool
r98LiteralProjectedPairingCarrierReused =
  R98.round98SelectedWeightedOutputFiberIdentificationClosed

s2LiteralSignedProductionEstimateClosed : Bool
s2LiteralSignedProductionEstimateClosed = false

literalCriticalProductionProjectedPairingSameObjectClosedIsTrue :
  literalCriticalProductionProjectedPairingSameObjectClosed ≡ true
literalCriticalProductionProjectedPairingSameObjectClosedIsTrue = refl

r98LiteralProjectedPairingCarrierReusedIsTrue :
  r98LiteralProjectedPairingCarrierReused ≡ true
r98LiteralProjectedPairingCarrierReusedIsTrue =
  R98.round98SelectedWeightedOutputFiberIdentificationClosedIsTrue

s2LiteralSignedProductionEstimateClosedIsFalse :
  s2LiteralSignedProductionEstimateClosed ≡ false
s2LiteralSignedProductionEstimateClosedIsFalse = refl
