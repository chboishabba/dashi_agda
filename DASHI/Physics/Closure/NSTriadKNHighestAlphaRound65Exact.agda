module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound65Exact where

------------------------------------------------------------------------
-- ROUND 65 HIGHEST-ALPHA DELTA
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 65 ADVANCES
--
-- B1 RAW SAME-OBJECT GRAM:
--   * repairs the finite complex Cauchy--Schwarz statement so it refers to the
--     literal Hermitian pairing rather than an arbitrary scalar;
--   * constructs literal Com self masses M_q and cross mass C_qr over the exact
--     physicalOutputFiber in Carrier(realField model);
--   * proves C_qr <= M_q M_r from the corrected same-support CS law.
--
-- B1/B3 SEMANTIC CORRECTION:
-- Ordinary normalized self-correlation cannot be the historical 17/64 object:
-- for a nonzero row it equals 1 at q=r, while 17/64<1.  Therefore the sharp
-- constants must bound the FULL factorized pair product, or an internal branch
-- overlap after outer contractions.  Round65 formalizes this no-go.
--
-- B1/B3 SAME-CARRIER CONSUMER:
-- A new physical factorized Gram cell lives entirely in the literal Fourier
-- realField.  With nonnegative multiplicative order, outer contractions imply
-- pairProduct<=overlap.  An internal six-three overlap bound therefore yields
-- the sharp physical pair-product bound without dividing by self masses and
-- without identifying physical energy with Q.
--
-- A1 FINITE INVARIANCE:
-- Round63 count preservation is strengthened to pointwise tangent invariance:
-- every literal RHS coefficient mode lies in the exact same canonical orbit
-- coordinate list.  Remaining A1 is finite-dimensional ODE existence and the
-- differentiated localized shell/Duhamel identity.
--
-- CORRECTED B FRONTIER AFTER THIS ROUND:
--   B1: construct the physical outer factors/internal branch overlap of the
--       literal dominant-hat row as PhysicalFactorizedGramCell;
--   B3: prove that INTERNAL overlap <= embedded six-three gap.
-- There is no need to manufacture an ordinary normalized self-correlation
-- ratio or prove a denominator-positive theorem merely to reach 17/64.
--
-- No Clay promotion is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound64Exact
import DASHI.Physics.Closure.NSTriadKNExactFiniteComplexCauchySchwarzRound65 as CS
import DASHI.Physics.Closure.NSTriadKNComLiteralPhysicalGramRowRound65Exact as RawGram
import DASHI.Physics.Closure.NSTriadKNComNormalizedSelfOverlapNoGoRound65Exact as SelfNoGo
import DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalGramFactorizationRound65Exact as PhysicalGram
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitRHSTangentRound65Exact as Tangent

round65ExactPhysicalGramMassesConstructed : Bool
round65ExactPhysicalGramMassesConstructed = true

round65OrdinarySelfCorrelationInterpretationRejected : Bool
round65OrdinarySelfCorrelationInterpretationRejected = true

round65SameCarrierFactorizedGramConsumerConstructed : Bool
round65SameCarrierFactorizedGramConsumerConstructed = true

round65CanonicalGalerkinVectorFieldTangentConstructed : Bool
round65CanonicalGalerkinVectorFieldTangentConstructed = true

round65ClayPromotion : Bool
round65ClayPromotion = false

round65ExactPhysicalGramMassesConstructedIsTrue :
  round65ExactPhysicalGramMassesConstructed ≡ true
round65ExactPhysicalGramMassesConstructedIsTrue = refl

round65OrdinarySelfCorrelationInterpretationRejectedIsTrue :
  round65OrdinarySelfCorrelationInterpretationRejected ≡ true
round65OrdinarySelfCorrelationInterpretationRejectedIsTrue = refl

round65SameCarrierFactorizedGramConsumerConstructedIsTrue :
  round65SameCarrierFactorizedGramConsumerConstructed ≡ true
round65SameCarrierFactorizedGramConsumerConstructedIsTrue = refl

round65CanonicalGalerkinVectorFieldTangentConstructedIsTrue :
  round65CanonicalGalerkinVectorFieldTangentConstructed ≡ true
round65CanonicalGalerkinVectorFieldTangentConstructedIsTrue = refl

round65ClayPromotionIsFalse : round65ClayPromotion ≡ false
round65ClayPromotionIsFalse = refl
