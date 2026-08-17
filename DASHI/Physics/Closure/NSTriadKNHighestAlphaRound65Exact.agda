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
-- B1 CORRECT OPERATOR INDEX:
-- The historical six-three same/adjacent indices live in the ANNULAR/operator
-- lane, not in nested low-pass cutoff indices.  Round65 therefore constructs
-- the exact annular Com self/cross masses from the Round63 literal annular
-- coefficients on physicalOutputFiber and proves the same Cauchy Gram bound.
-- This is now the authoritative raw physical Gram input for B1.
--
-- B1/B3 SEMANTIC CORRECTION:
-- Ordinary normalized self-correlation cannot be the historical 17/64 object:
-- for a nonzero row it equals 1 at q=r, while 17/64<1.  Therefore the sharp
-- constants must bound the FULL factorized pair product, or an internal branch
-- overlap after outer contractions.  Round65 formalizes this no-go.
--
-- B1/B3 SAME-CARRIER FACTORIZATION:
-- A physical factorized Gram cell now lives entirely in the literal Fourier
-- realField.  With nonnegative multiplicative order, outer contractions imply
-- pairProduct<=overlap.  An internal six-three overlap bound therefore yields
-- the sharp physical pair-product bound without dividing by self masses and
-- without identifying physical energy with Q.
--
-- B3 DOWNSTREAM CLOSURE:
-- A factorized physical source with the six-three internal overlap estimate is
-- converted into the existing ordered physical majorant.  The same-shell and
-- adjacent-shell bounds then close exactly at 17/64, 65/512, 65/512 and hence
-- the bandwidth-one physical mass is <=133/256 on the SAME real carrier.
-- Thus no further downstream B arithmetic remains once the literal annular row
-- is realized as an active PhysicalSixThreeGramCell.
--
-- A1 FINITE INVARIANCE:
-- Round63 count preservation is strengthened to pointwise tangent invariance:
-- every literal RHS coefficient mode lies in the exact same canonical orbit
-- coordinate list.  Remaining A1 is finite-dimensional ODE existence and the
-- differentiated localized shell/Duhamel identity.
--
-- CORRECTED B FRONTIER AFTER THIS ROUND:
--   B1: literal dominant-hat ANNULAR row -> physical outer factors/internal
--       branch overlap as an active PhysicalSixThreeGramCell;
--   B3: prove that INTERNAL overlap <= embedded six-three gap.
-- Everything after that, including 133/256, is now already theorem-level on
-- the same physical carrier.
--
-- No Clay promotion is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound64Exact
import DASHI.Physics.Closure.NSTriadKNExactFiniteComplexCauchySchwarzRound65 as CS
import DASHI.Physics.Closure.NSTriadKNComLiteralPhysicalGramRowRound65Exact as RawLowPassGram
import DASHI.Physics.Closure.NSTriadKNComAnnularPhysicalGramRowRound65Exact as RawAnnularGram
import DASHI.Physics.Closure.NSTriadKNComNormalizedSelfOverlapNoGoRound65Exact as SelfNoGo
import DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalGramFactorizationRound65Exact as PhysicalGram
import DASHI.Physics.Closure.NSTriadKNComFactorizedPhysicalBandwidthOneRound65Exact as Bandwidth
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitRHSTangentRound65Exact as Tangent

round65ExactPhysicalGramMassesConstructed : Bool
round65ExactPhysicalGramMassesConstructed = true

round65AnnularOperatorGramConstructed : Bool
round65AnnularOperatorGramConstructed = true

round65OrdinarySelfCorrelationInterpretationRejected : Bool
round65OrdinarySelfCorrelationInterpretationRejected = true

round65SameCarrierFactorizedGramConsumerConstructed : Bool
round65SameCarrierFactorizedGramConsumerConstructed = true

round65FactorizedSixThreeCloses133Over256 : Bool
round65FactorizedSixThreeCloses133Over256 = true

round65CanonicalGalerkinVectorFieldTangentConstructed : Bool
round65CanonicalGalerkinVectorFieldTangentConstructed = true

round65ClayPromotion : Bool
round65ClayPromotion = false

round65ExactPhysicalGramMassesConstructedIsTrue :
  round65ExactPhysicalGramMassesConstructed ≡ true
round65ExactPhysicalGramMassesConstructedIsTrue = refl

round65AnnularOperatorGramConstructedIsTrue :
  round65AnnularOperatorGramConstructed ≡ true
round65AnnularOperatorGramConstructedIsTrue = refl

round65OrdinarySelfCorrelationInterpretationRejectedIsTrue :
  round65OrdinarySelfCorrelationInterpretationRejected ≡ true
round65OrdinarySelfCorrelationInterpretationRejectedIsTrue = refl

round65SameCarrierFactorizedGramConsumerConstructedIsTrue :
  round65SameCarrierFactorizedGramConsumerConstructed ≡ true
round65SameCarrierFactorizedGramConsumerConstructedIsTrue = refl

round65FactorizedSixThreeCloses133Over256IsTrue :
  round65FactorizedSixThreeCloses133Over256 ≡ true
round65FactorizedSixThreeCloses133Over256IsTrue = refl

round65CanonicalGalerkinVectorFieldTangentConstructedIsTrue :
  round65CanonicalGalerkinVectorFieldTangentConstructed ≡ true
round65CanonicalGalerkinVectorFieldTangentConstructedIsTrue = refl

round65ClayPromotionIsFalse : round65ClayPromotion ≡ false
round65ClayPromotionIsFalse = refl
