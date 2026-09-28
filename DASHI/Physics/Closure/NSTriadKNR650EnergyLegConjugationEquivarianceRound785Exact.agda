{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650EnergyLegConjugationEquivarianceRound785Exact where

------------------------------------------------------------------------
-- ROUND785 / LITERAL R25 CLASSIFICATION IS CONJUGATION-INVARIANT
--            AND ENERGY-LEG COMPOSITIONS CLOSE EXACTLY
--
-- The literal shell index depends only on the infinity norm, so R777 already
-- proves
--
--   shell(-m) = shell(m).
--
-- Hence Fourier conjugation negates all three modes without changing the
-- executable R25 scale regime.
--
-- We also package the exact energy-leg composition identities needed by the
-- R784 orbit-closure seam:
--
--   pEnergyLeg(qEnergyLeg beta) = swapTriad beta
--   qEnergyLeg(pEnergyLeg beta) = orderedRealityMate beta.
--
-- No estimate or new analytic input is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree
import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777

literalScaleConjugateInvariant :
  (beta : Physical.PhysicalTriadIncidence) →
  Scale.classifyScale R25.literalShellPolicy
    (Symmetry.conjugateTriad beta)
  ≡
  Scale.classifyScale R25.literalShellPolicy beta
literalScaleConjugateInvariant beta
  rewrite Symmetry.conjugateTriadP beta
        | Symmetry.conjugateTriadQ beta
        | Symmetry.conjugateTriadK beta
        | R777.literalShellIndexNegate (Physical.p beta)
        | R777.literalShellIndexNegate (Physical.q beta)
        | R777.literalShellIndexNegate (Physical.k beta) =
  refl

pAfterQIsSwap :
  (beta : Physical.PhysicalTriadIncidence) →
  Orbit.pEnergyLeg (Orbit.qEnergyLeg beta)
  ≡ Symmetry.swapTriad beta
pAfterQIsSwap beta =
  KFree.physicalIncidenceExtPQ
    (Orbit.pEnergyLeg (Orbit.qEnergyLeg beta))
    (Symmetry.swapTriad beta)
    refl
    (Symmetry.negateModeInvolutive (Physical.p beta))

qAfterPIsRealityMate :
  (beta : Physical.PhysicalTriadIncidence) →
  Orbit.qEnergyLeg (Orbit.pEnergyLeg beta)
  ≡ Orbit.orderedRealityMate beta
qAfterPIsRealityMate beta =
  KFree.physicalIncidenceExtPQ
    (Orbit.qEnergyLeg (Orbit.pEnergyLeg beta))
    (Orbit.orderedRealityMate beta)
    refl
    refl

round785LiteralScaleConjugateInvariant : Bool
round785LiteralScaleConjugateInvariant = true

round785PAfterQIsSwap : Bool
round785PAfterQIsSwap = true

round785QAfterPIsRealityMate : Bool
round785QAfterPIsRealityMate = true

round785IntroducesEstimate : Bool
round785IntroducesEstimate = false

round785W2Closed : Bool
round785W2Closed = false

round785ClayPromotion : Bool
round785ClayPromotion = false

round785LiteralScaleConjugateInvariantIsTrue :
  round785LiteralScaleConjugateInvariant ≡ true
round785LiteralScaleConjugateInvariantIsTrue = refl

round785PAfterQIsSwapIsTrue :
  round785PAfterQIsSwap ≡ true
round785PAfterQIsSwapIsTrue = refl

round785QAfterPIsRealityMateIsTrue :
  round785QAfterPIsRealityMate ≡ true
round785QAfterPIsRealityMateIsTrue = refl

round785IntroducesEstimateIsFalse :
  round785IntroducesEstimate ≡ false
round785IntroducesEstimateIsFalse = refl

round785W2ClosedIsFalse :
  round785W2Closed ≡ false
round785W2ClosedIsFalse = refl

round785ClayPromotionIsFalse :
  round785ClayPromotion ≡ false
round785ClayPromotionIsFalse = refl
