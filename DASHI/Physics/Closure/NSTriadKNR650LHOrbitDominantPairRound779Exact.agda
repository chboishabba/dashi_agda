{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650LHOrbitDominantPairRound779Exact where

------------------------------------------------------------------------
-- ROUND779 / LH BASE TRIAD: THE P-ENERGY ROW HAS A WIDTH-ONE INPUT PAIR
--
-- For an R25 low-high base triad beta,
--
--   shell(k) ~ shell(q)   (distance at most one),
--
-- by the literal dyadic output-tracking theorem.  The p-energy leg has inputs
--
--   (k , -q),
--
-- and the literal shell index is invariant under mode negation (R777).
-- Therefore the two INPUT shells of pEnergyLeg beta are exactly width-one.
--
-- This is the first exact transition theorem after R778.  It deliberately
-- does not force a full R25 class for the cyclic row: the strict Csep=3
-- boundary can still decide whether the old low output p is classified HH
-- or CC.  No estimate or sign is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width
import DASHI.Physics.Closure.NSTriadKNComDominantInteractionHatRound63Exact as R63
import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777

lhOutputHighWithinOne :
  ∀ {beta : Physical.PhysicalTriadIncidence} →
  R25.TriadicClassCertificate beta R25.LH →
  Width.WithinOne
    (Shell.shellIndex (Physical.k beta))
    (Shell.shellIndex (Physical.q beta))
lhOutputHighWithinOne {beta} certificate =
  R63.absoluteDistanceOneGivesWithinOne
    (Shell.shellIndex (Physical.k beta))
    (Shell.shellIndex (Physical.q beta))
    (R25.lowHighOutputTracksHighOne certificate)

lhPEnergyInputsWithinOne :
  ∀ {beta : Physical.PhysicalTriadIncidence} →
  R25.TriadicClassCertificate beta R25.LH →
  Width.WithinOne
    (Shell.shellIndex (Physical.p (Orbit.pEnergyLeg beta)))
    (Shell.shellIndex (Physical.q (Orbit.pEnergyLeg beta)))
lhPEnergyInputsWithinOne {beta} certificate
  rewrite Orbit.pEnergyLegFirstInput beta
        | Orbit.pEnergyLegSecondInput beta
        | R777.literalShellIndexNegate (Physical.q beta) =
  lhOutputHighWithinOne certificate

lhPEnergyOutputIsOriginalLowShell :
  ∀ {beta : Physical.PhysicalTriadIncidence} →
  Shell.shellIndex (Physical.k (Orbit.pEnergyLeg beta))
  ≡ Shell.shellIndex (Physical.p beta)
lhPEnergyOutputIsOriginalLowShell {beta} =
  cong Shell.shellIndex (Orbit.pEnergyLegOutput beta)

round779LHPEnergyInputPairWidthOne : Bool
round779LHPEnergyInputPairWidthOne = true

round779LHPEnergyOutputIsOriginalLowLeg : Bool
round779LHPEnergyOutputIsOriginalLowLeg = true

round779FullPEnergyR25ClassForced : Bool
round779FullPEnergyR25ClassForced = false

round779IntroducesEstimate : Bool
round779IntroducesEstimate = false

round779W2Closed : Bool
round779W2Closed = false

round779ClayPromotion : Bool
round779ClayPromotion = false

round779LHPEnergyInputPairWidthOneIsTrue :
  round779LHPEnergyInputPairWidthOne ≡ true
round779LHPEnergyInputPairWidthOneIsTrue = refl

round779FullPEnergyR25ClassForcedIsFalse :
  round779FullPEnergyR25ClassForced ≡ false
round779FullPEnergyR25ClassForcedIsFalse = refl

round779IntroducesEstimateIsFalse :
  round779IntroducesEstimate ≡ false
round779IntroducesEstimateIsFalse = refl

round779W2ClosedIsFalse :
  round779W2Closed ≡ false
round779W2ClosedIsFalse = refl

round779ClayPromotionIsFalse :
  round779ClayPromotion ≡ false
round779ClayPromotionIsFalse = refl
