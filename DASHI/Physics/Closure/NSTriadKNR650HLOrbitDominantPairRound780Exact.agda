{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650HLOrbitDominantPairRound780Exact where

------------------------------------------------------------------------
-- ROUND780 / HL BASE TRIAD: THE Q-ENERGY ROW HAS A WIDTH-ONE INPUT PAIR
--
-- Symmetric companion to R779.
--
-- For an R25 high-low base triad beta,
--
--   shell(k) ~ shell(p)   (distance at most one).
--
-- The q-energy leg has inputs
--
--   (k , -p),
--
-- so negation invariance of the literal shell index turns the exact
-- output-tracking theorem into a width-one input-pair theorem for qEnergyLeg.
--
-- As in R779, this does not force the full cyclic R25 class across the strict
-- Csep=3 boundary.  No estimate or sign is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width
import DASHI.Physics.Closure.NSTriadKNComDominantInteractionHatRound63Exact as R63
import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777

hlOutputHighWithinOne :
  ∀ {beta : Physical.PhysicalTriadIncidence} →
  R25.TriadicClassCertificate beta R25.HL →
  Width.WithinOne
    (Shell.shellIndex (Physical.k beta))
    (Shell.shellIndex (Physical.p beta))
hlOutputHighWithinOne {beta} certificate =
  R63.absoluteDistanceOneGivesWithinOne
    (Shell.shellIndex (Physical.k beta))
    (Shell.shellIndex (Physical.p beta))
    (R25.highLowOutputTracksHighOne certificate)

hlQEnergyInputsWithinOne :
  ∀ {beta : Physical.PhysicalTriadIncidence} →
  R25.TriadicClassCertificate beta R25.HL →
  Width.WithinOne
    (Shell.shellIndex (Physical.p (Orbit.qEnergyLeg beta)))
    (Shell.shellIndex (Physical.q (Orbit.qEnergyLeg beta)))
hlQEnergyInputsWithinOne {beta} certificate
  rewrite Orbit.qEnergyLegFirstInput beta
        | Orbit.qEnergyLegSecondInput beta
        | R777.literalShellIndexNegate (Physical.p beta) =
  hlOutputHighWithinOne certificate

hlQEnergyOutputIsOriginalLowShell :
  ∀ {beta : Physical.PhysicalTriadIncidence} →
  Shell.shellIndex (Physical.k (Orbit.qEnergyLeg beta))
  ≡ Shell.shellIndex (Physical.q beta)
hlQEnergyOutputIsOriginalLowShell {beta} =
  cong Shell.shellIndex (Orbit.qEnergyLegOutput beta)

round780HLQEnergyInputPairWidthOne : Bool
round780HLQEnergyInputPairWidthOne = true

round780HLQEnergyOutputIsOriginalLowLeg : Bool
round780HLQEnergyOutputIsOriginalLowLeg = true

round780FullQEnergyR25ClassForced : Bool
round780FullQEnergyR25ClassForced = false

round780IntroducesEstimate : Bool
round780IntroducesEstimate = false

round780W2Closed : Bool
round780W2Closed = false

round780ClayPromotion : Bool
round780ClayPromotion = false

round780HLQEnergyInputPairWidthOneIsTrue :
  round780HLQEnergyInputPairWidthOne ≡ true
round780HLQEnergyInputPairWidthOneIsTrue = refl

round780FullQEnergyR25ClassForcedIsFalse :
  round780FullQEnergyR25ClassForced ≡ false
round780FullQEnergyR25ClassForcedIsFalse = refl

round780IntroducesEstimateIsFalse :
  round780IntroducesEstimate ≡ false
round780IntroducesEstimateIsFalse = refl

round780W2ClosedIsFalse :
  round780W2Closed ≡ false
round780W2ClosedIsFalse = refl

round780ClayPromotionIsFalse :
  round780ClayPromotion ≡ false
round780ClayPromotionIsFalse = refl
