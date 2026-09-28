{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact where

------------------------------------------------------------------------
-- ROUND775 / RETAIN THE THREE R25 CLASSES ACROSS ONE ENERGY-LEG ORBIT
--
-- The four coarse R25 classes are not closed under pEnergyLeg/qEnergyLeg:
-- an LH/HL boundary triad can lose one shell of separation when the output
-- becomes an input.  Therefore a fixed four-state cyclic transition table
-- would throw away information needed by the class-local R768 wall.
--
-- Retain instead the literal orbit profile
--
--   Pi(beta) =
--     ( class(beta)
--     , class(pEnergyLeg beta)
--     , class(qEnergyLeg beta) ).
--
-- This uses only the authoritative R25 classifier.  R119 and R129 give an
-- exact swap action:
--
--   Pi(swap beta) = (swapClass Pi0, Pi2, Pi1).
--
-- Thus swap pairing and cyclic-row class information can coexist on one
-- finite carrier.  No analytic estimate or strengthened shell hypothesis is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false; _&&_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeFullSwapAntisymmetryRound119Exact as R119

record EnergyOrbitBonyProfile : Set where
  constructor orbit-profile
  field
    baseClass : Scale.ScaleRegime
    pClass : Scale.ScaleRegime
    qClass : Scale.ScaleRegime

open EnergyOrbitBonyProfile public

orbitProfile :
  Physical.PhysicalTriadIncidence → EnergyOrbitBonyProfile
orbitProfile beta =
  orbit-profile
    (Scale.classifyScale R25.literalShellPolicy beta)
    (Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta))
    (Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta))

swapOrbitProfile :
  EnergyOrbitBonyProfile → EnergyOrbitBonyProfile
swapOrbitProfile profile =
  orbit-profile
    (R129.swapRegime (baseClass profile))
    (qClass profile)
    (pClass profile)

orbitProfileSwap :
  (beta : Physical.PhysicalTriadIncidence) →
  orbitProfile (Symmetry.swapTriad beta)
  ≡ swapOrbitProfile (orbitProfile beta)
orbitProfileSwap beta
  rewrite R129.classifyScaleSwapEquivariant R25.literalShellPolicy beta
        | R119.pEnergyLegSwapIsQEnergyLeg beta
        | R119.qEnergyLegSwapIsPEnergyLeg beta =
  refl

swapOrbitProfileInvolutive :
  (profile : EnergyOrbitBonyProfile) →
  swapOrbitProfile (swapOrbitProfile profile) ≡ profile
swapOrbitProfileInvolutive (orbit-profile base p q)
  rewrite R129.swapRegimeInvolutive base =
  refl

regimeEqual : Scale.ScaleRegime → Scale.ScaleRegime → Bool
regimeEqual Scale.lowHigh Scale.lowHigh = true
regimeEqual Scale.highLow Scale.highLow = true
regimeEqual Scale.highHigh Scale.highHigh = true
regimeEqual Scale.comparable Scale.comparable = true
regimeEqual _ _ = false

regimeEqualRefl :
  (regime : Scale.ScaleRegime) → regimeEqual regime regime ≡ true
regimeEqualRefl Scale.lowHigh = refl
regimeEqualRefl Scale.highLow = refl
regimeEqualRefl Scale.highHigh = refl
regimeEqualRefl Scale.comparable = refl

profileEqual :
  EnergyOrbitBonyProfile → EnergyOrbitBonyProfile → Bool
profileEqual left right =
  regimeEqual (baseClass left) (baseClass right)
  &&
  regimeEqual (pClass left) (pClass right)
  &&
  regimeEqual (qClass left) (qClass right)

profileEqualRefl :
  (profile : EnergyOrbitBonyProfile) →
  profileEqual profile profile ≡ true
profileEqualRefl (orbit-profile base p q)
  rewrite regimeEqualRefl base
        | regimeEqualRefl p
        | regimeEqualRefl q =
  refl

filterOrbitProfile :
  EnergyOrbitBonyProfile →
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence
filterOrbitProfile profile [] = []
filterOrbitProfile profile (beta ∷ rest)
  with profileEqual profile (orbitProfile beta)
... | true = beta ∷ filterOrbitProfile profile rest
... | false = filterOrbitProfile profile rest

------------------------------------------------------------------------
-- Exact coordinate readback.  These are intentionally first-class because
-- future class-local cyclic transport should consume these coordinates rather
-- than re-classify after erasing the orbit profile.
------------------------------------------------------------------------

orbitProfileBase :
  (beta : Physical.PhysicalTriadIncidence) →
  baseClass (orbitProfile beta)
  ≡ Scale.classifyScale R25.literalShellPolicy beta
orbitProfileBase beta = refl

orbitProfileP :
  (beta : Physical.PhysicalTriadIncidence) →
  pClass (orbitProfile beta)
  ≡ Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta)
orbitProfileP beta = refl

orbitProfileQ :
  (beta : Physical.PhysicalTriadIncidence) →
  qClass (orbitProfile beta)
  ≡ Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta)
orbitProfileQ beta = refl

orbitProfileSwapBase :
  (beta : Physical.PhysicalTriadIncidence) →
  baseClass (orbitProfile (Symmetry.swapTriad beta))
  ≡ R129.swapRegime (baseClass (orbitProfile beta))
orbitProfileSwapBase beta =
  cong baseClass (orbitProfileSwap beta)

orbitProfileSwapP :
  (beta : Physical.PhysicalTriadIncidence) →
  pClass (orbitProfile (Symmetry.swapTriad beta))
  ≡ qClass (orbitProfile beta)
orbitProfileSwapP beta =
  cong pClass (orbitProfileSwap beta)

orbitProfileSwapQ :
  (beta : Physical.PhysicalTriadIncidence) →
  qClass (orbitProfile (Symmetry.swapTriad beta))
  ≡ pClass (orbitProfile beta)
orbitProfileSwapQ beta =
  cong qClass (orbitProfileSwap beta)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round775ThreeEnergyLegClassesRetainedTogether : Bool
round775ThreeEnergyLegClassesRetainedTogether = true

round775SwapActionOnOrbitProfileClosed : Bool
round775SwapActionOnOrbitProfileClosed = true

round775CoarseFourClassCyclicTransitionAssumed : Bool
round775CoarseFourClassCyclicTransitionAssumed = false

round775ProfileSelectorConstructed : Bool
round775ProfileSelectorConstructed = true

round775IntroducesEstimate : Bool
round775IntroducesEstimate = false

round775ClayPromotion : Bool
round775ClayPromotion = false

round775ThreeEnergyLegClassesRetainedTogetherIsTrue :
  round775ThreeEnergyLegClassesRetainedTogether ≡ true
round775ThreeEnergyLegClassesRetainedTogetherIsTrue = refl

round775SwapActionOnOrbitProfileClosedIsTrue :
  round775SwapActionOnOrbitProfileClosed ≡ true
round775SwapActionOnOrbitProfileClosedIsTrue = refl

round775CoarseFourClassCyclicTransitionAssumedIsFalse :
  round775CoarseFourClassCyclicTransitionAssumed ≡ false
round775CoarseFourClassCyclicTransitionAssumedIsFalse = refl

round775ProfileSelectorConstructedIsTrue :
  round775ProfileSelectorConstructed ≡ true
round775ProfileSelectorConstructedIsTrue = refl

round775IntroducesEstimateIsFalse :
  round775IntroducesEstimate ≡ false
round775IntroducesEstimateIsFalse = refl

round775ClayPromotionIsFalse :
  round775ClayPromotion ≡ false
round775ClayPromotionIsFalse = refl
