{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SelfInnerThreeOuterLegOrbitRound707Exact where

------------------------------------------------------------------------
-- ROUND707 / THE R573 SELECTED SELF INNER TERM CLOSES UNDER THE OUTER 3-LEG ORBIT
--
-- R706 shows that a generic inner incidence does not automatically travel with
-- the outer p/q-energy-leg permutation.  The selected self interaction is
-- special: R95/R625 define the self forcing of an outer triad tau by the
-- p-energy-leg incidence.
--
-- Hence define
--
--   selfInner(tau) = pEnergyLeg(tau).
--
-- Then, exactly,
--
--   selfInner(tau)                  = pLeg tau,
--   selfInner(pEnergyLeg tau)       = tau,
--   selfInner(qEnergyLeg tau)       = swapTriad tau.
--
-- The first nontrivial equality is the existing p-leg involution.  The last
-- follows from the proof-bearing incidence coordinates.  Therefore the self
-- nested channel really does live on one finite closed outer/inner orbit.
--
-- This is why the historical self/external split is forced back into the
-- Clay-facing calculation by R703--R706: the self term has canonical cyclic
-- mates; a generic external inner interaction does not.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree

selfInner :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence
selfInner = Orbit.pEnergyLeg

selfInnerBase :
  (tau : Physical.PhysicalTriadIncidence) →
  selfInner tau ≡ Orbit.pEnergyLeg tau
selfInnerBase tau = refl

selfInnerOnPEnergyLeg :
  (tau : Physical.PhysicalTriadIncidence) →
  selfInner (Orbit.pEnergyLeg tau) ≡ tau
selfInnerOnPEnergyLeg tau =
  Orbit.pEnergyLegInvolution tau

selfInnerOnQEnergyLeg :
  (tau : Physical.PhysicalTriadIncidence) →
  selfInner (Orbit.qEnergyLeg tau) ≡ Symmetry.swapTriad tau
selfInnerOnQEnergyLeg tau =
  KFree.physicalIncidenceExtPQ
    (selfInner (Orbit.qEnergyLeg tau))
    (Symmetry.swapTriad tau)
    refl
    Symmetry.negateModeInvolutive (Physical.p tau)

selfInnerThreeOuterLegOrbit :
  (tau : Physical.PhysicalTriadIncidence) →
  let
    base = selfInner tau
    pLeg = selfInner (Orbit.pEnergyLeg tau)
    qLeg = selfInner (Orbit.qEnergyLeg tau)
  in
  (base ≡ Orbit.pEnergyLeg tau)
  × (pLeg ≡ tau)
  × (qLeg ≡ Symmetry.swapTriad tau)
selfInnerThreeOuterLegOrbit tau =
  selfInnerBase tau ,
  selfInnerOnPEnergyLeg tau ,
  selfInnerOnQEnergyLeg tau

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round707SelectedSelfInnerHasCanonicalThreeOuterLegMates : Bool
round707SelectedSelfInnerHasCanonicalThreeOuterLegMates = true

round707SelfInnerBaseIsPEnergyLeg : Bool
round707SelfInnerBaseIsPEnergyLeg = true

round707SelfInnerOnPEnergyLegReturnsBaseTriad : Bool
round707SelfInnerOnPEnergyLegReturnsBaseTriad = true

round707SelfInnerOnQEnergyLegIsSwapTriad : Bool
round707SelfInnerOnQEnergyLegIsSwapTriad = true

round707GenericExternalInnerHasSameCanonicalThreeMateClosure : Bool
round707GenericExternalInnerHasSameCanonicalThreeMateClosure = false

round707IntroducesEstimate : Bool
round707IntroducesEstimate = false

round707ClayPromotion : Bool
round707ClayPromotion = false

round707SelectedSelfInnerHasCanonicalThreeOuterLegMatesIsTrue :
  round707SelectedSelfInnerHasCanonicalThreeOuterLegMates ≡ true
round707SelectedSelfInnerHasCanonicalThreeOuterLegMatesIsTrue = refl

round707GenericExternalInnerHasSameCanonicalThreeMateClosureIsFalse :
  round707GenericExternalInnerHasSameCanonicalThreeMateClosure ≡ false
round707GenericExternalInnerHasSameCanonicalThreeMateClosureIsFalse = refl

round707IntroducesEstimateIsFalse :
  round707IntroducesEstimate ≡ false
round707IntroducesEstimateIsFalse = refl

round707ClayPromotionIsFalse :
  round707ClayPromotion ≡ false
round707ClayPromotionIsFalse = refl
