{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SingleSelfSpectatorFibreTransportRound715Exact where

------------------------------------------------------------------------
-- ROUND715 / THE THREE SELF-ORBIT ROWS DO NOT SHARE A FIBRE LOCALLY
--
-- R714 reduces the complete self contribution to one-copy commutator rows:
--
--   Row(beta)
--   + Row(pEnergyLeg beta)
--   + Row(qEnergyLeg beta).
--
-- A tempting shortcut is to try to reindex the spectator fibre of Row(beta)
-- directly into the spectator fibre of either transformed outer leg.  That is
-- not an automatic consequence of the energy-leg map.
--
-- For a spectator alpha,
--
--   k(pEnergyLeg alpha) = p(alpha),
--   k(qEnergyLeg alpha) = q(alpha).
--
-- Hence pEnergyLeg alpha belongs to the p(beta)-output fibre iff the extra
-- label condition p(alpha)=p(beta) holds (assuming alpha is on the complete
-- physical cutoff carrier), and similarly for q.
--
-- Therefore the exact cyclic cancellation question cannot be reduced to a
-- row-local fibre permutation.  Any cancellation using pEnergyLeg/qEnergyLeg
-- must be performed only after the COMPLETE outer beta-sum, where R38 supplies
-- the global incidence permutations.
--
-- No analytic estimate and no non-cancellation theorem is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38

pEnergyLegTargetImpliesMatchingP :
  ∀ {cutoff : Nat} {alpha beta : Physical.PhysicalTriadIncidence} →
  Orbit.pEnergyLeg alpha ∈
    Output.physicalOutputFiber cutoff (Physical.p beta) →
  Physical.p alpha ≡ Physical.p beta
pEnergyLegTargetImpliesMatchingP {alpha = alpha} member =
  trans
    (sym (Orbit.pEnergyLegOutput alpha))
    (Output.physicalOutputFiberSound member)

qEnergyLegTargetImpliesMatchingQ :
  ∀ {cutoff : Nat} {alpha beta : Physical.PhysicalTriadIncidence} →
  Orbit.qEnergyLeg alpha ∈
    Output.physicalOutputFiber cutoff (Physical.q beta) →
  Physical.q alpha ≡ Physical.q beta
qEnergyLegTargetImpliesMatchingQ {alpha = alpha} member =
  trans
    (sym (Orbit.qEnergyLegOutput alpha))
    (Output.physicalOutputFiberSound member)

pEnergyLegTargetFromMatchingP :
  ∀ {cutoff : Nat} {alpha beta : Physical.PhysicalTriadIncidence} →
  alpha ∈ Physical.physicalTriadEnumeration cutoff →
  Physical.p alpha ≡ Physical.p beta →
  Orbit.pEnergyLeg alpha ∈
    Output.physicalOutputFiber cutoff (Physical.p beta)
pEnergyLegTargetFromMatchingP {alpha = alpha} member pEqual =
  Output.physicalOutputFiberComplete
    (R38.pEnergyLegMember member)
    (trans (Orbit.pEnergyLegOutput alpha) pEqual)

qEnergyLegTargetFromMatchingQ :
  ∀ {cutoff : Nat} {alpha beta : Physical.PhysicalTriadIncidence} →
  alpha ∈ Physical.physicalTriadEnumeration cutoff →
  Physical.q alpha ≡ Physical.q beta →
  Orbit.qEnergyLeg alpha ∈
    Output.physicalOutputFiber cutoff (Physical.q beta)
qEnergyLegTargetFromMatchingQ {alpha = alpha} member qEqual =
  Output.physicalOutputFiberComplete
    (R38.qEnergyLegMember member)
    (trans (Orbit.qEnergyLegOutput alpha) qEqual)

pEnergyLegTargetCharacterization :
  ∀ {cutoff : Nat} {alpha beta : Physical.PhysicalTriadIncidence} →
  alpha ∈ Physical.physicalTriadEnumeration cutoff →
  (Orbit.pEnergyLeg alpha ∈
      Output.physicalOutputFiber cutoff (Physical.p beta))
    ×
  (Physical.p alpha ≡ Physical.p beta)
pEnergyLegTargetCharacterization member =
  let target =
        pEnergyLegTargetFromMatchingP member refl
  in
  target , pEnergyLegTargetImpliesMatchingP target

-- The useful exact statement is the pair of directional implications above.
-- This Boolean records that a fibre-local p-leg transport needs the additional
-- matching-p side condition; it is not supplied merely by source-fibre
-- membership at k(beta).
round715PEnergyLegTargetNeedsMatchingSpectatorP : Bool
round715PEnergyLegTargetNeedsMatchingSpectatorP = true

round715QEnergyLegTargetNeedsMatchingSpectatorQ : Bool
round715QEnergyLegTargetNeedsMatchingSpectatorQ = true

round715NaiveRowLocalEnergyLegFibreReindexAvailable : Bool
round715NaiveRowLocalEnergyLegFibreReindexAvailable = false

round715CompleteOuterSumStillHasGlobalR38Permutations : Bool
round715CompleteOuterSumStillHasGlobalR38Permutations = true

round715IntroducesEstimate : Bool
round715IntroducesEstimate = false

round715SelfOrbitExactCancellationClosed : Bool
round715SelfOrbitExactCancellationClosed = false

round715ClayPromotion : Bool
round715ClayPromotion = false

round715PEnergyLegTargetNeedsMatchingSpectatorPIsTrue :
  round715PEnergyLegTargetNeedsMatchingSpectatorP ≡ true
round715PEnergyLegTargetNeedsMatchingSpectatorPIsTrue = refl

round715QEnergyLegTargetNeedsMatchingSpectatorQIsTrue :
  round715QEnergyLegTargetNeedsMatchingSpectatorQ ≡ true
round715QEnergyLegTargetNeedsMatchingSpectatorQIsTrue = refl

round715NaiveRowLocalEnergyLegFibreReindexAvailableIsFalse :
  round715NaiveRowLocalEnergyLegFibreReindexAvailable ≡ false
round715NaiveRowLocalEnergyLegFibreReindexAvailableIsFalse = refl

round715IntroducesEstimateIsFalse :
  round715IntroducesEstimate ≡ false
round715IntroducesEstimateIsFalse = refl

round715SelfOrbitExactCancellationClosedIsFalse :
  round715SelfOrbitExactCancellationClosed ≡ false
round715SelfOrbitExactCancellationClosedIsFalse = refl

round715ClayPromotionIsFalse :
  round715ClayPromotion ≡ false
round715ClayPromotionIsFalse = refl
