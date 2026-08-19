module DASHI.Physics.YangMills.BalabanStrongContinuumSchwingerConvergenceMasterExact where

------------------------------------------------------------------------
-- ROUND64 MASTER THEOREM 6: STRONG CONTINUUM SCHWINGER CONVERGENCE
--
-- PRIMARY SOURCES
--
-- Yu. V. Prokhorov,
-- "Convergence of Random Processes and Limit Theorems in Probability Theory",
-- Theory of Probability and Its Applications 1 (1956), 157--214.
-- DOI: 10.1137/1101016.
--
-- Krzysztof Gawedzki and Antti Kupiainen,
-- "A Rigorous Block Spin Approach to Massless Lattice Theories",
-- Communications in Mathematical Physics 77 (1980), 31--64.
-- DOI: 10.1007/BF01205038.
--
-- Krzysztof Gawedzki and Antti Kupiainen,
-- "Massless Lattice phi^4_4 Theory: Rigorous Control of a Renormalizable
-- Asymptotically Free Model", Communications in Mathematical Physics 99
-- (1985), 197--252. DOI: 10.1007/BF01212281.
--
-- DASHI CONTRIBUTION
--
-- Round63 exposed scale-local Cauchy control, tightness and uniqueness as three
-- final physical leaves.  That is unnecessarily weak if the actual RG theorem
-- proves convergence in a topology strong enough to control all three.
--
-- This module makes that topology explicit.  A StrongConvergenceAuthority is
-- not a proof of Yang-Mills convergence; it states the ordinary consequences
-- that the chosen topology MUST have:
--
--   strong convergence -> tight family,
--   two strong limits of the same family -> equal.
--
-- The physical master theorem then supplies ONE actual strong convergence
-- witness for the renormalized Schwinger family.  Tightness and uniqueness are
-- derived from that same witness.  Separately, the existing scale-local RG
-- increment theorem gives an explicit geometric Cauchy modulus for observables.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (_*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

record StrongConvergenceAuthority (Family Limit : Set) : Set₁ where
  field
    StrongConverges : (Nat → Family) → Limit → Set
    TightFamily : (Nat → Family) → Set

    strongConvergenceImpliesTightness :
      ∀ sequence limit → StrongConverges sequence limit → TightFamily sequence

    strongLimitUnique :
      ∀ sequence left right →
      StrongConverges sequence left →
      StrongConverges sequence right →
      left ≡ right

open StrongConvergenceAuthority public

record StrongContinuumSchwingerConvergence
    {Family Limit : Set}
    (authority : StrongConvergenceAuthority Family Limit) : Set₁ where
  field
    schwingerAtCutoff : Nat → Family
    continuumLimit : Limit
    strongConvergence :
      StrongConverges authority schwingerAtCutoff continuumLimit

open StrongContinuumSchwingerConvergence public

strongMasterImpliesTightness :
  ∀ {Family Limit}
    {authority : StrongConvergenceAuthority Family Limit} →
  (master : StrongContinuumSchwingerConvergence authority) →
  TightFamily authority (schwingerAtCutoff master)
strongMasterImpliesTightness {authority = authority} master =
  strongConvergenceImpliesTightness authority
    (schwingerAtCutoff master)
    (continuumLimit master)
    (strongConvergence master)

strongMasterLimitIsUnique :
  ∀ {Family Limit}
    {authority : StrongConvergenceAuthority Family Limit}
    (master : StrongContinuumSchwingerConvergence authority)
    candidate →
  StrongConverges authority (schwingerAtCutoff master) candidate →
  candidate ≡ continuumLimit master
strongMasterLimitIsUnique {authority = authority} master candidate candidateConverges =
  strongLimitUnique authority
    (schwingerAtCutoff master)
    candidate
    (continuumLimit master)
    candidateConverges
    (strongConvergence master)

scaleLocalIncrementGivesObservableCauchyModulus :
  (dataSet : Scale.RenormalizedObservableScaleCauchyData) → ∀ start count →
  Scale.scaleDifferenceMagnitude dataSet start count
  ≤ Scale.coefficient (Scale.majorant dataSet)
      * (Geo.half * Geo.halfPower start)
scaleLocalIncrementGivesObservableCauchyModulus =
  Scale.renormalizedObservableCauchyModulus

strongContinuumTopologyConsequencesLevel : ProofLevel
strongContinuumTopologyConsequencesLevel = machineChecked

scaleLocalObservableCauchyClosureLevel : ProofLevel
scaleLocalObservableCauchyClosureLevel = machineChecked

physicalStrongContinuumSchwingerConvergenceLevel : ProofLevel
physicalStrongContinuumSchwingerConvergenceLevel = conditional
