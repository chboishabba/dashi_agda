module DASHI.Physics.YangMills.BalabanClayPhysicalCoupledMacrostepPromotionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- DASHI CONTRIBUTION
--
-- Join the five named physical polymer mechanisms to the genuinely coupled
-- running-coupling theorem.  The same current/next polymer norms are used in
-- both records; no silent duplicate K or K' is permitted.  The promotion gives
-- simultaneously
--
--   K' <= (1/2)K + perturbativeError,
--   0 <= g' <= g,
--   K' <= eta (g')^2.
--
-- The coupling remainder retains all three terms
--
--   O(g^5) + O(gK) + O(K^2).
--
-- Thus a physical macrostep need only inhabit the five mechanism bounds and
-- the explicit coupled coefficient budgets.  It cannot close by treating the
-- polymer and coupling errors as independent.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayStrictMacrostepComponentAssemblyExact as Strict
import DASHI.Physics.YangMills.BalabanClayCoupledPolymerFlowRemainderExact as Flow
import DASHI.Physics.YangMills.BalabanClayCoupledRGInvariantConeExact as Cone

record PhysicalCoupledMacrostep : Set₁ where
  field
    mechanisms : Strict.FiveMechanismMacrostep
    coneStep : Cone.CoupledRGInvariantConeStep

    currentNormIsCoupledPolymer :
      Strict.currentNorm mechanisms
      ≡ Flow.polymerNorm (Cone.flow coneStep)

    nextNormIsCoupledPolymer :
      Strict.nextNorm mechanisms
      ≡ Cone.nextPolymerNorm coneStep

open PhysicalCoupledMacrostep public

physicalStrictPolymerStep :
  (dataSet : PhysicalCoupledMacrostep) →
  Strict.nextNorm (mechanisms dataSet)
  ≤ Strict.strictContraction * Strict.currentNorm (mechanisms dataSet)
    + Strict.perturbativeError (mechanisms dataSet)
physicalStrictPolymerStep dataSet =
  Strict.strictMacrostepFromFiveMechanisms (mechanisms dataSet)

physicalCouplingNonnegativeAndMonotone :
  (dataSet : PhysicalCoupledMacrostep) →
  0ℚ ≤ Flow.nextCoupling (Cone.flow (coneStep dataSet))
  × Flow.nextCoupling (Cone.flow (coneStep dataSet))
      ≤ Flow.coupling (Cone.flow (coneStep dataSet))
physicalCouplingNonnegativeAndMonotone dataSet =
  Flow.nextCouplingNonnegative (Cone.flow (coneStep dataSet))
  , Flow.nextCouplingBelowCurrent (Cone.flow (coneStep dataSet))

physicalCoupledConePreserved :
  (dataSet : PhysicalCoupledMacrostep) →
  Strict.nextNorm (mechanisms dataSet)
  ≤ Flow.coneSlope (Cone.flow (coneStep dataSet))
    * Flow.square (Flow.nextCoupling (Cone.flow (coneStep dataSet)))
physicalCoupledConePreserved dataSet =
  subst
    (λ next →
      next
      ≤ Flow.coneSlope (Cone.flow (coneStep dataSet))
        * Flow.square (Flow.nextCoupling (Cone.flow (coneStep dataSet))))
    (sym (nextNormIsCoupledPolymer dataSet))
    (Cone.coupledInvariantConePreserved (coneStep dataSet))

record CoupledMacrostepConclusions (dataSet : PhysicalCoupledMacrostep) : Set where
  field
    strictPolymer :
      Strict.nextNorm (mechanisms dataSet)
      ≤ Strict.strictContraction * Strict.currentNorm (mechanisms dataSet)
        + Strict.perturbativeError (mechanisms dataSet)

    nextCouplingNonnegative :
      0ℚ ≤ Flow.nextCoupling (Cone.flow (coneStep dataSet))

    nextCouplingBelowCurrent :
      Flow.nextCoupling (Cone.flow (coneStep dataSet))
      ≤ Flow.coupling (Cone.flow (coneStep dataSet))

    invariantCone :
      Strict.nextNorm (mechanisms dataSet)
      ≤ Flow.coneSlope (Cone.flow (coneStep dataSet))
        * Flow.square (Flow.nextCoupling (Cone.flow (coneStep dataSet)))

open CoupledMacrostepConclusions public

physicalCoupledMacrostepConclusions :
  (dataSet : PhysicalCoupledMacrostep) →
  CoupledMacrostepConclusions dataSet
physicalCoupledMacrostepConclusions dataSet = record
  { strictPolymer = physicalStrictPolymerStep dataSet
  ; nextCouplingNonnegative =
      proj₁ (physicalCouplingNonnegativeAndMonotone dataSet)
  ; nextCouplingBelowCurrent =
      proj₂ (physicalCouplingNonnegativeAndMonotone dataSet)
  ; invariantCone = physicalCoupledConePreserved dataSet
  }

physicalCoupledMacrostepPromotionLevel : ProofLevel
physicalCoupledMacrostepPromotionLevel = machineChecked

physicalFiveMechanismAndFlowCompatibilityLevel : ProofLevel
physicalFiveMechanismAndFlowCompatibilityLevel = machineChecked

physicalRGMechanismEstimateInputsLevel : ProofLevel
physicalRGMechanismEstimateInputsLevel = conditional
