module DASHI.Physics.YangMills.BalabanP06DiameterComplexityAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Reinhard Diestel,
-- "Graph Theory", Graduate Texts in Mathematics 173, fifth edition,
-- Springer, 2017. DOI: 10.1007/978-3-662-53622-3.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Audit the precise P06 geometry claim.  Bounded degree and connectedness do
-- not by themselves imply that support or reduced complexity is linear in
-- diameter.  This module proves a reusable no-go theorem: any explicitly
-- superlinear family refutes every proposed uniform affine diameter bound.
-- It then records the two honest routes available to P06: prove a thin/sparse
-- physical-polymer restriction, or prove the shell count directly.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _^_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_<_; _≤_; z≤n; s≤s)
open import Relation.Nullary using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

≤-trans-local : ∀ {left middle right : Nat} →
  left ≤ middle → middle ≤ right → left ≤ right
≤-trans-local z≤n middle≤right = z≤n
≤-trans-local (s≤s left≤middle) (s≤s middle≤right) =
  s≤s (≤-trans-local left≤middle middle≤right)

sucNot≤self : ∀ value → ¬ (suc value ≤ value)
sucNot≤self zero ()
sucNot≤self (suc value) (s≤s impossible) =
  sucNot≤self value impossible

strictAndReverseWeakImpossible : ∀ {small large : Nat} →
  small < large → large ≤ small → ⊥
strictAndReverseWeakImpossible {small} small<large large≤small =
  sucNot≤self small (≤-trans-local small<large large≤small)

record DiameterComplexityFamily : Set₁ where
  field
    Polymer : Set
    supportSize : Polymer → Nat
    diameter : Polymer → Nat

open DiameterComplexityFamily public

LinearDiameterBound :
  DiameterComplexityFamily → Nat → Nat → Set
LinearDiameterBound family coefficient offset =
  ∀ polymer →
  supportSize family polymer
  ≤ coefficient * diameter family polymer + offset

record SuperlinearDiameterWitness
    (family : DiameterComplexityFamily) : Set₁ where
  field
    defeatsEveryAffineBound :
      ∀ coefficient offset →
      Σ (Polymer family) (λ polymer →
        coefficient * diameter family polymer + offset
        < supportSize family polymer)

open SuperlinearDiameterWitness public

superlinearFamilyRefutesUniformLinearDiameterBound :
  ∀ {family} →
  SuperlinearDiameterWitness family →
  ∀ coefficient offset →
  ¬ LinearDiameterBound family coefficient offset
superlinearFamilyRefutesUniformLinearDiameterBound witness coefficient offset bound
  with defeatsEveryAffineBound witness coefficient offset
... | polymer , proposedBoundFails =
  strictAndReverseWeakImpossible
    proposedBoundFails
    (bound polymer)

------------------------------------------------------------------------
-- The corrected theorem boundary.
------------------------------------------------------------------------

data DiameterCountingRoute
    (family : DiameterComplexityFamily) : Set₁ where
  thinPhysicalClass :
    (coefficient offset : Nat) →
    LinearDiameterBound family coefficient offset →
    DiameterCountingRoute family

  directDiameterShellCount :
    (shellCount : Nat → Nat) →
    (growthConstant : Nat) →
    (∀ diameterValue →
      shellCount diameterValue ≤ growthConstant ^ diameterValue) →
    DiameterCountingRoute family

record P06DiameterComplexityAudit
    (family : DiameterComplexityFamily) : Set₁ where
  field
    route : DiameterCountingRoute family

    boundedDegreeAloneIsNotUsedAsLinearDiameterProof : Set
    boundedDegreeAloneIsNotUsedAsLinearDiameterProofEvidence :
      boundedDegreeAloneIsNotUsedAsLinearDiameterProof

    theoremBoundary : Set
    theoremBoundaryEvidence : theoremBoundary

open P06DiameterComplexityAudit public

record ThinPhysicalPolymerCertificate
    (family : DiameterComplexityFamily) : Set₁ where
  field
    complexityCoefficient complexityOffset : Nat
    physicalThinness :
      LinearDiameterBound
        family complexityCoefficient complexityOffset

open ThinPhysicalPolymerCertificate public

thinCertificateSelectsValidRoute :
  ∀ {family} →
  ThinPhysicalPolymerCertificate family →
  DiameterCountingRoute family
thinCertificateSelectsValidRoute certificate =
  thinPhysicalClass
    (complexityCoefficient certificate)
    (complexityOffset certificate)
    (physicalThinness certificate)

p06DiameterNoGoReducerLevel : ProofLevel
p06DiameterNoGoReducerLevel = machineChecked

p06CorrectedCountingRouteLevel : ProofLevel
p06CorrectedCountingRouteLevel = machineChecked

periodicFourDimensionalSuperlinearWitnessLevel : ProofLevel
periodicFourDimensionalSuperlinearWitnessLevel = conditional

physicalThinPolymerCertificateLevel : ProofLevel
physicalThinPolymerCertificateLevel = conditional
