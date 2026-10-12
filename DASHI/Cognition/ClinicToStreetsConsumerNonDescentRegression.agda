module DASHI.Cognition.ClinicToStreetsConsumerNonDescentRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Cognition.ClinicToStreetsConsumerNonDescentExact as X

canonicalWitness :
  Descent.ConsumerNonDescentWitness X.atomisingObserver X.structuralConsumer
canonicalWitness = X.canonicalAtomisingNonDescent

atomisingObserverIsNotStructurallySufficient :
  Descent.ConsumerSufficient X.atomisingObserver X.structuralConsumer → ⊥
atomisingObserverIsNotStructurallySufficient =
  X.atomisingObserverBlocksStructuralSufficiency

atomisingObserverCannotFactorStructuralConsumer :
  Descent.FactorsThrough X.atomisingObserver X.structuralConsumer → ⊥
atomisingObserverCannotFactorStructuralConsumer =
  X.atomisingObserverBlocksStructuralFactorisation

contextObserverPaysStructuralConsumer :
  Descent.ConsumerSufficient X.contextObserver X.structuralConsumer
contextObserverPaysStructuralConsumer = X.contextObserverIsStructurallySufficient

structuralResidualRepairsTheCollision :
  Repair.RefinementRepairs
    X.atomisingObserver X.structuralResidual X.structuralConsumer
structuralResidualRepairsTheCollision = X.structuralResidualRepairsAtomisation

anySufficientRepairMustSeparateCanonicalCollision :
  ∀ {Refinement : Set} {refine : X.CausalWorld → Refinement} →
  Repair.RefinementRepairs X.atomisingObserver refine X.structuralConsumer →
  refine X.fullStructuralWorld ≡ refine X.sameSurfaceWithoutStructuralWorld →
  ⊥
anySufficientRepairMustSeparateCanonicalCollision =
  X.anySufficientRepairSeparatesCanonicalCollision
