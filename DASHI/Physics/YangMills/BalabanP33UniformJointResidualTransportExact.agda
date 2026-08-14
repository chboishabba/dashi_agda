module DASHI.Physics.YangMills.BalabanP33UniformJointResidualTransportExact where

open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as O
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as S
import DASHI.Physics.YangMills.BalabanP33JointCorrelatedResidualExact as J

record UniformJointResidual (C : Set) : Set₁ where
  field
    InRegion : C → Set
    Astar : C
    AstarIn : InRegion Astar
    family : C → O.CorrelatedResidualFamily
    charge : C → ℚ
    cancellation : ∀ A → InRegion A → O.ExactCorrelatedCancellation (family A)
    jointUpper : ∀ A → InRegion A → J.jointResidual (family A) ≤ S.remainingSingletonCoefficient * charge A
open UniformJointResidual public

uniformJointResidualAtSelected : ∀ {C} (d : UniformJointResidual C) →
  O.correlatedResidualTotal (family d (Astar d)) ≤ S.remainingSingletonCoefficient * charge d (Astar d)
uniformJointResidualAtSelected d =
  subst (λ x → x ≤ S.remainingSingletonCoefficient * charge d (Astar d))
    (sym (J.jointResidualIsPhysicalTotal (cancellation d (Astar d) (AstarIn d))))
    (jointUpper d (Astar d) (AstarIn d))

p33UniformJointResidualTransportLevel : ProofLevel
p33UniformJointResidualTransportLevel = machineChecked
