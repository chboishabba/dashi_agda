module DASHI.Physics.Closure.NSTriadKNUnifiedConcreteFiber where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as FTClass
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as FT
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as AdvClass
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as Adv
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as TrClass
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as Tr
open import DASHI.Physics.Closure.NSTriadKNUnifiedConcreteFiberSource public

open KernelFormula using (_∈_)

concreteFiberTargetAgreement :
  {N : Nat} {i : Relation.ConcreteNonResidualFiniteIndex N}
  {j : Relation.ConcreteNonResidualTailIndex N} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  τ ∈ concreteNonResidualFiber i j →
  Relation.concreteNonResidualTargetIndex τ ≡ j
concreteFiberTargetAgreement
  {i = Relation.forcedTailFiniteIndex FTClass.tailEnd h}
  {j = Relation.forcedTailTailIndex FTClass.tailEnd t} τ member =
  mappedPropertyWithMembership
    (forcedTailFiber h t) (Relation.forcedTailIncidence FTClass.tailEnd)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.forcedTailTailIndex FTClass.tailEnd t)
    (λ σ σMember → cong (Relation.forcedTailTailIndex FTClass.tailEnd)
      (forcedTailFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.forcedTailFiniteIndex FTClass.nearTail h}
  {j = Relation.forcedTailTailIndex FTClass.nearTail t} τ member =
  mappedPropertyWithMembership
    (forcedTailFiber h t) (Relation.forcedTailIncidence FTClass.nearTail)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.forcedTailTailIndex FTClass.nearTail t)
    (λ σ σMember → cong (Relation.forcedTailTailIndex FTClass.nearTail)
      (forcedTailFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.forcedTailFiniteIndex FTClass.transition h}
  {j = Relation.forcedTailTailIndex FTClass.transition t} τ member =
  mappedPropertyWithMembership
    (forcedTailFiber h t) (Relation.forcedTailIncidence FTClass.transition)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.forcedTailTailIndex FTClass.transition t)
    (λ σ σMember → cong (Relation.forcedTailTailIndex FTClass.transition)
      (forcedTailFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.forcedTailFiniteIndex FTClass.degenerate h}
  {j = Relation.forcedTailTailIndex FTClass.degenerate t} τ member =
  mappedPropertyWithMembership
    (forcedTailFiber h t) (Relation.forcedTailIncidence FTClass.degenerate)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.forcedTailTailIndex FTClass.degenerate t)
    (λ σ σMember → cong (Relation.forcedTailTailIndex FTClass.degenerate)
      (forcedTailFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.adversarialFiniteIndex AdvClass.sparseAdmissible h}
  {j = Relation.adversarialTailIndex AdvClass.sparseAdmissible t} τ member =
  mappedPropertyWithMembership
    (adversarialFiber h t) (Relation.adversarialIncidence AdvClass.sparseAdmissible)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.adversarialTailIndex AdvClass.sparseAdmissible t)
    (λ σ σMember → cong (Relation.adversarialTailIndex AdvClass.sparseAdmissible)
      (adversarialFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.adversarialFiniteIndex AdvClass.angularDegenerate h}
  {j = Relation.adversarialTailIndex AdvClass.angularDegenerate t} τ member =
  mappedPropertyWithMembership
    (adversarialFiber h t) (Relation.adversarialIncidence AdvClass.angularDegenerate)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.adversarialTailIndex AdvClass.angularDegenerate t)
    (λ σ σMember → cong (Relation.adversarialTailIndex AdvClass.angularDegenerate)
      (adversarialFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.adversarialFiniteIndex AdvClass.boundarySmallShell h}
  {j = Relation.adversarialTailIndex AdvClass.boundarySmallShell t} τ member =
  mappedPropertyWithMembership
    (adversarialFiber h t) (Relation.adversarialIncidence AdvClass.boundarySmallShell)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.adversarialTailIndex AdvClass.boundarySmallShell t)
    (λ σ σMember → cong (Relation.adversarialTailIndex AdvClass.boundarySmallShell)
      (adversarialFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.transitionFiniteIndex TrClass.thinTransition h}
  {j = Relation.transitionTailIndex TrClass.thinTransition t} τ member =
  mappedPropertyWithMembership
    (transitionFiber h t) (Relation.transitionIncidence TrClass.thinTransition)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.transitionTailIndex TrClass.thinTransition t)
    (λ σ σMember → cong (Relation.transitionTailIndex TrClass.thinTransition)
      (transitionFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.transitionFiniteIndex TrClass.balancedTransition h}
  {j = Relation.transitionTailIndex TrClass.balancedTransition t} τ member =
  mappedPropertyWithMembership
    (transitionFiber h t) (Relation.transitionIncidence TrClass.balancedTransition)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.transitionTailIndex TrClass.balancedTransition t)
    (λ σ σMember → cong (Relation.transitionTailIndex TrClass.balancedTransition)
      (transitionFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.transitionFiniteIndex TrClass.rowThickTransition h}
  {j = Relation.transitionTailIndex TrClass.rowThickTransition t} τ member =
  mappedPropertyWithMembership
    (transitionFiber h t) (Relation.transitionIncidence TrClass.rowThickTransition)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.transitionTailIndex TrClass.rowThickTransition t)
    (λ σ σMember → cong (Relation.transitionTailIndex TrClass.rowThickTransition)
      (transitionFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement
  {i = Relation.transitionFiniteIndex TrClass.columnThickTransition h}
  {j = Relation.transitionTailIndex TrClass.columnThickTransition t} τ member =
  mappedPropertyWithMembership
    (transitionFiber h t) (Relation.transitionIncidence TrClass.columnThickTransition)
    (λ σ → Relation.concreteNonResidualTargetIndex σ
      ≡ Relation.transitionTailIndex TrClass.columnThickTransition t)
    (λ σ σMember → cong (Relation.transitionTailIndex TrClass.columnThickTransition)
      (transitionFiberTargetAgreement h t σ σMember)) τ member
concreteFiberTargetAgreement {i = _} {j = _} τ ()

concreteFiberRetainedAgreement :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {N : Nat} {i : Relation.ConcreteNonResidualFiniteIndex N}
  {j : Relation.ConcreteNonResidualTailIndex N} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  τ ∈ concreteNonResidualFiber i j →
  PhysicalRetainedPositiveSector predicates τ
concreteFiberRetainedAgreement landing
  (Relation.forcedTailIncidence c τ) member = forcedTailIncidenceRetained landing τ
concreteFiberRetainedAgreement landing
  (Relation.adversarialIncidence c τ) member = adversarialIncidenceRetained landing τ
concreteFiberRetainedAgreement landing
  (Relation.transitionIncidence c τ) member = transitionIncidenceRetained landing τ

concreteFiberComplete :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {N : Nat} {i : Relation.ConcreteNonResidualFiniteIndex N}
  {j : Relation.ConcreteNonResidualTailIndex N} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  Relation.concreteNonResidualSourceIndex τ ≡ i →
  Relation.concreteNonResidualTargetIndex τ ≡ j →
  PhysicalRetainedPositiveSector predicates τ →
  τ ∈ concreteNonResidualFiber i j
concreteFiberComplete landing
  (Relation.forcedTailIncidence FTClass.tailEnd τ) refl refl retained =
  mapMembership (Relation.forcedTailIncidence FTClass.tailEnd)
    (forcedTailFiberComplete landing
      (FT.headParam τ) (FT.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.forcedTailIncidence FTClass.nearTail τ) refl refl retained =
  mapMembership (Relation.forcedTailIncidence FTClass.nearTail)
    (forcedTailFiberComplete landing
      (FT.headParam τ) (FT.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.forcedTailIncidence FTClass.transition τ) refl refl retained =
  mapMembership (Relation.forcedTailIncidence FTClass.transition)
    (forcedTailFiberComplete landing
      (FT.headParam τ) (FT.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.forcedTailIncidence FTClass.degenerate τ) refl refl retained =
  mapMembership (Relation.forcedTailIncidence FTClass.degenerate)
    (forcedTailFiberComplete landing
      (FT.headParam τ) (FT.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.adversarialIncidence AdvClass.sparseAdmissible τ) refl refl retained =
  mapMembership (Relation.adversarialIncidence AdvClass.sparseAdmissible)
    (adversarialFiberComplete landing
      (Adv.headParam τ) (Adv.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.adversarialIncidence AdvClass.angularDegenerate τ) refl refl retained =
  mapMembership (Relation.adversarialIncidence AdvClass.angularDegenerate)
    (adversarialFiberComplete landing
      (Adv.headParam τ) (Adv.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.adversarialIncidence AdvClass.boundarySmallShell τ) refl refl retained =
  mapMembership (Relation.adversarialIncidence AdvClass.boundarySmallShell)
    (adversarialFiberComplete landing
      (Adv.headParam τ) (Adv.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.transitionIncidence TrClass.thinTransition τ) refl refl retained =
  mapMembership (Relation.transitionIncidence TrClass.thinTransition)
    (transitionFiberComplete landing
      (Tr.headParam τ) (Tr.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.transitionIncidence TrClass.balancedTransition τ) refl refl retained =
  mapMembership (Relation.transitionIncidence TrClass.balancedTransition)
    (transitionFiberComplete landing
      (Tr.headParam τ) (Tr.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.transitionIncidence TrClass.rowThickTransition τ) refl refl retained =
  mapMembership (Relation.transitionIncidence TrClass.rowThickTransition)
    (transitionFiberComplete landing
      (Tr.headParam τ) (Tr.tailParam τ) τ refl refl retained)
concreteFiberComplete landing
  (Relation.transitionIncidence TrClass.columnThickTransition τ) refl refl retained =
  mapMembership (Relation.transitionIncidence TrClass.columnThickTransition)
    (transitionFiberComplete landing
      (Tr.headParam τ) (Tr.tailParam τ) τ refl refl retained)

concreteFiberNoDuplicates :
  {N : Nat} →
  (i : Relation.ConcreteNonResidualFiniteIndex N) →
  (j : Relation.ConcreteNonResidualTailIndex N) →
  NoDuplicates (concreteNonResidualFiber i j)
concreteFiberNoDuplicates
  (Relation.forcedTailFiniteIndex FTClass.tailEnd h)
  (Relation.forcedTailTailIndex FTClass.tailEnd t) =
  mapNoDuplicates (Relation.forcedTailIncidence FTClass.tailEnd)
    (λ x y equality → forcedTailTagInjective equality)
    (forcedTailFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.forcedTailFiniteIndex FTClass.nearTail h)
  (Relation.forcedTailTailIndex FTClass.nearTail t) =
  mapNoDuplicates (Relation.forcedTailIncidence FTClass.nearTail)
    (λ x y equality → forcedTailTagInjective equality)
    (forcedTailFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.forcedTailFiniteIndex FTClass.transition h)
  (Relation.forcedTailTailIndex FTClass.transition t) =
  mapNoDuplicates (Relation.forcedTailIncidence FTClass.transition)
    (λ x y equality → forcedTailTagInjective equality)
    (forcedTailFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.forcedTailFiniteIndex FTClass.degenerate h)
  (Relation.forcedTailTailIndex FTClass.degenerate t) =
  mapNoDuplicates (Relation.forcedTailIncidence FTClass.degenerate)
    (λ x y equality → forcedTailTagInjective equality)
    (forcedTailFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.adversarialFiniteIndex AdvClass.sparseAdmissible h)
  (Relation.adversarialTailIndex AdvClass.sparseAdmissible t) =
  mapNoDuplicates (Relation.adversarialIncidence AdvClass.sparseAdmissible)
    (λ x y equality → adversarialTagInjective equality)
    (adversarialFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.adversarialFiniteIndex AdvClass.angularDegenerate h)
  (Relation.adversarialTailIndex AdvClass.angularDegenerate t) =
  mapNoDuplicates (Relation.adversarialIncidence AdvClass.angularDegenerate)
    (λ x y equality → adversarialTagInjective equality)
    (adversarialFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.adversarialFiniteIndex AdvClass.boundarySmallShell h)
  (Relation.adversarialTailIndex AdvClass.boundarySmallShell t) =
  mapNoDuplicates (Relation.adversarialIncidence AdvClass.boundarySmallShell)
    (λ x y equality → adversarialTagInjective equality)
    (adversarialFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.transitionFiniteIndex TrClass.thinTransition h)
  (Relation.transitionTailIndex TrClass.thinTransition t) =
  mapNoDuplicates (Relation.transitionIncidence TrClass.thinTransition)
    (λ x y equality → transitionTagInjective equality)
    (transitionFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.transitionFiniteIndex TrClass.balancedTransition h)
  (Relation.transitionTailIndex TrClass.balancedTransition t) =
  mapNoDuplicates (Relation.transitionIncidence TrClass.balancedTransition)
    (λ x y equality → transitionTagInjective equality)
    (transitionFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.transitionFiniteIndex TrClass.rowThickTransition h)
  (Relation.transitionTailIndex TrClass.rowThickTransition t) =
  mapNoDuplicates (Relation.transitionIncidence TrClass.rowThickTransition)
    (λ x y equality → transitionTagInjective equality)
    (transitionFiberNoDuplicates h t)
concreteFiberNoDuplicates
  (Relation.transitionFiniteIndex TrClass.columnThickTransition h)
  (Relation.transitionTailIndex TrClass.columnThickTransition t) =
  mapNoDuplicates (Relation.transitionIncidence TrClass.columnThickTransition)
    (λ x y equality → transitionTagInjective equality)
    (transitionFiberNoDuplicates h t)
concreteFiberNoDuplicates _ _ = unique[]
