module DASHI.Physics.Closure.NSTriadKNUnifiedConcreteFiberSource where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; [])
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as FTClass
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as FT
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as AdvClass
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as Adv
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as TrClass
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as Tr
open import DASHI.Physics.Closure.NSTriadKNClassFiniteFibers public

open KernelFormula using (_∈_)

concreteNonResidualFiber :
  {N : Nat} →
  Relation.ConcreteNonResidualFiniteIndex N →
  Relation.ConcreteNonResidualTailIndex N →
  List (Relation.ConcreteNonResidualTriadIncidence N)
concreteNonResidualFiber
  (Relation.forcedTailFiniteIndex FTClass.tailEnd h)
  (Relation.forcedTailTailIndex FTClass.tailEnd t) =
  mapList (Relation.forcedTailIncidence FTClass.tailEnd) (forcedTailFiber h t)
concreteNonResidualFiber
  (Relation.forcedTailFiniteIndex FTClass.nearTail h)
  (Relation.forcedTailTailIndex FTClass.nearTail t) =
  mapList (Relation.forcedTailIncidence FTClass.nearTail) (forcedTailFiber h t)
concreteNonResidualFiber
  (Relation.forcedTailFiniteIndex FTClass.transition h)
  (Relation.forcedTailTailIndex FTClass.transition t) =
  mapList (Relation.forcedTailIncidence FTClass.transition) (forcedTailFiber h t)
concreteNonResidualFiber
  (Relation.forcedTailFiniteIndex FTClass.degenerate h)
  (Relation.forcedTailTailIndex FTClass.degenerate t) =
  mapList (Relation.forcedTailIncidence FTClass.degenerate) (forcedTailFiber h t)
concreteNonResidualFiber
  (Relation.adversarialFiniteIndex AdvClass.sparseAdmissible h)
  (Relation.adversarialTailIndex AdvClass.sparseAdmissible t) =
  mapList (Relation.adversarialIncidence AdvClass.sparseAdmissible) (adversarialFiber h t)
concreteNonResidualFiber
  (Relation.adversarialFiniteIndex AdvClass.angularDegenerate h)
  (Relation.adversarialTailIndex AdvClass.angularDegenerate t) =
  mapList (Relation.adversarialIncidence AdvClass.angularDegenerate) (adversarialFiber h t)
concreteNonResidualFiber
  (Relation.adversarialFiniteIndex AdvClass.boundarySmallShell h)
  (Relation.adversarialTailIndex AdvClass.boundarySmallShell t) =
  mapList (Relation.adversarialIncidence AdvClass.boundarySmallShell) (adversarialFiber h t)
concreteNonResidualFiber
  (Relation.transitionFiniteIndex TrClass.thinTransition h)
  (Relation.transitionTailIndex TrClass.thinTransition t) =
  mapList (Relation.transitionIncidence TrClass.thinTransition) (transitionFiber h t)
concreteNonResidualFiber
  (Relation.transitionFiniteIndex TrClass.balancedTransition h)
  (Relation.transitionTailIndex TrClass.balancedTransition t) =
  mapList (Relation.transitionIncidence TrClass.balancedTransition) (transitionFiber h t)
concreteNonResidualFiber
  (Relation.transitionFiniteIndex TrClass.rowThickTransition h)
  (Relation.transitionTailIndex TrClass.rowThickTransition t) =
  mapList (Relation.transitionIncidence TrClass.rowThickTransition) (transitionFiber h t)
concreteNonResidualFiber
  (Relation.transitionFiniteIndex TrClass.columnThickTransition h)
  (Relation.transitionTailIndex TrClass.columnThickTransition t) =
  mapList (Relation.transitionIncidence TrClass.columnThickTransition) (transitionFiber h t)
concreteNonResidualFiber _ _ = []

forcedTailTagInjective :
  {N : Nat} {c : FTClass.ForcedTailClass} →
  {x y : FT.ForcedTailTriadIncidence c N} →
  Relation.forcedTailIncidence c x ≡ Relation.forcedTailIncidence c y → x ≡ y
forcedTailTagInjective refl = refl

adversarialTagInjective :
  {N : Nat} {c : AdvClass.AdversarialClass} →
  {x y : Adv.AdversarialTriadIncidence c N} →
  Relation.adversarialIncidence c x ≡ Relation.adversarialIncidence c y → x ≡ y
adversarialTagInjective refl = refl

transitionTagInjective :
  {N : Nat} {c : TrClass.TransitionClass} →
  {x y : Tr.TransitionTriadIncidence c N} →
  Relation.transitionIncidence c x ≡ Relation.transitionIncidence c y → x ≡ y
transitionTagInjective refl = refl

concreteFiberSourceAgreement :
  {N : Nat} {i : Relation.ConcreteNonResidualFiniteIndex N}
  {j : Relation.ConcreteNonResidualTailIndex N} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  τ ∈ concreteNonResidualFiber i j →
  Relation.concreteNonResidualSourceIndex τ ≡ i
concreteFiberSourceAgreement
  {i = Relation.forcedTailFiniteIndex FTClass.tailEnd h}
  {j = Relation.forcedTailTailIndex FTClass.tailEnd t} τ member =
  mappedPropertyWithMembership
    (forcedTailFiber h t) (Relation.forcedTailIncidence FTClass.tailEnd)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.forcedTailFiniteIndex FTClass.tailEnd h)
    (λ σ σMember → cong (Relation.forcedTailFiniteIndex FTClass.tailEnd)
      (forcedTailFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.forcedTailFiniteIndex FTClass.nearTail h}
  {j = Relation.forcedTailTailIndex FTClass.nearTail t} τ member =
  mappedPropertyWithMembership
    (forcedTailFiber h t) (Relation.forcedTailIncidence FTClass.nearTail)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.forcedTailFiniteIndex FTClass.nearTail h)
    (λ σ σMember → cong (Relation.forcedTailFiniteIndex FTClass.nearTail)
      (forcedTailFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.forcedTailFiniteIndex FTClass.transition h}
  {j = Relation.forcedTailTailIndex FTClass.transition t} τ member =
  mappedPropertyWithMembership
    (forcedTailFiber h t) (Relation.forcedTailIncidence FTClass.transition)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.forcedTailFiniteIndex FTClass.transition h)
    (λ σ σMember → cong (Relation.forcedTailFiniteIndex FTClass.transition)
      (forcedTailFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.forcedTailFiniteIndex FTClass.degenerate h}
  {j = Relation.forcedTailTailIndex FTClass.degenerate t} τ member =
  mappedPropertyWithMembership
    (forcedTailFiber h t) (Relation.forcedTailIncidence FTClass.degenerate)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.forcedTailFiniteIndex FTClass.degenerate h)
    (λ σ σMember → cong (Relation.forcedTailFiniteIndex FTClass.degenerate)
      (forcedTailFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.adversarialFiniteIndex AdvClass.sparseAdmissible h}
  {j = Relation.adversarialTailIndex AdvClass.sparseAdmissible t} τ member =
  mappedPropertyWithMembership
    (adversarialFiber h t) (Relation.adversarialIncidence AdvClass.sparseAdmissible)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.adversarialFiniteIndex AdvClass.sparseAdmissible h)
    (λ σ σMember → cong (Relation.adversarialFiniteIndex AdvClass.sparseAdmissible)
      (adversarialFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.adversarialFiniteIndex AdvClass.angularDegenerate h}
  {j = Relation.adversarialTailIndex AdvClass.angularDegenerate t} τ member =
  mappedPropertyWithMembership
    (adversarialFiber h t) (Relation.adversarialIncidence AdvClass.angularDegenerate)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.adversarialFiniteIndex AdvClass.angularDegenerate h)
    (λ σ σMember → cong (Relation.adversarialFiniteIndex AdvClass.angularDegenerate)
      (adversarialFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.adversarialFiniteIndex AdvClass.boundarySmallShell h}
  {j = Relation.adversarialTailIndex AdvClass.boundarySmallShell t} τ member =
  mappedPropertyWithMembership
    (adversarialFiber h t) (Relation.adversarialIncidence AdvClass.boundarySmallShell)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.adversarialFiniteIndex AdvClass.boundarySmallShell h)
    (λ σ σMember → cong (Relation.adversarialFiniteIndex AdvClass.boundarySmallShell)
      (adversarialFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.transitionFiniteIndex TrClass.thinTransition h}
  {j = Relation.transitionTailIndex TrClass.thinTransition t} τ member =
  mappedPropertyWithMembership
    (transitionFiber h t) (Relation.transitionIncidence TrClass.thinTransition)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.transitionFiniteIndex TrClass.thinTransition h)
    (λ σ σMember → cong (Relation.transitionFiniteIndex TrClass.thinTransition)
      (transitionFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.transitionFiniteIndex TrClass.balancedTransition h}
  {j = Relation.transitionTailIndex TrClass.balancedTransition t} τ member =
  mappedPropertyWithMembership
    (transitionFiber h t) (Relation.transitionIncidence TrClass.balancedTransition)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.transitionFiniteIndex TrClass.balancedTransition h)
    (λ σ σMember → cong (Relation.transitionFiniteIndex TrClass.balancedTransition)
      (transitionFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.transitionFiniteIndex TrClass.rowThickTransition h}
  {j = Relation.transitionTailIndex TrClass.rowThickTransition t} τ member =
  mappedPropertyWithMembership
    (transitionFiber h t) (Relation.transitionIncidence TrClass.rowThickTransition)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.transitionFiniteIndex TrClass.rowThickTransition h)
    (λ σ σMember → cong (Relation.transitionFiniteIndex TrClass.rowThickTransition)
      (transitionFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement
  {i = Relation.transitionFiniteIndex TrClass.columnThickTransition h}
  {j = Relation.transitionTailIndex TrClass.columnThickTransition t} τ member =
  mappedPropertyWithMembership
    (transitionFiber h t) (Relation.transitionIncidence TrClass.columnThickTransition)
    (λ σ → Relation.concreteNonResidualSourceIndex σ
      ≡ Relation.transitionFiniteIndex TrClass.columnThickTransition h)
    (λ σ σMember → cong (Relation.transitionFiniteIndex TrClass.columnThickTransition)
      (transitionFiberSourceAgreement h t σ σMember)) τ member
concreteFiberSourceAgreement {i = _} {j = _} τ ()
