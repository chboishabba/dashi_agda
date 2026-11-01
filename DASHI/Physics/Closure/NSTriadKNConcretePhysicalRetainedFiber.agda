module DASHI.Physics.Closure.NSTriadKNConcretePhysicalRetainedFiber where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; [])
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNRetainedPositiveSectorKernelOperator as RetainedKernel
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNResidualClosureDependency as ResidualClosure
open import DASHI.Physics.Closure.NSTriadKNUnifiedConcreteFiber public

open KernelFormula using (_∈_)

one : Nat
one = suc zero

data PhysicalStage3Index (N : Nat) : Set where
  sourceStage3Index :
    Relation.ConcreteNonResidualFiniteIndex N → PhysicalStage3Index N
  targetStage3Index :
    Relation.ConcreteNonResidualTailIndex N → PhysicalStage3Index N

physicalStage3SourceIndex :
  {N : Nat} →
  Relation.ConcreteNonResidualTriadIncidence N → PhysicalStage3Index N
physicalStage3SourceIndex τ =
  sourceStage3Index (Relation.concreteNonResidualSourceIndex τ)

physicalStage3TargetIndex :
  {N : Nat} →
  Relation.ConcreteNonResidualTriadIncidence N → PhysicalStage3Index N
physicalStage3TargetIndex τ =
  targetStage3Index (Relation.concreteNonResidualTargetIndex τ)

physicalStage3Fiber :
  {N : Nat} →
  PhysicalStage3Index N → PhysicalStage3Index N →
  List (Relation.ConcreteNonResidualTriadIncidence N)
physicalStage3Fiber (sourceStage3Index i) (targetStage3Index j) =
  concreteNonResidualFiber i j
physicalStage3Fiber _ _ = []

physicalStage3FiberSourceAgreement :
  {N : Nat} {i j : PhysicalStage3Index N} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  τ ∈ physicalStage3Fiber i j → physicalStage3SourceIndex τ ≡ i
physicalStage3FiberSourceAgreement
  {i = sourceStage3Index i} {j = targetStage3Index j} τ member =
  cong sourceStage3Index (concreteFiberSourceAgreement τ member)
physicalStage3FiberSourceAgreement {i = _} {j = _} τ ()

physicalStage3FiberTargetAgreement :
  {N : Nat} {i j : PhysicalStage3Index N} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  τ ∈ physicalStage3Fiber i j → physicalStage3TargetIndex τ ≡ j
physicalStage3FiberTargetAgreement
  {i = sourceStage3Index i} {j = targetStage3Index j} τ member =
  cong targetStage3Index (concreteFiberTargetAgreement τ member)
physicalStage3FiberTargetAgreement {i = _} {j = _} τ ()

physicalStage3FiberRetainedAgreement :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {N : Nat} {i j : PhysicalStage3Index N} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  τ ∈ physicalStage3Fiber i j →
  PhysicalRetainedPositiveSector predicates τ
physicalStage3FiberRetainedAgreement landing
  {i = sourceStage3Index i} {j = targetStage3Index j} τ member =
  concreteFiberRetainedAgreement landing τ member
physicalStage3FiberRetainedAgreement landing {i = _} {j = _} τ ()

physicalStage3FiberComplete :
  {realization : ConcreteFourierRealization} →
  {weights : PhysicalTriadWeightAuthority realization} →
  {predicates : PhysicalRetainedSectorPredicates realization weights} →
  (landing : PhysicalRetainedFamilyLanding predicates) →
  {N : Nat} {i j : PhysicalStage3Index N} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  physicalStage3SourceIndex τ ≡ i →
  physicalStage3TargetIndex τ ≡ j →
  PhysicalRetainedPositiveSector predicates τ →
  τ ∈ physicalStage3Fiber i j
physicalStage3FiberComplete landing τ refl refl retained =
  concreteFiberComplete landing τ refl refl retained

physicalStage3FiberNoDuplicates :
  {N : Nat} → (i j : PhysicalStage3Index N) →
  NoDuplicates (physicalStage3Fiber i j)
physicalStage3FiberNoDuplicates
  (sourceStage3Index i) (targetStage3Index j) =
  concreteFiberNoDuplicates i j
physicalStage3FiberNoDuplicates _ _ = unique[]

record CanonicalPhysicalRetainedAuthorities : Set₁ where
  constructor mkCanonicalPhysicalRetainedAuthorities
  field
    realization : ConcreteFourierRealization
    weights : PhysicalTriadWeightAuthority realization
    predicates : PhysicalRetainedSectorPredicates realization weights
    landing : PhysicalRetainedFamilyLanding predicates

open CanonicalPhysicalRetainedAuthorities public

canonicalRetainedPositiveSectorFiberData :
  CanonicalPhysicalRetainedAuthorities →
  RetainedKernel.RetainedPositiveSectorFiberData
canonicalRetainedPositiveSectorFiberData authorities =
  RetainedKernel.mkRetainedPositiveSectorFiberData
    (PhysicalStage3Index one)
    (Relation.ConcreteNonResidualTriadIncidence one)
    physicalStage3SourceIndex
    physicalStage3TargetIndex
    (concreteIncidenceToRetainedTriad
      (realization authorities) (weights authorities))
    (PhysicalRetainedPositiveSector (predicates authorities))
    (physicalTriadWeight (weights authorities))
    physicalStage3Fiber
    physicalStage3FiberSourceAgreement
    physicalStage3FiberTargetAgreement
    (physicalStage3FiberRetainedAgreement (landing authorities))
    (physicalStage3FiberComplete (landing authorities))

canonicalActualPairIncidenceKernelFormula :
  CanonicalPhysicalRetainedAuthorities →
  KernelFormula.ActualPairIncidenceKernelFormulaTarget
    ResidueNorm.nWeightedResidueNormModel one
canonicalActualPairIncidenceKernelFormula authorities =
  RetainedKernel.retainedFiberToKernelFormulaTarget
    ResidueNorm.nWeightedResidueNormModel
    (canonicalRetainedPositiveSectorFiberData authorities)

canonicalActualKernelFormula :
  (authorities : CanonicalPhysicalRetainedAuthorities) →
  (i j : PhysicalStage3Index one) →
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
    (canonicalActualPairIncidenceKernelFormula authorities) i j
    ≡
  KernelFormula.RetainedTriadFiberEnumerationInputs.fiberAggregate
    (KernelFormula.ActualPairIncidenceKernelFormulaTarget.enumeration
      (canonicalActualPairIncidenceKernelFormula authorities)) i j
canonicalActualKernelFormula authorities =
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernelFormula
    (canonicalActualPairIncidenceKernelFormula authorities)

canonicalActualKernelNonnegative :
  (authorities : CanonicalPhysicalRetainedAuthorities) →
  (i j : PhysicalStage3Index one) →
  zero ≤ KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
    (canonicalActualPairIncidenceKernelFormula authorities) i j
canonicalActualKernelNonnegative authorities =
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernelNonnegative
    (canonicalActualPairIncidenceKernelFormula authorities)

residualPhysicalKernelDominatedByNonResidualAggregate :
  ResidualClosure.residualKernelDominatedByClosedProfiles ≡ true
residualPhysicalKernelDominatedByNonResidualAggregate =
  Relation.canonicalResidualContributionControlledByNonResidualRelation
    ResidueNorm.nWeightedResidueNormModel

residualDominationPreservedByFiberAggregate :
  ResidualClosure.residualKernelDominatedByClosedProfiles ≡ true
residualDominationPreservedByFiberAggregate =
  residualPhysicalKernelDominatedByNonResidualAggregate

classSpecificFiniteFibersImplemented : Bool
classSpecificFiniteFibersImplemented = true

classSpecificFiniteFibersImplementedIsTrue :
  classSpecificFiniteFibersImplemented ≡ true
classSpecificFiniteFibersImplementedIsTrue = refl

unifiedRetainedFiberImplemented : Bool
unifiedRetainedFiberImplemented = true

unifiedRetainedFiberImplementedIsTrue :
  unifiedRetainedFiberImplemented ≡ true
unifiedRetainedFiberImplementedIsTrue = refl

physicalAuthorityToKernelFormulaImplemented : Bool
physicalAuthorityToKernelFormulaImplemented = true

physicalAuthorityToKernelFormulaImplementedIsTrue :
  physicalAuthorityToKernelFormulaImplemented ≡ true
physicalAuthorityToKernelFormulaImplementedIsTrue = refl

canonicalPhysicalRetainedAuthoritiesInhabited : Bool
canonicalPhysicalRetainedAuthoritiesInhabited = false

canonicalPhysicalRetainedAuthoritiesInhabitedIsFalse :
  canonicalPhysicalRetainedAuthoritiesInhabited ≡ false
canonicalPhysicalRetainedAuthoritiesInhabitedIsFalse = refl

physicalConstrainedSpectralGapClosed : Bool
physicalConstrainedSpectralGapClosed = false

physicalConstrainedSpectralGapClosedIsFalse :
  physicalConstrainedSpectralGapClosed ≡ false
physicalConstrainedSpectralGapClosedIsFalse = refl
