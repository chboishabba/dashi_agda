module DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban, "Large Field Renormalization. I. The Basic Step of the
-- R Operation", Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", Communications in
-- Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- Target locator pending primary-source verification:
-- equation (1.89), p. 387, for the T-operation small factor.
--
-- Relationship: this module distinguishes Bałaban's component classes from
-- the separate localized-expression intersection classes already represented
-- in BalabanClayGate4TypedReuseAndFiniteGeometryExact.  Only a certified
-- second/large-field-class component may be passed to the T operation.
------------------------------------------------------------------------

data LargeFieldComponentClass : Set where
  firstSmallFieldComponentClass : LargeFieldComponentClass
  secondTOperationComponentClass : LargeFieldComponentClass

record ComponentClassData (Scale Component : Set) : Set₁ where
  field
    classifyComponent : Scale → Component → LargeFieldComponentClass

open ComponentClassData public

record SecondClassComponent
    {Scale Component : Set}
    (classData : ComponentClassData Scale Component)
    (scale : Scale) : Set where
  constructor secondClassComponent
  field
    component : Component
    componentIsSecondClass :
      classifyComponent classData scale component
      ≡ secondTOperationComponentClass

open SecondClassComponent public

------------------------------------------------------------------------
-- Concrete finite T operation over the repository's constrained integral.
------------------------------------------------------------------------

record FiniteLocalTOperationData
    (Scale Fine SlowField Component Functional Scalar : Set) : Set₁ where
  field
    sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar
    classData : ComponentClassData Scale Component

    fastFibre : Scale → Component → List Fine
    localDensity : Scale → Component → SlowField → Fine → Scalar
    evaluateFunctional : Functional → Fine → Scalar
    multiply : Scalar → Scalar → Scalar

    zeroFunctional oneFunctional : Functional
    largeFieldIndicator : Scale → Component → Functional

open FiniteLocalTOperationData public

localIntegrand :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    (dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) →
  Scale → Component → SlowField → Functional → Fine → Scalar
localIntegrand dataSet scale component slow functional fine =
  multiply dataSet
    (localDensity dataSet scale component slow fine)
    (evaluateFunctional dataSet functional fine)

localizedTOperation :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    (dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) →
  (scale : Scale) →
  SecondClassComponent (classData dataSet) scale →
  SlowField → Functional → Scalar
localizedTOperation dataSet scale selected slow functional =
  Integral.constrainedIntegral
    (sumData dataSet)
    (fastFibre dataSet scale (component selected))
    (localIntegrand dataSet scale (component selected) slow functional)
    slow

------------------------------------------------------------------------
-- Ordered finite-sum consequences: positivity and monotonicity are derived
-- once the scalar/order laws and pointwise density facts are supplied.
------------------------------------------------------------------------

record FiniteTOperationOrderLaws
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    LessEqual : Scalar → Scalar → Set
    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addNonnegative : ∀ {left right} →
      LessEqual (Integral.zero (sumData dataSet)) left →
      LessEqual (Integral.zero (sumData dataSet)) right →
      LessEqual (Integral.zero (sumData dataSet))
        (Integral.add (sumData dataSet) left right)

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual
        (Integral.add (sumData dataSet) left right)
        (Integral.add (sumData dataSet) leftUpper rightUpper)

    densityNonnegative : ∀ scale component slow fine →
      LessEqual (Integral.zero (sumData dataSet))
        (localDensity dataSet scale component slow fine)

    multiplyRightMonotone : ∀ coefficient {left right} →
      LessEqual (Integral.zero (sumData dataSet)) coefficient →
      LessEqual left right →
      LessEqual (multiply dataSet coefficient left)
        (multiply dataSet coefficient right)

    multiplyZeroRight : ∀ coefficient →
      multiply dataSet coefficient (Integral.zero (sumData dataSet))
      ≡ Integral.zero (sumData dataSet)

    zeroFunctionalExact : ∀ fine →
      evaluateFunctional dataSet (zeroFunctional dataSet) fine
      ≡ Integral.zero (sumData dataSet)

open FiniteTOperationOrderLaws public

PointwiseNonnegative :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar} →
  FiniteTOperationOrderLaws dataSet → Functional → Set
PointwiseNonnegative order functional =
  ∀ fine → LessEqual order
    (Integral.zero (sumData _))
    (evaluateFunctional _ functional fine)

PointwiseLessEqual :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar} →
  FiniteTOperationOrderLaws dataSet → Functional → Functional → Set
PointwiseLessEqual order left right =
  ∀ fine → LessEqual order
    (evaluateFunctional _ left fine)
    (evaluateFunctional _ right fine)

foldPointwiseMonotone :
  ∀ {Fine SlowField Scalar}
    (sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar)
    (LessEqual : Scalar → Scalar → Set) →
  (∀ value → LessEqual value value) →
  (∀ {left leftUpper right rightUpper} →
    LessEqual left leftUpper → LessEqual right rightUpper →
    LessEqual (Integral.add sumData left right)
      (Integral.add sumData leftUpper rightUpper)) →
  (fields : List Fine) (lower upper : Fine → Scalar) (slow : SlowField) →
  (∀ fine → LessEqual (lower fine) (upper fine)) →
  LessEqual
    (Integral.foldSelected sumData lower slow fields)
    (Integral.foldSelected sumData upper slow fields)
foldPointwiseMonotone sumData LessEqual reflexive addMonotone [] lower upper slow pointwise =
  reflexive (Integral.zero sumData)
foldPointwiseMonotone sumData LessEqual reflexive addMonotone
  (fine ∷ fields) lower upper slow pointwise =
  addMonotone
    (pointwise fine)
    (foldPointwiseMonotone sumData LessEqual reflexive addMonotone
      fields lower upper slow pointwise)

selectedIntegrandMonotone :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (order : FiniteTOperationOrderLaws dataSet)
    scale component slow left right →
  PointwiseLessEqual order left right →
  ∀ fine →
  LessEqual order
    (Integral.selectedWith (sumData dataSet)
      (localIntegrand dataSet scale component slow left) slow fine)
    (Integral.selectedWith (sumData dataSet)
      (localIntegrand dataSet scale component slow right) slow fine)
selectedIntegrandMonotone {dataSet = dataSet}
  order scale component slow left right pointwise fine
  with Integral.coarseMatches (sumData dataSet) fine slow
... | false = reflexive order (Integral.zero (sumData dataSet))
... | true =
  multiplyRightMonotone order
    (localDensity dataSet scale component slow fine)
    (densityNonnegative order scale component slow fine)
    (pointwise fine)

tOperationMonotone :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (order : FiniteTOperationOrderLaws dataSet)
    scale (selected : SecondClassComponent (classData dataSet) scale)
    slow left right →
  PointwiseLessEqual order left right →
  LessEqual order
    (localizedTOperation dataSet scale selected slow left)
    (localizedTOperation dataSet scale selected slow right)
tOperationMonotone {dataSet = dataSet}
  order scale selected slow left right pointwise =
  foldPointwiseMonotone
    (sumData dataSet)
    (LessEqual order)
    (reflexive order)
    (addMonotone order)
    (fastFibre dataSet scale (component selected))
    (Integral.selectedWith (sumData dataSet)
      (localIntegrand dataSet scale (component selected) slow left) slow)
    (Integral.selectedWith (sumData dataSet)
      (localIntegrand dataSet scale (component selected) slow right) slow)
    slow
    (selectedIntegrandMonotone order scale (component selected)
      slow left right pointwise)

selectedIntegrandNonnegative :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (order : FiniteTOperationOrderLaws dataSet)
    scale component slow functional →
  PointwiseNonnegative order functional →
  ∀ fine →
  LessEqual order
    (Integral.zero (sumData dataSet))
    (Integral.selectedWith (sumData dataSet)
      (localIntegrand dataSet scale component slow functional) slow fine)
selectedIntegrandNonnegative {dataSet = dataSet}
  order scale component slow functional nonnegative fine
  with Integral.coarseMatches (sumData dataSet) fine slow
... | false = reflexive order (Integral.zero (sumData dataSet))
... | true =
  subst
    (λ left → LessEqual order left
      (multiply dataSet
        (localDensity dataSet scale component slow fine)
        (evaluateFunctional dataSet functional fine)))
    (multiplyZeroRight order
      (localDensity dataSet scale component slow fine))
    (multiplyRightMonotone order
      (localDensity dataSet scale component slow fine)
      (densityNonnegative order scale component slow fine)
      (nonnegative fine))

foldNonnegative :
  ∀ {Fine SlowField Scalar}
    (sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar)
    (LessEqual : Scalar → Scalar → Set) →
  (∀ value → LessEqual value value) →
  (∀ {left right} →
    LessEqual (Integral.zero sumData) left →
    LessEqual (Integral.zero sumData) right →
    LessEqual (Integral.zero sumData) (Integral.add sumData left right)) →
  (fields : List Fine) (selector : Fine → Scalar) (slow : SlowField) →
  (∀ fine → LessEqual (Integral.zero sumData) (selector fine)) →
  LessEqual (Integral.zero sumData)
    (Integral.foldSelected sumData selector slow fields)
foldNonnegative sumData LessEqual reflexive addNonnegative [] selector slow pointwise =
  reflexive (Integral.zero sumData)
foldNonnegative sumData LessEqual reflexive addNonnegative
  (fine ∷ fields) selector slow pointwise =
  addNonnegative
    (pointwise fine)
    (foldNonnegative sumData LessEqual reflexive addNonnegative
      fields selector slow pointwise)

tOperationPositive :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (order : FiniteTOperationOrderLaws dataSet)
    scale (selected : SecondClassComponent (classData dataSet) scale)
    slow functional →
  PointwiseNonnegative order functional →
  LessEqual order
    (Integral.zero (sumData dataSet))
    (localizedTOperation dataSet scale selected slow functional)
tOperationPositive {dataSet = dataSet}
  order scale selected slow functional nonnegative =
  foldNonnegative
    (sumData dataSet)
    (LessEqual order)
    (reflexive order)
    (addNonnegative order)
    (fastFibre dataSet scale (component selected))
    (Integral.selectedWith (sumData dataSet)
      (localIntegrand dataSet scale (component selected) slow functional) slow)
    slow
    (selectedIntegrandNonnegative order scale (component selected)
      slow functional nonnegative)

------------------------------------------------------------------------
-- Structural and normalization laws remain representation-specific, but they
-- are now tied to the concrete finite T operation above.
------------------------------------------------------------------------

record LocalTOperationStructuralLaws
    {Scale Fine SlowField Component Functional Scalar Gauge : Set}
    (dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    transformSlowField : Gauge → SlowField → SlowField
    transformFunctional : Gauge → Functional → Functional

    AdmissibleSlowField : Scale → SlowField → Set
    IntegrandDefinedOnFastFibre : Scale → Component → SlowField → Set
    AgreeOnEnlargement : Scale → Component → SlowField → SlowField → Set

    tOperationDomainClosed : ∀ scale selected slow →
      AdmissibleSlowField scale slow →
      IntegrandDefinedOnFastFibre scale (component selected) slow

    tOperationGaugeCovariant : ∀ gauge scale selected slow functional →
      localizedTOperation dataSet scale selected
        (transformSlowField gauge slow)
        (transformFunctional gauge functional)
      ≡ localizedTOperation dataSet scale selected slow functional

    tOperationDependsOnlyOnEnlargement :
      ∀ scale selected left right functional →
      AgreeOnEnlargement scale (component selected) left right →
      localizedTOperation dataSet scale selected left functional
      ≡ localizedTOperation dataSet scale selected right functional

open LocalTOperationStructuralLaws public

record LargeFieldActivationRatioData
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    divide : Scalar → Scalar → Scalar
    conditionalLargeFieldWeight : Scale → Component → SlowField → Scalar
    denominatorNonzero : ∀ scale selected slow → Set
    largeFieldActivationAsTRatio : ∀ scale selected slow →
      conditionalLargeFieldWeight scale (component selected) slow
      ≡ divide
          (localizedTOperation dataSet scale selected slow
            (largeFieldIndicator dataSet scale (component selected)))
          (localizedTOperation dataSet scale selected slow
            (oneFunctional dataSet))

open LargeFieldActivationRatioData public

record ExactBalabanTOperationSmallFactor
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    LessEqual : Scalar → Scalar → Set
    one two beta0 : Scalar
    add divide multiply : Scalar → Scalar → Scalar
    expNegative : Scalar → Scalar
    p0 : Scale → Scalar
    AdmissibleCoupling : Scale → Set

    primaryEquation189Checked : Set

    tOperationSmallFactor : ∀ scale selected slow →
      AdmissibleCoupling scale →
      LessEqual
        (localizedTOperation dataSet scale selected slow
          (oneFunctional dataSet))
        (expNegative
          (multiply
            (divide two (add one beta0))
            (p0 scale)))

open ExactBalabanTOperationSmallFactor public

componentClassVocabularyLevel : ProofLevel
componentClassVocabularyLevel = machineChecked

finiteLocalTOperationDefinitionLevel : ProofLevel
finiteLocalTOperationDefinitionLevel = machineChecked

finiteTOperationPositivityMonotonicityLevel : ProofLevel
finiteTOperationPositivityMonotonicityLevel = machineChecked

tOperationStructuralLawInputsLevel : ProofLevel
tOperationStructuralLawInputsLevel = conditional

tOperationActivationRatioInputsLevel : ProofLevel
tOperationActivationRatioInputsLevel = conditional

tOperationEquation189InhabitantLevel : ProofLevel
tOperationEquation189InhabitantLevel = conditional
