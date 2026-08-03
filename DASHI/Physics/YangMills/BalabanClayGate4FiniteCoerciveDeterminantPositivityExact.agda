module DASHI.Physics.YangMills.BalabanClayGate4FiniteCoerciveDeterminantPositivityExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- Barry Simon,
-- "Trace Ideals and Their Applications", second edition,
-- American Mathematical Society (2005). DOI: 10.1090/surv/120.
--
-- E. V. Haynsworth,
-- "Determination of the inertia of a partitioned Hermitian matrix",
-- Linear Algebra and its Applications 1 (1968), 73--81.
-- DOI: 10.1016/0024-3795(68)90050-5.
--
-- In the finite lattice fibre the determinant is an ordinary finite product.
-- The exact reduction below separates the spectral representation from the
-- elementary theorem that a product of strictly positive eigenvalues is
-- strictly positive.
------------------------------------------------------------------------

record StrictPositiveMultiplicativeAlgebra (Scalar : Set) : Set₁ where
  field
    one : Scalar
    multiply : Scalar → Scalar → Scalar
    Positive : Scalar → Set
    onePositive : Positive one
    multiplyPositive : ∀ {left right} →
      Positive left → Positive right → Positive (multiply left right)

open StrictPositiveMultiplicativeAlgebra public

data AllPositive {Scalar : Set}
    (algebra : StrictPositiveMultiplicativeAlgebra Scalar) :
    List Scalar → Set where
  allPositiveNil : AllPositive algebra []
  allPositiveCons : ∀ {value values} →
    Positive algebra value →
    AllPositive algebra values →
    AllPositive algebra (value ∷ values)

finiteProduct :
  ∀ {Scalar} →
  StrictPositiveMultiplicativeAlgebra Scalar → List Scalar → Scalar
finiteProduct algebra [] = one algebra
finiteProduct algebra (value ∷ values) =
  multiply algebra value (finiteProduct algebra values)

finiteProductPositive :
  ∀ {Scalar}
    (algebra : StrictPositiveMultiplicativeAlgebra Scalar)
    {values} →
  AllPositive algebra values →
  Positive algebra (finiteProduct algebra values)
finiteProductPositive algebra allPositiveNil = onePositive algebra
finiteProductPositive algebra
  (allPositiveCons valuePositive tailPositive) =
  multiplyPositive algebra valuePositive
    (finiteProductPositive algebra tailPositive)

record FiniteCoerciveDeterminantData
    (Index Scalar : Set)
    (algebra : StrictPositiveMultiplicativeAlgebra Scalar) : Set₁ where
  field
    eigenvalues : Index → List Scalar
    determinantFactor : Index → Scalar
    Coercive : Index → Set

    determinantSpectralRepresentation : ∀ index →
      determinantFactor index ≡ finiteProduct algebra (eigenvalues index)

    coercivityGivesPositiveEigenvalues : ∀ index →
      Coercive index → AllPositive algebra (eigenvalues index)

open FiniteCoerciveDeterminantData public

coerciveDeterminantPositive :
  ∀ {Index Scalar}
    {algebra : StrictPositiveMultiplicativeAlgebra Scalar} →
  (dataSet : FiniteCoerciveDeterminantData Index Scalar algebra) →
  ∀ index → Coercive dataSet index →
  Positive algebra (determinantFactor dataSet index)
coerciveDeterminantPositive {algebra = algebra} dataSet index coercive =
  subst
    (Positive algebra)
    (sym (determinantSpectralRepresentation dataSet index))
    (finiteProductPositive algebra
      (coercivityGivesPositiveEigenvalues dataSet index coercive))

record RelativeHessianSpectralPositivity
    (Index Scalar : Set)
    (algebra : StrictPositiveMultiplicativeAlgebra Scalar) : Set₁ where
  field
    reference : FiniteCoerciveDeterminantData Index Scalar algebra
    physical : FiniteCoerciveDeterminantData Index Scalar algebra

    SmallFieldIndex : Index → Set
    referenceCoercive : ∀ index → Coercive reference index
    physicalCoerciveOnSmallField : ∀ index →
      SmallFieldIndex index → Coercive physical index

open RelativeHessianSpectralPositivity public

referenceDeterminantPositive :
  ∀ {Index Scalar}
    {algebra : StrictPositiveMultiplicativeAlgebra Scalar} →
  (dataSet : RelativeHessianSpectralPositivity Index Scalar algebra) →
  ∀ index → Positive algebra
    (determinantFactor (reference dataSet) index)
referenceDeterminantPositive dataSet index =
  coerciveDeterminantPositive (reference dataSet) index
    (referenceCoercive dataSet index)

physicalDeterminantPositiveOnSmallField :
  ∀ {Index Scalar}
    {algebra : StrictPositiveMultiplicativeAlgebra Scalar} →
  (dataSet : RelativeHessianSpectralPositivity Index Scalar algebra) →
  ∀ index → SmallFieldIndex dataSet index →
  Positive algebra (determinantFactor (physical dataSet) index)
physicalDeterminantPositiveOnSmallField dataSet index small =
  coerciveDeterminantPositive (physical dataSet) index
    (physicalCoerciveOnSmallField dataSet index small)

finitePositiveProductLevel : ProofLevel
finitePositiveProductLevel = machineChecked

coerciveDeterminantPositivityReductionLevel : ProofLevel
coerciveDeterminantPositivityReductionLevel = machineChecked

relativeHessianDeterminantPositivityLevel : ProofLevel
relativeHessianDeterminantPositivityLevel = machineChecked

physicalFiniteSpectralRepresentationInputsLevel : ProofLevel
physicalFiniteSpectralRepresentationInputsLevel = conditional

physicalCoercivityToEigenvaluePositivityInputsLevel : ProofLevel
physicalCoercivityToEigenvaluePositivityInputsLevel = conditional
