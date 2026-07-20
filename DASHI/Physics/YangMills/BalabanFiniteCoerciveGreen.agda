module DASHI.Physics.YangMills.BalabanFiniteCoerciveGreen where

------------------------------------------------------------------------
-- Finite-dimensional coercivity-to-Green interface.
--
-- The theorem that a coercive finite-dimensional self-adjoint operator is
-- invertible with inverse norm bounded by the reciprocal coercivity constant is
-- standard imported linear analysis.  Conversion of that authority into the
-- repository's inverse and Green-bound certificates is checked here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore using
  (FiniteInverseCertificate)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record CoerciveFiniteOperator
    (Vector Scalar Bound : Set) : Set₁ where
  field
    operator : Vector → Vector
    inner : Vector → Vector → Scalar
    vectorNorm : Vector → Bound
    energy : Vector → Scalar
    coercivityConstant : Bound

    LessEqual : Bound → Bound → Set
    Positive : Bound → Set
    positiveCoercivity : Positive coercivityConstant

    energyDefinition : ∀ vector →
      energy vector ≡ inner vector (operator vector)
    Coercive : Set
    coercive : Coercive

open CoerciveFiniteOperator public

record FiniteCoerciveInverseAuthority
    {Vector Scalar Bound : Set}
    (dataSet : CoerciveFiniteOperator Vector Scalar Bound) : Set₁ where
  field
    inverse : Vector → Vector
    inverseLeft : ∀ vector → inverse (operator dataSet vector) ≡ vector
    inverseRight : ∀ vector → operator dataSet (inverse vector) ≡ vector

    reciprocalCoercivity : Bound
    multiplyBound : Bound → Bound → Bound
    inverseNormBound : ∀ vector →
      LessEqual dataSet
        (vectorNorm dataSet (inverse vector))
        (multiplyBound reciprocalCoercivity (vectorNorm dataSet vector))

open FiniteCoerciveInverseAuthority public

toFiniteInverseCertificate :
  ∀ {Vector Scalar Bound : Set}
    {dataSet : CoerciveFiniteOperator Vector Scalar Bound} →
  FiniteCoerciveInverseAuthority dataSet →
  FiniteInverseCertificate Vector
toFiniteInverseCertificate {dataSet = dataSet} authority = record
  { operator = operator dataSet
  ; inverse = inverse authority
  ; inverseLeft = inverseLeft authority
  ; inverseRight = inverseRight authority
  }

record GreenOperatorBound
    (Vector Bound : Set) : Set₁ where
  field
    green : Vector → Vector
    norm : Vector → Bound
    prefactor : Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    bound : ∀ source →
      LessEqual (norm (green source)) (multiply prefactor (norm source))

open GreenOperatorBound public

toGreenOperatorBound :
  ∀ {Vector Scalar Bound : Set}
    {dataSet : CoerciveFiniteOperator Vector Scalar Bound} →
  (authority : FiniteCoerciveInverseAuthority dataSet) →
  GreenOperatorBound Vector Bound
toGreenOperatorBound {dataSet = dataSet} authority = record
  { green = inverse authority
  ; norm = vectorNorm dataSet
  ; prefactor = reciprocalCoercivity authority
  ; multiply = multiplyBound authority
  ; LessEqual = LessEqual dataSet
  ; bound = inverseNormBound authority
  }

finiteCoerciveGreenAssemblyLevel : ProofLevel
finiteCoerciveGreenAssemblyLevel = machineChecked

finiteCoerciveInverseAuthorityLevel : ProofLevel
finiteCoerciveInverseAuthorityLevel = standardImported
