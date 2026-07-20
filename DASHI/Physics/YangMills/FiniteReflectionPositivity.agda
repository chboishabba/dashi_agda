module DASHI.Physics.YangMills.FiniteReflectionPositivity where

------------------------------------------------------------------------
-- Finite reflection positivity from a sum-of-squares factorization.
--
-- The analytic/representation-theoretic work is the construction of the
-- factorization. Once each square term lies in a positive additive cone, the
-- Osterwalder--Schrader inequality is a finite induction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record PositiveAdditiveScalar (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    Nonnegative : Scalar → Set
    zeroNonnegative : Nonnegative zero
    addNonnegative : ∀ {left right} →
      Nonnegative left → Nonnegative right →
      Nonnegative (add left right)

open PositiveAdditiveScalar public

sumTerms :
  ∀ {Index Scalar : Set} →
  PositiveAdditiveScalar Scalar →
  (Index → Scalar) → List Index → Scalar
sumTerms scalar [] terms = zero scalar
sumTerms scalar term (index ∷ rest) =
  add scalar (term index) (sumTerms scalar term rest)

sumTermsNonnegative :
  ∀ {Index Scalar : Set} →
  (scalar : PositiveAdditiveScalar Scalar) →
  (term : Index → Scalar) →
  (∀ index → Nonnegative scalar (term index)) →
  ∀ indices → Nonnegative scalar (sumTerms scalar term indices)
sumTermsNonnegative scalar term termPositive [] =
  zeroNonnegative scalar
sumTermsNonnegative scalar term termPositive (index ∷ rest) =
  addNonnegative scalar
    (termPositive index)
    (sumTermsNonnegative scalar term termPositive rest)

record ReflectionSquareFactorization
    (Observable Index Scalar : Set)
    (scalar : PositiveAdditiveScalar Scalar) : Set₁ where
  field
    indices : List Index
    squareTerm : Observable → Index → Scalar
    squareTermNonnegative : ∀ observable index →
      Nonnegative scalar (squareTerm observable index)
    osForm : Observable → Scalar
    factorization : ∀ observable →
      osForm observable ≡
      sumTerms scalar (squareTerm observable) indices

open ReflectionSquareFactorization public

osFormNonnegative :
  ∀ {Observable Index Scalar : Set}
    {scalar : PositiveAdditiveScalar Scalar} →
  (dataSet : ReflectionSquareFactorization Observable Index Scalar scalar) →
  ∀ observable → Nonnegative scalar (osForm dataSet observable)
osFormNonnegative {scalar = scalar} dataSet observable =
  subst
    (Nonnegative scalar)
    (symmetry (factorization dataSet observable))
    (sumTermsNonnegative scalar
      (squareTerm dataSet observable)
      (squareTermNonnegative dataSet observable)
      (indices dataSet))
  where
    symmetry : ∀ {A : Set} {left right : A} → left ≡ right → right ≡ left
    symmetry refl = refl

record FiniteReflectionPositive
    (Observable Scalar : Set)
    (scalar : PositiveAdditiveScalar Scalar) : Set₁ where
  field
    osForm : Observable → Scalar
    reflectionPositive : ∀ observable → Nonnegative scalar (osForm observable)

open FiniteReflectionPositive public

factorizationToReflectionPositive :
  ∀ {Observable Index Scalar : Set}
    {scalar : PositiveAdditiveScalar Scalar} →
  ReflectionSquareFactorization Observable Index Scalar scalar →
  FiniteReflectionPositive Observable Scalar scalar
factorizationToReflectionPositive dataSet = record
  { osForm = ReflectionSquareFactorization.osForm dataSet
  ; reflectionPositive = osFormNonnegative dataSet
  }

finiteReflectionPositivityLevel : ProofLevel
finiteReflectionPositivityLevel = machineChecked

reflectionSquareFactorizationInputLevel : ProofLevel
reflectionSquareFactorizationInputLevel = standardImported
