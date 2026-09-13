{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact where

------------------------------------------------------------------------
-- NORMALIZED TWO-SOURCE GENERATING FUNCTIONAL -> CONNECTED COVARIANCE
--
-- This is source-independent finite calculus.  For a normalized generating
-- functional Z[J] with Z[0]=1, first source derivatives give one-point
-- expectations and the mixed second derivative gives the two-point moment.
-- The mixed Hessian of log Z is therefore the connected two-point cumulant:
--
--   D_F D_G log Z |0 = <FG> - <F><G>.
--
-- The theorem below deliberately separates:
--   * standard normalized log-derivative calculus;
--   * physical/source semantics identifying literal J-directions with F,G.
--
-- A citation or a generic `connected` label cannot supply the latter.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record TwoSourceMomentAlgebra (Observable Scalar : Set) : Set₁ where
  field
    subtract multiply : Scalar → Scalar → Scalar
    productObservable : Observable → Observable → Observable
    expectation : Observable → Scalar

open TwoSourceMomentAlgebra public

connectedCovariance :
  ∀ {Observable Scalar} →
  TwoSourceMomentAlgebra Observable Scalar →
  Observable → Observable → Scalar
connectedCovariance algebra left right =
  subtract algebra
    (expectation algebra (productObservable algebra left right))
    (multiply algebra (expectation algebra left) (expectation algebra right))

record NormalizedLogSourceCalculus
    {Observable Scalar : Set}
    (algebra : TwoSourceMomentAlgebra Observable Scalar) : Set₁ where
  field
    firstSourceDerivative : Observable → Scalar
    mixedSecondSourceDerivative : Observable → Observable → Scalar
    mixedSecondLogDerivative : Observable → Observable → Scalar

    -- Standard source differentiation at the normalized base point.
    normalizedFirstDerivativeMeaning : ∀ observable →
      firstSourceDerivative observable
      ≡ expectation algebra observable

    normalizedMixedSecondDerivativeMeaning : ∀ left right →
      mixedSecondSourceDerivative left right
      ≡ expectation algebra (productObservable algebra left right)

    -- Quotient/chain rule for log Z at Z[0]=1.
    normalizedLogHessianRule : ∀ left right →
      mixedSecondLogDerivative left right
      ≡ subtract algebra
          (mixedSecondSourceDerivative left right)
          (multiply algebra
            (firstSourceDerivative left)
            (firstSourceDerivative right))

open NormalizedLogSourceCalculus public

mixedSecondLogDerivativeIsConnectedCovariance :
  ∀ {Observable Scalar}
    {algebra : TwoSourceMomentAlgebra Observable Scalar} →
  (calculus : NormalizedLogSourceCalculus algebra) →
  ∀ left right →
  mixedSecondLogDerivative calculus left right
  ≡ connectedCovariance algebra left right
mixedSecondLogDerivativeIsConnectedCovariance {algebra = algebra}
  calculus left right =
  trans
    (normalizedLogHessianRule calculus left right)
    (trans
      (cong
        (λ value → subtract algebra value
          (multiply algebra
            (firstSourceDerivative calculus left)
            (firstSourceDerivative calculus right)))
        (normalizedMixedSecondDerivativeMeaning calculus left right))
      (trans
        (cong
          (λ value → subtract algebra
            (expectation algebra (productObservable algebra left right))
            (multiply algebra value
              (firstSourceDerivative calculus right)))
          (normalizedFirstDerivativeMeaning calculus left))
        (cong
          (λ value → subtract algebra
            (expectation algebra (productObservable algebra left right))
            (multiply algebra (expectation algebra left) value))
          (normalizedFirstDerivativeMeaning calculus right))))

------------------------------------------------------------------------
-- Literal source-direction weld.
------------------------------------------------------------------------

record LiteralTwoSourceInsertionMeaning
    {Observable Scalar : Set}
    {algebra : TwoSourceMomentAlgebra Observable Scalar}
    (calculus : NormalizedLogSourceCalculus algebra)
    (SourceDirection : Set) : Set₁ where
  field
    sourceDirectionOf : Observable → SourceDirection

    literalFirstDerivative : SourceDirection → Scalar
    literalMixedSecondDerivative : SourceDirection → SourceDirection → Scalar
    literalMixedSecondLogDerivative :
      SourceDirection → SourceDirection → Scalar

    firstDirectionAgrees : ∀ observable →
      literalFirstDerivative (sourceDirectionOf observable)
      ≡ firstSourceDerivative calculus observable

    secondDirectionAgrees : ∀ left right →
      literalMixedSecondDerivative
        (sourceDirectionOf left) (sourceDirectionOf right)
      ≡ mixedSecondSourceDerivative calculus left right

    logSecondDirectionAgrees : ∀ left right →
      literalMixedSecondLogDerivative
        (sourceDirectionOf left) (sourceDirectionOf right)
      ≡ mixedSecondLogDerivative calculus left right

open LiteralTwoSourceInsertionMeaning public

literalMixedLogDerivativeIsConnectedCovariance :
  ∀ {Observable Scalar SourceDirection}
    {algebra : TwoSourceMomentAlgebra Observable Scalar}
    {calculus : NormalizedLogSourceCalculus algebra} →
  (meaning : LiteralTwoSourceInsertionMeaning calculus SourceDirection) →
  ∀ left right →
  literalMixedSecondLogDerivative meaning
    (sourceDirectionOf meaning left) (sourceDirectionOf meaning right)
  ≡ connectedCovariance algebra left right
literalMixedLogDerivativeIsConnectedCovariance {calculus = calculus}
  meaning left right =
  trans
    (logSecondDirectionAgrees meaning left right)
    (mixedSecondLogDerivativeIsConnectedCovariance calculus left right)

twoSourceConnectedCumulantCompilerLevel : ProofLevel
twoSourceConnectedCumulantCompilerLevel = machineChecked

-- Standard one/two-variable differentiation and the normalized log quotient
-- rule.  This is generic calculus, not a Yang--Mills research estimate.
normalizedLogSourceCalculusLevel : ProofLevel
normalizedLogSourceCalculusLevel = standardImported

-- Physical seam: the literal CMP116/CMP119 J directions must be identified with
-- the selected gauge-invariant observable insertions on the SAME density.
literalYMSourceInsertionMeaningLevel : ProofLevel
literalYMSourceInsertionMeaningLevel = conditional
