module DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact finite SU(2) dexp^{-1} architecture.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
-- Relationship: differentiating log(exp X) = X on the principal chart gives
-- D log = (D exp)^{-1}.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
-- Relationship: SU(2), its principal exponential chart, and the adjoint
-- representation.
--
-- For su(2), Cayley--Hamilton for ad_X reduces every analytic function of ad_X
-- to the span {I, ad_X, ad_X^2}.  In the standard left-trivialized convention,
--
--   dexp_X^{-1}
--     = I - (1/2) ad_X + c(theta) ad_X^2,
--
--   c(theta)
--     = 1/theta^2 - (1 + cos theta)/(2 theta sin theta)
--
-- away from theta = 0, with removable value 1/12 at zero.  The module fixes
-- that polynomial shape, proves its zero value, and derives equality with the
-- derivative of log from inverse uniqueness.  The real trigonometric scalar
-- identities and the selected norm convention remain explicit chart inputs.
------------------------------------------------------------------------

Endomorphism : Set → Set
Endomorphism Vector = Vector → Vector

compose : ∀ {Vector : Set} →
  Endomorphism Vector → Endomorphism Vector → Endomorphism Vector
compose outer inner vector = outer (inner vector)

identityEndomorphism : ∀ {Vector : Set} → Endomorphism Vector
identityEndomorphism vector = vector

PointwiseEqual : ∀ {Vector : Set} →
  Endomorphism Vector → Endomorphism Vector → Set
PointwiseEqual left right = ∀ vector → left vector ≡ right vector

inverseUniquePointwise :
  ∀ {Vector : Set}
    (forward leftInverse rightInverse : Endomorphism Vector) →
  (∀ vector → forward (rightInverse vector) ≡ vector) →
  (∀ vector → leftInverse (forward vector) ≡ vector) →
  PointwiseEqual leftInverse rightInverse
inverseUniquePointwise forward leftInverse rightInverse
    forwardAfterRight leftAfterForward vector =
  trans
    (cong leftInverse (sym (forwardAfterRight vector)))
    (leftAfterForward (rightInverse vector))

record SU2AdjointPolynomialAlgebra
    (Lie Scalar : Set) : Set₁ where
  field
    zeroLie : Lie
    addLie : Lie → Lie → Lie
    negateLie : Lie → Lie
    scaleLie : Scalar → Lie → Lie
    bracket : Lie → Lie → Lie

    half : Scalar
    dexpInverseQuadraticCoefficient : Lie → Scalar

    bracketZeroLeft : ∀ vector → bracket zeroLie vector ≡ zeroLie
    scaleZeroVector : ∀ scalar → scaleLie scalar zeroLie ≡ zeroLie
    negateZero : negateLie zeroLie ≡ zeroLie
    addZeroLeft : ∀ vector → addLie zeroLie vector ≡ vector
    addZeroRight : ∀ vector → addLie vector zeroLie ≡ vector

open SU2AdjointPolynomialAlgebra public

ad :
  ∀ {Lie Scalar} →
  SU2AdjointPolynomialAlgebra Lie Scalar →
  Lie → Endomorphism Lie
ad algebra x vector = bracket algebra x vector

adSquared :
  ∀ {Lie Scalar} →
  SU2AdjointPolynomialAlgebra Lie Scalar →
  Lie → Endomorphism Lie
adSquared algebra x vector =
  bracket algebra x (bracket algebra x vector)

su2DexpInverseClosed :
  ∀ {Lie Scalar} →
  SU2AdjointPolynomialAlgebra Lie Scalar →
  Lie → Endomorphism Lie
su2DexpInverseClosed algebra x vector =
  addLie algebra vector
    (addLie algebra
      (negateLie algebra
        (scaleLie algebra (half algebra)
          (ad algebra x vector)))
      (scaleLie algebra
        (dexpInverseQuadraticCoefficient algebra x)
        (adSquared algebra x vector)))

su2DexpInverseFiniteSpan :
  ∀ {Lie Scalar}
    (algebra : SU2AdjointPolynomialAlgebra Lie Scalar)
    x vector →
  su2DexpInverseClosed algebra x vector
  ≡ addLie algebra vector
      (addLie algebra
        (negateLie algebra
          (scaleLie algebra (half algebra)
            (bracket algebra x vector)))
        (scaleLie algebra
          (dexpInverseQuadraticCoefficient algebra x)
          (bracket algebra x (bracket algebra x vector))))
su2DexpInverseFiniteSpan algebra x vector = refl

su2DexpInverseAtZero :
  ∀ {Lie Scalar}
    (algebra : SU2AdjointPolynomialAlgebra Lie Scalar)
    vector →
  su2DexpInverseClosed algebra (zeroLie algebra) vector ≡ vector
su2DexpInverseAtZero algebra vector
  rewrite bracketZeroLeft algebra vector
        | scaleZeroVector algebra (half algebra)
        | negateZero algebra
        | bracketZeroLeft algebra (zeroLie algebra)
        | scaleZeroVector algebra
            (dexpInverseQuadraticCoefficient algebra (zeroLie algebra))
        | addZeroLeft algebra (zeroLie algebra)
        | addZeroRight algebra vector =
  refl

record SU2RodriguesCoefficientMeaning
    (Lie Scalar : Set)
    (algebra : SU2AdjointPolynomialAlgebra Lie Scalar) : Set₁ where
  field
    theta : Lie → Scalar
    one two oneTwelfth : Scalar
    add multiply subtract divide : Scalar → Scalar → Scalar
    sine cosine : Scalar → Scalar

    Nonzero : Scalar → Set
    IsZeroLie : Lie → Set

    coefficientAwayFromZero : ∀ x →
      Nonzero (theta x) →
      dexpInverseQuadraticCoefficient algebra x
      ≡ subtract
          (divide one (multiply (theta x) (theta x)))
          (divide
            (add one (cosine (theta x)))
            (multiply two
              (multiply (theta x) (sine (theta x)))))

    coefficientAtZero : ∀ x →
      IsZeroLie x →
      dexpInverseQuadraticCoefficient algebra x ≡ oneTwelfth

open SU2RodriguesCoefficientMeaning public

record SU2ExpLogDifferentialData
    (Lie : Set) : Set₁ where
  field
    dexp : Lie → Endomorphism Lie
    derivativeLogAtExp : Lie → Endomorphism Lie
    closedDexpInverse : Lie → Endomorphism Lie

    dexpAfterDerivativeLog : ∀ x vector →
      dexp x (derivativeLogAtExp x vector) ≡ vector

    derivativeLogAfterDexp : ∀ x vector →
      derivativeLogAtExp x (dexp x vector) ≡ vector

    dexpAfterClosedInverse : ∀ x vector →
      dexp x (closedDexpInverse x vector) ≡ vector

    closedInverseAfterDexp : ∀ x vector →
      closedDexpInverse x (dexp x vector) ≡ vector

open SU2ExpLogDifferentialData public

derivativeLogEqualsClosedDexpInverse :
  ∀ {Lie}
    (dataSet : SU2ExpLogDifferentialData Lie)
    x →
  PointwiseEqual
    (derivativeLogAtExp dataSet x)
    (closedDexpInverse dataSet x)
derivativeLogEqualsClosedDexpInverse dataSet x =
  inverseUniquePointwise
    (dexp dataSet x)
    (derivativeLogAtExp dataSet x)
    (closedDexpInverse dataSet x)
    (dexpAfterClosedInverse dataSet x)
    (derivativeLogAfterDexp dataSet x)

record SU2ClosedFormDifferentialInstantiation
    (Lie Scalar : Set) : Set₁ where
  field
    algebra : SU2AdjointPolynomialAlgebra Lie Scalar
    differential : SU2ExpLogDifferentialData Lie

    closedInverseIsSU2Polynomial : ∀ x →
      PointwiseEqual
        (closedDexpInverse differential x)
        (su2DexpInverseClosed algebra x)

open SU2ClosedFormDifferentialInstantiation public

derivativeLogAtExpSU2ClosedForm :
  ∀ {Lie Scalar}
    (meaning : SU2ClosedFormDifferentialInstantiation Lie Scalar)
    x vector →
  derivativeLogAtExp (differential meaning) x vector
  ≡ su2DexpInverseClosed (algebra meaning) x vector
derivativeLogAtExpSU2ClosedForm meaning x vector =
  trans
    (derivativeLogEqualsClosedDexpInverse
      (differential meaning) x vector)
    (closedInverseIsSU2Polynomial meaning x vector)

su2DexpInversePolynomialDefinitionLevel : ProofLevel
su2DexpInversePolynomialDefinitionLevel = computed

su2DexpInverseFiniteSpanLevel : ProofLevel
su2DexpInverseFiniteSpanLevel = machineChecked

su2DexpInverseZeroValueLevel : ProofLevel
su2DexpInverseZeroValueLevel = machineChecked

inverseDifferentialUniquenessLevel : ProofLevel
inverseDifferentialUniquenessLevel = machineChecked

derivativeLogClosedFormAssemblyLevel : ProofLevel
derivativeLogClosedFormAssemblyLevel = machineChecked

su2RodriguesCoefficientProvenanceLevel : ProofLevel
su2RodriguesCoefficientProvenanceLevel = standardImported

physicalSU2NormAndThetaInputsLevel : ProofLevel
physicalSU2NormAndThetaInputsLevel = conditional

physicalSU2TrigonometricCoefficientInputsLevel : ProofLevel
physicalSU2TrigonometricCoefficientInputsLevel = conditional

physicalExpLogDifferentialIdentificationInputsLevel : ProofLevel
physicalExpLogDifferentialIdentificationInputsLevel = conditional
