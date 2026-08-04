module DASHI.Physics.YangMills.BalabanSU2AdjointParityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- PURPOSE
-- Prove the parity which is independent of trigonometric estimates:
-- ad_{-X} is odd and ad_{-X}^2 is even.  The scalar coefficient c(|X|) in
-- dexp^{-1} remains a separate evenness input.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.PhysicalInvolutionParityExact as Parity
open import DASHI.Physics.YangMills.CompactLieProofLevel

record LieNegationKernel (Lie : Set) : Set₁ where
  field
    negate : Lie → Lie
    bracket : Lie → Lie → Lie

    negateInvolutive : ∀ value → negate (negate value) ≡ value

    bracketNegateLeft : ∀ left right →
      bracket (negate left) right ≡ negate (bracket left right)

    bracketNegateRight : ∀ left right →
      bracket left (negate right) ≡ negate (bracket left right)

open LieNegationKernel public

lieNegationInvolution :
  ∀ {Lie} → LieNegationKernel Lie → Parity.Involution Lie
lieNegationInvolution kernel = record
  { Parity.Involution.reverse = negate kernel
  ; Parity.Involution.reverseInvolutive = negateInvolutive kernel
  }

adAction :
  ∀ {Lie} → LieNegationKernel Lie → Lie → Lie → Lie
adAction kernel x vector = bracket kernel x vector

adSquaredAction :
  ∀ {Lie} → LieNegationKernel Lie → Lie → Lie → Lie
adSquaredAction kernel x vector =
  bracket kernel x (bracket kernel x vector)

adNegateOdd :
  ∀ {Lie}
    (kernel : LieNegationKernel Lie)
    x vector →
  adAction kernel (negate kernel x) vector
  ≡ negate kernel (adAction kernel x vector)
adNegateOdd kernel x vector =
  bracketNegateLeft kernel x vector

adSquaredNegateEven :
  ∀ {Lie}
    (kernel : LieNegationKernel Lie)
    x vector →
  adSquaredAction kernel (negate kernel x) vector
  ≡ adSquaredAction kernel x vector
adSquaredNegateEven kernel x vector =
  trans
    (cong
      (bracket kernel (negate kernel x))
      (bracketNegateLeft kernel x vector))
    (trans
      (bracketNegateLeft kernel x
        (negate kernel (bracket kernel x vector)))
      (trans
        (cong (negate kernel)
          (bracketNegateRight kernel x (bracket kernel x vector)))
        (negateInvolutive kernel
          (bracket kernel x (bracket kernel x vector)))))

record SU2DexpCoefficientParity (Lie Scalar : Set)
    (lie : LieNegationKernel Lie) : Set₁ where
  field
    theta : Lie → Scalar
    coefficient : Lie → Scalar
    ScalarEquivalent : Scalar → Scalar → Set

    thetaEven : ∀ x →
      ScalarEquivalent (theta (negate lie x)) (theta x)

    coefficientEven : ∀ x →
      ScalarEquivalent (coefficient (negate lie x)) (coefficient x)

open SU2DexpCoefficientParity public

record SU2DexpParityCertificate (Lie Scalar Operator : Set) : Set₁ where
  field
    lie : LieNegationKernel Lie
    coefficientParity : SU2DexpCoefficientParity Lie Scalar lie

    operatorCodomain : Parity.ParityCodomain Operator
    linearPart quadraticPart : Lie → Operator

    linearPartOdd :
      Parity.OddUnder
        (lieNegationInvolution lie)
        operatorCodomain
        linearPart

    quadraticPartEven :
      Parity.EvenUnder
        (lieNegationInvolution lie)
        operatorCodomain
        quadraticPart

open SU2DexpParityCertificate public

su2LinearPairCancels :
  ∀ {Lie Scalar Operator}
    (certificate : SU2DexpParityCertificate Lie Scalar Operator) →
  ∀ x →
  Parity.Equivalent (operatorCodomain certificate)
    (Parity.add (operatorCodomain certificate)
      (linearPart certificate x)
      (linearPart certificate
        (negate (lie certificate) x)))
    (Parity.zero (operatorCodomain certificate))
su2LinearPairCancels certificate =
  Parity.oddPairCancels (linearPartOdd certificate)

su2AdjointOddLevel : ProofLevel
su2AdjointOddLevel = machineChecked

su2AdjointSquaredEvenLevel : ProofLevel
su2AdjointSquaredEvenLevel = machineChecked

su2DexpScalarCoefficientParityLevel : ProofLevel
su2DexpScalarCoefficientParityLevel = conditional

su2DexpOperatorParityAssemblyLevel : ProofLevel
su2DexpOperatorParityAssemblyLevel = machineChecked
