module DASHI.Physics.Closure.NSTriadKNLuoSpectralProjectorGapDependenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / AUDIT CONTEXT
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators".
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- DASHI CONTRIBUTION
--
-- The exact two-by-two crossing family
--
--   S_+(r) = diag(r,-r),   S_-(r) = diag(-r,r)
--
-- has positive projectors
--
--   P_+ = diag(1,0),       P_- = diag(0,1).
--
-- Their squared projector jump is the constant 2, while the squared matrix
-- difference is 8 r^2 and the spectral gap is 2 r.  Division-free:
--
--   |P_+-P_-|_F^2 * gap(r)^2 = |S_+(r)-S_-(r)|_F^2.
--
-- Thus projector control necessarily carries inverse-gap behaviour.  At the
-- zero crossing the matrices coincide while the one-sided projectors remain
-- distinct.  Measurability of the projector cannot supply the derivative
-- estimate used in the audited manuscript.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; -_; _-_; _<_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record SymmetricMatrix2 : Set where
  constructor symmetricMatrix2
  field
    m11 m12 m22 : ℚ

open SymmetricMatrix2 public

positiveSideMatrix : ℚ → SymmetricMatrix2
positiveSideMatrix radius = symmetricMatrix2 radius 0ℚ (- radius)

negativeSideMatrix : ℚ → SymmetricMatrix2
negativeSideMatrix radius = symmetricMatrix2 (- radius) 0ℚ radius

positiveSideProjector : SymmetricMatrix2
positiveSideProjector = symmetricMatrix2 1 0ℚ 0ℚ

negativeSideProjector : SymmetricMatrix2
negativeSideProjector = symmetricMatrix2 0ℚ 0ℚ 1

zeroProjector : SymmetricMatrix2
zeroProjector = symmetricMatrix2 0ℚ 0ℚ 0ℚ

frobeniusDifferenceSquared :
  SymmetricMatrix2 → SymmetricMatrix2 → ℚ
frobeniusDifferenceSquared left right =
  L2.square (m11 left - m11 right)
  + 2 * L2.square (m12 left - m12 right)
  + L2.square (m22 left - m22 right)

matrixDifferenceSquared : ℚ → ℚ
matrixDifferenceSquared radius =
  frobeniusDifferenceSquared
    (positiveSideMatrix radius)
    (negativeSideMatrix radius)

projectorJumpSquared : ℚ
projectorJumpSquared =
  frobeniusDifferenceSquared
    positiveSideProjector
    negativeSideProjector

positiveToZeroProjectorDistanceSquared : ℚ
positiveToZeroProjectorDistanceSquared =
  frobeniusDifferenceSquared positiveSideProjector zeroProjector

spectralGap : ℚ → ℚ
spectralGap radius = 2 * radius

matrixDifferenceClosedForm :
  ∀ radius →
  matrixDifferenceSquared radius ≡ 8 * L2.square radius
matrixDifferenceClosedForm radius = solve (radius ∷ [])

projectorJumpIsTwo : projectorJumpSquared ≡ 2
projectorJumpIsTwo = solve []

positiveToZeroProjectorDistanceIsOne :
  positiveToZeroProjectorDistanceSquared ≡ 1
positiveToZeroProjectorDistanceIsOne = solve []

inverseGapIdentity :
  ∀ radius →
  projectorJumpSquared * L2.square (spectralGap radius)
  ≡ matrixDifferenceSquared radius
inverseGapIdentity radius = solve (radius ∷ [])

crossingMatricesCoincide :
  positiveSideMatrix 0ℚ ≡ negativeSideMatrix 0ℚ
crossingMatricesCoincide = refl
  where
  open import Agda.Builtin.Equality using (refl)

projectorSidesDistinct :
  positiveSideProjector ≢ negativeSideProjector
projectorSidesDistinct ()

projectorJumpPositive : 0ℚ < projectorJumpSquared
projectorJumpPositive =
  subst
    (λ right → 0ℚ < right)
    (sym projectorJumpIsTwo)
    (ℚₚ.positive⁻¹ 2)

zeroMatrixDifference : matrixDifferenceSquared 0ℚ ≡ 0ℚ
zeroMatrixDifference = solve []

oneSidedProjectorDoesNotConvergeToZeroProjectorAlgebraically :
  positiveToZeroProjectorDistanceSquared ≢ 0ℚ
oneSidedProjectorDoesNotConvergeToZeroProjectorAlgebraically equality =
  let
    oneEqualsZero : (1 : ℚ) ≡ 0ℚ
    oneEqualsZero =
      subst
        (λ value → value ≡ 0ℚ)
        positiveToZeroProjectorDistanceIsOne
        equality
  in
  ℚₚ.1≢0 oneEqualsZero

record SpectralProjectorAuditConclusion : Set where
  constructor spectralProjectorAuditConclusion
  field
    projectorDerivativeUniformWithoutGap : Set
    crossingFamilyChecked : Set
    inverseGapDependenceChecked : Set
    measurabilitySuppliesDerivativeControl : Set

canonicalSpectralProjectorAuditConclusion :
  SpectralProjectorAuditConclusion
canonicalSpectralProjectorAuditConclusion =
  spectralProjectorAuditConclusion ⊥ ⊤ ⊤ ⊥
  where
  open import Data.Empty using (⊥)
  open import Data.Unit using (⊤)
