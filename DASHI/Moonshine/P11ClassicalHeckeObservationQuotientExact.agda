module DASHI.Moonshine.P11ClassicalHeckeObservationQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- David Blackwell,
-- "Equivalent Comparisons of Experiments",
-- Annals of Mathematical Statistics 24(2):265--272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977.
-- DOI: 10.1145/512950.512973.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the observation-relative compression principle on the first
-- source-faithful classical arithmetic correspondence.
--
-- Collapse both p=11 j-labels to one coarse class.  This quotient is perfectly
-- stable under the degree-three ell=2 correspondence, so the constant coarse
-- observable has an exact induced Hecke operator.  Nevertheless the quotient
-- is non-injective and the nonconstant (-3,2) spectral mode cannot factor
-- through it.
--
-- Therefore operator-safe for a declared coarse observation is strictly weaker
-- than lossless for the full arithmetic state/spectrum.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ; +_; -[1+_])

import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as ExistingQuotient
import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical
import DASHI.Moonshine.ClassicalHeckeQuotientDescentExact as ClassicalDescent
import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11

coarseProjection : P11.J11Class → ⊤
coarseProjection state = tt

coarseEquivalence : Quotient.EquivalenceOn P11.J11Class
coarseEquivalence =
  record
    { _≈_ = λ left right → ⊤
    ; refl = λ state → tt
    ; sym = λ proof → tt
    ; trans = λ first second → tt
    }

coarseQuotient : Quotient.QuotientInterfaceOn P11.J11Class ⊤
coarseQuotient =
  record
    { equiv = coarseEquivalence
    ; proj = coarseProjection
    ; respect-proj = λ proof → refl
    ; representative = λ coarse → P11.j0
    ; section = λ coarse → refl
    }

coarseExactPresentation :
  ExistingQuotient.ExactQuotientPresentation coarseQuotient
coarseExactPresentation =
  record
    { projectionComplete = λ equality → tt
    }

coarseNeighbourCongruence :
  ∀ {left right : P11.J11Class} →
  ⊤ →
  (edge : Fin 3) →
  coarseProjection (P11.twoIsogenyNeighbour left edge)
  ≡ coarseProjection (P11.twoIsogenyNeighbour right edge)
coarseNeighbourCongruence proof edge = refl

coarseClassicalDescent :
  ClassicalDescent.QuotientStableClassicalCorrespondence
    coarseQuotient P11.p11TwoIsogenyCorrespondence
coarseClassicalDescent =
  record
    { exactPresentation = coarseExactPresentation
    ; neighbourRespectsEquiv = coarseNeighbourCongruence
    }

coarseOne : ⊤ → Nat
coarseOne coarse = 1

coarseOperatorCommutes :
  (state : P11.J11Class) →
  Classical.classicalOperator P11.p11TwoIsogenyCorrespondence
    (λ fine → coarseOne (coarseProjection fine)) state
  ≡
  Classical.classicalOperator
    (ClassicalDescent.inducedClassicalCorrespondence coarseClassicalDescent)
    coarseOne tt
coarseOperatorCommutes =
  ClassicalDescent.projectedClassicalOperatorCommutes
    coarseClassicalDescent coarseOne

inducedCoarseDegreeIsThree :
  Classical.classicalOperator
    (ClassicalDescent.inducedClassicalCorrespondence coarseClassicalDescent)
    coarseOne tt
  ≡ 3
inducedCoarseDegreeIsThree = refl

j0NotJ1 : P11.j0 ≡ P11.j1 → ⊥
j0NotJ1 ()

coarseProjectionCollision : coarseProjection P11.j0 ≡ coarseProjection P11.j1
coarseProjectionCollision = refl

noExactDecoder :
  (decoder : ⊤ → P11.J11Class) →
  ((state : P11.J11Class) → decoder (coarseProjection state) ≡ state) →
  ⊥
noExactDecoder decoder exact =
  j0NotJ1
    (trans
      (sym (exact P11.j0))
      (exact P11.j1))

nonconstantModeValue : P11.J11Class → ℤ
nonconstantModeValue P11.j0 = -[1+ 2 ]
nonconstantModeValue P11.j1 = + 2

minusThreeNotTwo : (-[1+ 2 ] : ℤ) ≡ + 2 → ⊥
minusThreeNotTwo ()

nonconstantModeDoesNotFactorThroughCoarse :
  (coarseMode : ⊤ → ℤ) →
  ((state : P11.J11Class) →
    coarseMode (coarseProjection state) ≡ nonconstantModeValue state) →
  ⊥
nonconstantModeDoesNotFactorThroughCoarse coarseMode factors =
  minusThreeNotTwo
    (trans
      (sym (factors P11.j0))
      (factors P11.j1))

record P11ObservationQuotientBoundary : Set where
  field
    coarseQuotientHeckeStable : Bool
    coarseQuotientHeckeStableIsTrue : coarseQuotientHeckeStable ≡ true

    coarseQuotientLossless : Bool
    coarseQuotientLosslessIsFalse : coarseQuotientLossless ≡ false

    nonconstantSpectralModeRetained : Bool
    nonconstantSpectralModeRetainedIsFalse :
      nonconstantSpectralModeRetained ≡ false

canonicalP11ObservationQuotientBoundary : P11ObservationQuotientBoundary
canonicalP11ObservationQuotientBoundary =
  record
    { coarseQuotientHeckeStable = true
    ; coarseQuotientHeckeStableIsTrue = refl
    ; coarseQuotientLossless = false
    ; coarseQuotientLosslessIsFalse = refl
    ; nonconstantSpectralModeRetained = false
    ; nonconstantSpectralModeRetainedIsFalse = refl
    }
