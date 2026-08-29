module DASHI.Physics.Closure.NSTriadKNMixedHelicitySobolevEndpointRound248Exact where

------------------------------------------------------------------------
-- ROUND248 / STANDARD SOBOLEV ENDPOINT -> W1 POINTWISE MIXED-HELICITY BOUND
--
-- Round247 closes the repo-specific normalized-curl homogeneous H^1 isometry
-- on the literal finite Galerkin mode list.  The remaining W1 analysis is the
-- standard torus endpoint:
--
--   ||H u x u||_2^2 <= ||H u||_6^2 ||u||_3^2,
--   ||u||_3^2        <= C_(1/2) ||u||_{H^(1/2)}^2,
--   ||H u||_6^2      <= C_1     ||H u||_{H^1}^2,
--   ||H u||_{H^1}^2  =           ||u||_{H^1}^2.
--
-- Therefore
--
--   Q_+-(t) <= C_1 C_(1/2) A(t) D(t).
--
-- This file proves only the ordered scalar compiler once the standard
-- analytic Hölder/Sobolev receipts are supplied.  It does not manufacture the
-- continuum embeddings and does not reopen the helical geometry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96

record SobolevMixedHelicityEndpoint : Set where
  constructor sobolev-mixed-helicity-endpoint
  field
    mixedMass huL6Squared uL3Squared : ℚ
    criticalSize dissipationDensity : ℚ
    halfEmbeddingConstant oneEmbeddingConstant : ℚ

    mixedMassNN : 0ℚ ≤ mixedMass
    huL6SquaredNN : 0ℚ ≤ huL6Squared
    uL3SquaredNN : 0ℚ ≤ uL3Squared
    criticalSizeNN : 0ℚ ≤ criticalSize
    dissipationDensityNN : 0ℚ ≤ dissipationDensity
    halfEmbeddingConstantNN : 0ℚ ≤ halfEmbeddingConstant
    oneEmbeddingConstantNN : 0ℚ ≤ oneEmbeddingConstant

    holderSquared : mixedMass ≤ huL6Squared * uL3Squared

    halfSobolevSquared :
      uL3Squared ≤ halfEmbeddingConstant * criticalSize

    oneSobolevAfterNormalizedCurlIsometry :
      huL6Squared ≤ oneEmbeddingConstant * dissipationDensity

open SobolevMixedHelicityEndpoint public

sobolevMixedHelicityPointwiseBound :
  (R : SobolevMixedHelicityEndpoint) →
  mixedMass R
  ≤ (oneEmbeddingConstant R * halfEmbeddingConstant R)
      * criticalSize R * dissipationDensity R
sobolevMixedHelicityPointwiseBound R =
  let
    halfCriticalNN :
      0ℚ ≤ halfEmbeddingConstant R * criticalSize R
    halfCriticalNN =
      R96.productNonnegative
        (halfEmbeddingConstantNN R)
        (criticalSizeNN R)

    oneDissNN :
      0ℚ ≤ oneEmbeddingConstant R * dissipationDensity R
    oneDissNN =
      R96.productNonnegative
        (oneEmbeddingConstantNN R)
        (dissipationDensityNN R)

    productStep :
      huL6Squared R * uL3Squared R
      ≤ (oneEmbeddingConstant R * dissipationDensity R)
          * (halfEmbeddingConstant R * criticalSize R)
    productStep =
      Rational.nonnegativeProductMonotone
        (huL6SquaredNN R)
        (uL3SquaredNN R)
        oneDissNN
        halfCriticalNN
        (oneSobolevAfterNormalizedCurlIsometry R)
        (halfSobolevSquared R)

    endpoint :
      (oneEmbeddingConstant R * dissipationDensity R)
        * (halfEmbeddingConstant R * criticalSize R)
      ≡ (oneEmbeddingConstant R * halfEmbeddingConstant R)
          * criticalSize R * dissipationDensity R
    endpoint =
      solve
        ( oneEmbeddingConstant R
        ∷ halfEmbeddingConstant R
        ∷ criticalSize R
        ∷ dissipationDensity R
        ∷ [])
  in
  ℚP.≤-trans
    (holderSquared R)
    (subst
      (λ upper → huL6Squared R * uL3Squared R ≤ upper)
      endpoint
      productStep)

round248Round247NormalizedCurlHOneIsometryConsumed : Bool
round248Round247NormalizedCurlHOneIsometryConsumed = true

round248OrderedSobolevEndpointCompilerClosed : Bool
round248OrderedSobolevEndpointCompilerClosed = true

round248PhysicalHolderInstalled : Bool
round248PhysicalHolderInstalled = false

round248TorusHalfSobolevEmbeddingInstalled : Bool
round248TorusHalfSobolevEmbeddingInstalled = false

round248TorusOneSobolevEmbeddingInstalled : Bool
round248TorusOneSobolevEmbeddingInstalled = false

round248W1PointwisePhysicallyInstalled : Bool
round248W1PointwisePhysicallyInstalled = false

round248PackageAClosed : Bool
round248PackageAClosed = false

round248ClayPromotion : Bool
round248ClayPromotion = false

round248OrderedSobolevEndpointCompilerClosedIsTrue :
  round248OrderedSobolevEndpointCompilerClosed ≡ true
round248OrderedSobolevEndpointCompilerClosedIsTrue = refl

round248W1PointwisePhysicallyInstalledIsFalse :
  round248W1PointwisePhysicallyInstalled ≡ false
round248W1PointwisePhysicallyInstalledIsFalse = refl

round248PackageAClosedIsFalse : round248PackageAClosed ≡ false
round248PackageAClosedIsFalse = refl

round248ClayPromotionIsFalse : round248ClayPromotion ≡ false
round248ClayPromotionIsFalse = refl
