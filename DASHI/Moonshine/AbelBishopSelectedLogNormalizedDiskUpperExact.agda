module DASHI.Moonshine.AbelBishopSelectedLogNormalizedDiskUpperExact where

------------------------------------------------------------------------
-- SELECTED AFFINE LOG GERM: ACTUAL DISK INEQUALITY NORMALIZATION.
--
-- Existing AbelBishopSelectedLogAffineReconstructionExact has
--   N(p^-1*t) ~= N(p)^-1 * N(t),
-- but its original radius lemma assumes an exact equality
--   N(t) ~= r^2*N(p).
-- Actual Bishop disks only guarantee N(t) <= r^2*N(p).
--
-- This module proves the missing constructive same-carrier inequality:
--   N(t) <= r^2*N(p)
--   => N(p^-1*t) <= r^2
-- for the LITERAL Bishop complex reciprocal and positive N(p).
--
-- Reuses the already written inequality-based complex power envelope
-- for every natural power of the normalized displacement. No sqrt,
-- choice of an exact radius or surrogate logarithm is introduced.
------------------------------------------------------------------------

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Moonshine.AbelBishopSelectedLogAffineReconstructionExact as Affine

originalBishopNormalizedDisplacementUpperBound :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t r →
  BishopReal._≤_
    (Norm.normSqC t)
    (BishopReal._*_
      (Norm.square r)
      (Norm.normSqC p)) →
  BishopReal._≤_
    (Norm.normSqC (Affine.normalizedDisplacement p nz t))
    (Norm.square r)
originalBishopNormalizedDisplacementUpperBound
  p nz t r relativeBound =
  let
    d = Norm.normSqC p
    inv = BishopInverse._⁻¹ d (Reciprocal.normSquareNonzero nz)
    rSq = Norm.square r

    inverseNonnegative : BishopReal.NonNegative inv
    inverseNonnegative =
      BishopP.pos⇒nonNeg
        (BishopP.0<x⇒posx
          (BishopInverse.0<x⇒0<x⁻¹
            (Reciprocal.normSquareNonzero nz)
            (Reciprocal.normSquarePositive nz)))

    inverseScale :
      BishopReal._≤_
        (BishopReal._*_ inv (Norm.normSqC t))
        (BishopReal._*_ inv (BishopReal._*_ rSq d))
    inverseScale =
      BishopP.*-monoˡ-≤-nonNeg
        relativeBound inverseNonnegative

    sourceNormalization :
      BishopReal._≃_
        (BishopReal._*_ inv (BishopReal._*_ rSq d))
        (BishopReal._*_ rSq (BishopReal._*_ d inv))
    sourceNormalization =
      let open BishopP.ℝ-Solver in
      solve 3
        (λ inv′ radiusSquare pNorm →
          inv′ ⊗ (radiusSquare ⊗ pNorm)
          ⊜ radiusSquare ⊗ (pNorm ⊗ inv′))
        BishopP.≃-refl inv rSq d

    rightIsRadius :
      BishopReal._≃_
        (BishopReal._*_ inv (BishopReal._*_ rSq d))
        rSq
    rightIsRadius =
      BishopP.≃-trans
        sourceNormalization
        (BishopP.≃-trans
          (BishopP.*-congˡ
            (BishopInverse.*-inverseʳ
              d (Reciprocal.normSquareNonzero nz)))
          (BishopP.*-identityʳ rSq))
  in
  BishopP.≤-respˡ-≃
    (Affine.originalBishopNormalizedDisplacementNormSquare p nz t)
    (BishopP.≤-respʳ-≃
      rightIsRadius
      inverseScale)

originalBishopNormalizedDisplacementUpperPowerEnvelope :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t r →
  BishopReal.NonNegative r →
  BishopReal._≤_
    (Norm.normSqC t)
    (BishopReal._*_
      (Norm.square r)
      (Norm.normSqC p)) →
  Norm.BishopQPowerComponentEnvelope
    (Affine.normalizedDisplacement p nz t) r
originalBishopNormalizedDisplacementUpperPowerEnvelope
  p nz t r radiusNN relativeBound =
  Upper.upperBoundBuildsOriginalPowerEnvelope
    (record
      { Upper.radiusNonnegative = radiusNN
      ; Upper.normSqBelowRadiusSquare =
          originalBishopNormalizedDisplacementUpperBound
            p nz t r relativeBound
      })
