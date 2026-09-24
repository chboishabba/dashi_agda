module DASHI.Physics.Closure.NSTriadKNEuclideanProjectedGramQuadraticMajorantExact where

------------------------------------------------------------------------
-- A / PROJECTED WHOLE-SPACE GRAM REMAINS QUADRATIC IN OUTPUT FREQUENCY
--
-- Define the physical punctured-frequency convection cell by applying the
-- literal Bishop-real Leray projector to the divergence-form raw cell.
--
-- Leray is contractive:
--
--   |P_xi N|^2 <= |N|^2.
--
-- Therefore the raw quadratic cell estimate survives projection, and
-- Hermitian Young gives the projected R290-style Gram bound
--
--   Gram_P(xi)
--      <= |xi|^2
--         ( |u_a(eta)|^2 |u_a(zeta)|^2
--         + |u_b(eta)|^2 |u_b(zeta)|^2 ).
--
-- This is exactly the physical low-frequency input needed by the saturation
-- branch.  No second-order resolvent curvature is used near xi=0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopCauchyGramExact as Cauchy
import DASHI.Physics.Closure.NSTriadKNEuclideanRawGramQuadraticMajorantExact as Raw
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayProjectionExact as Leray
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanRawGramOutputQuadraticExact as Gram

projectedConvectionCell :
  Leray.PuncturedFrequency →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
projectedConvectionCell point uEta uZeta =
  Leray.lerayProject point
    (Output.divergenceFormRawCell
      (Leray.frequency point)
      uEta uZeta)

projectedCellQuadraticBound :
  (point : Leray.PuncturedFrequency) →
  (uEta uZeta : Physical.BishopComplex3) →
  BishopReal._≤_
    (Cauchy.complex3NormSquared
      (projectedConvectionCell point uEta uZeta))
    (BishopReal._*_
      (Heat.frequencyNormSquared (Leray.frequency point))
      (Raw.statePairMass uEta uZeta))
projectedCellQuadraticBound point uEta uZeta =
  BishopP.≤-trans
    (Leray.lerayNormSquaredContraction point
      (Output.divergenceFormRawCell
        (Leray.frequency point)
        uEta uZeta))
    (Raw.rawCellQuadraticBound
      (Leray.frequency point)
      uEta uZeta)

projectedGram :
  Leray.PuncturedFrequency →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  BishopReal.ℝ
projectedGram point aEta aZeta bEta bZeta =
  BishopReal._*_
    Gram.two
    (Gram.realHermitianCross
      (projectedConvectionCell point aEta aZeta)
      (projectedConvectionCell point bEta bZeta))

projectedGramQuadraticMajorant :
  (point : Leray.PuncturedFrequency) →
  (aEta aZeta bEta bZeta : Physical.BishopComplex3) →
  BishopReal._≤_
    (projectedGram point aEta aZeta bEta bZeta)
    (BishopReal._*_
      (Heat.frequencyNormSquared (Leray.frequency point))
      (Raw.rawGramStateMajorant
        aEta aZeta bEta bZeta))
projectedGramQuadraticMajorant
    point aEta aZeta bEta bZeta =
  let
    A = projectedConvectionCell point aEta aZeta
    B = projectedConvectionCell point bEta bZeta

    young :
      BishopReal._≤_
        (projectedGram point aEta aZeta bEta bZeta)
        (BishopReal._+_
          (Cauchy.complex3NormSquared A)
          (Cauchy.complex3NormSquared B))
    young = Cauchy.realHermitianYoung A B

    aBound =
      projectedCellQuadraticBound point aEta aZeta
    bBound =
      projectedCellQuadraticBound point bEta bZeta

    summed =
      BishopP.+-mono-≤ aBound bBound

    q = Heat.frequencyNormSquared (Leray.frequency point)
    ma = Raw.statePairMass aEta aZeta
    mb = Raw.statePairMass bEta bZeta

    open BishopP.ℝ-Solver
    regroup :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_ q ma)
          (BishopReal._*_ q mb))
        (BishopReal._*_
          q
          (Raw.rawGramStateMajorant
            aEta aZeta bEta bZeta))
    regroup =
      solve 3
        (λ q' a b →
          (q' ⊗ a) ⊕ (q' ⊗ b)
          ⊜ q' ⊗ (a ⊕ b))
        BishopP.≃-refl
        q ma mb
  in
  BishopP.≤-trans young
    (BishopP.≤-respʳ-≃ regroup summed)

projectedGramMajorantNonnegative :
  (aEta aZeta bEta bZeta : Physical.BishopComplex3) →
  BishopReal.NonNegative
    (Raw.rawGramStateMajorant
      aEta aZeta bEta bZeta)
projectedGramMajorantNonnegative =
  Raw.rawGramStateMajorantNonnegative

projectedConvectionCellLiteral : Bool
projectedConvectionCellLiteral = true

projectedGramQuadraticMajorantClosed : Bool
projectedGramQuadraticMajorantClosed = true

projectedGramUsesPeriodicGap : Bool
projectedGramUsesPeriodicGap = false

projectedGramUsesSecondOrderCurvatureAtOrigin : Bool
projectedGramUsesSecondOrderCurvatureAtOrigin = false

clayPromotion : Bool
clayPromotion = false

projectedGramQuadraticMajorantClosedIsTrue :
  projectedGramQuadraticMajorantClosed ≡ true
projectedGramQuadraticMajorantClosedIsTrue = refl

projectedGramUsesPeriodicGapIsFalse :
  projectedGramUsesPeriodicGap ≡ false
projectedGramUsesPeriodicGapIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
