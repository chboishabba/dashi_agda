module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowProjectedProductChainExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Implement the complete inequality composition behind HH1.  The continuum
-- producer supplies the three standard steps
--
--   ||Delta_q P div F||_(H^-1) <= ||Delta_q F||_2,
--   ||Delta_q F||_2 <= lambda_q^(3/2) ||F||_1,
--   ||f tensor g||_1 <= ||f||_2 ||g||_2.
--
-- Once these are visible fields and the output scale factor is nonnegative,
-- this module proves
--
--   ||Delta_q P div(f tensor g)||_(H^-1)
--     <= lambda_q^(3/2) ||f||_2 ||g||_2.
--
-- The theorem is not a placeholder for the continuum estimates: it closes
-- their exact order-theoretic composition and keeps each analytic input
-- independently auditable.
------------------------------------------------------------------------

open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

record ProjectedProductChainData : Set where
  constructor projected-product-chain-data
  field
    projectedHMinusOne projectedProductL2 tensorProductL1 : ℚ
    leftL2 rightL2 outputThreeHalfScale : ℚ

    outputScaleNonnegative : 0ℚ ≤ outputThreeHalfScale

    derivativeProjectionBound :
      projectedHMinusOne ≤ projectedProductL2

    outputBernsteinBound :
      projectedProductL2
      ≤ outputThreeHalfScale * tensorProductL1

    tensorHolderBound :
      tensorProductL1 ≤ leftL2 * rightL2

open ProjectedProductChainData public

projectedHighHighLowProductBound :
  (dataSet : ProjectedProductChainData) →
  projectedHMinusOne dataSet
  ≤ outputThreeHalfScale dataSet
      * (leftL2 dataSet * rightL2 dataSet)
projectedHighHighLowProductBound dataSet =
  let
    scaledHolder :
      outputThreeHalfScale dataSet * tensorProductL1 dataSet
      ≤ outputThreeHalfScale dataSet
          * (leftL2 dataSet * rightL2 dataSet)
    scaledHolder =
      let
        instance
          outputScaleIsNonnegative =
            nonNegative (outputScaleNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (outputThreeHalfScale dataSet)
        (tensorHolderBound dataSet)
  in
  ℚₚ.≤-trans
    (derivativeProjectionBound dataSet)
    (ℚₚ.≤-trans
      (outputBernsteinBound dataSet)
      scaledHolder)
