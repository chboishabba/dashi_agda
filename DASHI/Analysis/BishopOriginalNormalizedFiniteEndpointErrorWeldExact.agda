module DASHI.Analysis.BishopOriginalNormalizedFiniteEndpointErrorWeldExact where

------------------------------------------------------------------------
-- K04d P0.06: EXACT ORIGINAL ENDPOINT ERROR / NORMALIZED WELD.
--
-- For the LITERAL original finite negative-log exponential
-- F_N(x) and w(x)=1-x, let G_N=F_N(x)*inv_B(w(x)).
--
-- At zero, G_N(0)=1 for all N.
-- For any original unit-interval point x:
--    w(x)*(G_N(x)-1) = F_N(x)-w(x) = E_N(x).
--
-- This identifies the endpoint source of the previous normalized
-- mesh comparison with the ACTUAL finite P0 LOG error. No second
-- exponential, quotient or uniqueness axiom is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as RP
import Inverse as Inv

import DASHI.Analysis.BishopOriginalNormalizedExpIncrementExact as Norm
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExpInitialValueExact as Initial
import DASHI.Analysis.BishopOriginalNegativeLogFiniteErrorDerivativeExact as Error
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as Pos

sourceOriginUnitIntervalRatio : Gap.BishopUnitIntervalRatio R.0ℝ
sourceOriginUnitIntervalRatio = record
  { ratioNonnegative = RP.≤-refl
  ; ratioBelowOne = Pos.onePositive
  }

originalBishopOriginGapIsOne :
  R._≃_ (Cross.oneMinus R.0ℝ) R.1ℝ
originalBishopOriginGapIsOne =
  let open RP.ℝ-Solver in
  solve 0
    (Κ 1ℚᵘ ⊖ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ)
    RP.≃-refl

originalBishopOriginGapInverseIsOne :
  R._≃_
    (Gap.oneMinusInverse sourceOriginUnitIntervalRatio)
    R.1ℝ
originalBishopOriginGapInverseIsOne =
  RP.≃-symm
    (Inv.⁻¹-unique
      R.1ℝ
      (Cross.oneMinus R.0ℝ)
      (Gap.oneMinusNonzero sourceOriginUnitIntervalRatio)
      (let open RP.ℝ-Solver in
       solve 0
         (Κ 1ℚᵘ ⊗ (Κ 1ℚᵘ ⊖ Κ 0ℚᵘ)
           ⊜ Κ 1ℚᵘ)
         RP.≃-refl))

originalFiniteNormalizedExpAtZeroIsOne :
  (stage : Nat) →
  R._≃_
    (Norm.originalNormalizedFiniteExp
      stage R.0ℝ sourceOriginUnitIntervalRatio)
    R.1ℝ
originalFiniteNormalizedExpAtZeroIsOne stage =
  RP.≃-trans
    (RP.*-cong
      (Initial.originalFiniteNegativeLogExpAtZero stage)
      originalBishopOriginGapInverseIsOne)
    (RP.*-identityˡ R.1ℝ)

originalFiniteNormalizedExpErrorWeld :
  (stage : Nat) (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  R._≃_
    (R._*_
      (Cross.oneMinus x)
      (R._-_
        (Norm.originalNormalizedFiniteExp stage x ratio)
        R.1ℝ))
    (Error.originalFiniteLogExpError stage x)
originalFiniteNormalizedExpErrorWeld stage x ratio =
  let
    w = Cross.oneMinus x
    inv = Gap.oneMinusInverse ratio
    f = Finite.originalNegativeLogFiniteExponential x stage
    cancel = Inv.*-inverseˡ w (Gap.oneMinusNonzero ratio)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 3
      (λ ww ff ii →
        ww ⊗ ((ff ⊗ ii) ⊖ Κ 1ℚᵘ)
        ⊜ (ff ⊗ (ii ⊗ ww)) ⊖ ww)
      RP.≃-refl w f inv)
    (RP.≃-trans
      (RP.+-cong
        (RP.*-cong RP.≃-refl cancel)
        RP.≃-refl)
      (solve 2
        (λ ff ww →
          (ff ⊗ Κ 1ℚᵘ) ⊖ ww
          ⊜ ff ⊖ ww)
        RP.≃-refl f w))

originalFiniteNormalizedEndpointErrorWeld :
  (stage : Nat) (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  R._≃_
    (Error.originalFiniteLogExpError stage x)
    (R._*_
      (Cross.oneMinus x)
      (R._-_
        (Norm.originalNormalizedFiniteExp stage x ratio)
        (Norm.originalNormalizedFiniteExp
          stage R.0ℝ sourceOriginUnitIntervalRatio)))
originalFiniteNormalizedEndpointErrorWeld stage x ratio =
  RP.≃-trans
    (RP.≃-symm
      (originalFiniteNormalizedExpErrorWeld stage x ratio))
    (RP.*-cong
      RP.≃-refl
      (RP.-‿cong
        (RP.≃-symm
          (originalFiniteNormalizedExpAtZeroIsOne stage))))
