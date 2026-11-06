module DASHI.Physics.YangMills.YMClayNativePairsSpectatorsFubiniExact where

------------------------------------------------------------------------
-- YM M.02: flat ordered Haar over 2*n+m original positive links
-- equals original F19 nested n ordered link-pairs plus m spectators.
-- No independent measure and no assumption of factored integrands.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact as Original
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  originalFlatEqualsNestedPairsSpectators :
    ∀ {n m : Nat}
      (integrand : Vec.Vec Link (Original.twice n + m) →
        ℝ) →
    Haar.productIntegral source integrand
    ≡
    Fibre.finePairsIntegral theory source bilateral
      (λ pairs →
        Haar.productIntegral source
          (λ spectators →
            integrand
              (Original.appendVec
                (Original.flattenPairs pairs) spectators)))
  originalFlatEqualsNestedPairsSpectators {n = zero} integrand = refl
  originalFlatEqualsNestedPairsSpectators {n = suc n} integrand =
    Haar.integrateCongruent source _ _
      (λ first →
        Haar.integrateCongruent source _ _
          (λ second →
            originalFlatEqualsNestedPairsSpectators
              (λ tail → integrand (first Vec.∷ second Vec.∷ tail))))
