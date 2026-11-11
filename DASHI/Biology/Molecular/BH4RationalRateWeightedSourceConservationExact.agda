module DASHI.Biology.Molecular.BH4RationalRateWeightedSourceConservationExact where

-- Exact finite rational rate-weighted conservation theorem for the
-- existing original 29 species, 12 finite columns and 27 voxel chart.
-- Reactant/product vectors are gross signed-source sides (not net
-- kinetic approximations). If each column is left-kernel balanced
-- over rational equivalence, arbitrary signed rational rates
-- preserve the SAME left-kernel coordinate at every site.
--
-- A source-specific proof that these rational columns are exactly
-- the image of SourceCertifiedOriginal29x12 Nat columns remains
-- a separate P0 obligation. No synthetic Rhea data, rate values,
-- postulate, classical axiom or measured source is introduced.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as R
import RealProperties as RP
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed
import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift

-- Keep the existing weighted-dot implementation canonical.
weightedColumn : ∀ {n} →
  V.Vec Q.ℚᵘ n → V.Vec Q.ℚᵘ n → Q.ℚᵘ
weightedColumn = Lift.sourceWeightedRow

rateWeightedReactantTotal :
  ∀ {columns species} →
  V.Vec Q.ℚᵘ species →
  V.Vec (V.Vec Q.ℚᵘ species) columns →
  V.Vec Q.ℚᵘ columns → Q.ℚᵘ
rateWeightedReactantTotal weights V.[] V.[] = Q.0ℚᵘ
rateWeightedReactantTotal weights
  (V._∷_ column columns) (V._∷_ rate rates) =
  Q._+_ (Q._*_ rate (weightedColumn weights column))
        (rateWeightedReactantTotal weights columns rates)

-- The product-side type is identical; the original source identity
-- distinguishes gross reactants from gross products by its arguments.
rateWeightedProductTotal = rateWeightedReactantTotal

-- Finite-column theorem: *any* rate vector respects a certified
-- columnwise rational left kernel. No independent assumption about
-- the finite weighted rate sums is supplied.
rationalAllColumnsRateBalanced :
  ∀ {columns species}
  (weights : V.Vec Q.ℚᵘ species)
  (reactants products :
    V.Vec (V.Vec Q.ℚᵘ species) columns)
  (rates : V.Vec Q.ℚᵘ columns) →
  ((column : F.Fin columns) →
    Q._≃_
      (weightedColumn weights (V.lookup reactants column))
      (weightedColumn weights (V.lookup products column))) →
  Q._≃_
    (rateWeightedReactantTotal weights reactants rates)
    (rateWeightedProductTotal weights products rates)
rationalAllColumnsRateBalanced weights V.[] V.[] V.[] balanced =
  QP.≃-refl
rationalAllColumnsRateBalanced weights
  (V._∷_ reactant reactants) (V._∷_ product products)
  (V._∷_ rate rates) balanced =
  QP.+-cong
    (QP.*-cong QP.≃-refl (balanced F.zero))
    (rationalAllColumnsRateBalanced weights reactants products
      rates (λ j → balanced (F.suc j)))

spatialRateWeightedTotal :
  ∀ {sites columns species} →
  V.Vec Q.ℚᵘ species →
  V.Vec (V.Vec Q.ℚᵘ species) columns →
  V.Vec (V.Vec Q.ℚᵘ columns) sites → Q.ℚᵘ
spatialRateWeightedTotal weights columns V.[] = Q.0ℚᵘ
spatialRateWeightedTotal weights columns
  (V._∷_ rates rest) =
  Q._+_ (rateWeightedReactantTotal weights columns rates)
        (spatialRateWeightedTotal weights columns rest)

rationalAllSitesRateBalanced :
  ∀ {sites columns species}
  (weights : V.Vec Q.ℚᵘ species)
  (reactants products :
    V.Vec (V.Vec Q.ℚᵘ species) columns)
  (rates : V.Vec (V.Vec Q.ℚᵘ columns) sites) →
  ((column : F.Fin columns) →
    Q._≃_
      (weightedColumn weights (V.lookup reactants column))
      (weightedColumn weights (V.lookup products column))) →
  Q._≃_
    (spatialRateWeightedTotal weights reactants rates)
    (spatialRateWeightedTotal weights products rates)
rationalAllSitesRateBalanced weights reactants products V.[] balanced =
  QP.≃-refl
rationalAllSitesRateBalanced weights reactants products
  (V._∷_ rates rest) balanced =
  QP.+-cong
    (rationalAllColumnsRateBalanced
      weights reactants products rates balanced)
    (rationalAllSitesRateBalanced
      weights reactants products rest balanced)

-- Concrete original chart dimensions, not a new synthetic chemistry.
original369x29x12RationalRatesPreserveKernel :
  (weights : V.Vec Q.ℚᵘ 29)
  (reactants products : V.Vec (V.Vec Q.ℚᵘ 29) 12)
  (rates : V.Vec (V.Vec Q.ℚᵘ 12) 27) →
  ((column : F.Fin 12) →
    Q._≃_
      (weightedColumn weights (V.lookup reactants column))
      (weightedColumn weights (V.lookup products column))) →
  Q._≃_
    (spatialRateWeightedTotal weights reactants rates)
    (spatialRateWeightedTotal weights products rates)
original369x29x12RationalRatesPreserveKernel =
  rationalAllSitesRateBalanced

-- Rational balance is promoted only to Bishop setoid equality.
-- This is not the identification of physiological SG currents
-- or an original measured reaction-rate law.
original369RationalRateBalanceLiftsToBishop :
  (weights : V.Vec Q.ℚᵘ 29)
  (reactants products : V.Vec (V.Vec Q.ℚᵘ 29) 12)
  (rates : V.Vec (V.Vec Q.ℚᵘ 12) 27) →
  ((column : F.Fin 12) →
    Q._≃_
      (weightedColumn weights (V.lookup reactants column))
      (weightedColumn weights (V.lookup products column))) →
  R._≃_
    (Embed.embed (spatialRateWeightedTotal weights reactants rates))
    (Embed.embed (spatialRateWeightedTotal weights products rates))
original369RationalRateBalanceLiftsToBishop
  weights reactants products rates balanced =
  RP.⋆-cong
    (original369x29x12RationalRatesPreserveKernel
      weights reactants products rates balanced)
