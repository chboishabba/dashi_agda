module DASHI.Biology.Molecular.BH4OriginalBishopArbitraryReactionRatesExact where

-- High-alpha P0 exact finite reaction accounting for ARBITRARY
-- Bishop-real rate fields, not only the rational rates that are
-- the image of a finite rational chart. The source chemistry's
-- gross reaction sides/29 weights remain source-derived rationals.
--
-- The proof depends only on the source's twelve rational column
-- left-kernel equivalences and the repository's existing Bishop
-- rational embedding and real setoid ring congruence. The
-- 27 original voxels can each have arbitrary REAL rate values.
--
-- This does NOT assert the physical mass-action law, actual source
-- kinetics, SG continuity or Brouwer existence. No postulates.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Real as R
import RealProperties as RP
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed
import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift

-- The canonical Bishop weighted finite row is reused directly.
bishopSourceColumn : ∀ {n} →
  V.Vec R.ℝ n → V.Vec R.ℝ n → R.ℝ
bishopSourceColumn = Lift.bishopWeightedRow

bishopRateWeightedTotal :
  ∀ {columns species} →
  V.Vec R.ℝ species →
  V.Vec (V.Vec R.ℝ species) columns →
  V.Vec R.ℝ columns → R.ℝ
bishopRateWeightedTotal weights V.[] V.[] =
  Embed.embed Q.0ℚᵘ
bishopRateWeightedTotal weights
  (V._∷_ column columns) (V._∷_ rate rates) =
  R._+_
    (R._*_ rate (bishopSourceColumn weights column))
    (bishopRateWeightedTotal weights columns rates)

bishopSpatialRateWeightedTotal :
  ∀ {sites columns species} →
  V.Vec R.ℝ species →
  V.Vec (V.Vec R.ℝ species) columns →
  V.Vec (V.Vec R.ℝ columns) sites → R.ℝ
bishopSpatialRateWeightedTotal weights columns V.[] =
  Embed.embed Q.0ℚᵘ
bishopSpatialRateWeightedTotal weights columns
  (V._∷_ rates rest) =
  R._+_
    (bishopRateWeightedTotal weights columns rates)
    (bishopSpatialRateWeightedTotal weights columns rest)

-- No rational rate limitation: scalar multiplication by an arbitrary
-- Bishop real preserves a previously certified real column equality.
bishopAllColumnsArbitraryRatesConserve :
  ∀ {columns species}
  (weights : V.Vec R.ℝ species)
  (reactants products :
    V.Vec (V.Vec R.ℝ species) columns)
  (rates : V.Vec R.ℝ columns) →
  ((column : F.Fin columns) →
    R._≃_
      (bishopSourceColumn weights (V.lookup reactants column))
      (bishopSourceColumn weights (V.lookup products column))) →
  R._≃_
    (bishopRateWeightedTotal weights reactants rates)
    (bishopRateWeightedTotal weights products rates)
bishopAllColumnsArbitraryRatesConserve weights V.[] V.[] V.[] balance =
  RP.≃-refl
bishopAllColumnsArbitraryRatesConserve weights
  (V._∷_ reactant reactants) (V._∷_ product products)
  (V._∷_ rate rates) balance =
  RP.+-cong
    (RP.*-cong RP.≃-refl (balance F.zero))
    (bishopAllColumnsArbitraryRatesConserve
      weights reactants products rates
      (λ column → balance (F.suc column)))

bishopAllSitesArbitraryRatesConserve :
  ∀ {sites columns species}
  (weights : V.Vec R.ℝ species)
  (reactants products :
    V.Vec (V.Vec R.ℝ species) columns)
  (rates : V.Vec (V.Vec R.ℝ columns) sites) →
  ((column : F.Fin columns) →
    R._≃_
      (bishopSourceColumn weights (V.lookup reactants column))
      (bishopSourceColumn weights (V.lookup products column))) →
  R._≃_
    (bishopSpatialRateWeightedTotal weights reactants rates)
    (bishopSpatialRateWeightedTotal weights products rates)
bishopAllSitesArbitraryRatesConserve weights
  reactants products V.[] balance = RP.≃-refl
bishopAllSitesArbitraryRatesConserve weights
  reactants products (V._∷_ rates rest) balance =
  RP.+-cong
    (bishopAllColumnsArbitraryRatesConserve
      weights reactants products rates balance)
    (bishopAllSitesArbitraryRatesConserve
      weights reactants products rest balance)

-- The SAME original source rational column balance lifts by the
-- existing Bishop weighted-row embedding, without importing
-- independent/new chemistry or requiring the rate to be rational.
bishopOriginalColumnBalanceFromRationalSource :
  ∀ {species}
  (weights reactants products : V.Vec Q.ℚᵘ species) →
  Q._≃_
    (Lift.sourceWeightedRow weights reactants)
    (Lift.sourceWeightedRow weights products) →
  R._≃_
    (bishopSourceColumn
      (V.map Embed.embed weights) (V.map Embed.embed reactants))
    (bishopSourceColumn
      (V.map Embed.embed weights) (V.map Embed.embed products))
bishopOriginalColumnBalanceFromRationalSource weights reactants products source =
  RP.≃-trans
    (RP.≃-symm (Lift.weightedRowEmbeds weights reactants))
    (RP.≃-trans
      (RP.⋆-cong source)
      (Lift.weightedRowEmbeds weights products))

-- Original 29 species, 12 source reactions and 27 voxel locations.
-- No restriction whatever on the 324 individual Bishop-real rates.
original369BishopArbitraryReactionRatesConserve :
  (weights : V.Vec Q.ℚᵘ 29)
  (reactants products : V.Vec (V.Vec Q.ℚᵘ 29) 12)
  (rates : V.Vec (V.Vec R.ℝ 12) 27) →
  ((column : F.Fin 12) →
    Q._≃_
      (Lift.sourceWeightedRow weights
        (V.lookup reactants column))
      (Lift.sourceWeightedRow weights
        (V.lookup products column))) →
  R._≃_
    (bishopSpatialRateWeightedTotal
      (V.map Embed.embed weights)
      (V.map (V.map Embed.embed) reactants) rates)
    (bishopSpatialRateWeightedTotal
      (V.map Embed.embed weights)
      (V.map (V.map Embed.embed) products) rates)
original369BishopArbitraryReactionRatesConserve
  weights reactants products rates source =
  bishopAllSitesArbitraryRatesConserve
    (V.map Embed.embed weights)
    (V.map (V.map Embed.embed) reactants)
    (V.map (V.map Embed.embed) products)
    rates
    (λ column →
      bishopOriginalColumnBalanceFromRationalSource
        weights
        (V.lookup reactants column)
        (V.lookup products column)
        (source column))
