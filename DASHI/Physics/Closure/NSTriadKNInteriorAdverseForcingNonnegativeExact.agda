module DASHI.Physics.Closure.NSTriadKNInteriorAdverseForcingNonnegativeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- DASHI MAKE-OR-BREAK CONSEQUENCE
--
-- Round106 proves on every INTERIOR adverse episode
--
--   nu * integral P_tau = g_tau * integral F_tau.
--
-- Once the physical orientation supplies nu>=0 and integral P_tau>=0, the
-- supposedly "signed" episode forcing cost on the right is itself
-- nonnegative.  Therefore episode restriction preserves cancellation INSIDE
-- one episode (negative pieces of F may cancel positive pieces), but the final
-- scalar costs of different interior adverse episodes cannot cancel one
-- another merely because their unmasked pointwise forcings do.
--
-- This sharply limits the Round106 cancellation route.  To improve on a
-- positive forcing estimate one now needs either intra-episode oscillation,
-- phase synchronization/common masks, or a direct unconditional masked
-- operator estimate.  Cross-triad telescoping after independent episode
-- selection is not available for free.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNSignedPhaseTimeNormalFormRound106Exact as Normal
import DASHI.Physics.Closure.NSTriadKNAdverseEpisodeSignedForcingRound106Exact as Episode

record PhysicalInteriorAdverseCost : Set where
  constructor physical-interior-adverse-cost
  field
    interior : Episode.InteriorAdverseSignedForcingEpisode
    viscosityNonnegative :
      0ℚ ≤ Normal.viscosity (Episode.cell (Episode.episode interior))
    integratedProductionNonnegative :
      0ℚ ≤ Normal.integratedCriticalProduction
        (Episode.cell (Episode.episode interior))

open PhysicalInteriorAdverseCost public

weightedSignedForcing : PhysicalInteriorAdverseCost → ℚ
weightedSignedForcing C =
  Normal.normalFormWeight
    (Episode.cell (Episode.episode (interior C)))
  * Normal.integratedForcing
    (Episode.cell (Episode.episode (interior C)))

viscosityTimesProductionNonnegative :
  (C : PhysicalInteriorAdverseCost) →
  0ℚ ≤
    Normal.viscosity (Episode.cell (Episode.episode (interior C)))
    * Normal.integratedCriticalProduction
        (Episode.cell (Episode.episode (interior C)))
viscosityTimesProductionNonnegative C =
  let
    nu = Normal.viscosity (Episode.cell (Episode.episode (interior C)))
    production = Normal.integratedCriticalProduction
      (Episode.cell (Episode.episode (interior C)))
    instance
      nuNN = nonNegative (viscosityNonnegative C)
      productionNN = nonNegative (integratedProductionNonnegative C)
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg nu production
  in
  ℚP.nonNegative⁻¹ (nu * production)

interiorWeightedSignedForcingNonnegative :
  (C : PhysicalInteriorAdverseCost) →
  0ℚ ≤ weightedSignedForcing C
interiorWeightedSignedForcingNonnegative C =
  let
    exact = Episode.interiorEpisodePaidExactlyBySignedForcing (interior C)
  in
  subst
    (0ℚ ≤_)
    exact
    (viscosityTimesProductionNonnegative C)

sumWeightedSignedForcing : List PhysicalInteriorAdverseCost → ℚ
sumWeightedSignedForcing [] = 0ℚ
sumWeightedSignedForcing (C ∷ Cs) =
  weightedSignedForcing C + sumWeightedSignedForcing Cs

finiteInteriorEpisodeForcingSumNonnegative :
  (Cs : List PhysicalInteriorAdverseCost) →
  0ℚ ≤ sumWeightedSignedForcing Cs
finiteInteriorEpisodeForcingSumNonnegative [] = ℚP.≤-refl
finiteInteriorEpisodeForcingSumNonnegative (C ∷ Cs) =
  ℚP.+-mono-≤
    (interiorWeightedSignedForcingNonnegative C)
    (finiteInteriorEpisodeForcingSumNonnegative Cs)

interiorEpisodeSignedCostIsNonnegative : Bool
interiorEpisodeSignedCostIsNonnegative = true

crossEpisodeCancellationIsNotCreatedByKeepingForcingSigned : Bool
crossEpisodeCancellationIsNotCreatedByKeepingForcingSigned = true

interiorEpisodeSignedCostIsNonnegativeIsTrue :
  interiorEpisodeSignedCostIsNonnegative ≡ true
interiorEpisodeSignedCostIsNonnegativeIsTrue = refl

crossEpisodeCancellationIsNotCreatedByKeepingForcingSignedIsTrue :
  crossEpisodeCancellationIsNotCreatedByKeepingForcingSigned ≡ true
crossEpisodeCancellationIsNotCreatedByKeepingForcingSignedIsTrue = refl
