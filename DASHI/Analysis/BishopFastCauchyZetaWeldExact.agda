module DASHI.Analysis.BishopFastCauchyZetaWeldExact where

------------------------------------------------------------------------
-- CONNECT THE GENUINE CATEGORICITY OWNER TO THE ZETA WITNESS WELD.
--
-- Geuvers--Niqui constructive Cauchy-completion categoricity;
-- Murray/Csimma Bishop real source; DASHI FastCauchy representation.
--
-- This module consumes the EXISTING
-- BishopFastCauchyCategoricityInstanceExact.bishopFastCauchyCanonicalEquivalence.
-- It does not construct its pending reindexing, field capabilities,
-- rational agreement, or actual zeta-value identification.
--
-- The theorem transports an irrationality witness only after the actual
-- selected Bishop and Fast values have been matched through the
-- same faithful canonical map.
------------------------------------------------------------------------

open import Agda.Builtin.Sigma using (Σ)
open import Data.Fin using (Fin)
open import Data.Rational.Unnormalised using (ℚᵘ)

import Real as BishopReal
import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.BishopConstructedRealBackendExact as Bishop
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as FastBackend
import DASHI.Analysis.BishopFastCauchyCategoricityInstanceExact as Canonical
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.BishopSetoidWeldExact as Weld

module _
    {A : Fast.RationalMetricAuthority}
    {operations : Fast.FastCauchyOperations A}
    {bishopPackaging : Bishop.BishopAlgebraOrderPackaging}
    {fastPackaging : FastBackend.FastCauchyBackendPackaging A operations}
    (dataSet : Canonical.BishopFastCauchyCategoricityData
      A operations bishopPackaging fastPackaging)
  where

  SelectedBishopBackend : Spine.SetoidOrderedCompleteReal
  SelectedBishopBackend =
    Bishop.bishopSetoidOrderedCompleteReal bishopPackaging

  SelectedFastBackend : Spine.SetoidOrderedCompleteReal
  SelectedFastBackend =
    FastBackend.fastCauchySetoidOrderedCompleteReal
      operations fastPackaging

  canonicalEquivalence :
    Spine.SetoidRealEquivalence SelectedBishopBackend SelectedFastBackend
  canonicalEquivalence =
    Canonical.bishopFastCauchyCanonicalEquivalence dataSet

  -- The only rational embedding comparison not already provided by
  -- the above categorical structure. For concrete Bishop/Fast models
  -- it must be established from their original rational approximants.
  -- Unlike the generic reusable weld, this concrete instantiation
  -- fixes the rational carrier to the ACTUAL Bishop library ℚᵘ and
  -- its pre-existing rational-to-real embedding (_⋆). The Fast
  -- embedding and comparison still require original source proofs.
  makeRationalWeld :
    (fastRational : ℚᵘ → Fast.FastCauchyReal A) →
    ((q : ℚᵘ) →
      Fast._≈R_
        (Spine.map (Spine.toRight canonicalEquivalence)
          (BishopReal._⋆ q))
        (fastRational q)) →
    Weld.RationalSetoidWeld SelectedBishopBackend SelectedFastBackend
  makeRationalWeld fastRational agree =
    record
      { equivalence = canonicalEquivalence
      ; Rational = ℚᵘ
      ; leftEmbed = BishopReal._⋆
      ; rightEmbed = fastRational
      ; rationalAgreement = agree
      }

  -- Precisely the original selected fifteen-value witness cut:
  -- no abstract proof is promoted to the actual zeta without `same`.
  bishopOddZetaToFastWitness :
    (W : Weld.RationalSetoidWeld SelectedBishopBackend SelectedFastBackend)
    (source : Fin 15 → BishopReal.ℝ)
    (target : Fin 15 → Fast.FastCauchyReal A) →
    ((i : Fin 15) →
      Fast._≈R_
        (Weld.toRightValue W (source i))
        (target i)) →
    Σ (Fin 15) (λ i → Weld.IrrationalLeft W (source i)) →
    Σ (Fin 15) (λ i → Weld.IrrationalRight W (target i))
  bishopOddZetaToFastWitness W source target same witness =
    Weld.existentialIrrationalityTransport W
      (Fin 15) source target same witness
