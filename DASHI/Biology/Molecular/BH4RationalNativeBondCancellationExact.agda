module DASHI.Biology.Molecular.BH4RationalNativeBondCancellationExact where

-- P0 exact rational cancellation of paired native-edge contributions.
--
-- Every one of the 54 original cubical internal bonds has one source
-- and one target. For each of the 29 source species, its signed flux
-- leaves one endpoint and enters the other with the same weight.
-- This module proves the purely algebraic finite-sum cancellation for
-- arbitrary rational weights/fluxes, then lifts that zero through the
-- previously established rational-to-Bishop embedding.
--
-- This DOES NOT construct the original signed 27x54 incidence map or
-- source-authorised Rhea stoichiometry: identifying this paired form
-- with the actual voxel divergence is a separate remaining gate.
-- No postulates, external source data, measured rates or Agda compiler
-- acceptance are claimed by this source-written file.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QSolver
import Real as R
import RealProperties as RP
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed

-- A source endpoint contributes negative signed flux; a target
-- contributes positive signed flux, for the SAME weight and flux.
pairedSpeciesContribution : Q.ℚᵘ → Q.ℚᵘ → Q.ℚᵘ
pairedSpeciesContribution weight flux =
  Q._+_
    (Q._*_ weight (Q.- flux))
    (Q._*_ weight flux)

pairedSpeciesContributionCancels :
  (weight flux : Q.ℚᵘ) →
  Q._≃_ (pairedSpeciesContribution weight flux) Q.0ℚᵘ
pairedSpeciesContributionCancels weight flux =
  let open QSolver in
  solve 2
    (λ w f → ((w ⊗ (⊝ f)) ⊕ (w ⊗ f)) ⊜ Κ Q.0ℚᵘ)
    QP.≃-refl weight flux

-- One *actual bond slot* has exactly 29 signed species fluxes.
-- No assumption about concentrations or kinetics is needed.
pairedBondWeightedSum :
  ∀ {species} →
  V.Vec Q.ℚᵘ species →
  V.Vec Q.ℚᵘ species → Q.ℚᵘ
pairedBondWeightedSum V.[] V.[] = Q.0ℚᵘ
pairedBondWeightedSum
  (V._∷_ weight weights) (V._∷_ flux fluxes) =
  Q._+_ (pairedSpeciesContribution weight flux)
        (pairedBondWeightedSum weights fluxes)

pairedBondWeightedSumCancels :
  ∀ {species}
  (weights fluxes : V.Vec Q.ℚᵘ species) →
  Q._≃_ (pairedBondWeightedSum weights fluxes) Q.0ℚᵘ
pairedBondWeightedSumCancels V.[] V.[] = QP.≃-refl
pairedBondWeightedSumCancels
  (V._∷_ weight weights) (V._∷_ flux fluxes) =
  QP.≃-trans
    (QP.+-cong
      (pairedSpeciesContributionCancels weight flux)
      (pairedBondWeightedSumCancels weights fluxes))
    (QP.+-identityˡ Q.0ℚᵘ)

pairedNativeBondCollection :
  ∀ {bonds species} →
  V.Vec Q.ℚᵘ species →
  V.Vec (V.Vec Q.ℚᵘ species) bonds → Q.ℚᵘ
pairedNativeBondCollection weights V.[] = Q.0ℚᵘ
pairedNativeBondCollection weights (V._∷_ flux fluxes) =
  Q._+_ (pairedBondWeightedSum weights flux)
        (pairedNativeBondCollection weights fluxes)

pairedNativeBondCollectionCancels :
  ∀ {bonds species}
  (weights : V.Vec Q.ℚᵘ species)
  (fluxes : V.Vec (V.Vec Q.ℚᵘ species) bonds) →
  Q._≃_ (pairedNativeBondCollection weights fluxes) Q.0ℚᵘ
pairedNativeBondCollectionCancels weights V.[] = QP.≃-refl
pairedNativeBondCollectionCancels weights (V._∷_ flux fluxes) =
  QP.≃-trans
    (QP.+-cong
      (pairedBondWeightedSumCancels weights flux)
      (pairedNativeBondCollectionCancels weights fluxes))
    (QP.+-identityˡ Q.0ℚᵘ)

-- Dimension-specialized result: original 54 edge slots, 29 species.
-- The separate 27x54 incidence-to-paired-endpoints equality is OPEN.
original54x29PairedNativeFluxCancels :
  (weights : V.Vec Q.ℚᵘ 29)
  (fluxes : V.Vec (V.Vec Q.ℚᵘ 29) 54) →
  Q._≃_ (pairedNativeBondCollection weights fluxes) Q.0ℚᵘ
original54x29PairedNativeFluxCancels =
  pairedNativeBondCollectionCancels

-- Consequent Bishop-real zero, using the SAME embedding as the
-- earlier rational-to-Bishop finite continuity owner.
original54x29PairedNativeFluxBishopZero :
  (weights : V.Vec Q.ℚᵘ 29)
  (fluxes : V.Vec (V.Vec Q.ℚᵘ 29) 54) →
  R._≃_
    (Embed.embed (pairedNativeBondCollection weights fluxes))
    (Embed.embed Q.0ℚᵘ)
original54x29PairedNativeFluxBishopZero weights fluxes =
  RP.⋆-cong (original54x29PairedNativeFluxCancels weights fluxes)
