module DASHI.Biology.Molecular.BH4OriginalBishopSGComputedRHSExact where

------------------------------------------------------------------------
-- Original 27 x 29 Bishop-real finite-volume SG / reaction RHS.
--
-- Reuses:
--   (i) exact 27x54 native incidence from BH4OriginalNative369IncidenceExact;
--   (ii) 54x29 Bishop SG currents from the pre-existing semiconductor
--        flux owner via BH4OriginalScharfetterGummelDissipationExact;
-- (iii) source-indexed 29x12 rational stoichiometry, embedded in the
--       same canonical Bishop ℝ, and arbitrary 27x12 Bishop-real rates.
--
-- This proves a concrete typed *operator definition* and every pointwise
-- RHS split. Does NOT prove the abstract SG face states are generated
-- from one 27-node c, one Poisson potential phi(c), the source valences,
-- or physical D,h,RT,F calibration. Those are P0 physical welds.
-- It does NOT claim Brouwer, positivity or free-energy dissipation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Series
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed
import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Original
import DASHI.Biology.Molecular.BH4OriginalNative369IncidenceExact as Native
import DASHI.Biology.Molecular.BH4OriginalScharfetterGummelDissipationExact as SG

BishopMatrix : Nat → Nat → Set
BishopMatrix = SG.BishopMatrix

-- Source-preserving real matrix operations, without NumPy or floats.
bishopOriginalDot :
  ∀ {n} → V.Vec R.ℝ n → V.Vec R.ℝ n → R.ℝ
bishopOriginalDot V.[] V.[] = Embed.embed Q.0ℚᵘ
bishopOriginalDot (V._∷_ a row) (V._∷_ b rates) =
  R._+_ (R._*_ a b) (bishopOriginalDot row rates)

bishopOriginalColumn :
  ∀ {rows columns} →
  BishopMatrix rows columns → F.Fin columns → V.Vec R.ℝ rows
bishopOriginalColumn rows column =
  V.map (λ row → V.lookup row column) rows

-- The exact same original 27×54 integer incidence, embedded in
-- Bishop reals at every original source and target coordinate.
bishopOriginalIncidence : BishopMatrix 27 54
bishopOriginalIncidence =
  V.map (V.map Embed.embed) Native.sourceNativeIncidence

-- Signed native bond contribution, already per-voxel normalized
-- by its external D_s/h² scale in originalBishopSGFluxes.
bishopOriginalBondContribution :
  BishopMatrix 54 29 → F.Fin 27 → F.Fin 29 → R.ℝ
bishopOriginalBondContribution fluxes site species =
  bishopOriginalDot
    (V.lookup bishopOriginalIncidence site)
    (bishopOriginalColumn fluxes species)

-- Original 29×12 source chemistry is only converted by the canonical
-- rational injection, with no replacement reaction inventory.
bishopOriginalReactionContribution :
  Original.Matrix 29 12 →
  BishopMatrix 27 12 →
  F.Fin 27 → F.Fin 29 → R.ℝ
bishopOriginalReactionContribution stoichiometry rates site species =
  bishopOriginalDot
    (V.map Embed.embed (V.lookup stoichiometry species))
    (V.lookup rates site)

bishopOriginalSGReactionRHS :
  BishopMatrix 54 29 →
  Original.Matrix 29 12 →
  BishopMatrix 27 12 →
  BishopMatrix 27 29
bishopOriginalSGReactionRHS fluxes stoichiometry rates =
  V.tabulate (λ site →
    V.tabulate (λ species →
      R._+_
        (bishopOriginalBondContribution fluxes site species)
        (bishopOriginalReactionContribution stoichiometry rates
          site species)))

-- Symbolic Fin 27 / Fin 29 proof: no illegal lookup-tabulate refl.
bishopOriginalRHSAt :
  (fluxes : BishopMatrix 54 29)
  (stoichiometry : Original.Matrix 29 12)
  (rates : BishopMatrix 27 12)
  (site : F.Fin 27) (species : F.Fin 29) →
  V.lookup
    (V.lookup
      (bishopOriginalSGReactionRHS fluxes stoichiometry rates)
      site) species
    ≡
  R._+_
    (bishopOriginalBondContribution fluxes site species)
    (bishopOriginalReactionContribution stoichiometry rates
      site species)
bishopOriginalRHSAt fluxes stoichiometry rates site species =
  trans
    (cong (λ row → V.lookup row species)
      (Original.lookupTabulateExact
        (λ site′ → V.tabulate
          (λ species′ →
            R._+_
              (bishopOriginalBondContribution fluxes site′ species′)
              (bishopOriginalReactionContribution
                stoichiometry rates site′ species′)))
        site))
    (Original.lookupTabulateExact
      (λ species′ →
        R._+_
          (bishopOriginalBondContribution fluxes site species′)
          (bishopOriginalReactionContribution
            stoichiometry rates site species′))
      species)

-- The SG faces are NOT invented here: each is an actual face datum
-- from the repository's Bishop semiconductor SG owner.
original54FaceBishopSGRHS :
  (series : Series.BishopElementaryPowerSeriesData)
  (prefactors : V.Vec R.ℝ 29)
  (faces : SG.bishopSGFaces series)
  (stoichiometry : Original.Matrix 29 12)
  (rates : BishopMatrix 27 12) →
  BishopMatrix 27 29
original54FaceBishopSGRHS series prefactors faces stoichiometry rates =
  bishopOriginalSGReactionRHS
    (SG.originalBishopSGFluxes series prefactors faces)
    stoichiometry rates

original54FaceBishopSGRHSAt :
  (series : Series.BishopElementaryPowerSeriesData)
  (prefactors : V.Vec R.ℝ 29)
  (faces : SG.bishopSGFaces series)
  (stoichiometry : Original.Matrix 29 12)
  (rates : BishopMatrix 27 12)
  (site : F.Fin 27) (species : F.Fin 29) →
  V.lookup
    (V.lookup
      (original54FaceBishopSGRHS
        series prefactors faces stoichiometry rates)
      site) species
    ≡
  R._+_
    (bishopOriginalBondContribution
      (SG.originalBishopSGFluxes series prefactors faces)
      site species)
    (bishopOriginalReactionContribution
      stoichiometry rates site species)
original54FaceBishopSGRHSAt series prefactors faces stoichiometry rates =
  bishopOriginalRHSAt
    (SG.originalBishopSGFluxes series prefactors faces)
    stoichiometry rates

-- All real RHS coefficients are explicitly built from the SAME
-- finite geometry and source chemistry. This file contains no
-- physical source rate or independently inferred Poisson potential.
