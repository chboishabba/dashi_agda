module DASHI.Physics.Closure.NSTriadKNLuoFilteredEnstrophySurplusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
-- Status: arXiv preprint, submitted 25 June 2026.
--
-- Relevant source results: Proposition 6.1, Theorem 9.3 and Theorem 10.1.
-- The source proves a finite-scale localized filtered-enstrophy balance in
-- which near-field stretching and differentiated commutator forcing consume
-- explicit portions eta_near and eta_com of filtered diffusion.  The surviving
-- positive surplus is assigned to far-field strain, an increment defect, and
-- localization shells.
--
-- DASHI CONTRIBUTION
--
-- This module proves the complete signed coefficient algebra and finite
-- nonnegative-weight summation:
--
--   E_out + P <= E_in + V_near + V_far + F_com + L,
--   V_near <= eta_near P + O,
--   F_com  <= eta_com  P + S_inc + L_com
--
-- imply
--
--   E_out + (1-eta_near-eta_com) P
--     <= E_in + O + V_far + S_inc + L + L_com.
--
-- No residual is hidden and no conditional unweighted Carleson or increment
-- summability hypothesis is promoted to an unconditional theorem.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record FilteredEnstrophyScale : Set where
  constructor filteredEnstrophyScale
  field
    endpointIn endpointOut diffusion : ℚ
    nearField farField commutator : ℚ
    lowerEnstrophy incrementDefect : ℚ
    localization commutatorLocalization : ℚ
    etaNear etaCommutator : ℚ

    endpointInNonnegative : 0ℚ ≤ endpointIn
    endpointOutNonnegative : 0ℚ ≤ endpointOut
    diffusionNonnegative : 0ℚ ≤ diffusion
    nearFieldNonnegative : 0ℚ ≤ nearField
    farFieldNonnegative : 0ℚ ≤ farField
    commutatorNonnegative : 0ℚ ≤ commutator
    lowerEnstrophyNonnegative : 0ℚ ≤ lowerEnstrophy
    incrementDefectNonnegative : 0ℚ ≤ incrementDefect
    localizationNonnegative : 0ℚ ≤ localization
    commutatorLocalizationNonnegative :
      0ℚ ≤ commutatorLocalization
    etaNearNonnegative : 0ℚ ≤ etaNear
    etaCommutatorNonnegative : 0ℚ ≤ etaCommutator
    remainingDiffusionNonnegative :
      0ℚ ≤ 1ℚ - etaNear - etaCommutator

    localizedFilteredEnstrophyBalance :
      endpointOut + diffusion
      ≤ endpointIn + nearField + farField + commutator + localization

    nearFieldCoercivity :
      nearField ≤ etaNear * diffusion + lowerEnstrophy

    derivativeCompatibleCommutator :
      commutator
      ≤ etaCommutator * diffusion
        + incrementDefect + commutatorLocalization

open FilteredEnstrophyScale public

remainingDiffusion : FilteredEnstrophyScale → ℚ
remainingDiffusion scale =
  1ℚ - etaNear scale - etaCommutator scale

filteredScaleLeft : FilteredEnstrophyScale → ℚ
filteredScaleLeft scale =
  endpointOut scale + remainingDiffusion scale * diffusion scale

filteredScaleRight : FilteredEnstrophyScale → ℚ
filteredScaleRight scale =
  endpointIn scale
  + lowerEnstrophy scale
  + farField scale
  + incrementDefect scale
  + localization scale
  + commutatorLocalization scale

etaNearDiffusionNonnegative :
  ∀ scale → 0ℚ ≤ etaNear scale * diffusion scale
etaNearDiffusionNonnegative scale =
  let
    instance
      etaNN = nonNegative (etaNearNonnegative scale)
      diffusionNN = nonNegative (diffusionNonnegative scale)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (etaNear scale) (diffusion scale)
  in
  ℚₚ.nonNegative⁻¹ (etaNear scale * diffusion scale)

etaCommutatorDiffusionNonnegative :
  ∀ scale → 0ℚ ≤ etaCommutator scale * diffusion scale
etaCommutatorDiffusionNonnegative scale =
  let
    instance
      etaNN = nonNegative (etaCommutatorNonnegative scale)
      diffusionNN = nonNegative (diffusionNonnegative scale)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (etaCommutator scale) (diffusion scale)
  in
  ℚₚ.nonNegative⁻¹
    (etaCommutator scale * diffusion scale)

remainingDiffusionContributionNonnegative :
  ∀ scale →
  0ℚ ≤ remainingDiffusion scale * diffusion scale
remainingDiffusionContributionNonnegative scale =
  let
    instance
      marginNN = nonNegative (remainingDiffusionNonnegative scale)
      diffusionNN = nonNegative (diffusionNonnegative scale)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (remainingDiffusion scale) (diffusion scale)
  in
  ℚₚ.nonNegative⁻¹
    (remainingDiffusion scale * diffusion scale)

filteredScaleLeftNonnegative :
  ∀ scale → 0ℚ ≤ filteredScaleLeft scale
filteredScaleLeftNonnegative scale =
  L2.addNonnegative
    (endpointOutNonnegative scale)
    (remainingDiffusionContributionNonnegative scale)

filteredScaleRightNonnegative :
  ∀ scale → 0ℚ ≤ filteredScaleRight scale
filteredScaleRightNonnegative scale =
  L2.addNonnegative
    (L2.addNonnegative
      (L2.addNonnegative
        (L2.addNonnegative
          (L2.addNonnegative
            (endpointInNonnegative scale)
            (lowerEnstrophyNonnegative scale))
          (farFieldNonnegative scale))
        (incrementDefectNonnegative scale))
      (localizationNonnegative scale))
    (commutatorLocalizationNonnegative scale)

filteredEnstrophySurplusBound :
  ∀ scale → filteredScaleLeft scale ≤ filteredScaleRight scale
filteredEnstrophySurplusBound scale =
  let
    groupedSourceReplacement :
      (nearField scale + farField scale)
        + (commutator scale + localization scale)
      ≤
      ((etaNear scale * diffusion scale + lowerEnstrophy scale)
        + farField scale)
      +
      ((etaCommutator scale * diffusion scale
        + incrementDefect scale + commutatorLocalization scale)
        + localization scale)
    groupedSourceReplacement =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (nearFieldCoercivity scale)
          ℚₚ.≤-refl)
        (ℚₚ.+-mono-≤
          (derivativeCompatibleCommutator scale)
          ℚₚ.≤-refl)

    sourceLeftMeaning :
      (nearField scale + farField scale)
        + (commutator scale + localization scale)
      ≡
      nearField scale + farField scale
        + commutator scale + localization scale
    sourceLeftMeaning =
      solve
        ( nearField scale ∷ farField scale
        ∷ commutator scale ∷ localization scale ∷ [])

    sourceRightMeaning :
      ((etaNear scale * diffusion scale + lowerEnstrophy scale)
        + farField scale)
      +
      ((etaCommutator scale * diffusion scale
        + incrementDefect scale + commutatorLocalization scale)
        + localization scale)
      ≡
      (etaNear scale * diffusion scale + lowerEnstrophy scale)
      + farField scale
      +
      (etaCommutator scale * diffusion scale
        + incrementDefect scale + commutatorLocalization scale)
      + localization scale
    sourceRightMeaning =
      solve
        ( etaNear scale ∷ etaCommutator scale ∷ diffusion scale
        ∷ lowerEnstrophy scale ∷ farField scale
        ∷ incrementDefect scale ∷ commutatorLocalization scale
        ∷ localization scale ∷ [])

    sourceReplacement :
      nearField scale + farField scale
        + commutator scale + localization scale
      ≤
      (etaNear scale * diffusion scale + lowerEnstrophy scale)
      + farField scale
      +
      (etaCommutator scale * diffusion scale
        + incrementDefect scale + commutatorLocalization scale)
      + localization scale
    sourceReplacement =
      subst
        (λ left →
          left
          ≤
          (etaNear scale * diffusion scale + lowerEnstrophy scale)
          + farField scale
          +
          (etaCommutator scale * diffusion scale
            + incrementDefect scale + commutatorLocalization scale)
          + localization scale)
        sourceLeftMeaning
        (subst
          (λ right →
            (nearField scale + farField scale)
              + (commutator scale + localization scale)
            ≤ right)
          sourceRightMeaning
          groupedSourceReplacement)

    withEndpoint :
      endpointIn scale
        + (nearField scale + farField scale
          + commutator scale + localization scale)
      ≤
      endpointIn scale
        +
        ((etaNear scale * diffusion scale + lowerEnstrophy scale)
          + farField scale
          +
          (etaCommutator scale * diffusion scale
            + incrementDefect scale + commutatorLocalization scale)
          + localization scale)
    withEndpoint =
      ℚₚ.+-monoʳ-≤ (endpointIn scale) sourceReplacement

    balanceNormalized :
      endpointOut scale + diffusion scale
      ≤
      endpointIn scale
        + (nearField scale + farField scale
          + commutator scale + localization scale)
    balanceNormalized =
      subst
        (λ upper → endpointOut scale + diffusion scale ≤ upper)
        (solve
          ( endpointIn scale ∷ nearField scale ∷ farField scale
          ∷ commutator scale ∷ localization scale ∷ []))
        (localizedFilteredEnstrophyBalance scale)

    assembled :
      endpointOut scale + diffusion scale
      ≤
      endpointIn scale
        +
        ((etaNear scale * diffusion scale + lowerEnstrophy scale)
          + farField scale
          +
          (etaCommutator scale * diffusion scale
            + incrementDefect scale + commutatorLocalization scale)
          + localization scale)
    assembled = ℚₚ.≤-trans balanceNormalized withEndpoint

    shift =
      - (etaNear scale * diffusion scale
        + etaCommutator scale * diffusion scale)

    shiftedLeft :
      shift + (endpointOut scale + diffusion scale)
      ≤
      shift
      +
      (endpointIn scale
        +
        ((etaNear scale * diffusion scale + lowerEnstrophy scale)
          + farField scale
          +
          (etaCommutator scale * diffusion scale
            + incrementDefect scale + commutatorLocalization scale)
          + localization scale))
    shiftedLeft = ℚₚ.+-monoʳ-≤ shift assembled

    shifted :
      (endpointOut scale + diffusion scale) + shift
      ≤
      (endpointIn scale
        +
        ((etaNear scale * diffusion scale + lowerEnstrophy scale)
          + farField scale
          +
          (etaCommutator scale * diffusion scale
            + incrementDefect scale + commutatorLocalization scale)
          + localization scale))
      + shift
    shifted =
      subst
        (λ left →
          left
          ≤
          (endpointIn scale
            +
            ((etaNear scale * diffusion scale + lowerEnstrophy scale)
              + farField scale
              +
              (etaCommutator scale * diffusion scale
                + incrementDefect scale + commutatorLocalization scale)
              + localization scale))
          + shift)
        (solve
          ( shift ∷ endpointOut scale ∷ diffusion scale ∷ []))
        (subst
          (λ right →
            shift + (endpointOut scale + diffusion scale) ≤ right)
          (solve
            ( shift ∷ endpointIn scale
            ∷ etaNear scale ∷ etaCommutator scale ∷ diffusion scale
            ∷ lowerEnstrophy scale ∷ farField scale
            ∷ incrementDefect scale ∷ commutatorLocalization scale
            ∷ localization scale ∷ []))
          shiftedLeft)

    leftMeaning :
      (endpointOut scale + diffusion scale) + shift
      ≡ filteredScaleLeft scale
    leftMeaning =
      solve
        ( endpointOut scale ∷ diffusion scale
        ∷ etaNear scale ∷ etaCommutator scale ∷ [])

    rightMeaning :
      (endpointIn scale
        +
        ((etaNear scale * diffusion scale + lowerEnstrophy scale)
          + farField scale
          +
          (etaCommutator scale * diffusion scale
            + incrementDefect scale + commutatorLocalization scale)
          + localization scale))
      + shift
      ≡ filteredScaleRight scale
    rightMeaning =
      solve
        ( endpointIn scale ∷ diffusion scale
        ∷ etaNear scale ∷ etaCommutator scale
        ∷ lowerEnstrophy scale ∷ farField scale
        ∷ incrementDefect scale ∷ localization scale
        ∷ commutatorLocalization scale ∷ [])
  in
  subst
    (λ left → left ≤ filteredScaleRight scale)
    leftMeaning
    (subst
      (λ right →
        (endpointOut scale + diffusion scale) + shift ≤ right)
      rightMeaning
      shifted)

record WeightedFilteredScale : Set where
  constructor weightedFilteredScale
  field
    weight : ℚ
    weightNonnegative : 0ℚ ≤ weight
    scale : FilteredEnstrophyScale

open WeightedFilteredScale public

weightedLeft : List WeightedFilteredScale → ℚ
weightedLeft [] = 0ℚ
weightedLeft (cell ∷ cells) =
  weight cell * filteredScaleLeft (scale cell) + weightedLeft cells

weightedRight : List WeightedFilteredScale → ℚ
weightedRight [] = 0ℚ
weightedRight (cell ∷ cells) =
  weight cell * filteredScaleRight (scale cell) + weightedRight cells

localWeightedFilteredSurplus :
  ∀ cell →
  weight cell * filteredScaleLeft (scale cell)
  ≤ weight cell * filteredScaleRight (scale cell)
localWeightedFilteredSurplus cell =
  L2.nonnegativeProductMonotone
    (weightNonnegative cell)
    (filteredScaleLeftNonnegative (scale cell))
    (weightNonnegative cell)
    (filteredScaleRightNonnegative (scale cell))
    ℚₚ.≤-refl
    (filteredEnstrophySurplusBound (scale cell))

finiteWeightedFilteredSurplus :
  ∀ cells → weightedLeft cells ≤ weightedRight cells
finiteWeightedFilteredSurplus [] = ℚₚ.≤-refl
finiteWeightedFilteredSurplus (cell ∷ cells) =
  ℚₚ.+-mono-≤
    (localWeightedFilteredSurplus cell)
    (finiteWeightedFilteredSurplus cells)

record FilteredSurplusAuthorityBoundary : Set where
  constructor filteredSurplusAuthorityBoundary
  field
    signedScaleAlgebraProved : Set
    finiteWeightedSummationProved : Set
    unweightedFarFieldCarlesonClosureProved : Set
    infiniteIncrementDefectSummabilityProved : Set
    localizationSummabilityProved : Set

canonicalFilteredSurplusAuthorityBoundary :
  FilteredSurplusAuthorityBoundary
canonicalFilteredSurplusAuthorityBoundary =
  filteredSurplusAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
