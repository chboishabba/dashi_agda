module DASHI.Physics.Closure.NSTriadKNAdverseEpisodeSignedForcingRound106Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- ROUND106 / ADVERSE EPISODES KEEP THE FORCING SIGN
--
-- Apply the signed time normal form only on one connected adverse phase
-- episode.  Orient the phase so that the static normal-form weight g is
-- nonnegative and adverse production means A>=0.  The exact identity is
--
--   nu integral P = g A(start) - g A(end) + g integral F.
--
-- Since A(end)>=0, the terminal term is favourable and may be dropped:
--
--   nu integral P <= g A(start) + g integral F.
--
-- Crucially, `integral F` is SIGNED.  Round105's replacement by
-- `integral F_+` is unnecessary.  Interior adverse episodes start and end at
-- A=0, so their production is paid exactly by the signed forcing integral.
-- Only an episode touching the initial time carries an initial phase boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNSignedPhaseTimeNormalFormRound106Exact as Normal

record AdverseSignedForcingEpisode : Set where
  constructor adverse-signed-forcing-episode
  field
    cell : Normal.IntegratedSignedPhaseCell
    weightNonnegative : 0ℚ ≤ Normal.normalFormWeight cell
    terminalAmplitudeNonnegative : 0ℚ ≤ Normal.terminalAmplitude cell

open AdverseSignedForcingEpisode public

adverseEpisodePaidByInitialPhaseAndSignedForcing :
  (E : AdverseSignedForcingEpisode) →
  Normal.viscosity (cell E) * Normal.integratedCriticalProduction (cell E)
  ≤ Normal.normalFormWeight (cell E) * Normal.initialAmplitude (cell E)
      + Normal.normalFormWeight (cell E) * Normal.integratedForcing (cell E)
adverseEpisodePaidByInitialPhaseAndSignedForcing E =
  let
    C = cell E
    g = Normal.normalFormWeight C
    a0 = Normal.initialAmplitude C
    aT = Normal.terminalAmplitude C
    f = Normal.integratedForcing C
    exact = Normal.signedPhaseTimeNormalForm C

    terminalProductNN : 0ℚ ≤ g * aT
    terminalProductNN =
      let
        instance
          gNN = nonNegative (weightNonnegative E)
          aNN = nonNegative (terminalAmplitudeNonnegative E)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg g aT
      in ℚP.nonNegative⁻¹ (g * aT)

    negTerminalRaw : -(g * aT) ≤ - 0ℚ
    negTerminalRaw = ℚP.neg-antimono-≤ terminalProductNN

    negTerminal≤Zero : -(g * aT) ≤ 0ℚ
    negTerminal≤Zero =
      subst (λ right → -(g * aT) ≤ right)
        (solve []) negTerminalRaw

    first = ℚP.+-mono-≤ ℚP.≤-refl negTerminal≤Zero
    second = ℚP.+-mono-≤ first ℚP.≤-refl

    dropNegativeTerminal :
      g * a0 + (- (g * aT)) + g * f
      ≤ g * a0 + g * f
    dropNegativeTerminal =
      subst
        (λ right →
          g * a0 + (- (g * aT)) + g * f ≤ right)
        (cong (λ y → y + g * f) (ℚP.+-identityʳ (g * a0)))
        second
  in
  subst
    (λ left → left ≤ g * a0 + g * f)
    (sym exact)
    dropNegativeTerminal

record InteriorAdverseSignedForcingEpisode : Set where
  constructor interior-adverse-signed-forcing-episode
  field
    episode : AdverseSignedForcingEpisode
    initialAmplitudeZero : Normal.initialAmplitude (cell episode) ≡ 0ℚ
    terminalAmplitudeZero : Normal.terminalAmplitude (cell episode) ≡ 0ℚ

open InteriorAdverseSignedForcingEpisode public

interiorEpisodePaidExactlyBySignedForcing :
  (E : InteriorAdverseSignedForcingEpisode) →
  Normal.viscosity (cell (episode E))
    * Normal.integratedCriticalProduction (cell (episode E))
  ≡ Normal.normalFormWeight (cell (episode E))
      * Normal.integratedForcing (cell (episode E))
interiorEpisodePaidExactlyBySignedForcing E
  rewrite Normal.signedPhaseTimeNormalForm (cell (episode E))
        | initialAmplitudeZero E
        | terminalAmplitudeZero E
        | ℚP.*-zeroʳ (Normal.normalFormWeight (cell (episode E))) =
  trans
    (cong
      (λ y → y + Normal.normalFormWeight (cell (episode E))
        * Normal.integratedForcing (cell (episode E)))
      (solve []))
    (ℚP.+-identityˡ
      (Normal.normalFormWeight (cell (episode E))
        * Normal.integratedForcing (cell (episode E))))

sumEpisodeProduction : List AdverseSignedForcingEpisode → ℚ
sumEpisodeProduction [] = 0ℚ
sumEpisodeProduction (E ∷ Es) =
  Normal.integratedCriticalProduction (cell E) + sumEpisodeProduction Es

sumEpisodeInitialBoundary : List AdverseSignedForcingEpisode → ℚ
sumEpisodeInitialBoundary [] = 0ℚ
sumEpisodeInitialBoundary (E ∷ Es) =
  Normal.normalFormWeight (cell E) * Normal.initialAmplitude (cell E)
    + sumEpisodeInitialBoundary Es

sumEpisodeSignedForcing : List AdverseSignedForcingEpisode → ℚ
sumEpisodeSignedForcing [] = 0ℚ
sumEpisodeSignedForcing (E ∷ Es) =
  Normal.normalFormWeight (cell E) * Normal.integratedForcing (cell E)
    + sumEpisodeSignedForcing Es

record CommonViscosityAdverseEpisodes : Set where
  constructor common-viscosity-adverse-episodes
  field
    viscosity : ℚ
    episodes : List AdverseSignedForcingEpisode
    sameViscosity : (E : AdverseSignedForcingEpisode) →
      Normal.viscosity (cell E) ≡ viscosity

open CommonViscosityAdverseEpisodes public

finiteAdverseEpisodesPaidBySignedForcing :
  (N : CommonViscosityAdverseEpisodes) →
  viscosity N * sumEpisodeProduction (episodes N)
  ≤ sumEpisodeInitialBoundary (episodes N)
      + sumEpisodeSignedForcing (episodes N)
finiteAdverseEpisodesPaidBySignedForcing N = go (episodes N)
  where
  nu = viscosity N

  go : (Es : List AdverseSignedForcingEpisode) →
    nu * sumEpisodeProduction Es
    ≤ sumEpisodeInitialBoundary Es + sumEpisodeSignedForcing Es
  go [] = ℚP.≤-refl
  go (E ∷ Es)
    rewrite sameViscosity N E =
    let
      head = adverseEpisodePaidByInitialPhaseAndSignedForcing E
      tail = go Es
      added = ℚP.+-mono-≤ head tail
      leftMeaning :
        Normal.viscosity (cell E)
          * Normal.integratedCriticalProduction (cell E)
          + nu * sumEpisodeProduction Es
        ≡ nu * sumEpisodeProduction (E ∷ Es)
      leftMeaning = solve
        (nu ∷ Normal.integratedCriticalProduction (cell E)
         ∷ sumEpisodeProduction Es ∷ [])
      rightMeaning :
        (Normal.normalFormWeight (cell E) * Normal.initialAmplitude (cell E)
          + Normal.normalFormWeight (cell E) * Normal.integratedForcing (cell E))
          + (sumEpisodeInitialBoundary Es + sumEpisodeSignedForcing Es)
        ≡ sumEpisodeInitialBoundary (E ∷ Es)
          + sumEpisodeSignedForcing (E ∷ Es)
      rightMeaning = solve
        ( Normal.normalFormWeight (cell E)
        ∷ Normal.initialAmplitude (cell E)
        ∷ Normal.integratedForcing (cell E)
        ∷ sumEpisodeInitialBoundary Es ∷ sumEpisodeSignedForcing Es ∷ [])
    in
    subst
      (λ left → left ≤
        sumEpisodeInitialBoundary (E ∷ Es)
          + sumEpisodeSignedForcing (E ∷ Es))
      leftMeaning
      (subst
        (λ right →
          Normal.viscosity (cell E)
            * Normal.integratedCriticalProduction (cell E)
            + nu * sumEpisodeProduction Es ≤ right)
        rightMeaning added)

round106AdverseEpisodeKeepsSignedForcing : Bool
round106AdverseEpisodeKeepsSignedForcing = true

round106PositivePartOfNetworkForcingRequired : Bool
round106PositivePartOfNetworkForcingRequired = false

round106InteriorAdverseEpisodeHasOnlySignedForcingCost : Bool
round106InteriorAdverseEpisodeHasOnlySignedForcingCost = true

round106AdverseEpisodeKeepsSignedForcingIsTrue :
  round106AdverseEpisodeKeepsSignedForcing ≡ true
round106AdverseEpisodeKeepsSignedForcingIsTrue = refl

round106PositivePartOfNetworkForcingRequiredIsFalse :
  round106PositivePartOfNetworkForcingRequired ≡ false
round106PositivePartOfNetworkForcingRequiredIsFalse = refl

round106InteriorAdverseEpisodeHasOnlySignedForcingCostIsTrue :
  round106InteriorAdverseEpisodeHasOnlySignedForcingCost ≡ true
round106InteriorAdverseEpisodeHasOnlySignedForcingCostIsTrue = refl
