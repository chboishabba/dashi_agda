module DASHI.Physics.Closure.NSTriadKNPositiveTransferOffPacketCoercivityRound99Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND99 / POSITIVE-TRANSFER OFF-PACKET CLOSURE
--
-- Round98 proved the exact cross-multiplied ratio numerator
--
--   R_num = -F E + E_off D_P - D_off E_P.
--
-- The compact-Gamma derivative surface is explicitly the resolved
-- positive-transfer branch.  Hence F >= 0 on the branch where Gamma is used.
-- Since total energy E >= 0, the apparently surviving packet-outflow term is
-- then NONPOSITIVE.  Combining this sign with Round98's exact spectral
-- cross-dissipation theorem gives
--
--   -F E + E_off D_P - D_off E_P
--     <= -(lambda_off-lambda_P) E_off E_P.
--
-- Therefore there is no additional nonlinear off-packet occupation estimate
-- on the positive compact-Gamma branch.  The only required quantitative input
-- is the already-isolated packet/off-packet spectral gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNOffPacketSpectralCrossDissipationRound98Exact as Spectral

positiveTransferContributionNonpositive :
  ∀ {flux totalEnergy : ℚ} →
  0ℚ ≤ flux →
  0ℚ ≤ totalEnergy →
  (- flux) * totalEnergy ≤ 0ℚ
positiveTransferContributionNonpositive {flux} {totalEnergy} fluxNN energyNN =
  let
    productNN : 0ℚ ≤ flux * totalEnergy
    productNN =
      let instance
        fNN = nonNegative fluxNN
        eNN = nonNegative energyNN
        pNN = ℚP.nonNeg*nonNeg⇒nonNeg flux totalEnergy
      in ℚP.nonNegative⁻¹ _

    negProductNonpositive : -(flux * totalEnergy) ≤ 0ℚ
    negProductNonpositive =
      subst
        (λ lower → lower ≤ 0ℚ)
        (solve (flux * totalEnergy ∷ []))
        productNN
  in
  subst
    (λ lower → lower ≤ 0ℚ)
    (solve (flux ∷ totalEnergy ∷ []))
    negProductNonpositive

positiveTransferOffPacketSpectralCoercivity :
  (D : Spectral.SpectralCrossDissipationDatum) →
  (gap : Spectral.PositiveSpectralGap D) →
  (flux totalEnergy : ℚ) →
  0ℚ ≤ flux →
  0ℚ ≤ totalEnergy →
  (- flux) * totalEnergy
    + (Spectral.offPacketEnergy D * Spectral.packetDissipation D
      - Spectral.offPacketDissipation D * Spectral.packetEnergy D)
  ≤ - ((Spectral.offPacketFrequencyFloor D
          - Spectral.packetFrequencyCeiling D)
        * (Spectral.offPacketEnergy D * Spectral.packetEnergy D))
positiveTransferOffPacketSpectralCoercivity D gap flux totalEnergy fluxNN energyNN =
  let
    fluxTerm = positiveTransferContributionNonpositive fluxNN energyNN
    crossTerm = Spectral.spectralCrossDissipationCoercive D
    added = ℚP.+-mono-≤ fluxTerm crossTerm
  in
  subst
    (λ lower → lower ≤
      - ((Spectral.offPacketFrequencyFloor D
          - Spectral.packetFrequencyCeiling D)
        * (Spectral.offPacketEnergy D * Spectral.packetEnergy D)))
    (solve
      ( Spectral.offPacketFrequencyFloor D
      ∷ Spectral.packetFrequencyCeiling D
      ∷ Spectral.offPacketEnergy D
      ∷ Spectral.packetEnergy D
      ∷ []))
    added

positiveTransferOffPacketNumeratorNonpositive :
  (D : Spectral.SpectralCrossDissipationDatum) →
  (gap : Spectral.PositiveSpectralGap D) →
  (flux totalEnergy : ℚ) →
  0ℚ ≤ flux →
  0ℚ ≤ totalEnergy →
  (- flux) * totalEnergy
    + (Spectral.offPacketEnergy D * Spectral.packetDissipation D
      - Spectral.offPacketDissipation D * Spectral.packetEnergy D)
  ≤ 0ℚ
positiveTransferOffPacketNumeratorNonpositive D gap flux totalEnergy fluxNN energyNN =
  ℚP.≤-trans
    (positiveTransferOffPacketSpectralCoercivity
      D gap flux totalEnergy fluxNN energyNN)
    negativeGapCostNonpositive
  where
  gapEnergyNN :
    0ℚ ≤ (Spectral.offPacketFrequencyFloor D
      - Spectral.packetFrequencyCeiling D)
      * (Spectral.offPacketEnergy D * Spectral.packetEnergy D)
  gapEnergyNN =
    let
      energiesNN : 0ℚ ≤ Spectral.offPacketEnergy D * Spectral.packetEnergy D
      energiesNN =
        let instance
          oNN = nonNegative (Spectral.offPacketEnergyNonnegative D)
          pNN = nonNegative (Spectral.packetEnergyNonnegative D)
          epNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (Spectral.offPacketEnergy D) (Spectral.packetEnergy D)
        in ℚP.nonNegative⁻¹ _
    in
    let instance
      gNN = nonNegative (Spectral.gapPositive gap)
      eNN = nonNegative energiesNN
      geNN = ℚP.nonNeg*nonNeg⇒nonNeg
        (Spectral.offPacketFrequencyFloor D - Spectral.packetFrequencyCeiling D)
        (Spectral.offPacketEnergy D * Spectral.packetEnergy D)
    in ℚP.nonNegative⁻¹ _

  negativeGapCostNonpositive :
    - ((Spectral.offPacketFrequencyFloor D
        - Spectral.packetFrequencyCeiling D)
      * (Spectral.offPacketEnergy D * Spectral.packetEnergy D)) ≤ 0ℚ
  negativeGapCostNonpositive =
    subst
      (λ lower → lower ≤ 0ℚ)
      (solve
        ((Spectral.offPacketFrequencyFloor D
          - Spectral.packetFrequencyCeiling D)
          * (Spectral.offPacketEnergy D * Spectral.packetEnergy D) ∷ []))
      gapEnergyNN

round99PositiveCompactGammaBranchKillsPacketOutflowCost : Bool
round99PositiveCompactGammaBranchKillsPacketOutflowCost = true

round99AdditionalOffPacketNonlinearOccupationLemmaRequired : Bool
round99AdditionalOffPacketNonlinearOccupationLemmaRequired = false

round99OffPacketRatioIsSpectrallyCoerciveOnPositiveTransferBranch : Bool
round99OffPacketRatioIsSpectrallyCoerciveOnPositiveTransferBranch = true

round99AdditionalOffPacketNonlinearOccupationLemmaRequiredIsFalse :
  round99AdditionalOffPacketNonlinearOccupationLemmaRequired ≡ false
round99AdditionalOffPacketNonlinearOccupationLemmaRequiredIsFalse = refl
