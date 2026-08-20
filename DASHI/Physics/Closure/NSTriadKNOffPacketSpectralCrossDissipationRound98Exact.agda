module DASHI.Physics.Closure.NSTriadKNOffPacketSpectralCrossDissipationRound98Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphaël Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Grundlehren der mathematischen Wissenschaften 343, Springer (2011).
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND98 / SPECTRAL CROSS-DISSIPATION COERCIVITY
--
-- Round98's exact off-packet quotient recut leaves the viscous cross term
--
--   E_off D_P - D_off E_P.
--
-- If the selected packet lies below a squared-frequency ceiling lambdaP and
-- the genuinely remote off-packet region lies above a squared-frequency floor
-- lambdaO, then
--
--   D_P   <= lambdaP E_P,
--   D_off >= lambdaO E_off.
--
-- Multiplying by the nonnegative opposite energies and subtracting gives
--
--   E_off D_P - D_off E_P
--      <= -(lambdaO-lambdaP) E_off E_P.
--
-- This theorem is deliberately finite and exact. It isolates the only input
-- that shell geometry must provide: a positive spectral gap. No nonlinear
-- estimate, residence theorem, or Schur bound is needed for this viscous part.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; -_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record SpectralCrossDissipationDatum : Set where
  constructor spectral-cross-dissipation-datum
  field
    packetEnergy offPacketEnergy : ℚ
    packetDissipation offPacketDissipation : ℚ
    packetFrequencyCeiling offPacketFrequencyFloor : ℚ

    packetEnergyNonnegative : 0ℚ ≤ packetEnergy
    offPacketEnergyNonnegative : 0ℚ ≤ offPacketEnergy
    packetFrequencyCeilingNonnegative : 0ℚ ≤ packetFrequencyCeiling
    offPacketFrequencyFloorNonnegative : 0ℚ ≤ offPacketFrequencyFloor

    packetDissipationUpper :
      packetDissipation ≤ packetFrequencyCeiling * packetEnergy
    offPacketDissipationLower :
      offPacketFrequencyFloor * offPacketEnergy ≤ offPacketDissipation

open SpectralCrossDissipationDatum public

packetUpperAfterOffEnergyWeight :
  (D : SpectralCrossDissipationDatum) →
  offPacketEnergy D * packetDissipation D
  ≤ offPacketEnergy D *
      (packetFrequencyCeiling D * packetEnergy D)
packetUpperAfterOffEnergyWeight D =
  let instance offNN = nonNegative (offPacketEnergyNonnegative D)
  in ℚP.*-monoˡ-≤-nonNeg (offPacketEnergy D) (packetDissipationUpper D)

offLowerAfterPacketEnergyWeight :
  (D : SpectralCrossDissipationDatum) →
  (offPacketFrequencyFloor D * offPacketEnergy D) * packetEnergy D
  ≤ offPacketDissipation D * packetEnergy D
offLowerAfterPacketEnergyWeight D =
  let instance packetNN = nonNegative (packetEnergyNonnegative D)
  in ℚP.*-monoʳ-≤-nonNeg (packetEnergy D) (offPacketDissipationLower D)

-- Elementary subtraction monotonicity, proved only from +-monotonicity and
-- ring normalization so this file does not depend on a large order wrapper.
subtractMonotone : ∀ {a b c d : ℚ} → a ≤ b → c ≤ d → a - d ≤ b - c
subtractMonotone {a} {b} {c} {d} a≤b c≤d =
  let
    negOrder : - d ≤ - c
    negOrder =
      let
        shifted : 0ℚ ≤ d - c
        shifted = subst
          (λ x → x ≤ d - c)
          (solve (c ∷ []))
          (ℚP.+-monoʳ-≤ (- c) c≤d)
      in
      subst
        (λ x → x ≤ - c)
        (solve (d ∷ c ∷ []))
        (ℚP.+-monoˡ-≤ (- d) shifted)
    added = ℚP.+-mono-≤ a≤b negOrder
  in
  subst
    (λ lhs → lhs ≤ b - c)
    (solve (a ∷ d ∷ []))
    (subst
      (λ rhs → a + (- d) ≤ rhs)
      (solve (b ∷ c ∷ []))
      added)

spectralCrossDissipationCoercive :
  (D : SpectralCrossDissipationDatum) →
  offPacketEnergy D * packetDissipation D
    - offPacketDissipation D * packetEnergy D
  ≤ - ((offPacketFrequencyFloor D - packetFrequencyCeiling D)
        * (offPacketEnergy D * packetEnergy D))
spectralCrossDissipationCoercive D =
  let
    first = packetUpperAfterOffEnergyWeight D
    second = offLowerAfterPacketEnergyWeight D
    bounded = subtractMonotone first second
    normalized :
      offPacketEnergy D *
          (packetFrequencyCeiling D * packetEnergy D)
        - (offPacketFrequencyFloor D * offPacketEnergy D)
          * packetEnergy D
      ≡ - ((offPacketFrequencyFloor D - packetFrequencyCeiling D)
          * (offPacketEnergy D * packetEnergy D))
    normalized = solve
      ( offPacketEnergy D
      ∷ packetEnergy D
      ∷ packetFrequencyCeiling D
      ∷ offPacketFrequencyFloor D
      ∷ [])
  in
  subst
    (λ upper →
      offPacketEnergy D * packetDissipation D
        - offPacketDissipation D * packetEnergy D ≤ upper)
    normalized bounded

record PositiveSpectralGap (D : SpectralCrossDissipationDatum) : Set where
  field
    gapPositive : 0ℚ ≤ offPacketFrequencyFloor D - packetFrequencyCeiling D

open PositiveSpectralGap public

spectralCrossDissipationNonpositive :
  (D : SpectralCrossDissipationDatum) →
  PositiveSpectralGap D →
  offPacketEnergy D * packetDissipation D
    - offPacketDissipation D * packetEnergy D ≤ 0ℚ
spectralCrossDissipationNonpositive D G =
  let
    energiesNN : 0ℚ ≤ offPacketEnergy D * packetEnergy D
    energiesNN =
      let
        instance
          offNN = nonNegative (offPacketEnergyNonnegative D)
          packetNN = nonNegative (packetEnergyNonnegative D)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (offPacketEnergy D) (packetEnergy D)
      in ℚP.nonNegative⁻¹
        (offPacketEnergy D * packetEnergy D)

    gapProductNN :
      0ℚ ≤ (offPacketFrequencyFloor D - packetFrequencyCeiling D)
        * (offPacketEnergy D * packetEnergy D)
    gapProductNN =
      let
        instance
          gapNN = nonNegative (gapPositive G)
          energyNN = nonNegative energiesNN
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (offPacketFrequencyFloor D - packetFrequencyCeiling D)
            (offPacketEnergy D * packetEnergy D)
      in ℚP.nonNegative⁻¹ _

    negativeUpper :
      - ((offPacketFrequencyFloor D - packetFrequencyCeiling D)
        * (offPacketEnergy D * packetEnergy D)) ≤ 0ℚ
    negativeUpper =
      subst
        (λ lower → lower ≤ 0ℚ)
        (solve
          ((offPacketFrequencyFloor D - packetFrequencyCeiling D)
            * (offPacketEnergy D * packetEnergy D) ∷ []))
        gapProductNN
  in
  ℚP.≤-trans (spectralCrossDissipationCoercive D) negativeUpper

round98SpectralCrossDissipationCoercivityClosed : Bool
round98SpectralCrossDissipationCoercivityClosed = true

round98OffPacketViscousCrossTermNeedsNonlinearEstimate : Bool
round98OffPacketViscousCrossTermNeedsNonlinearEstimate = false

round98SpectralCrossDissipationCoercivityClosedIsTrue :
  round98SpectralCrossDissipationCoercivityClosed ≡ true
round98SpectralCrossDissipationCoercivityClosedIsTrue = refl
