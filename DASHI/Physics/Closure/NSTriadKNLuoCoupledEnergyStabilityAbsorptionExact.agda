module DASHI.Physics.Closure.NSTriadKNLuoCoupledEnergyStabilityAbsorptionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / AUDIT CONTEXT
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO.  DOI: none located in the public record.
-- Status: manuscript/preprint.  The coupled-functional architecture is
-- audited here; no claimed PDE estimate is imported.
--
-- Shin-ichi Inage,
-- "Conditional Regularity of the Three-Dimensional Navier-Stokes Equations
-- via High-High Triadic Absorption".
-- DOI: 10.20944/preprints202603.1591.v1.
-- Status: non-peer-reviewed preprint.
--
-- Roger Temam,
-- "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- The exact cancellation mechanism behind a coupled energy/stability
-- functional is proved.  If
--
--   E' + D <= N + R_E
--   alpha S' <= -N + R_S,
--
-- then
--
--   (E' + alpha S') + D <= R_E + R_S.
--
-- If the combined residual is itself bounded by eta D, the exact strict
-- margin follows:
--
--   (E' + alpha S') + (1-eta) D <= 0.
--
-- This isolates the real producer.  Algebraic cancellation is complete;
-- proving the stability-response inequality and the residual absorption from
-- the Navier-Stokes equations is not supplied by trace-free spectral algebra.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

record CoupledDifferentialStep : Set where
  constructor coupledDifferentialStep
  field
    energyDerivative : ℚ
    weightedStabilityDerivative : ℚ
    dissipation : ℚ
    nonlinearTransfer : ℚ
    energyResidual : ℚ
    stabilityResidual : ℚ

    energyBalance :
      energyDerivative + dissipation
      ≤ nonlinearTransfer + energyResidual

    stabilityResponse :
      weightedStabilityDerivative
      ≤ - nonlinearTransfer + stabilityResidual

open CoupledDifferentialStep public

coupledDerivative : CoupledDifferentialStep → ℚ
coupledDerivative step =
  energyDerivative step + weightedStabilityDerivative step

combinedResidual : CoupledDifferentialStep → ℚ
combinedResidual step =
  energyResidual step + stabilityResidual step

coupledCancellation :
  ∀ step →
  coupledDerivative step + dissipation step
  ≤ combinedResidual step
coupledCancellation step =
  let
    summed :
      (energyDerivative step + dissipation step)
        + weightedStabilityDerivative step
      ≤
      (nonlinearTransfer step + energyResidual step)
        + (- nonlinearTransfer step + stabilityResidual step)
    summed =
      ℚₚ.+-mono-≤
        (energyBalance step)
        (stabilityResponse step)

    leftRearranged :
      (energyDerivative step + dissipation step)
        + weightedStabilityDerivative step
      ≡ coupledDerivative step + dissipation step
    leftRearranged =
      solve
        ( energyDerivative step
        ∷ dissipation step
        ∷ weightedStabilityDerivative step
        ∷ [])

    rightCancelled :
      (nonlinearTransfer step + energyResidual step)
        + (- nonlinearTransfer step + stabilityResidual step)
      ≡ combinedResidual step
    rightCancelled =
      solve
        ( nonlinearTransfer step
        ∷ energyResidual step
        ∷ stabilityResidual step
        ∷ [])

    normalizedLeft :
      coupledDerivative step + dissipation step
      ≤
      (nonlinearTransfer step + energyResidual step)
        + (- nonlinearTransfer step + stabilityResidual step)
    normalizedLeft =
      subst
        (λ left →
          left
          ≤
          (nonlinearTransfer step + energyResidual step)
            + (- nonlinearTransfer step + stabilityResidual step))
        leftRearranged
        summed
  in
  subst
    (λ right → coupledDerivative step + dissipation step ≤ right)
    rightCancelled
    normalizedLeft

record ResidualAbsorption (step : CoupledDifferentialStep) : Set where
  constructor residualAbsorption
  field
    eta : ℚ
    oneMinusEtaNonnegative : 0ℚ ≤ 1ℚ - eta
    residualBelowEtaDissipation :
      combinedResidual step ≤ eta * dissipation step

open ResidualAbsorption public

strictCoupledAbsorption :
  ∀ step →
  (absorption : ResidualAbsorption step) →
  coupledDerivative step
    + (1ℚ - eta absorption) * dissipation step
  ≤ 0ℚ
strictCoupledAbsorption step absorption =
  let
    throughResidual :
      coupledDerivative step + dissipation step
      ≤ eta absorption * dissipation step
    throughResidual =
      ℚₚ.≤-trans
        (coupledCancellation step)
        (residualBelowEtaDissipation absorption)

    shifted :
      (- (eta absorption * dissipation step))
        + (coupledDerivative step + dissipation step)
      ≤
      (- (eta absorption * dissipation step))
        + eta absorption * dissipation step
    shifted =
      ℚₚ.+-monoʳ-≤
        (- (eta absorption * dissipation step))
        throughResidual

    leftClosed :
      (- (eta absorption * dissipation step))
        + (coupledDerivative step + dissipation step)
      ≡
      coupledDerivative step
        + (1ℚ - eta absorption) * dissipation step
    leftClosed =
      solve
        ( coupledDerivative step
        ∷ eta absorption
        ∷ dissipation step
        ∷ [])

    rightClosed :
      (- (eta absorption * dissipation step))
        + eta absorption * dissipation step
      ≡ 0ℚ
    rightClosed =
      solve (eta absorption ∷ dissipation step ∷ [])

    normalizedLeft :
      coupledDerivative step
        + (1ℚ - eta absorption) * dissipation step
      ≤
      (- (eta absorption * dissipation step))
        + eta absorption * dissipation step
    normalizedLeft =
      subst
        (λ left →
          left
          ≤
          (- (eta absorption * dissipation step))
            + eta absorption * dissipation step)
        leftClosed
        shifted
  in
  subst
    (λ right →
      coupledDerivative step
        + (1ℚ - eta absorption) * dissipation step
      ≤ right)
    rightClosed
    normalizedLeft

record CoupledAbsorptionProducerBoundary : Set where
  constructor coupledAbsorptionProducerBoundary
  field
    cancellationAlgebraClosed : Set
    stabilityResponseProducedFromNavierStokes : Set
    residualAbsorptionProducedFromNavierStokes : Set
    spectralRigidityAloneProducesBoth : Set

canonicalCoupledAbsorptionProducerBoundary :
  CoupledAbsorptionProducerBoundary
canonicalCoupledAbsorptionProducerBoundary =
  coupledAbsorptionProducerBoundary
    ⊤
    ⊥
    ⊥
    ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
