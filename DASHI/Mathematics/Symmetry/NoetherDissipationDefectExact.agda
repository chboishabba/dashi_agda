module DASHI.Mathematics.Symmetry.NoetherDissipationDefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Emmy Noether,
-- "Invariante Variationsprobleme",
-- Nachrichten von der Gesellschaft der Wissenschaften zu Göttingen,
-- Mathematisch-Physikalische Klasse (1918), 235--257.
-- No DOI was assigned to the original publication.
--
-- Emmy Noether, translated by M. A. Tavel,
-- "Invariant Variation Problems".
-- DOI: 10.48550/arXiv.physics/0503066.
--
-- DASHI CONTRIBUTION
--
-- Formalize the exact algebraic ledger used after a symmetry/current theorem
-- has supplied a differential identity.  The common form is
--
--   chargeRate + dissipation = residual.
--
-- For Euler or an exact Noether current, dissipation and residual may vanish.
-- For Navier--Stokes, viscosity contributes dissipation.  For gauge theory the
-- relevant derivative is normally covariant, so ordinary, covariant and
-- dissipative conservation are kept as distinct constructors.
--
-- This module does not derive Noether currents from a variational bicomplex,
-- differentiate a Lie-group action, or prove any PDE energy identity.  It
-- checks the downstream cancellation and defect arithmetic exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

data ConservationKind : Set where
  ordinaryConservation : ConservationKind
  covariantConservation : ConservationKind
  dissipativeDefectLaw : ConservationKind

record DefectLedger : Set where
  constructor defectLedger
  field
    chargeRate dissipation residual : ℚ
    balanceLaw : chargeRate + dissipation ≡ residual

open DefectLedger public

rearrangeDissipativeLaw : ∀ rate dissipationTerm residualTerm →
  rate ≡ - dissipationTerm + residualTerm →
  rate + dissipationTerm ≡ residualTerm
rearrangeDissipativeLaw rate dissipationTerm residualTerm law =
  trans
    (cong (_+ dissipationTerm) law)
    (solve (dissipationTerm ∷ residualTerm ∷ []))

ledgerFromRearrangedLaw : ∀ rate dissipationTerm residualTerm →
  rate ≡ - dissipationTerm + residualTerm →
  DefectLedger
ledgerFromRearrangedLaw rate dissipationTerm residualTerm law =
  defectLedger rate dissipationTerm residualTerm
    (rearrangeDissipativeLaw rate dissipationTerm residualTerm law)

combineDefectLaws :
  ∀ rate1 rate2 dissipation1 dissipation2 residual1 residual2 →
  rate1 + dissipation1 ≡ residual1 →
  rate2 + dissipation2 ≡ residual2 →
  (rate1 + rate2) + (dissipation1 + dissipation2)
  ≡ residual1 + residual2
combineDefectLaws
    rate1 rate2 dissipation1 dissipation2 residual1 residual2
    firstLaw secondLaw =
  trans
    (solve
      (rate1 ∷ rate2 ∷ dissipation1 ∷ dissipation2 ∷ []))
    (cong₂ _+_ firstLaw secondLaw)

combineLedgers : DefectLedger → DefectLedger → DefectLedger
combineLedgers firstLedger secondLedger =
  defectLedger
    (chargeRate firstLedger + chargeRate secondLedger)
    (dissipation firstLedger + dissipation secondLedger)
    (residual firstLedger + residual secondLedger)
    (combineDefectLaws
      (chargeRate firstLedger)
      (chargeRate secondLedger)
      (dissipation firstLedger)
      (dissipation secondLedger)
      (residual firstLedger)
      (residual secondLedger)
      (balanceLaw firstLedger)
      (balanceLaw secondLedger))

coupledNonlinearCancellation :
  ∀ energyRate stabilityRate dissipationTerm nonlinearTerm
    energyResidual stabilityResidual →
  energyRate + dissipationTerm
    ≡ nonlinearTerm + energyResidual →
  stabilityRate ≡ - nonlinearTerm + stabilityResidual →
  (energyRate + stabilityRate) + dissipationTerm
    ≡ energyResidual + stabilityResidual
coupledNonlinearCancellation
    energyRate stabilityRate dissipationTerm nonlinearTerm
    energyResidual stabilityResidual energyLaw stabilityLaw =
  trans
    (solve (energyRate ∷ stabilityRate ∷ dissipationTerm ∷ []))
    (trans
      (cong (_+ stabilityRate) energyLaw)
      (trans
        (cong ((nonlinearTerm + energyResidual) +_) stabilityLaw)
        (solve
          (nonlinearTerm ∷ energyResidual ∷ stabilityResidual ∷ []))))

zeroDissipationZeroResidualGivesConservation : ∀ rate →
  rate + 0ℚ ≡ 0ℚ → rate ≡ 0ℚ
zeroDissipationZeroResidualGivesConservation rate law =
  trans (solve (rate ∷ [])) law

exactConservationLedger : DefectLedger
exactConservationLedger =
  defectLedger 0ℚ 0ℚ 0ℚ (solve [])

exactConservationKind : ConservationKind
exactConservationKind = ordinaryConservation

yangMillsBianchiKind : ConservationKind
yangMillsBianchiKind = covariantConservation

navierStokesEnergyKind : ConservationKind
navierStokesEnergyKind = dissipativeDefectLaw
