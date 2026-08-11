module DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualBoundsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Expose the two named physical inequalities requested by the Round-40 proof
-- order while retaining cancellation-before-majorisation.  The localization
-- side groups the raw-localization and transport owners; the multiplier side
-- groups the near- and far-Green owners.  Their coefficient sums, rather than
-- an arbitrary 27+28 allocation, are the quantities optimized physically.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership

rawLocalizationSpillover : Ownership.CorrelatedResidualFamily → ℚ
rawLocalizationSpillover family =
  Ownership.ownerContribution family Ownership.localizationOwner
  + Ownership.ownerContribution family Ownership.transportOwner

selectedMultiplierDefectContribution :
  Ownership.CorrelatedResidualFamily → ℚ
selectedMultiplierDefectContribution family =
  Ownership.ownerContribution family Ownership.nearGreenOwner
  + Ownership.ownerContribution family Ownership.farGreenOwner

rawLocalizationCoefficient :
  ∀ {family charge} →
  Ownership.CorrelatedOwnerBudgets family charge → ℚ
rawLocalizationCoefficient budgets =
  Ownership.localizationCoefficient budgets
  + Ownership.transportCoefficient budgets

multiplierDefectCoefficient :
  ∀ {family charge} →
  Ownership.CorrelatedOwnerBudgets family charge → ℚ
multiplierDefectCoefficient budgets =
  Ownership.nearGreenCoefficient budgets
  + Ownership.farGreenCoefficient budgets

rawLocalizationSpilloverUpper :
  ∀ {family charge}
    (budgets : Ownership.CorrelatedOwnerBudgets family charge) →
  rawLocalizationSpillover family
  ≤ rawLocalizationCoefficient budgets * charge
rawLocalizationSpilloverUpper {family} {charge} budgets =
  subst
    (λ upper → rawLocalizationSpillover family ≤ upper)
    (ℚRing.solve-∀
      (Ownership.localizationCoefficient budgets)
      (Ownership.transportCoefficient budgets)
      charge)
    (ℚP.+-mono-≤
      (Ownership.localizationUpper budgets)
      (Ownership.transportUpper budgets))

selectedMultiplierDefectPairingUpper :
  ∀ {family charge}
    (budgets : Ownership.CorrelatedOwnerBudgets family charge) →
  selectedMultiplierDefectContribution family
  ≤ multiplierDefectCoefficient budgets * charge
selectedMultiplierDefectPairingUpper {family} {charge} budgets =
  subst
    (λ upper → selectedMultiplierDefectContribution family ≤ upper)
    (ℚRing.solve-∀
      (Ownership.nearGreenCoefficient budgets)
      (Ownership.farGreenCoefficient budgets)
      charge)
    (ℚP.+-mono-≤
      (Ownership.nearGreenUpper budgets)
      (Ownership.farGreenUpper budgets))

selectedCorrelatedResidualAtomCancellationExact :
  ∀ {family} →
  Ownership.ExactCorrelatedCancellation family →
  Ownership.correlatedResidualTotal family
  ≡ rawLocalizationSpillover family
    + selectedMultiplierDefectContribution family
selectedCorrelatedResidualAtomCancellationExact {family} cancellation =
  let
    removed =
      Ownership.exactCorrelatedCancellationRemovedBeforeMajorisation
        cancellation
  in
  subst
    (λ right →
      Ownership.correlatedResidualTotal family ≡ right)
    (ℚRing.solve-∀
      (Ownership.ownerContribution family Ownership.localizationOwner)
      (Ownership.ownerContribution family Ownership.transportOwner)
      (Ownership.ownerContribution family Ownership.nearGreenOwner)
      (Ownership.ownerContribution family Ownership.farGreenOwner))
    removed

selectedCorrelatedResidualBoundsLevel : ProofLevel
selectedCorrelatedResidualBoundsLevel = machineChecked
