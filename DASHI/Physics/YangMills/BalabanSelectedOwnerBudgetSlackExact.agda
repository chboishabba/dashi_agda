module DASHI.Physics.YangMills.BalabanSelectedOwnerBudgetSlackExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Replace the equality-only four-owner budget interface by a robust
-- less-than-or-equal interface with explicit slack
--
--   Delta_YM = 55/18874368 - (c_loc+c_tr+c_near+c_far).
--
-- The slack is allocated to the far owner only when converting to the legacy
-- equality reducer.  Since the physical charge and the slack are nonnegative,
-- the enlarged far coefficient remains a valid upper bound.  This lets exact
-- or interval-generated estimates expose unused margin instead of silently
-- spending the whole singleton allowance.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership

ownerCoefficientTotal :
  ℚ → ℚ → ℚ → ℚ → ℚ
ownerCoefficientTotal localization transport near far =
  localization + transport + near + far

ownerBudgetSlack :
  ℚ → ℚ → ℚ → ℚ → ℚ
ownerBudgetSlack localization transport near far =
  Selector.remainingSingletonCoefficient
  - ownerCoefficientTotal localization transport near far

ownerTotalPlusSlackExact : ∀ localization transport near far →
  ownerCoefficientTotal localization transport near far
    + ownerBudgetSlack localization transport near far
  ≡ Selector.remainingSingletonCoefficient
ownerTotalPlusSlackExact localization transport near far =
  ℚRing.solve-∀ localization transport near far

record CorrelatedOwnerBoundsWithSlack
    (family : Ownership.CorrelatedResidualFamily)
    (charge : ℚ) : Set where
  field
    localizationCoefficient transportCoefficient
      nearGreenCoefficient farGreenCoefficient : ℚ

    localizationUpper :
      Ownership.ownerContribution family Ownership.localizationOwner
      ≤ localizationCoefficient * charge
    transportUpper :
      Ownership.ownerContribution family Ownership.transportOwner
      ≤ transportCoefficient * charge
    nearGreenUpper :
      Ownership.ownerContribution family Ownership.nearGreenOwner
      ≤ nearGreenCoefficient * charge
    farGreenUpper :
      Ownership.ownerContribution family Ownership.farGreenOwner
      ≤ farGreenCoefficient * charge

    coefficientTotalFits :
      ownerCoefficientTotal localizationCoefficient transportCoefficient
        nearGreenCoefficient farGreenCoefficient
      ≤ Selector.remainingSingletonCoefficient

    chargeNonnegative : 0ℚ ≤ charge
open CorrelatedOwnerBoundsWithSlack public

slackNonnegative :
  ∀ {family charge}
    (bounds : CorrelatedOwnerBoundsWithSlack family charge) →
  0ℚ ≤ ownerBudgetSlack
    (localizationCoefficient bounds)
    (transportCoefficient bounds)
    (nearGreenCoefficient bounds)
    (farGreenCoefficient bounds)
slackNonnegative bounds =
  ℚP.p≤q⇒0≤q-p (coefficientTotalFits bounds)

farCoefficientBelowSlackCompletion :
  ∀ {family charge}
    (bounds : CorrelatedOwnerBoundsWithSlack family charge) →
  farGreenCoefficient bounds
  ≤ farGreenCoefficient bounds
      + ownerBudgetSlack
          (localizationCoefficient bounds)
          (transportCoefficient bounds)
          (nearGreenCoefficient bounds)
          (farGreenCoefficient bounds)
farCoefficientBelowSlackCompletion bounds =
  let
    instance
      slackNN : NonNegative
        (ownerBudgetSlack
          (localizationCoefficient bounds)
          (transportCoefficient bounds)
          (nearGreenCoefficient bounds)
          (farGreenCoefficient bounds))
      slackNN = nonNegative (slackNonnegative bounds)
  in
  ℚP.p≤p+q
    (farGreenCoefficient bounds)
    (ownerBudgetSlack
      (localizationCoefficient bounds)
      (transportCoefficient bounds)
      (nearGreenCoefficient bounds)
      (farGreenCoefficient bounds))

farUpperAfterSlackCompletion :
  ∀ {family charge}
    (bounds : CorrelatedOwnerBoundsWithSlack family charge) →
  Ownership.ownerContribution family Ownership.farGreenOwner
  ≤ (farGreenCoefficient bounds
      + ownerBudgetSlack
          (localizationCoefficient bounds)
          (transportCoefficient bounds)
          (nearGreenCoefficient bounds)
          (farGreenCoefficient bounds))
      * charge
farUpperAfterSlackCompletion {charge = charge} bounds =
  let
    instance
      chargeNN : NonNegative charge
      chargeNN = nonNegative (chargeNonnegative bounds)

    enlarged = ℚP.*-monoʳ-≤-nonNeg charge
      (farCoefficientBelowSlackCompletion bounds)
  in
  ℚP.≤-trans (farGreenUpper bounds) enlarged

slackCompletesLegacyOwnerBudget :
  ∀ {family charge} →
  CorrelatedOwnerBoundsWithSlack family charge →
  Ownership.CorrelatedOwnerBudgets family charge
slackCompletesLegacyOwnerBudget bounds = record
  { Ownership.CorrelatedOwnerBudgets.localizationCoefficient =
      localizationCoefficient bounds
  ; Ownership.CorrelatedOwnerBudgets.transportCoefficient =
      transportCoefficient bounds
  ; Ownership.CorrelatedOwnerBudgets.nearGreenCoefficient =
      nearGreenCoefficient bounds
  ; Ownership.CorrelatedOwnerBudgets.farGreenCoefficient =
      farGreenCoefficient bounds
      + ownerBudgetSlack
          (localizationCoefficient bounds)
          (transportCoefficient bounds)
          (nearGreenCoefficient bounds)
          (farGreenCoefficient bounds)
  ; Ownership.CorrelatedOwnerBudgets.localizationUpper =
      localizationUpper bounds
  ; Ownership.CorrelatedOwnerBudgets.transportUpper =
      transportUpper bounds
  ; Ownership.CorrelatedOwnerBudgets.nearGreenUpper =
      nearGreenUpper bounds
  ; Ownership.CorrelatedOwnerBudgets.farGreenUpper =
      farUpperAfterSlackCompletion bounds
  ; Ownership.CorrelatedOwnerBudgets.coefficientsCloseSingletonBudget =
      let
        localization = localizationCoefficient bounds
        transport = transportCoefficient bounds
        near = nearGreenCoefficient bounds
        far = farGreenCoefficient bounds
      in
      trans
        (ℚRing.solve-∀ localization transport near far)
        (ownerTotalPlusSlackExact localization transport near far) }

correlatedResidualClosesWithUnusedSlack :
  ∀ {family charge} →
  Ownership.ExactCorrelatedCancellation family →
  CorrelatedOwnerBoundsWithSlack family charge →
  Ownership.correlatedResidualTotal family
  ≤ Selector.remainingSingletonCoefficient * charge
correlatedResidualClosesWithUnusedSlack cancellation bounds =
  Ownership.correlatedResidualClosesSingletonBudget
    cancellation (slackCompletesLegacyOwnerBudget bounds)

selectedOwnerBudgetSlackLevel : ProofLevel
selectedOwnerBudgetSlackLevel = machineChecked
