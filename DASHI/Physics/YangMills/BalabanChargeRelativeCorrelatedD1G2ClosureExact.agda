module DASHI.Physics.YangMills.BalabanChargeRelativeCorrelatedD1G2ClosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Highest-alpha G2 compiler after the exact degree-one falsifier.  The literal
-- residual is already proved to be
--
--   R_corr = (R1-G11) + (R2+R3+R4).
--
-- This module therefore asks for exactly TWO physical charge-relative bounds:
--
--   R1-G11       <= a Q,
--   R2+R3+R4     <= b Q,
--
-- and proves
--
--   R_corr <= (a+b) Q.
--
-- No source norm, defect norm, pseudoinverse row norm, LBB constant, sixteen
-- Green-cell boxes, or positive charge floor appears.  Signed cancellation is
-- retained until the physical enclosure boundary where it is actually needed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as Blocks
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanCanonicalCorrelatedDegreeOneBeforePolarizationExact as D1

record ChargeRelativeCorrelatedD1G2Data
    (Configuration Multiplier : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    pseudoDataAt : Configuration →
      Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationAt : Configuration → KKT.StateVector
    bondFieldAt : Configuration → Physical.PhysicalSU2BondField4
    plaquetteAt : Configuration → Plaquette.Plaquette4

    canonicalInputsAt : ∀ configuration →
      Canonical.CanonicalSubsetCorrelatedAuthorityInputs
        (pseudoDataAt configuration)
        (firstVariationAt configuration)
        (bondFieldAt configuration)
        (plaquetteAt configuration)

    chargeAt : Configuration → ℚ
    chargeNonnegative : ∀ configuration →
      InCertifiedRegion configuration → 0ℚ ≤ chargeAt configuration

    correlatedD1Ratio rawHigherRatio : ℚ

    correlatedD1RelativeSound : ∀ configuration →
      InCertifiedRegion configuration →
      D1.canonicalCorrelatedDegreeOne (canonicalInputsAt configuration)
      ≤ correlatedD1Ratio * chargeAt configuration

    rawHigherRelativeSound : ∀ configuration →
      InCertifiedRegion configuration →
      D1.canonicalRawHigherDegreeTotal (canonicalInputsAt configuration)
      ≤ rawHigherRatio * chargeAt configuration

open ChargeRelativeCorrelatedD1G2Data public

residualRatio :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCorrelatedD1G2Data Configuration Multiplier → ℚ
residualRatio dataSet = correlatedD1Ratio dataSet + rawHigherRatio dataSet

correlatedResidualRelativeBound :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCorrelatedD1G2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (Blocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ residualRatio dataSet * chargeAt dataSet configuration
correlatedResidualRelativeBound dataSet configuration inRegion =
  let
    inputs = canonicalInputsAt dataSet configuration
    d1Bound = correlatedD1RelativeSound dataSet configuration inRegion
    higherBound = rawHigherRelativeSound dataSet configuration inRegion
    summed = ℚP.+-mono-≤ d1Bound higherBound
    coefficientExact :
      correlatedD1Ratio dataSet * chargeAt dataSet configuration
      + rawHigherRatio dataSet * chargeAt dataSet configuration
      ≡ residualRatio dataSet * chargeAt dataSet configuration
    coefficientExact = ℚRing.solve-∀
      (correlatedD1Ratio dataSet)
      (rawHigherRatio dataSet)
      (chargeAt dataSet configuration)
  in
  subst
    (λ upper →
      Ownership.correlatedResidualTotal (Blocks.canonicalFamily inputs) ≤ upper)
    coefficientExact
    (subst
      (λ lower → lower
        ≤ correlatedD1Ratio dataSet * chargeAt dataSet configuration
          + rawHigherRatio dataSet * chargeAt dataSet configuration)
      (sym (D1.canonicalCorrelatedResidualDegreeOneBeforePolarization inputs))
      summed)

record CorrelatedD1G2Headroom
    {Configuration Multiplier}
    (dataSet : ChargeRelativeCorrelatedD1G2Data Configuration Multiplier)
    (target : ℚ) : Set where
  field
    correlatedD1Budget rawHigherBudget : ℚ
    correlatedD1WithinBudget :
      correlatedD1Ratio dataSet ≤ correlatedD1Budget
    rawHigherWithinBudget : rawHigherRatio dataSet ≤ rawHigherBudget
    budgetsFitTarget : correlatedD1Budget + rawHigherBudget ≤ target

open CorrelatedD1G2Headroom public

residualRatioWithinHeadroom :
  ∀ {Configuration Multiplier target}
    {dataSet : ChargeRelativeCorrelatedD1G2Data Configuration Multiplier} →
  CorrelatedD1G2Headroom dataSet target → residualRatio dataSet ≤ target
residualRatioWithinHeadroom headroom =
  ℚP.≤-trans
    (ℚP.+-mono-≤
      (correlatedD1WithinBudget headroom)
      (rawHigherWithinBudget headroom))
    (budgetsFitTarget headroom)

regionG2ClosesFromHeadroom :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCorrelatedD1G2Data Configuration Multiplier)
    (headroom : CorrelatedD1G2Headroom
      dataSet Selector.remainingSingletonCoefficient)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (Blocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
regionG2ClosesFromHeadroom dataSet headroom configuration inRegion =
  let
    ratioBound = residualRatioWithinHeadroom headroom
    scaled = Norm.scaleNonnegative
      (chargeAt dataSet configuration)
      (chargeNonnegative dataSet configuration inRegion)
      ratioBound
  in
  ℚP.≤-trans
    (correlatedResidualRelativeBound dataSet configuration inRegion)
    (subst
      (λ upper → residualRatio dataSet * chargeAt dataSet configuration ≤ upper)
      (ℚRing.solve-∀
        Selector.remainingSingletonCoefficient
        (chargeAt dataSet configuration))
      (subst
        (λ lower → lower
          ≤ chargeAt dataSet configuration * Selector.remainingSingletonCoefficient)
        (ℚRing.solve-∀
          (residualRatio dataSet) (chargeAt dataSet configuration))
        scaled))

selectedMinimizerG2ClosesFromHeadroom :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCorrelatedD1G2Data Configuration Multiplier)
    (headroom : CorrelatedD1G2Headroom
      dataSet Selector.remainingSingletonCoefficient) →
  Ownership.correlatedResidualTotal
    (Blocks.canonicalFamily
      (canonicalInputsAt dataSet (selectedMinimizer dataSet)))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt dataSet (selectedMinimizer dataSet)
selectedMinimizerG2ClosesFromHeadroom dataSet headroom =
  regionG2ClosesFromHeadroom dataSet headroom
    (selectedMinimizer dataSet) (selectedMinimizerInRegion dataSet)

chargeRelativeCorrelatedD1G2CompilerLevel : ProofLevel
chargeRelativeCorrelatedD1G2CompilerLevel = machineChecked

-- Exactly two physical estimates remain in this compiler.
selectedRegionCorrelatedD1BoundLevel : ProofLevel
selectedRegionCorrelatedD1BoundLevel = conditional

selectedRegionRawHigherAggregateBoundLevel : ProofLevel
selectedRegionRawHigherAggregateBoundLevel = conditional
