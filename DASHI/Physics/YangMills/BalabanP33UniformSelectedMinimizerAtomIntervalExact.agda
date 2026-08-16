module DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerAtomIntervalExact where

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
-- Ramon E. Moore, R. Baker Kearfott, Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- DASHI CONTRIBUTION
--
-- Finish the structural part of G2 without a residual-upper-bound receipt.
-- Over a certified region containing the selected minimizer, the caller gives
-- interval boxes for EACH LITERAL raw and Green atom. The previous module
-- evaluates those boxes into a signed residual endpoint
--
--       U(A) = sum rawUpper_S - sum greenLower_(S,T).
--
-- The only final numerical certificate accepted here is the endpoint check
--
--       U(A) <= (55/18874368) Q(A),
--
-- uniformly on the region. Since U(A) is definitionally computed from the
-- atom boxes, this is not the desired physical residual inequality smuggled in
-- as a field. The selected minimizer theorem follows by transitivity.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33CorrelatedAtomIntervalEvaluationExact as Atom

record UniformSelectedMinimizerAtomInterval (Configuration : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    familyAt : Configuration → Ownership.CorrelatedResidualFamily
    chargeAt : Configuration → ℚ

    atomEnvelopeAt : ∀ configuration →
      InCertifiedRegion configuration →
      Atom.CorrelatedAtomIntervalEnvelope (familyAt configuration)

    computedEndpointFitsAt : ∀ configuration inRegion →
      Atom.atomIntervalResidualUpper
        (atomEnvelopeAt configuration inRegion)
      ≤ Selector.remainingSingletonCoefficient * chargeAt configuration

open UniformSelectedMinimizerAtomInterval public

uniformRegionResidualClosesFromComputedAtomEndpoint :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerAtomInterval Configuration)
    configuration →
  (inRegion : InCertifiedRegion dataSet configuration) →
  Ownership.correlatedResidualTotal (familyAt dataSet configuration)
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
uniformRegionResidualClosesFromComputedAtomEndpoint dataSet configuration inRegion =
  ℚP.≤-trans
    (Atom.correlatedResidualBelowAtomIntervalUpper
      (atomEnvelopeAt dataSet configuration inRegion))
    (computedEndpointFitsAt dataSet configuration inRegion)

selectedMinimizerCorrelatedResidualClosesFromAtomIntervals :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerAtomInterval Configuration) →
  Ownership.correlatedResidualTotal
    (familyAt dataSet (selectedMinimizer dataSet))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt dataSet (selectedMinimizer dataSet)
selectedMinimizerCorrelatedResidualClosesFromAtomIntervals dataSet =
  uniformRegionResidualClosesFromComputedAtomEndpoint
    dataSet
    (selectedMinimizer dataSet)
    (selectedMinimizerInRegion dataSet)

p33UniformSelectedMinimizerAtomIntervalTransportLevel : ProofLevel
p33UniformSelectedMinimizerAtomIntervalTransportLevel = machineChecked

-- The remaining G2 calculation is now precisely a certified interval run that
-- constructs atomEnvelopeAt and checks the resulting rational endpoint. No
-- theorem-level R_corr <= target assumption remains in this route.
p33PhysicalSelectedMinimizerAtomIntervalEvaluationLevel : ProofLevel
p33PhysicalSelectedMinimizerAtomIntervalEvaluationLevel = conditional
