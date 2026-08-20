module DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerDegreeEnvelopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- DASHI CONTRIBUTION
--
-- Round57 proved the exact 4 raw + 16 Green Möbius-degree decomposition and
-- sound grouped interval transport, but the grouped envelope was still local
-- to one configuration.  This module makes that estimate genuinely uniform on
-- the selected-minimizer region without accepting a target-shaped residual
-- inequality at each configuration.
--
-- A caller supplies ONE shared family of twenty grouped endpoints, proves each
-- endpoint sound for EVERY configuration in the certified region, supplies ONE
-- lower charge Q_*, and checks ONE rational inequality
--
--   U_* <= (55 / 18874368) Q_*.
--
-- The theorem derives the desired correlated-residual inequality throughout
-- the region and therefore at the selected minimizer.  No configuration-local
-- `R_corr <= target` premise occurs in this route.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _-_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeIntervalExact as Interval

record UniformSelectedMinimizerDegreeEnvelope (Configuration : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    familyAt : Configuration → Ownership.CorrelatedResidualFamily
    chargeAt : Configuration → ℚ

    -- Shared grouped endpoints: four raw and sixteen Green values.
    rawUpper : Degree.MobiusDegree → ℚ
    greenLower : Degree.MobiusDegree → Degree.MobiusDegree → ℚ

    rawSoundUniform : ∀ configuration →
      InCertifiedRegion configuration →
      ∀ degree →
      Degree.rawDegreeBlock (familyAt configuration) degree
      ≤ rawUpper degree

    greenSoundUniform : ∀ configuration →
      InCertifiedRegion configuration →
      ∀ left right →
      greenLower left right
      ≤ Degree.greenDegreeBlock (familyAt configuration) left right

    chargeLower : ℚ
    chargeLowerBound : ∀ configuration →
      InCertifiedRegion configuration →
      chargeLower ≤ chargeAt configuration

open UniformSelectedMinimizerDegreeEnvelope public

sharedRawUpperTotal :
  ∀ {Configuration} → UniformSelectedMinimizerDegreeEnvelope Configuration → ℚ
sharedRawUpperTotal dataSet =
  Sums.sumRational Degree.allDegrees (rawUpper dataSet)

sharedGreenLowerRow :
  ∀ {Configuration} → UniformSelectedMinimizerDegreeEnvelope Configuration →
  Degree.MobiusDegree → ℚ
sharedGreenLowerRow dataSet left =
  Sums.sumRational Degree.allDegrees (greenLower dataSet left)

sharedGreenLowerTotal :
  ∀ {Configuration} → UniformSelectedMinimizerDegreeEnvelope Configuration → ℚ
sharedGreenLowerTotal dataSet =
  Sums.sumRational Degree.allDegrees (sharedGreenLowerRow dataSet)

sharedResidualUpper :
  ∀ {Configuration} → UniformSelectedMinimizerDegreeEnvelope Configuration → ℚ
sharedResidualUpper dataSet =
  sharedRawUpperTotal dataSet - sharedGreenLowerTotal dataSet

jointEnvelopeAt :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerDegreeEnvelope Configuration)
    configuration →
  InCertifiedRegion dataSet configuration →
  Interval.JointDegreeEnvelope (familyAt dataSet configuration)
jointEnvelopeAt dataSet configuration inRegion = record
  { Interval.JointDegreeEnvelope.raw1 =
      Interval.rawUpper
        (rawUpper dataSet Degree.degree1)
        (rawSoundUniform dataSet configuration inRegion Degree.degree1)
  ; Interval.JointDegreeEnvelope.raw2 =
      Interval.rawUpper
        (rawUpper dataSet Degree.degree2)
        (rawSoundUniform dataSet configuration inRegion Degree.degree2)
  ; Interval.JointDegreeEnvelope.raw3 =
      Interval.rawUpper
        (rawUpper dataSet Degree.degree3)
        (rawSoundUniform dataSet configuration inRegion Degree.degree3)
  ; Interval.JointDegreeEnvelope.raw4 =
      Interval.rawUpper
        (rawUpper dataSet Degree.degree4)
        (rawSoundUniform dataSet configuration inRegion Degree.degree4)

  ; Interval.JointDegreeEnvelope.green11 = green Degree.degree1 Degree.degree1
  ; Interval.JointDegreeEnvelope.green12 = green Degree.degree1 Degree.degree2
  ; Interval.JointDegreeEnvelope.green13 = green Degree.degree1 Degree.degree3
  ; Interval.JointDegreeEnvelope.green14 = green Degree.degree1 Degree.degree4
  ; Interval.JointDegreeEnvelope.green21 = green Degree.degree2 Degree.degree1
  ; Interval.JointDegreeEnvelope.green22 = green Degree.degree2 Degree.degree2
  ; Interval.JointDegreeEnvelope.green23 = green Degree.degree2 Degree.degree3
  ; Interval.JointDegreeEnvelope.green24 = green Degree.degree2 Degree.degree4
  ; Interval.JointDegreeEnvelope.green31 = green Degree.degree3 Degree.degree1
  ; Interval.JointDegreeEnvelope.green32 = green Degree.degree3 Degree.degree2
  ; Interval.JointDegreeEnvelope.green33 = green Degree.degree3 Degree.degree3
  ; Interval.JointDegreeEnvelope.green34 = green Degree.degree3 Degree.degree4
  ; Interval.JointDegreeEnvelope.green41 = green Degree.degree4 Degree.degree1
  ; Interval.JointDegreeEnvelope.green42 = green Degree.degree4 Degree.degree2
  ; Interval.JointDegreeEnvelope.green43 = green Degree.degree4 Degree.degree3
  ; Interval.JointDegreeEnvelope.green44 = green Degree.degree4 Degree.degree4
  }
  where
  green : ∀ left right →
    Interval.DegreeGreenLower
      (familyAt dataSet configuration) left right
  green left right =
    Interval.greenLower
      (greenLower dataSet left right)
      (greenSoundUniform dataSet configuration inRegion left right)

jointEnvelopeUsesSharedEndpoint :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerDegreeEnvelope Configuration)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.rawUpperTotal (jointEnvelopeAt dataSet configuration inRegion)
    - Interval.greenLowerTotal (jointEnvelopeAt dataSet configuration inRegion)
  ≡ sharedResidualUpper dataSet
jointEnvelopeUsesSharedEndpoint dataSet configuration inRegion = refl

uniformRegionResidualBelowSharedEndpoint :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerDegreeEnvelope Configuration)
    configuration →
  (inRegion : InCertifiedRegion dataSet configuration) →
  Ownership.correlatedResidualTotal (familyAt dataSet configuration)
  ≤ sharedResidualUpper dataSet
uniformRegionResidualBelowSharedEndpoint dataSet configuration inRegion =
  subst
    (λ upper →
      Ownership.correlatedResidualTotal (familyAt dataSet configuration)
      ≤ upper)
    (jointEnvelopeUsesSharedEndpoint dataSet configuration inRegion)
    (Interval.correlatedResidualJointDegreeUpper
      (jointEnvelopeAt dataSet configuration inRegion))

remainingSingletonCoefficientNonnegative :
  0ℚ ≤ Selector.remainingSingletonCoefficient
remainingSingletonCoefficientNonnegative =
  ℚP.nonNegative⁻¹ Selector.remainingSingletonCoefficient

uniformLowerChargeBelowActualTarget :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerDegreeEnvelope Configuration)
    configuration →
  (inRegion : InCertifiedRegion dataSet configuration) →
  Selector.remainingSingletonCoefficient * chargeLower dataSet
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
uniformLowerChargeBelowActualTarget dataSet configuration inRegion =
  Norm.scaleNonnegative
    Selector.remainingSingletonCoefficient
    remainingSingletonCoefficientNonnegative
    (chargeLowerBound dataSet configuration inRegion)

record UniformSelectedMinimizerDegreeClosure
    {Configuration : Set}
    (dataSet : UniformSelectedMinimizerDegreeEnvelope Configuration) : Set where
  field
    uniformEndpointFitsLowerCharge :
      sharedResidualUpper dataSet
      ≤ Selector.remainingSingletonCoefficient * chargeLower dataSet

open UniformSelectedMinimizerDegreeClosure public

uniformRegionResidualClosesFromSharedDegreeEndpoint :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerDegreeEnvelope Configuration)
    (closure : UniformSelectedMinimizerDegreeClosure dataSet)
    configuration →
  (inRegion : InCertifiedRegion dataSet configuration) →
  Ownership.correlatedResidualTotal (familyAt dataSet configuration)
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
uniformRegionResidualClosesFromSharedDegreeEndpoint dataSet closure configuration inRegion =
  ℚP.≤-trans
    (uniformRegionResidualBelowSharedEndpoint dataSet configuration inRegion)
    (ℚP.≤-trans
      (uniformEndpointFitsLowerCharge closure)
      (uniformLowerChargeBelowActualTarget dataSet configuration inRegion))

selectedMinimizerCorrelatedResidualClosesFromSharedDegreeEndpoint :
  ∀ {Configuration}
    (dataSet : UniformSelectedMinimizerDegreeEnvelope Configuration)
    (closure : UniformSelectedMinimizerDegreeClosure dataSet) →
  Ownership.correlatedResidualTotal
      (familyAt dataSet (selectedMinimizer dataSet))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt dataSet (selectedMinimizer dataSet)
selectedMinimizerCorrelatedResidualClosesFromSharedDegreeEndpoint dataSet closure =
  uniformRegionResidualClosesFromSharedDegreeEndpoint
    dataSet closure
    (selectedMinimizer dataSet)
    (selectedMinimizerInRegion dataSet)

uniformSelectedMinimizerDegreeEnvelopeTransportLevel : ProofLevel
uniformSelectedMinimizerDegreeEnvelopeTransportLevel = machineChecked

uniformSelectedMinimizerDegreeEndpointClosureLevel : ProofLevel
uniformSelectedMinimizerDegreeEndpointClosureLevel = machineChecked

-- Remaining G2 producer on this route is now physically irreducible:
--   * construct the SAME four raw and sixteen Green grouped functions from the
--     literal selected background/KKT/Green objects over the selected region;
--   * prove their shared rational endpoints;
--   * prove one positive charge floor;
--   * evaluate the single endpoint comparison above.
-- No grouped target inequality is accepted as a premise.
selectedRegionPhysicalJointDegreeBoundsLevel : ProofLevel
selectedRegionPhysicalJointDegreeBoundsLevel = conditional
