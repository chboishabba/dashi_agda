module DASHI.Physics.YangMills.BalabanChargeRelativeCanonicalStateNormG2ClosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Replace the Round60/61 global rowMass(K+) hypothesis by the source-native
-- state-norm theorem.  The canonical degree vectors are literal constraint
-- images L g_d and L w_d, hence
--
--   <L g_d,K+ L g_d> <= ||g_d||^2,
--   <L w_d,K+ L w_d> <= ||w_d||^2.
--
-- Therefore every signed Green block has the charge-relative lower endpoint
--
--   G_de >= -1/2 (s_d+t_e) Q,
--
-- whenever ||g_d||^2 <= s_d Q and ||w_d||^2 <= t_d Q.  Summing the exact four
-- by four degree table gives
--
--   residualRatio
--     = rawTotal + 2 (sourceStateTotal + defectStateTotal).
--
-- No K+ row/entry norm, spectral denominator, fixed null-space dimension or
-- stabilizer transport is required.  This is robust across the already-proved
-- background stabilizer stratification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeIntervalExact as Interval
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as CanonicalBlocks
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as GreenDegree
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact as Pairing
import DASHI.Physics.YangMills.BalabanCanonicalGreenStateNormReductionExact as StateNorm
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record ChargeRelativeCanonicalStateNormG2Data
    (Configuration Multiplier : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    pseudoDataAt : Configuration →
      Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationAt : Configuration → _
    bondFieldAt : Configuration → _
    plaquetteAt : Configuration → _

    canonicalInputsAt : ∀ configuration →
      Canonical.CanonicalSubsetCorrelatedAuthorityInputs
        (pseudoDataAt configuration)
        (firstVariationAt configuration)
        (bondFieldAt configuration)
        (plaquetteAt configuration)

    chargeAt : Configuration → ℚ
    chargeNonnegative : ∀ configuration →
      InCertifiedRegion configuration → 0ℚ ≤ chargeAt configuration

    rawRatio : Degree.MobiusDegree → ℚ
    sourceStateNormRatio : Degree.MobiusDegree → ℚ
    defectStateNormRatio : Degree.MobiusDegree → ℚ

    rawRelativeSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      CanonicalBlocks.canonicalRawDegreeBlock
        (canonicalInputsAt configuration) degree
      ≤ rawRatio degree * chargeAt configuration

    sourceStateNormRelativeSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      StateNorm.sourceStateNormSq
        (canonicalInputsAt configuration) degree
      ≤ sourceStateNormRatio degree * chargeAt configuration

    defectStateNormRelativeSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      StateNorm.defectStateNormSq
        (canonicalInputsAt configuration) degree
      ≤ defectStateNormRatio degree * chargeAt configuration

open ChargeRelativeCanonicalStateNormG2Data public

relativeGreenRatio :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier →
  Degree.MobiusDegree → Degree.MobiusDegree → ℚ
relativeGreenRatio dataSet left right =
  - ((+ 1 / 2)
      * (sourceStateNormRatio dataSet left
        + defectStateNormRatio dataSet right))

relativeGreenEndpoint :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier →
  Configuration → Degree.MobiusDegree → Degree.MobiusDegree → ℚ
relativeGreenEndpoint dataSet configuration left right =
  relativeGreenRatio dataSet left right * chargeAt dataSet configuration

relativeGreenSound :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
    ∀ left right →
  relativeGreenEndpoint dataSet configuration left right
  ≤ CanonicalBlocks.canonicalGreenDegreeBlock
      (canonicalInputsAt dataSet configuration) left right
relativeGreenSound dataSet configuration inRegion left right =
  let
    inputs = canonicalInputsAt dataSet configuration
    sourceActual = StateNorm.sourceStateNormSq inputs left
    defectActual = StateNorm.defectStateNormSq inputs right
    sourceCap = sourceStateNormRatio dataSet left * chargeAt dataSet configuration
    defectCap = defectStateNormRatio dataSet right * chargeAt dataSet configuration

    sumBound : sourceActual + defectActual ≤ sourceCap + defectCap
    sumBound = ℚP.+-mono-≤
      (sourceStateNormRelativeSound dataSet configuration inRegion left)
      (defectStateNormRelativeSound dataSet configuration inRegion right)

    negated : - (sourceCap + defectCap) ≤ - (sourceActual + defectActual)
    negated = ℚP.neg-antimono-≤ sumBound

    scaled = Norm.scaleNonnegative
      (+ 1 / 2) (ℚP.nonNegative⁻¹ (+ 1 / 2)) negated

    endpointToStateLower :
      relativeGreenEndpoint dataSet configuration left right
      ≤ StateNorm.greenLowerFromStateNorms inputs left right
    endpointToStateLower =
      subst
        (λ lower → lower ≤ StateNorm.greenLowerFromStateNorms inputs left right)
        (ℚRing.solve-∀
          (sourceStateNormRatio dataSet left)
          (defectStateNormRatio dataSet right)
          (chargeAt dataSet configuration))
        (subst
          (λ upper → (+ 1 / 2) * (- (sourceCap + defectCap)) ≤ upper)
          (ℚRing.solve-∀ sourceActual defectActual)
          scaled)

    toPairing = ℚP.≤-trans endpointToStateLower
      (StateNorm.greenLowerFromStateNormsSound inputs left right)
  in
  subst
    (λ upper → relativeGreenEndpoint dataSet configuration left right ≤ upper)
    (sym (Pairing.canonicalGreenIsBilinearPairing inputs left right))
    toPairing

relativeEnvelopeAt :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  Interval.JointDegreeEnvelope
    (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
relativeEnvelopeAt dataSet configuration inRegion = record
  { Interval.JointDegreeEnvelope.raw1 = raw Degree.degree1
  ; Interval.JointDegreeEnvelope.raw2 = raw Degree.degree2
  ; Interval.JointDegreeEnvelope.raw3 = raw Degree.degree3
  ; Interval.JointDegreeEnvelope.raw4 = raw Degree.degree4
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
  charge = chargeAt dataSet configuration
  raw : ∀ degree →
    Interval.DegreeRawUpper
      (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
      degree
  raw degree = Interval.rawUpper
    (rawRatio dataSet degree * charge)
    (rawRelativeSound dataSet configuration inRegion degree)

  green : ∀ left right →
    Interval.DegreeGreenLower
      (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
      left right
  green left right = Interval.greenLower
    (relativeGreenEndpoint dataSet configuration left right)
    (relativeGreenSound dataSet configuration inRegion left right)

rawRatioTotal :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier → ℚ
rawRatioTotal dataSet = Sums.sumRational Degree.allDegrees (rawRatio dataSet)

sourceStateNormRatioTotal :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier → ℚ
sourceStateNormRatioTotal dataSet =
  Sums.sumRational Degree.allDegrees (sourceStateNormRatio dataSet)

defectStateNormRatioTotal :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier → ℚ
defectStateNormRatioTotal dataSet =
  Sums.sumRational Degree.allDegrees (defectStateNormRatio dataSet)

greenRatioRow :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier →
  Degree.MobiusDegree → ℚ
greenRatioRow dataSet left =
  Sums.sumRational Degree.allDegrees (relativeGreenRatio dataSet left)

greenRatioTotal :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier → ℚ
greenRatioTotal dataSet =
  Sums.sumRational Degree.allDegrees (greenRatioRow dataSet)

residualRatio :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier → ℚ
residualRatio dataSet = rawRatioTotal dataSet - greenRatioTotal dataSet

greenRatioTotalAggregateExact :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier) →
  greenRatioTotal dataSet
  ≡ - ((+ 2 / 1)
      * (sourceStateNormRatioTotal dataSet
        + defectStateNormRatioTotal dataSet))
greenRatioTotalAggregateExact dataSet =
  ℚRing.solve-∀
    (sourceStateNormRatio dataSet Degree.degree1)
    (sourceStateNormRatio dataSet Degree.degree2)
    (sourceStateNormRatio dataSet Degree.degree3)
    (sourceStateNormRatio dataSet Degree.degree4)
    (defectStateNormRatio dataSet Degree.degree1)
    (defectStateNormRatio dataSet Degree.degree2)
    (defectStateNormRatio dataSet Degree.degree3)
    (defectStateNormRatio dataSet Degree.degree4)

residualRatioAggregate :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier → ℚ
residualRatioAggregate dataSet =
  rawRatioTotal dataSet
  + (+ 2 / 1)
      * (sourceStateNormRatioTotal dataSet
        + defectStateNormRatioTotal dataSet)

residualRatioAggregateExact :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier) →
  residualRatio dataSet ≡ residualRatioAggregate dataSet
residualRatioAggregateExact dataSet =
  trans
    (cong (λ green → rawRatioTotal dataSet - green)
      (greenRatioTotalAggregateExact dataSet))
    (ℚRing.solve-∀
      (rawRatioTotal dataSet)
      (sourceStateNormRatioTotal dataSet)
      (defectStateNormRatioTotal dataSet))

rawUpperValueRelativeExact :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration)
    degree →
  Interval.rawUpperValue (relativeEnvelopeAt dataSet configuration inRegion) degree
  ≡ rawRatio dataSet degree * chargeAt dataSet configuration
rawUpperValueRelativeExact dataSet configuration inRegion Degree.degree1 = refl
rawUpperValueRelativeExact dataSet configuration inRegion Degree.degree2 = refl
rawUpperValueRelativeExact dataSet configuration inRegion Degree.degree3 = refl
rawUpperValueRelativeExact dataSet configuration inRegion Degree.degree4 = refl

greenLowerValueRelativeExact :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration)
    left right →
  Interval.greenLowerValue (relativeEnvelopeAt dataSet configuration inRegion) left right
  ≡ relativeGreenEndpoint dataSet configuration left right
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree1 Degree.degree1 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree1 Degree.degree2 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree1 Degree.degree3 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree1 Degree.degree4 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree2 Degree.degree1 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree2 Degree.degree2 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree2 Degree.degree3 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree2 Degree.degree4 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree3 Degree.degree1 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree3 Degree.degree2 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree3 Degree.degree3 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree3 Degree.degree4 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree4 Degree.degree1 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree4 Degree.degree2 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree4 Degree.degree3 = refl
greenLowerValueRelativeExact dataSet configuration inRegion Degree.degree4 Degree.degree4 = refl

rawEndpointFactorsCharge :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.rawUpperTotal (relativeEnvelopeAt dataSet configuration inRegion)
  ≡ chargeAt dataSet configuration * rawRatioTotal dataSet
rawEndpointFactorsCharge dataSet configuration inRegion =
  trans
    (Sums.sumRationalCong Degree.allDegrees _ _
      (λ degree → trans
        (rawUpperValueRelativeExact dataSet configuration inRegion degree)
        (ℚP.*-comm
          (rawRatio dataSet degree) (chargeAt dataSet configuration))))
    (Sums.sumRationalScale
      (chargeAt dataSet configuration) Degree.allDegrees (rawRatio dataSet))

greenRowEndpointFactorsCharge :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration)
    left →
  Interval.greenLowerRow (relativeEnvelopeAt dataSet configuration inRegion) left
  ≡ chargeAt dataSet configuration * greenRatioRow dataSet left
greenRowEndpointFactorsCharge dataSet configuration inRegion left =
  trans
    (Sums.sumRationalCong Degree.allDegrees _ _
      (λ right → trans
        (greenLowerValueRelativeExact dataSet configuration inRegion left right)
        (ℚP.*-comm
          (relativeGreenRatio dataSet left right)
          (chargeAt dataSet configuration))))
    (Sums.sumRationalScale
      (chargeAt dataSet configuration) Degree.allDegrees
      (relativeGreenRatio dataSet left))

greenEndpointFactorsCharge :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.greenLowerTotal (relativeEnvelopeAt dataSet configuration inRegion)
  ≡ chargeAt dataSet configuration * greenRatioTotal dataSet
greenEndpointFactorsCharge dataSet configuration inRegion =
  trans
    (Sums.sumRationalCong Degree.allDegrees _ _
      (greenRowEndpointFactorsCharge dataSet configuration inRegion))
    (Sums.sumRationalScale
      (chargeAt dataSet configuration) Degree.allDegrees (greenRatioRow dataSet))

relativeEnvelopeEndpointExact :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.rawUpperTotal (relativeEnvelopeAt dataSet configuration inRegion)
    - Interval.greenLowerTotal (relativeEnvelopeAt dataSet configuration inRegion)
  ≡ residualRatio dataSet * chargeAt dataSet configuration
relativeEnvelopeEndpointExact dataSet configuration inRegion
  rewrite rawEndpointFactorsCharge dataSet configuration inRegion
        | greenEndpointFactorsCharge dataSet configuration inRegion =
  ℚRing.solve-∀
    (rawRatioTotal dataSet)
    (greenRatioTotal dataSet)
    (chargeAt dataSet configuration)

relativeResidualBound :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ residualRatio dataSet * chargeAt dataSet configuration
relativeResidualBound dataSet configuration inRegion =
  subst
    (λ upper →
      Ownership.correlatedResidualTotal
        (CanonicalBlocks.canonicalFamily
          (canonicalInputsAt dataSet configuration)) ≤ upper)
    (relativeEnvelopeEndpointExact dataSet configuration inRegion)
    (Interval.correlatedResidualJointDegreeUpper
      (relativeEnvelopeAt dataSet configuration inRegion))

------------------------------------------------------------------------
-- Direct non-overlapping headroom on the sharpened aggregate scalar.
------------------------------------------------------------------------

greenCorrectionAggregate :
  ∀ {Configuration Multiplier} →
  ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier → ℚ
greenCorrectionAggregate dataSet =
  (+ 2 / 1)
    * (sourceStateNormRatioTotal dataSet + defectStateNormRatioTotal dataSet)

record StateNormG2AggregateHeadroom
    {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    (target : ℚ) : Set where
  field
    rawBudget greenBudget : ℚ
    rawWithinBudget : rawRatioTotal dataSet ≤ rawBudget
    greenWithinBudget : greenCorrectionAggregate dataSet ≤ greenBudget
    budgetsFitTarget : rawBudget + greenBudget ≤ target

open StateNormG2AggregateHeadroom public

aggregateResidualWithinHeadroom :
  ∀ {Configuration Multiplier target}
    {dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier} →
  StateNormG2AggregateHeadroom dataSet target →
  residualRatio dataSet ≤ target
aggregateResidualWithinHeadroom {dataSet = dataSet} budget =
  subst
    (λ lower → lower ≤ _)
    (sym (residualRatioAggregateExact dataSet))
    (ℚP.≤-trans
      (ℚP.+-mono-≤
        (rawWithinBudget budget)
        (greenWithinBudget budget))
      (budgetsFitTarget budget))

record ChargeRelativeCanonicalStateNormG2Closure
    {Configuration Multiplier : Set}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier) : Set where
  field
    ratioFitsTarget : residualRatio dataSet ≤ Selector.remainingSingletonCoefficient
open ChargeRelativeCanonicalStateNormG2Closure public

closureFromHeadroom :
  ∀ {Configuration Multiplier}
    {dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier} →
  StateNormG2AggregateHeadroom dataSet Selector.remainingSingletonCoefficient →
  ChargeRelativeCanonicalStateNormG2Closure dataSet
closureFromHeadroom budget = record
  { ratioFitsTarget = aggregateResidualWithinHeadroom budget }

relativeRegionG2Closes :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    (closure : ChargeRelativeCanonicalStateNormG2Closure dataSet)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
relativeRegionG2Closes dataSet closure configuration inRegion =
  let
    scaledRatio = Norm.scaleNonnegative
      (chargeAt dataSet configuration)
      (chargeNonnegative dataSet configuration inRegion)
      (ratioFitsTarget closure)
  in
  ℚP.≤-trans
    (relativeResidualBound dataSet configuration inRegion)
    (subst
      (λ upper → residualRatio dataSet * chargeAt dataSet configuration ≤ upper)
      (ℚRing.solve-∀
        Selector.remainingSingletonCoefficient
        (chargeAt dataSet configuration))
      (subst
        (λ lower → lower ≤
          chargeAt dataSet configuration * Selector.remainingSingletonCoefficient)
        (ℚRing.solve-∀
          (residualRatio dataSet)
          (chargeAt dataSet configuration))
        scaledRatio))

selectedMinimizerG2ClosesChargeRelatively :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeCanonicalStateNormG2Data Configuration Multiplier)
    (closure : ChargeRelativeCanonicalStateNormG2Closure dataSet) →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily
      (canonicalInputsAt dataSet (selectedMinimizer dataSet)))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt dataSet (selectedMinimizer dataSet)
selectedMinimizerG2ClosesChargeRelatively dataSet closure =
  relativeRegionG2Closes dataSet closure
    (selectedMinimizer dataSet) (selectedMinimizerInRegion dataSet)

chargeRelativeCanonicalStateNormG2CompilerLevel : ProofLevel
chargeRelativeCanonicalStateNormG2CompilerLevel = machineChecked

chargeRelativeStateNormG2AggregateLevel : ProofLevel
chargeRelativeStateNormG2AggregateLevel = machineChecked

chargeRelativeStateNormG2HeadroomLevel : ProofLevel
chargeRelativeStateNormG2HeadroomLevel = machineChecked

-- Remaining G2 physical producers are now exactly charge-relative bounds on:
--   * the four raw degree blocks (or their aggregate),
--   * the four source degree-state norms,
--   * the four defect degree-state norms.
-- No pseudoinverse locality/norm theorem remains on the G2 dependency path.
selectedRegionStateNormG2PhysicalBoundsLevel : ProofLevel
selectedRegionStateNormG2PhysicalBoundsLevel = conditional
