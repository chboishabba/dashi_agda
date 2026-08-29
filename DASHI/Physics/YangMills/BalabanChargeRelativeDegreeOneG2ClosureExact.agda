module DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ClosureExact where

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
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- Compile the exact degree-one-only Green theorem into the selected G2
-- headroom calculation.  Four raw degree blocks remain because the raw scalar
-- localization need not itself be linear in the subset state.  The Green term,
-- however, has only G_11.  Thus physical input is reduced to
--
--   raw_d <= r_d Q          (d=1..4),
--   ||g_1||^2 <= s Q,
--   ||w_1||^2 <= t Q,
--
-- and the correlated residual satisfies
--
--   R_corr <= [sum_d r_d + 1/2 (s+t)] Q.
--
-- The previous generic state-norm compiler charged 2(sum s_d + sum t_d)
-- because it lower-bounded all sixteen Green cells independently.  Exact
-- higher-degree vanishing improves that coefficient by a factor of four even
-- when the unused higher norm ratios are set to zero.
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
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeIntervalExact as Interval
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as CanonicalBlocks
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact as Pairing
import DASHI.Physics.YangMills.BalabanCanonicalGreenStateNormReductionExact as StateNorm
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeOneOnlyExact as DegreeOne
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record ChargeRelativeDegreeOneG2Data
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

    rawRatio : Degree.MobiusDegree → ℚ
    sourceDegreeOneNormRatio : ℚ
    defectDegreeOneNormRatio : ℚ

    rawRelativeSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      CanonicalBlocks.canonicalRawDegreeBlock
        (canonicalInputsAt configuration) degree
      ≤ rawRatio degree * chargeAt configuration

    sourceDegreeOneNormRelativeSound : ∀ configuration →
      InCertifiedRegion configuration →
      StateNorm.sourceStateNormSq
        (canonicalInputsAt configuration) Degree.degree1
      ≤ sourceDegreeOneNormRatio * chargeAt configuration

    defectDegreeOneNormRelativeSound : ∀ configuration →
      InCertifiedRegion configuration →
      StateNorm.defectStateNormSq
        (canonicalInputsAt configuration) Degree.degree1
      ≤ defectDegreeOneNormRatio * chargeAt configuration

open ChargeRelativeDegreeOneG2Data public

rawRatioTotal :
  ∀ {Configuration Multiplier} →
  ChargeRelativeDegreeOneG2Data Configuration Multiplier → ℚ
rawRatioTotal dataSet = Sums.sumRational Degree.allDegrees (rawRatio dataSet)

green11Ratio :
  ∀ {Configuration Multiplier} →
  ChargeRelativeDegreeOneG2Data Configuration Multiplier → ℚ
green11Ratio dataSet =
  - ((+ 1 / 2)
      * (sourceDegreeOneNormRatio dataSet + defectDegreeOneNormRatio dataSet))

greenCorrectionRatio :
  ∀ {Configuration Multiplier} →
  ChargeRelativeDegreeOneG2Data Configuration Multiplier → ℚ
greenCorrectionRatio dataSet =
  (+ 1 / 2)
    * (sourceDegreeOneNormRatio dataSet + defectDegreeOneNormRatio dataSet)

residualRatio :
  ∀ {Configuration Multiplier} →
  ChargeRelativeDegreeOneG2Data Configuration Multiplier → ℚ
residualRatio dataSet = rawRatioTotal dataSet + greenCorrectionRatio dataSet

green11Endpoint :
  ∀ {Configuration Multiplier} →
  ChargeRelativeDegreeOneG2Data Configuration Multiplier →
  Configuration → ℚ
green11Endpoint dataSet configuration =
  green11Ratio dataSet * chargeAt dataSet configuration

green11Sound :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  green11Endpoint dataSet configuration
  ≤ CanonicalBlocks.canonicalGreenDegreeBlock
      (canonicalInputsAt dataSet configuration)
      Degree.degree1 Degree.degree1
green11Sound dataSet configuration inRegion =
  let
    inputs = canonicalInputsAt dataSet configuration
    sourceActual = StateNorm.sourceStateNormSq inputs Degree.degree1
    defectActual = StateNorm.defectStateNormSq inputs Degree.degree1
    sourceCap = sourceDegreeOneNormRatio dataSet * chargeAt dataSet configuration
    defectCap = defectDegreeOneNormRatio dataSet * chargeAt dataSet configuration

    sumBound : sourceActual + defectActual ≤ sourceCap + defectCap
    sumBound = ℚP.+-mono-≤
      (sourceDegreeOneNormRelativeSound dataSet configuration inRegion)
      (defectDegreeOneNormRelativeSound dataSet configuration inRegion)

    negated : - (sourceCap + defectCap) ≤ - (sourceActual + defectActual)
    negated = ℚP.neg-antimono-≤ sumBound

    scaled = Norm.scaleNonnegative
      (+ 1 / 2) (ℚP.nonNegative⁻¹ (+ 1 / 2)) negated

    endpointToStateLower :
      green11Endpoint dataSet configuration
      ≤ StateNorm.greenLowerFromStateNorms
          inputs Degree.degree1 Degree.degree1
    endpointToStateLower =
      subst
        (λ lower → lower ≤
          StateNorm.greenLowerFromStateNorms inputs Degree.degree1 Degree.degree1)
        (ℚRing.solve-∀
          (sourceDegreeOneNormRatio dataSet)
          (defectDegreeOneNormRatio dataSet)
          (chargeAt dataSet configuration))
        (subst
          (λ upper → (+ 1 / 2) * (- (sourceCap + defectCap)) ≤ upper)
          (ℚRing.solve-∀ sourceActual defectActual)
          scaled)

    toPairing = ℚP.≤-trans endpointToStateLower
      (StateNorm.greenLowerFromStateNormsSound
        inputs Degree.degree1 Degree.degree1)
  in
  subst
    (λ upper → green11Endpoint dataSet configuration ≤ upper)
    (sym (Pairing.canonicalGreenIsBilinearPairing
      inputs Degree.degree1 Degree.degree1))
    toPairing

zeroGreenLower :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    left right →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs left right ≡ 0ℚ →
  Interval.DegreeGreenLower
    (CanonicalBlocks.canonicalFamily inputs) left right
zeroGreenLower inputs left right exactZero =
  Interval.greenLower 0ℚ
    (subst
      (λ upper → 0ℚ ≤ upper)
      (sym exactZero)
      ℚP.≤-refl)

degreeOneEnvelopeAt :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  Interval.JointDegreeEnvelope
    (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
degreeOneEnvelopeAt dataSet configuration inRegion = record
  { Interval.JointDegreeEnvelope.raw1 = raw Degree.degree1
  ; Interval.JointDegreeEnvelope.raw2 = raw Degree.degree2
  ; Interval.JointDegreeEnvelope.raw3 = raw Degree.degree3
  ; Interval.JointDegreeEnvelope.raw4 = raw Degree.degree4
  ; Interval.JointDegreeEnvelope.green11 =
      Interval.greenLower
        (green11Endpoint dataSet configuration)
        (green11Sound dataSet configuration inRegion)
  ; Interval.JointDegreeEnvelope.green12 =
      zeroGreen Degree.degree1 Degree.degree2
        (DegreeOne.g12Zero inputs)
  ; Interval.JointDegreeEnvelope.green13 =
      zeroGreen Degree.degree1 Degree.degree3
        (DegreeOne.g13Zero inputs)
  ; Interval.JointDegreeEnvelope.green14 =
      zeroGreen Degree.degree1 Degree.degree4
        (DegreeOne.g14Zero inputs)
  ; Interval.JointDegreeEnvelope.green21 =
      zeroGreen Degree.degree2 Degree.degree1
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher2 Degree.degree1)
  ; Interval.JointDegreeEnvelope.green22 =
      zeroGreen Degree.degree2 Degree.degree2
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher2 Degree.degree2)
  ; Interval.JointDegreeEnvelope.green23 =
      zeroGreen Degree.degree2 Degree.degree3
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher2 Degree.degree3)
  ; Interval.JointDegreeEnvelope.green24 =
      zeroGreen Degree.degree2 Degree.degree4
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher2 Degree.degree4)
  ; Interval.JointDegreeEnvelope.green31 =
      zeroGreen Degree.degree3 Degree.degree1
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher3 Degree.degree1)
  ; Interval.JointDegreeEnvelope.green32 =
      zeroGreen Degree.degree3 Degree.degree2
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher3 Degree.degree2)
  ; Interval.JointDegreeEnvelope.green33 =
      zeroGreen Degree.degree3 Degree.degree3
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher3 Degree.degree3)
  ; Interval.JointDegreeEnvelope.green34 =
      zeroGreen Degree.degree3 Degree.degree4
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher3 Degree.degree4)
  ; Interval.JointDegreeEnvelope.green41 =
      zeroGreen Degree.degree4 Degree.degree1
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher4 Degree.degree1)
  ; Interval.JointDegreeEnvelope.green42 =
      zeroGreen Degree.degree4 Degree.degree2
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher4 Degree.degree2)
  ; Interval.JointDegreeEnvelope.green43 =
      zeroGreen Degree.degree4 Degree.degree3
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher4 Degree.degree3)
  ; Interval.JointDegreeEnvelope.green44 =
      zeroGreen Degree.degree4 Degree.degree4
        (DegreeOne.canonicalGreenZeroFromHigherSource
          inputs DegreeOne.higher4 Degree.degree4)
  }
  where
  inputs = canonicalInputsAt dataSet configuration

  raw : ∀ degree →
    Interval.DegreeRawUpper
      (CanonicalBlocks.canonicalFamily inputs) degree
  raw degree = Interval.rawUpper
    (rawRatio dataSet degree * chargeAt dataSet configuration)
    (rawRelativeSound dataSet configuration inRegion degree)

  zeroGreen : ∀ left right →
    CanonicalBlocks.canonicalGreenDegreeBlock inputs left right ≡ 0ℚ →
    Interval.DegreeGreenLower
      (CanonicalBlocks.canonicalFamily inputs) left right
  zeroGreen = zeroGreenLower inputs

rawEndpointFactorsCharge :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.rawUpperTotal (degreeOneEnvelopeAt dataSet configuration inRegion)
  ≡ chargeAt dataSet configuration * rawRatioTotal dataSet
rawEndpointFactorsCharge dataSet configuration inRegion =
  trans
    (Sums.sumRationalCong Degree.allDegrees _ _
      (λ degree →
        ℚP.*-comm
          (rawRatio dataSet degree)
          (chargeAt dataSet configuration)))
    (Sums.sumRationalScale
      (chargeAt dataSet configuration) Degree.allDegrees (rawRatio dataSet))

greenEndpointIsSingleBlock :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.greenLowerTotal (degreeOneEnvelopeAt dataSet configuration inRegion)
  ≡ green11Endpoint dataSet configuration
greenEndpointIsSingleBlock dataSet configuration inRegion =
  ℚRing.solve-∀ (green11Endpoint dataSet configuration)

degreeOneEnvelopeEndpointExact :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier)
    configuration
    (inRegion : InCertifiedRegion dataSet configuration) →
  Interval.rawUpperTotal (degreeOneEnvelopeAt dataSet configuration inRegion)
    - Interval.greenLowerTotal (degreeOneEnvelopeAt dataSet configuration inRegion)
  ≡ residualRatio dataSet * chargeAt dataSet configuration
degreeOneEnvelopeEndpointExact dataSet configuration inRegion
  rewrite rawEndpointFactorsCharge dataSet configuration inRegion
        | greenEndpointIsSingleBlock dataSet configuration inRegion =
  ℚRing.solve-∀
    (rawRatioTotal dataSet)
    (sourceDegreeOneNormRatio dataSet)
    (defectDegreeOneNormRatio dataSet)
    (chargeAt dataSet configuration)

degreeOneRelativeResidualBound :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ residualRatio dataSet * chargeAt dataSet configuration
degreeOneRelativeResidualBound dataSet configuration inRegion =
  subst
    (λ upper →
      Ownership.correlatedResidualTotal
        (CanonicalBlocks.canonicalFamily
          (canonicalInputsAt dataSet configuration)) ≤ upper)
    (degreeOneEnvelopeEndpointExact dataSet configuration inRegion)
    (Interval.correlatedResidualJointDegreeUpper
      (degreeOneEnvelopeAt dataSet configuration inRegion))

record DegreeOneG2AggregateHeadroom
    {Configuration Multiplier}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier)
    (target : ℚ) : Set where
  field
    rawBudget greenBudget : ℚ
    rawWithinBudget : rawRatioTotal dataSet ≤ rawBudget
    greenWithinBudget : greenCorrectionRatio dataSet ≤ greenBudget
    budgetsFitTarget : rawBudget + greenBudget ≤ target

open DegreeOneG2AggregateHeadroom public

aggregateResidualWithinHeadroom :
  ∀ {Configuration Multiplier target}
    {dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier} →
  DegreeOneG2AggregateHeadroom dataSet target →
  residualRatio dataSet ≤ target
aggregateResidualWithinHeadroom budget =
  ℚP.≤-trans
    (ℚP.+-mono-≤
      (rawWithinBudget budget)
      (greenWithinBudget budget))
    (budgetsFitTarget budget)

record ChargeRelativeDegreeOneG2Closure
    {Configuration Multiplier : Set}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier) : Set where
  field
    ratioFitsTarget : residualRatio dataSet ≤ Selector.remainingSingletonCoefficient
open ChargeRelativeDegreeOneG2Closure public

closureFromHeadroom :
  ∀ {Configuration Multiplier}
    {dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier} →
  DegreeOneG2AggregateHeadroom dataSet Selector.remainingSingletonCoefficient →
  ChargeRelativeDegreeOneG2Closure dataSet
closureFromHeadroom budget = record
  { ratioFitsTarget = aggregateResidualWithinHeadroom budget }

degreeOneRegionG2Closes :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier)
    (closure : ChargeRelativeDegreeOneG2Closure dataSet)
    configuration → InCertifiedRegion dataSet configuration →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily (canonicalInputsAt dataSet configuration))
  ≤ Selector.remainingSingletonCoefficient * chargeAt dataSet configuration
degreeOneRegionG2Closes dataSet closure configuration inRegion =
  let
    scaledRatio = Norm.scaleNonnegative
      (chargeAt dataSet configuration)
      (chargeNonnegative dataSet configuration inRegion)
      (ratioFitsTarget closure)
  in
  ℚP.≤-trans
    (degreeOneRelativeResidualBound dataSet configuration inRegion)
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

selectedMinimizerDegreeOneG2Closes :
  ∀ {Configuration Multiplier}
    (dataSet : ChargeRelativeDegreeOneG2Data Configuration Multiplier)
    (closure : ChargeRelativeDegreeOneG2Closure dataSet) →
  Ownership.correlatedResidualTotal
    (CanonicalBlocks.canonicalFamily
      (canonicalInputsAt dataSet (selectedMinimizer dataSet)))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt dataSet (selectedMinimizer dataSet)
selectedMinimizerDegreeOneG2Closes dataSet closure =
  degreeOneRegionG2Closes dataSet closure
    (selectedMinimizer dataSet) (selectedMinimizerInRegion dataSet)

chargeRelativeDegreeOneG2CompilerLevel : ProofLevel
chargeRelativeDegreeOneG2CompilerLevel = machineChecked

-- Remaining physical G2 producers are now exactly:
--   (1) one aggregate/raw four-degree charge-relative bound,
--   (2) the degree-one source-state norm bound,
--   (3) the degree-one defect-state norm bound,
-- together with one rational headroom check against the already fixed target.
selectedRegionDegreeOneG2PhysicalBoundsLevel : ProofLevel
selectedRegionDegreeOneG2PhysicalBoundsLevel = conditional
