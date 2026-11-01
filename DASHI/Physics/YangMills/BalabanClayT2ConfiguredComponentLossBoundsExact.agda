module DASHI.Physics.YangMills.BalabanClayT2ConfiguredComponentLossBoundsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCommonRationalSincCertificateExact as Sinc
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredCommonRadiusCertificateExact as Radius
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredLossBudgetCertificateExact as Budget

------------------------------------------------------------------------
-- Literature normalization.
--
-- Barry Simon, "Trace Ideals and Their Applications", second edition,
-- American Mathematical Society (2005). DOI: 10.1090/surv/120
-- Relationship: trace-log estimate for the determinant lane.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022
-- Relationship: localization and polymer-norm bookkeeping.
--
-- Sergio Blanes and Fernando Casas, "On the Convergence and Optimization of
-- the Baker--Campbell--Hausdorff Formula", Linear Algebra and its Applications
-- 378 (2004), 135--158. DOI: 10.1016/j.laa.2003.09.010
-- Relationship: generic cubic-remainder comparison; the physical SU(2) owner
-- remains the exact quaternion product.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Haar/Jacobian budget.
--
-- At the configured chart radius 1/2048 the half-angle is 1/4096.  Charging a
-- deliberately large 64 links per block and the squared SU(2) Haar density
-- still lies far below the allocated Jacobian loss 1/16.
------------------------------------------------------------------------

configuredHalfAngle configuredLinksPerBlock configuredHaarUpper : ℚ
configuredHalfAngle = + 1 / 4096
configuredLinksPerBlock = + 64 / 1
configuredHaarUpper =
  (+ 2 / 1) * configuredLinksPerBlock
  * (Sinc.sixthℚ * (configuredHalfAngle * configuredHalfAngle)
    + Sinc.oneNinetiethℚ
      * (configuredHalfAngle * configuredHalfAngle
        * configuredHalfAngle * configuredHalfAngle))

configuredHalfAngleExact :
  configuredHalfAngle + configuredHalfAngle ≡ Radius.configuredRadius
configuredHalfAngleExact = ℚRing.solve []
configuredHaarBelowAllocated :
  configuredHaarUpper ≤ Budget.configuredJacobianLoss
configuredHaarBelowAllocated = ℚP.≤ᵇ⇒≤ tt

------------------------------------------------------------------------
-- Determinant budget.
--
-- If ||K|| <= 1/2, the trace-log series gives
--   |Tr log(1+K)| <= ||K||_1/(1-||K||) <= 2 ||K||_1.
-- Thus localized trace norm <= 1/8 closes the allocated 1/4 slot.
------------------------------------------------------------------------

configuredRelativeOperatorNorm configuredTraceNorm configuredDeterminantUpper : ℚ
configuredRelativeOperatorNorm = + 1 / 2
configuredTraceNorm = + 1 / 8
configuredDeterminantUpper = (+ 2 / 1) * configuredTraceNorm

configuredDeterminantUpperExact :
  configuredDeterminantUpper ≡ Budget.configuredDeterminantLoss
configuredDeterminantUpperExact = ℚRing.solve []
------------------------------------------------------------------------
-- Quaternion/BCH budget.
--
-- The allocation permits a cubic coefficient 1024 and 96 plaquette charges per
-- block at radius 1/2048.  This is intentionally much looser than the exact
-- four-quaternion expansion is expected to produce.
------------------------------------------------------------------------

configuredQuaternionCubicConstant configuredPlaquettesPerBlock : ℚ
configuredQuaternionCubicConstant = + 1024 / 1
configuredPlaquettesPerBlock = + 96 / 1

configuredBCHUpper : ℚ
configuredBCHUpper =
  configuredQuaternionCubicConstant * configuredPlaquettesPerBlock
  * (Radius.configuredRadius * Radius.configuredRadius * Radius.configuredRadius)

configuredBCHBelowAllocated :
  configuredBCHUpper ≤ Budget.configuredBCHLoss
configuredBCHBelowAllocated = ℚP.≤ᵇ⇒≤ tt

------------------------------------------------------------------------
-- Localization and patch allocations.
------------------------------------------------------------------------

configuredLocalizationDerivativeGain configuredLocalizationCollarCharge : ℚ
configuredLocalizationDerivativeGain = + 1 / 32
configuredLocalizationCollarCharge = + 4 / 1

configuredLocalizationUpper : ℚ
configuredLocalizationUpper =
  configuredLocalizationDerivativeGain * configuredLocalizationCollarCharge

configuredLocalizationUpperExact :
  configuredLocalizationUpper ≡ Budget.configuredLocalizationLoss
configuredLocalizationUpperExact = ℚRing.solve []
configuredPatchUpper : ℚ
configuredPatchUpper = + 1 / 8

configuredPatchUpperExact :
  configuredPatchUpper ≡ Budget.configuredPatchLoss
configuredPatchUpperExact = ℚRing.solve []
------------------------------------------------------------------------
-- Physical component producer.  Only model-specific inequalities remain; all
-- numeric comparisons with the common 1/16 budget are exact rational theorems.
------------------------------------------------------------------------

record ConfiguredPhysicalComponentLosses
    (Scale Polymer : Set) : Set₁ where
  field
    haarLoss determinantLoss bchLoss localizationLoss patchLoss :
      Scale → Polymer → ℚ

    haarLossBelowComputed : ∀ scale polymer →
      haarLoss scale polymer ≤ configuredHaarUpper

    relativeOperatorNormBelowHalf : ∀ scale polymer → Set
    localizedTraceNormBelowEighth : ∀ scale polymer → Set
    traceLogEstimateExact : ∀ scale polymer →
      determinantLoss scale polymer ≤ configuredDeterminantUpper

    quaternionCubicRemainderBelowComputed : ∀ scale polymer →
      bchLoss scale polymer ≤ configuredBCHUpper

    localizationLossBelowComputed : ∀ scale polymer →
      localizationLoss scale polymer ≤ configuredLocalizationUpper

    patchLossBelowComputed : ∀ scale polymer →
      patchLoss scale polymer ≤ configuredPatchUpper

    transitive : ∀ {left middle right : ℚ} →
      left ≤ middle → middle ≤ right → left ≤ right

open ConfiguredPhysicalComponentLosses public

haarLossBelowConfigured :
  ∀ {Scale Polymer}
    (dataSet : ConfiguredPhysicalComponentLosses Scale Polymer)
    scale polymer →
  haarLoss dataSet scale polymer ≤ Budget.configuredJacobianLoss
haarLossBelowConfigured dataSet scale polymer =
  transitive dataSet
    (haarLossBelowComputed dataSet scale polymer)
    configuredHaarBelowAllocated

determinantLossBelowConfigured :
  ∀ {Scale Polymer}
    (dataSet : ConfiguredPhysicalComponentLosses Scale Polymer)
    scale polymer →
  determinantLoss dataSet scale polymer ≤ Budget.configuredDeterminantLoss
determinantLossBelowConfigured dataSet scale polymer =
  Relation.Binary.PropositionalEquality.subst
    (λ upper → determinantLoss dataSet scale polymer ≤ upper)
    configuredDeterminantUpperExact
    (traceLogEstimateExact dataSet scale polymer)
  where
  open import Relation.Binary.PropositionalEquality

bchLossBelowConfigured :
  ∀ {Scale Polymer}
    (dataSet : ConfiguredPhysicalComponentLosses Scale Polymer)
    scale polymer →
  bchLoss dataSet scale polymer ≤ Budget.configuredBCHLoss
bchLossBelowConfigured dataSet scale polymer =
  transitive dataSet
    (quaternionCubicRemainderBelowComputed dataSet scale polymer)
    configuredBCHBelowAllocated

localizationLossBelowConfigured :
  ∀ {Scale Polymer}
    (dataSet : ConfiguredPhysicalComponentLosses Scale Polymer)
    scale polymer →
  localizationLoss dataSet scale polymer ≤ Budget.configuredLocalizationLoss
localizationLossBelowConfigured dataSet scale polymer =
  Relation.Binary.PropositionalEquality.subst
    (λ upper → localizationLoss dataSet scale polymer ≤ upper)
    configuredLocalizationUpperExact
    (localizationLossBelowComputed dataSet scale polymer)
  where
  open import Relation.Binary.PropositionalEquality

patchLossBelowConfigured :
  ∀ {Scale Polymer}
    (dataSet : ConfiguredPhysicalComponentLosses Scale Polymer)
    scale polymer →
  patchLoss dataSet scale polymer ≤ Budget.configuredPatchLoss
patchLossBelowConfigured dataSet scale polymer =
  Relation.Binary.PropositionalEquality.subst
    (λ upper → patchLoss dataSet scale polymer ≤ upper)
    configuredPatchUpperExact
    (patchLossBelowComputed dataSet scale polymer)
  where
  open import Relation.Binary.PropositionalEquality

configuredComponentArithmeticLevel : ProofLevel
configuredComponentArithmeticLevel = machineChecked

configuredComponentBudgetReductionLevel : ProofLevel
configuredComponentBudgetReductionLevel = machineChecked

physicalHaarTraceQuaternionLocalizationPatchInputsLevel : ProofLevel
physicalHaarTraceQuaternionLocalizationPatchInputsLevel = conditional
