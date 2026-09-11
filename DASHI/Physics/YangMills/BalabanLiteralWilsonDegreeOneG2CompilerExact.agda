{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralWilsonDegreeOneG2CompilerExact where

------------------------------------------------------------------------
-- LITERAL WILSON -> SHARP DEGREE-ONE G2 COMPILER
--
-- The current sharp selected-region G2 route has already proved:
--
--   * all Green degree blocks except G_11 vanish exactly;
--   * the degree-one defect norm is exactly (1/3) times the plaquette charge;
--   * the degree-one source state is exactly the literal Wilson first
--     variation, not an independent KKT/Moebius object.
--
-- Therefore the physical producer can be stated directly on the literal
-- Wilson carrier.  It supplies only:
--
--   (A) four charge-relative raw degree bounds;
--   (B) one charge-relative norm-square bound for the literal Wilson gradient.
--
-- One rational coefficient check then feeds the already-proved exact-defect
-- degree-one G2 compiler.  No K+ row bound, positive charge floor, higher Green
-- degree norm, or independent defect estimate is part of this interface.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as Blocks
import DASHI.Physics.YangMills.BalabanCanonicalGreenStateNormReductionExact as StateNorm
import DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ClosureExact as G2
import DASHI.Physics.YangMills.BalabanChargeRelativeDegreeOneG2ExactDefectCompiler as ExactDefect
import DASHI.Physics.YangMills.BalabanLiteralWilsonSourceDegreeOneStateCollapseExact as Collapse
import DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact as WilsonSource
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership

record LiteralWilsonDegreeOneG2Data
    (Configuration Multiplier : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    pseudoDataAt : Configuration →
      Pseudo.FiniteKKTPseudoinverseData Multiplier
    backgroundAt : Configuration → Plaquette.RationalSU2Background4
    bondFieldAt : Configuration → Physical.PhysicalSU2BondField4
    plaquetteAt : Configuration → Plaquette.Plaquette4

    canonicalInputsAt : ∀ configuration →
      Canonical.CanonicalSubsetCorrelatedAuthorityInputs
        (pseudoDataAt configuration)
        (WilsonSource.plaquetteFirstVariationCovector
          (backgroundAt configuration) (plaquetteAt configuration))
        (bondFieldAt configuration)
        (plaquetteAt configuration)

    chargeNonnegative : ∀ configuration →
      InCertifiedRegion configuration →
      0ℚ ≤ Wilson.plaquetteCrossCharge
        (bondFieldAt configuration) (plaquetteAt configuration)

    rawRatio : Degree.MobiusDegree → ℚ
    wilsonGradientNormRatio : ℚ

    rawRelativeSound : ∀ configuration →
      InCertifiedRegion configuration → ∀ degree →
      Blocks.canonicalRawDegreeBlock
        (canonicalInputsAt configuration) degree
      ≤ rawRatio degree
        * Wilson.plaquetteCrossCharge
            (bondFieldAt configuration) (plaquetteAt configuration)

    literalWilsonGradientNormRelativeSound : ∀ configuration →
      InCertifiedRegion configuration →
      Rect.finiteNormSq KKT.physicalStateCarrier
        (WilsonSource.plaquetteFirstVariationCovector
          (backgroundAt configuration) (plaquetteAt configuration))
      ≤ wilsonGradientNormRatio
        * Wilson.plaquetteCrossCharge
            (bondFieldAt configuration) (plaquetteAt configuration)

open LiteralWilsonDegreeOneG2Data public

sourceDegreeOneNormRelativeSound :
  ∀ {Configuration Multiplier}
    (dataSet : LiteralWilsonDegreeOneG2Data Configuration Multiplier)
    configuration → InCertifiedRegion dataSet configuration →
  StateNorm.sourceStateNormSq
      (canonicalInputsAt dataSet configuration) Degree.degree1
  ≤ wilsonGradientNormRatio dataSet
      * Wilson.plaquetteCrossCharge
          (bondFieldAt dataSet configuration) (plaquetteAt dataSet configuration)
sourceDegreeOneNormRelativeSound dataSet configuration inRegion =
  subst
    (λ lower → lower ≤
      wilsonGradientNormRatio dataSet
        * Wilson.plaquetteCrossCharge
            (bondFieldAt dataSet configuration) (plaquetteAt dataSet configuration))
    (sym
      (Collapse.literalWilsonSourceDegreeOneNormExact
        (backgroundAt dataSet configuration)
        (bondFieldAt dataSet configuration)
        (plaquetteAt dataSet configuration)
        (canonicalInputsAt dataSet configuration)))
    (literalWilsonGradientNormRelativeSound dataSet configuration inRegion)

toExactDefectDegreeOneG2Data :
  ∀ {Configuration Multiplier} →
  LiteralWilsonDegreeOneG2Data Configuration Multiplier →
  ExactDefect.ExactDefectDegreeOneG2Data Configuration Multiplier
toExactDefectDegreeOneG2Data dataSet = record
  { ExactDefect.ExactDefectDegreeOneG2Data.InCertifiedRegion =
      InCertifiedRegion dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.selectedMinimizer =
      selectedMinimizer dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.selectedMinimizerInRegion =
      selectedMinimizerInRegion dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.pseudoDataAt = pseudoDataAt dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.firstVariationAt =
      λ configuration → WilsonSource.plaquetteFirstVariationCovector
        (backgroundAt dataSet configuration) (plaquetteAt dataSet configuration)
  ; ExactDefect.ExactDefectDegreeOneG2Data.bondFieldAt = bondFieldAt dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.plaquetteAt = plaquetteAt dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.canonicalInputsAt =
      canonicalInputsAt dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.chargeNonnegative =
      chargeNonnegative dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.rawRatio = rawRatio dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.sourceDegreeOneNormRatio =
      wilsonGradientNormRatio dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.rawRelativeSound =
      rawRelativeSound dataSet
  ; ExactDefect.ExactDefectDegreeOneG2Data.sourceDegreeOneNormRelativeSound =
      sourceDegreeOneNormRelativeSound dataSet
  }

literalWilsonResidualRatio :
  ∀ {Configuration Multiplier} →
  LiteralWilsonDegreeOneG2Data Configuration Multiplier → ℚ
literalWilsonResidualRatio dataSet =
  ExactDefect.exactDefectResidualRatio (toExactDefectDegreeOneG2Data dataSet)

record LiteralWilsonDegreeOneG2Closure
    {Configuration Multiplier}
    (dataSet : LiteralWilsonDegreeOneG2Data Configuration Multiplier) : Set where
  field
    ratioFitsTarget :
      literalWilsonResidualRatio dataSet ≤ Selector.remainingSingletonCoefficient

open LiteralWilsonDegreeOneG2Closure public

asDegreeOneClosure :
  ∀ {Configuration Multiplier}
    {dataSet : LiteralWilsonDegreeOneG2Data Configuration Multiplier} →
  LiteralWilsonDegreeOneG2Closure dataSet →
  G2.ChargeRelativeDegreeOneG2Closure
    (ExactDefect.toDegreeOneG2Data (toExactDefectDegreeOneG2Data dataSet))
asDegreeOneClosure closure = record
  { G2.ChargeRelativeDegreeOneG2Closure.ratioFitsTarget = ratioFitsTarget closure }

literalWilsonSelectedMinimizerG2Closes :
  ∀ {Configuration Multiplier}
    (dataSet : LiteralWilsonDegreeOneG2Data Configuration Multiplier)
    (closure : LiteralWilsonDegreeOneG2Closure dataSet) →
  Ownership.correlatedResidualTotal
    (Blocks.canonicalFamily
      (canonicalInputsAt dataSet (selectedMinimizer dataSet)))
  ≤ Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge
          (bondFieldAt dataSet (selectedMinimizer dataSet))
          (plaquetteAt dataSet (selectedMinimizer dataSet))
literalWilsonSelectedMinimizerG2Closes dataSet closure =
  G2.selectedMinimizerDegreeOneG2Closes
    (ExactDefect.toDegreeOneG2Data (toExactDefectDegreeOneG2Data dataSet))
    (asDegreeOneClosure closure)

literalWilsonDegreeOneG2CompilerLevel : ProofLevel
literalWilsonDegreeOneG2CompilerLevel = machineChecked

-- Genuine physical inputs after this compiler:
--   * aggregate/four-degree raw localization relative to plaquette cross charge;
--   * literal Wilson first-variation norm-square relative to the same charge;
--   * one rational residual/headroom comparison.
-- No defect estimate or Green/pseudoinverse norm is independently required.
literalWilsonDegreeOneG2PhysicalBoundsLevel : ProofLevel
literalWilsonDegreeOneG2PhysicalBoundsLevel = conditional
