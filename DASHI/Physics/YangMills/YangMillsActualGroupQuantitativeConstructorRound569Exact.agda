{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeConstructorRound569Exact where

------------------------------------------------------------------------
-- GOAL-1 G1 / ROUND569:
-- CONSTRUCT THE QUANTITATIVE PACKAGE ON THE ACTUAL COMPACT-SIMPLE GROUP
--
-- R541 had to choose a classification-tag quantitative package and then prove
-- four same-object equations:
--
--   quantitative bracket = actual bracket
--   quantitative exp     = actual exp
--   quantitative log     = actual log
--   quantitative adjoint = actual Ad.
--
-- Those equations express a model choice.  R569 fixes the operations from the
-- proof-bearing CompactSimpleLieGroup in the constructor.  The remaining input
-- is genuinely quantitative: norms, local charts, BCH/Haar data, constants and
-- bounds on those ACTUAL operations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Quant
import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as Structural
import DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeAlignmentRound541Exact as R541

record ActualGroupQuantitativeData
    (Scalar LieElement GroupElement : Set)
    (actual : Core.CompactSimpleLieGroup GroupElement LieElement)
    (classification : Quant.CompactSimpleLieGroup)
    : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set

    norm : LieElement → Scalar
    distance : GroupElement → GroupElement → Scalar

    bch : LieElement → LieElement → LieElement
    haarDensity : LieElement → Scalar

    localRadius bracketConstant bchConstant expLogConstant
      adjointConstant haarDensityConstant : Scalar

    localRadiusPositive : StrictLess zero localRadius

    bracketBound : ∀ left right →
      LessEqual
        (norm (Core.bracket (Core.algebra actual) left right))
        (multiply bracketConstant (multiply (norm left) (norm right)))

    bchRemainder : LieElement → LieElement → LieElement
    bchRemainderBound : ∀ left right →
      LessEqual (norm (bchRemainder left right))
        (multiply bchConstant
          (multiply (add (norm left) (norm right))
            (multiply (add (norm left) (norm right))
              (add (norm left) (norm right)))))

    InLocalLieChart : LieElement → Set
    InLocalGroupChart : GroupElement → Set

    expLogLocalEquivalence :
      (∀ element →
        InLocalLieChart element →
        Core.log actual (Core.exp actual element) ≡ element)
      ×
      (∀ element →
        InLocalGroupChart element →
        Core.exp actual (Core.log actual element) ≡ element)

    adjointBound : ∀ group element →
      LessEqual
        (norm (Core.Ad actual group element))
        (multiply adjointConstant (norm element))

    haarLocalDensityBound : ∀ element →
      InLocalLieChart element →
      LessEqual (haarDensity element) haarDensityConstant

open ActualGroupQuantitativeData public

asQuantitativeCompactLiePackage :
  ∀ {Scalar LieElement GroupElement classification}
    {actual : Core.CompactSimpleLieGroup GroupElement LieElement} →
  ActualGroupQuantitativeData
    Scalar LieElement GroupElement actual classification →
  Quant.QuantitativeCompactLiePackage
    Scalar LieElement GroupElement classification
asQuantitativeCompactLiePackage {actual = actual} data = record
  { Quant.QuantitativeCompactLiePackage.zero =
      zero data
  ; Quant.QuantitativeCompactLiePackage.one =
      one data
  ; Quant.QuantitativeCompactLiePackage.add =
      add data
  ; Quant.QuantitativeCompactLiePackage.multiply =
      multiply data
  ; Quant.QuantitativeCompactLiePackage.LessEqual =
      LessEqual data
  ; Quant.QuantitativeCompactLiePackage.StrictLess =
      StrictLess data
  ; Quant.QuantitativeCompactLiePackage.norm =
      norm data
  ; Quant.QuantitativeCompactLiePackage.distance =
      distance data
  ; Quant.QuantitativeCompactLiePackage.bracket =
      Core.bracket (Core.algebra actual)
  ; Quant.QuantitativeCompactLiePackage.bch =
      bch data
  ; Quant.QuantitativeCompactLiePackage.exp =
      Core.exp actual
  ; Quant.QuantitativeCompactLiePackage.log =
      Core.log actual
  ; Quant.QuantitativeCompactLiePackage.adjoint =
      Core.Ad actual
  ; Quant.QuantitativeCompactLiePackage.haarDensity =
      haarDensity data
  ; Quant.QuantitativeCompactLiePackage.localRadius =
      localRadius data
  ; Quant.QuantitativeCompactLiePackage.bracketConstant =
      bracketConstant data
  ; Quant.QuantitativeCompactLiePackage.bchConstant =
      bchConstant data
  ; Quant.QuantitativeCompactLiePackage.expLogConstant =
      expLogConstant data
  ; Quant.QuantitativeCompactLiePackage.adjointConstant =
      adjointConstant data
  ; Quant.QuantitativeCompactLiePackage.haarDensityConstant =
      haarDensityConstant data
  ; Quant.QuantitativeCompactLiePackage.localRadiusPositive =
      localRadiusPositive data
  ; Quant.QuantitativeCompactLiePackage.bracketBound =
      bracketBound data
  ; Quant.QuantitativeCompactLiePackage.bchRemainder =
      bchRemainder data
  ; Quant.QuantitativeCompactLiePackage.bchRemainderBound =
      bchRemainderBound data
  ; Quant.QuantitativeCompactLiePackage.InLocalLieChart =
      InLocalLieChart data
  ; Quant.QuantitativeCompactLiePackage.InLocalGroupChart =
      InLocalGroupChart data
  ; Quant.QuantitativeCompactLiePackage.expLogLocalEquivalence =
      expLogLocalEquivalence data
  ; Quant.QuantitativeCompactLiePackage.adjointBound =
      adjointBound data
  ; Quant.QuantitativeCompactLiePackage.haarLocalDensityBound =
      haarLocalDensityBound data
  }

record ActualGroupQuantitativeSource
    (GaugeIndex X : Set)
    (structural : Structural.StructuralSourceBundle GaugeIndex X)
    : Set₂ where
  field
    classification :
      GaugeIndex → Quant.CompactSimpleLieGroup

    quantitativeData :
      ∀ group →
      ActualGroupQuantitativeData
        ℚ
        (Structural.LieCarrier structural group)
        (Structural.GroupCarrier structural group)
        (Structural.compactSimple structural group)
        (classification group)

open ActualGroupQuantitativeSource public

asActualGroupQuantitativeAlignment :
  ∀ {GaugeIndex X}
    {structural : Structural.StructuralSourceBundle GaugeIndex X} →
  ActualGroupQuantitativeSource GaugeIndex X structural →
  R541.ActualGroupQuantitativeAlignment
    GaugeIndex X structural
asActualGroupQuantitativeAlignment source = record
  { R541.ActualGroupQuantitativeAlignment.classification =
      classification source
  ; R541.ActualGroupQuantitativeAlignment.quantitative =
      λ group →
        asQuantitativeCompactLiePackage
          (quantitativeData source group)
  ; R541.ActualGroupQuantitativeAlignment.bracketIsActual =
      λ group left right → refl
  ; R541.ActualGroupQuantitativeAlignment.expIsActual =
      λ group element → refl
  ; R541.ActualGroupQuantitativeAlignment.logIsActual =
      λ group element → refl
  ; R541.ActualGroupQuantitativeAlignment.adjointIsActual =
      λ group groupElement lieElement → refl
  }

round569ActualGroupQuantitativeConstructorLevel : ProofLevel
round569ActualGroupQuantitativeConstructorLevel = machineChecked

round569BracketAlignmentLevel : ProofLevel
round569BracketAlignmentLevel = machineChecked

round569ExpLogAlignmentLevel : ProofLevel
round569ExpLogAlignmentLevel = machineChecked

round569AdjointAlignmentLevel : ProofLevel
round569AdjointAlignmentLevel = machineChecked

-- Genuine all-G analytic payment after the constructor refactor:
-- supply local quantitative estimates on the actual compact-simple group.
literalRound569ActualGroupQuantitativeBoundsLevel : ProofLevel
literalRound569ActualGroupQuantitativeBoundsLevel = conditional
