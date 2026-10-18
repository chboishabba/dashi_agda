{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsActualGroupFiveBlockConstructorRound570Exact where

------------------------------------------------------------------------
-- GOAL-1 G1 / ROUND570:
-- BUILD THE FIVE-BLOCK SOURCE ON THE ACTUAL-GROUP QUANTITATIVE PACKAGE
--
-- R569 fixes the quantitative Lie/group operations to the actual
-- CompactSimpleLieGroup.  Do the same for the G1 five-block object: callers
-- provide only the physical scalar source maps and inequalities.  The
-- quantitative package is inserted by the constructor, so the historical
-- fiveBlockQuantitativeIsAligned field is refl.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as Structural
import DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeConstructorRound569Exact as R569
import DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeAlignmentRound541Exact as R541
import DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact as G1
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector

record ActualGroupFiveBlockPhysicalData
    (GaugeIndex X : Set)
    (structural : Structural.StructuralSourceBundle GaugeIndex X)
    (quantitative :
      R569.ActualGroupQuantitativeSource GaugeIndex X structural)
    (group : GaugeIndex)
    : Set₁ where
  field
    Configuration : Set
    InCertifiedRegion : Configuration → Set

    charge raw1 raw2 raw3 raw4 green11 :
      Configuration → ℚ

    chargeNonnegative :
      ∀ configuration →
      InCertifiedRegion configuration →
      0ℚ ≤ charge configuration

    raw1Ratio raw2Ratio raw3Ratio raw4Ratio
      green11LowerRatio : ℚ

    raw1RelativeSound :
      ∀ configuration →
      InCertifiedRegion configuration →
      raw1 configuration
      ≤ raw1Ratio * charge configuration

    raw2RelativeSound :
      ∀ configuration →
      InCertifiedRegion configuration →
      raw2 configuration
      ≤ raw2Ratio * charge configuration

    raw3RelativeSound :
      ∀ configuration →
      InCertifiedRegion configuration →
      raw3 configuration
      ≤ raw3Ratio * charge configuration

    raw4RelativeSound :
      ∀ configuration →
      InCertifiedRegion configuration →
      raw4 configuration
      ≤ raw4Ratio * charge configuration

    green11RelativeLowerSound :
      ∀ configuration →
      InCertifiedRegion configuration →
      green11LowerRatio * charge configuration
      ≤ green11 configuration

    fiveBlockCoefficientFits :
      raw1Ratio + raw2Ratio + raw3Ratio + raw4Ratio
        - green11LowerRatio
      ≤ Selector.remainingSingletonCoefficient

open ActualGroupFiveBlockPhysicalData public

asGroupParametricFiveBlock :
  ∀ {GaugeIndex X structural quantitative group} →
  ActualGroupFiveBlockPhysicalData
    GaugeIndex X structural quantitative group →
  G1.GroupParametricFiveBlockG2Data
    (Structural.LieCarrier structural group)
    (Structural.GroupCarrier structural group)
    (R569.classification quantitative group)
asGroupParametricFiveBlock {quantitative = quantitative} {group = group} data = record
  { G1.GroupParametricFiveBlockG2Data.quantitativeLiePackage =
      R569.asQuantitativeCompactLiePackage
        (R569.quantitativeData quantitative group)
  ; G1.GroupParametricFiveBlockG2Data.Configuration =
      Configuration data
  ; G1.GroupParametricFiveBlockG2Data.InCertifiedRegion =
      InCertifiedRegion data
  ; G1.GroupParametricFiveBlockG2Data.charge =
      charge data
  ; G1.GroupParametricFiveBlockG2Data.raw1 =
      raw1 data
  ; G1.GroupParametricFiveBlockG2Data.raw2 =
      raw2 data
  ; G1.GroupParametricFiveBlockG2Data.raw3 =
      raw3 data
  ; G1.GroupParametricFiveBlockG2Data.raw4 =
      raw4 data
  ; G1.GroupParametricFiveBlockG2Data.green11 =
      green11 data
  ; G1.GroupParametricFiveBlockG2Data.chargeNonnegative =
      chargeNonnegative data
  ; G1.GroupParametricFiveBlockG2Data.raw1Ratio =
      raw1Ratio data
  ; G1.GroupParametricFiveBlockG2Data.raw2Ratio =
      raw2Ratio data
  ; G1.GroupParametricFiveBlockG2Data.raw3Ratio =
      raw3Ratio data
  ; G1.GroupParametricFiveBlockG2Data.raw4Ratio =
      raw4Ratio data
  ; G1.GroupParametricFiveBlockG2Data.green11LowerRatio =
      green11LowerRatio data
  ; G1.GroupParametricFiveBlockG2Data.raw1RelativeSound =
      raw1RelativeSound data
  ; G1.GroupParametricFiveBlockG2Data.raw2RelativeSound =
      raw2RelativeSound data
  ; G1.GroupParametricFiveBlockG2Data.raw3RelativeSound =
      raw3RelativeSound data
  ; G1.GroupParametricFiveBlockG2Data.raw4RelativeSound =
      raw4RelativeSound data
  ; G1.GroupParametricFiveBlockG2Data.green11RelativeLowerSound =
      green11RelativeLowerSound data
  ; G1.GroupParametricFiveBlockG2Data.fiveBlockCoefficientFits =
      fiveBlockCoefficientFits data
  }

record ActualGroupFiveBlockCompleteSource
    (GaugeIndex X : Set)
    (structural : Structural.StructuralSourceBundle GaugeIndex X)
    (quantitative :
      R569.ActualGroupQuantitativeSource GaugeIndex X structural)
    : Set₂ where
  field
    physical :
      ∀ group →
      ActualGroupFiveBlockPhysicalData
        GaugeIndex X structural quantitative group

open ActualGroupFiveBlockCompleteSource public

asR541FiveBlockSource :
  ∀ {GaugeIndex X}
    {structural : Structural.StructuralSourceBundle GaugeIndex X}
    (quantitative :
      R569.ActualGroupQuantitativeSource GaugeIndex X structural) →
  ActualGroupFiveBlockCompleteSource
    GaugeIndex X structural quantitative →
  R541.ActualGroupFiveBlockSource
    GaugeIndex X structural
    (R569.asActualGroupQuantitativeAlignment quantitative)
asR541FiveBlockSource quantitative source = record
  { R541.ActualGroupFiveBlockSource.fiveBlock =
      λ group →
        asGroupParametricFiveBlock
          (physical source group)
  ; R541.ActualGroupFiveBlockSource.fiveBlockQuantitativeIsAligned =
      λ group → refl
  }

round570FiveBlockConstructorLevel : ProofLevel
round570FiveBlockConstructorLevel = machineChecked

round570FiveBlockAlignmentLevel : ProofLevel
round570FiveBlockAlignmentLevel = machineChecked

-- Genuine G1 physical theorem after constructor specialization:
-- construct the five charge-relative scalar estimates on every actual G.
literalRound570ActualGroupFiveBlockPhysicalDataLevel : ProofLevel
literalRound570ActualGroupFiveBlockPhysicalDataLevel = conditional
