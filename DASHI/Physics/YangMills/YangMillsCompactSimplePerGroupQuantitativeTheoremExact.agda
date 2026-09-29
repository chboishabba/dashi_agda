{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCompactSimplePerGroupQuantitativeTheoremExact where

------------------------------------------------------------------------
-- G1 theorem-bearing constructor.
--
-- Structural compact-simple witnesses, quantitative bounds on their ACTUAL
-- operations, and the five charge-relative estimates are assembled directly
-- into R571.  Operation-equality and package-alignment debts remain erased by
-- the R569/R570 constructors.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as Structural
import DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeConstructorRound569Exact as R569
import DASHI.Physics.YangMills.YangMillsActualGroupFiveBlockConstructorRound570Exact as R570
import DASHI.Physics.YangMills.YangMillsActualGroupSourceFirstCompleteRound571Exact as R571

literalActualGroupSourceFirstComplete :
  ∀ {GaugeIndex X}
    (structural :
      Structural.StructuralSourceBundle GaugeIndex X)
    (quantitative :
      R569.ActualGroupQuantitativeSource GaugeIndex X structural)
    (fiveBlock :
      R570.ActualGroupFiveBlockCompleteSource
        GaugeIndex X structural quantitative) →
  R571.ActualGroupSourceFirstComplete GaugeIndex X
literalActualGroupSourceFirstComplete
    structural quantitative fiveBlock = record
  { R571.ActualGroupSourceFirstComplete.structural = structural
  ; R571.ActualGroupSourceFirstComplete.quantitative = quantitative
  ; R571.ActualGroupSourceFirstComplete.fiveBlock = fiveBlock
  }
