{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSSelectedWilsonH2Exact where

------------------------------------------------------------------------
-- H2(ii) ON THE EXACT H1/H3 SELECTED TESTS.
--
-- R278 already proves
--
--   E_n[F] -> E[F],  E_n[G] -> E[G],  E_n[FG] -> E[FG]
--
-- for bounded selected tests.  The physical same-object payment is therefore
-- only that the exact R278 left/right tests used by the R467/R281 mass-gap
-- chain are literal finite Wilson-cylinder products on the SAME observable
-- algebra, with the same multiplication and bound predicate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSameHGapExact as Direct
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo

record LiteralSelectedWilsonExpectationApplication
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {G : Top.CompactSimpleGroup C}
    (direct :
      Direct.LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G)
    : Set₂ where
  field
    Loop : Set

    wilson :
      Thermo.WilsonCylinderBoundData
        Loop (Top.Observable C) ℚ

    leftLoops rightLoops :
      R278.Index (Direct.tests direct) → List Loop

    leftIsLiteralWilsonProduct :
      ∀ index →
      R278.left (Direct.tests direct) index
      ≡
      Thermo.productLoopObservable wilson (leftLoops index)

    rightIsLiteralWilsonProduct :
      ∀ index →
      R278.right (Direct.tests direct) index
      ≡
      Thermo.productLoopObservable wilson (rightLoops index)

    wilsonMultiplyIsSelectedMultiply :
      ∀ left right →
      Thermo.multiplyObservable wilson left right
      ≡
      Gram.multiplyObservable
        (Gram.operations (Direct.dataSet direct))
        left right

    wilsonBoundImpliesSelectedBounded :
      ∀ observable bound →
      Thermo.Bound wilson observable bound →
      Gram.BoundedObservable (Direct.dataSet direct) observable

open LiteralSelectedWilsonExpectationApplication public

wilsonProductBounded :
  ∀ {C S Y G direct}
    (application :
      LiteralSelectedWilsonExpectationApplication
        {C = C} {S = S} {Y = Y} {G = G} direct)
    loops →
  Gram.BoundedObservable (Direct.dataSet direct)
    (Thermo.productLoopObservable (wilson application) loops)
wilsonProductBounded application loops =
  wilsonBoundImpliesSelectedBounded application
    (Thermo.productLoopObservable (wilson application) loops)
    (Thermo.productLoopBound (wilson application) loops)
    (Thermo.finiteProductWilsonObservableUniformBound
      (wilson application) loops)

leftSelectedBounded :
  ∀ {C S Y G direct}
    (application :
      LiteralSelectedWilsonExpectationApplication
        {C = C} {S = S} {Y = Y} {G = G} direct)
    index →
  Gram.BoundedObservable (Direct.dataSet direct)
    (R278.left (Direct.tests direct) index)
leftSelectedBounded application index =
  subst
    (Gram.BoundedObservable (Direct.dataSet _))
    (sym (leftIsLiteralWilsonProduct application index))
    (wilsonProductBounded application (leftLoops application index))

rightSelectedBounded :
  ∀ {C S Y G direct}
    (application :
      LiteralSelectedWilsonExpectationApplication
        {C = C} {S = S} {Y = Y} {G = G} direct)
    index →
  Gram.BoundedObservable (Direct.dataSet direct)
    (R278.right (Direct.tests direct) index)
rightSelectedBounded application index =
  subst
    (Gram.BoundedObservable (Direct.dataSet _))
    (sym (rightIsLiteralWilsonProduct application index))
    (wilsonProductBounded application (rightLoops application index))

selectedProductBounded :
  ∀ {C S Y G direct}
    (application :
      LiteralSelectedWilsonExpectationApplication
        {C = C} {S = S} {Y = Y} {G = G} direct)
    index →
  Gram.BoundedObservable (Direct.dataSet direct)
    (Gram.multiplyObservable
      (Gram.operations (Direct.dataSet direct))
      (R278.left (Direct.tests direct) index)
      (R278.right (Direct.tests direct) index))
selectedProductBounded application index =
  let
    w = wilson application
    leftW = Thermo.productLoopObservable w (leftLoops application index)
    rightW = Thermo.productLoopObservable w (rightLoops application index)

    productWilsonBound =
      Thermo.multiplyBound w
        leftW rightW
        (Thermo.productLoopBound w (leftLoops application index))
        (Thermo.productLoopBound w (rightLoops application index))
        (Thermo.finiteProductWilsonObservableUniformBound
          w (leftLoops application index))
        (Thermo.finiteProductWilsonObservableUniformBound
          w (rightLoops application index))

    productBoundedWilson :
      Gram.BoundedObservable (Direct.dataSet _)
        (Thermo.multiplyObservable w leftW rightW)
    productBoundedWilson =
      wilsonBoundImpliesSelectedBounded application
        (Thermo.multiplyObservable w leftW rightW)
        (Thermo.multiplyScalar w
          (Thermo.productLoopBound w (leftLoops application index))
          (Thermo.productLoopBound w (rightLoops application index)))
        productWilsonBound

    productBoundedSelected :
      Gram.BoundedObservable (Direct.dataSet _)
        (Gram.multiplyObservable
          (Gram.operations (Direct.dataSet _))
          leftW rightW)
    productBoundedSelected =
      subst
        (Gram.BoundedObservable (Direct.dataSet _))
        (wilsonMultiplyIsSelectedMultiply application leftW rightW)
        productBoundedWilson

    targetEquality :
      Gram.multiplyObservable
        (Gram.operations (Direct.dataSet _))
        (R278.left (Direct.tests _) index)
        (R278.right (Direct.tests _) index)
      ≡
      Gram.multiplyObservable
        (Gram.operations (Direct.dataSet _))
        leftW rightW
    targetEquality
      rewrite leftIsLiteralWilsonProduct application index
            | rightIsLiteralWilsonProduct application index = refl
  in
  subst
    (Gram.BoundedObservable (Direct.dataSet _))
    (sym targetEquality)
    productBoundedSelected

record LiteralSelectedWilsonExpectationLimits
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {G : Top.CompactSimpleGroup C}
    {direct :
      Direct.LiteralGroupDirectSourceSameHGap
        {C = C} {S = S} Y G}
    (application : LiteralSelectedWilsonExpectationApplication direct)
    (index : R278.Index (Direct.tests direct))
    : Set₁ where
  field
    leftExpectationConverges :
      Gram.Converges
        (Gram.scalarConvergence (Direct.dataSet direct))
        (λ cutoff →
          Gram.expectation (Gram.operations (Direct.dataSet direct))
            (Gram.measureSequence (Direct.dataSet direct) cutoff)
            (R278.left (Direct.tests direct) index))
        (Gram.expectation (Gram.operations (Direct.dataSet direct))
          (Gram.continuumMeasure (Direct.dataSet direct))
          (R278.left (Direct.tests direct) index))

    rightExpectationConverges :
      Gram.Converges
        (Gram.scalarConvergence (Direct.dataSet direct))
        (λ cutoff →
          Gram.expectation (Gram.operations (Direct.dataSet direct))
            (Gram.measureSequence (Direct.dataSet direct) cutoff)
            (R278.right (Direct.tests direct) index))
        (Gram.expectation (Gram.operations (Direct.dataSet direct))
          (Gram.continuumMeasure (Direct.dataSet direct))
          (R278.right (Direct.tests direct) index))

    productExpectationConverges :
      Gram.Converges
        (Gram.scalarConvergence (Direct.dataSet direct))
        (λ cutoff →
          Gram.expectation (Gram.operations (Direct.dataSet direct))
            (Gram.measureSequence (Direct.dataSet direct) cutoff)
            (Gram.multiplyObservable
              (Gram.operations (Direct.dataSet direct))
              (R278.left (Direct.tests direct) index)
              (R278.right (Direct.tests direct) index)))
        (Gram.expectation (Gram.operations (Direct.dataSet direct))
          (Gram.continuumMeasure (Direct.dataSet direct))
          (Gram.multiplyObservable
            (Gram.operations (Direct.dataSet direct))
            (R278.left (Direct.tests direct) index)
            (R278.right (Direct.tests direct) index)))

open LiteralSelectedWilsonExpectationLimits public

selectedWilsonExpectationLimits :
  ∀ {C S Y G direct}
    (application :
      LiteralSelectedWilsonExpectationApplication
        {C = C} {S = S} {Y = Y} {G = G} direct)
    index →
  LiteralSelectedWilsonExpectationLimits application index
selectedWilsonExpectationLimits {direct = direct} application index = record
  { LiteralSelectedWilsonExpectationLimits.leftExpectationConverges =
      R278.selectedExpectationConverges
        (Direct.dataSet direct)
        (R278.left (Direct.tests direct) index)
        (leftSelectedBounded application index)
  ; LiteralSelectedWilsonExpectationLimits.rightExpectationConverges =
      R278.selectedExpectationConverges
        (Direct.dataSet direct)
        (R278.right (Direct.tests direct) index)
        (rightSelectedBounded application index)
  ; LiteralSelectedWilsonExpectationLimits.productExpectationConverges =
      R278.selectedExpectationConverges
        (Direct.dataSet direct)
        (Gram.multiplyObservable
          (Gram.operations (Direct.dataSet direct))
          (R278.left (Direct.tests direct) index)
          (R278.right (Direct.tests direct) index))
        (selectedProductBounded application index)
  }

directSelectedWilsonH2CompilerLevel : ProofLevel
directSelectedWilsonH2CompilerLevel = machineChecked

-- H2(ii) physical payment after the max-cut: one same-carrier Wilson-cylinder
-- presentation of the exact selected tests.  The three expectation limits are
-- compiler output.
directSelectedWilsonH2SameCarrierPresentationLevel : ProofLevel
directSelectedWilsonH2SameCarrierPresentationLevel = conditional
