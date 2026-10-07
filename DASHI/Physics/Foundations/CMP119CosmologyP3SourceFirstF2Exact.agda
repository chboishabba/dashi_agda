{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3SourceFirstF2Exact where

------------------------------------------------------------------------
-- S3a SOURCE-FIRST F^2 SELECTION.
--
-- A completed marked-curvature family already constructs the continuum local
-- operator for every curvature polynomial.  Therefore, once the physical F^2
-- polynomial is selected, the preferred construction should choose the literal
-- Clay curvature operator FROM that source family rather than choose an
-- unrelated operator first and later demand a same-object equality.
--
-- This does not manufacture the marked source.  Its Hilbert modulus,
-- gauge/local semantics and completed-state provenance remain the genuine
-- analytic construction.  What disappears is only the post-hoc equation
--
--   completed marked F^2 = independently selected literal F^2.
--
-- On the source-first construction that equation is definitional.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature
import DASHI.Physics.YangMills.YangMillsSourceFirstCurvatureChoiceRound523Exact as R523

record SourceFirstPhysicalF2Choice
    (C : Top.LiteralYangMillsCarriers) : Set₂ where
  field
    curvatureChoice : R523.SourceFirstCurvatureChoice C

    fieldStrengthSquarePolynomial :
      Top.CompactSimpleGroup C → Top.CurvaturePolynomial C

open SourceFirstPhysicalF2Choice public

selectedMarkedF2 :
  ∀ {C} →
  SourceFirstPhysicalF2Choice C →
  (group : Top.CompactSimpleGroup C) →
  Top.LocalOperator C
selectedMarkedF2 data group =
  Curvature.localOperator
    (R523.family (curvatureChoice data) group)
    (fieldStrengthSquarePolynomial data group)

selectedLiteralF2 :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S) →
  SourceFirstPhysicalF2Choice C →
  (group : Top.CompactSimpleGroup C) →
  Top.LocalOperator C
selectedLiteralF2 Y data group =
  Top.curvatureOperator
    (R523.withSourceFirstCurvature Y (curvatureChoice data))
    group
    (fieldStrengthSquarePolynomial data group)

selectedMarkedF2IsChosenLiteralF2 :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (data : SourceFirstPhysicalF2Choice C)
    group →
  selectedMarkedF2 data group ≡ selectedLiteralF2 Y data group
selectedMarkedF2IsChosenLiteralF2 Y data group = refl

selectedPhysicalF2GaugeInvariant :
  ∀ {C}
    (data : SourceFirstPhysicalF2Choice C)
    group →
  Curvature.GaugeInvariant
    (R523.family (curvatureChoice data) group)
    (selectedMarkedF2 data group)
selectedPhysicalF2GaugeInvariant data group =
  R523.selectedCurvatureGaugeInvariant
    (curvatureChoice data) group
    (fieldStrengthSquarePolynomial data group)

selectedPhysicalF2Local :
  ∀ {C}
    (data : SourceFirstPhysicalF2Choice C)
    group position →
  Curvature.LocalAt
    (R523.family (curvatureChoice data) group)
    (selectedMarkedF2 data group)
    position
selectedPhysicalF2Local data group position =
  R523.selectedCurvatureLocal
    (curvatureChoice data) group
    (fieldStrengthSquarePolynomial data group)
    position

postHocCompletedF2EqualityRequired : Bool
postHocCompletedF2EqualityRequired = false

physicalMarkedCurvatureFamilyStillRequired : Bool
physicalMarkedCurvatureFamilyStillRequired = true

sourceFirstF2SelectionMakesLiteralEqualityDefinitional : Bool
sourceFirstF2SelectionMakesLiteralEqualityDefinitional = true
