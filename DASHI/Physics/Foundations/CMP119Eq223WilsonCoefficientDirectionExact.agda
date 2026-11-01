{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119Eq223WilsonCoefficientDirectionExact where

------------------------------------------------------------------------
-- EXACT EQ.(2.23) WILSON-COEFFICIENT DIRECTION.
--
-- Hold the Wilson basis object and every E/R/B/vacuum sector fixed.  The
-- canonical Eq.(2.23) assembly is affine in its Wilson coefficient:
--
--   S(c + delta) = delta * W + S(c).
--
-- This is stronger than a projector statement: it is equality of the full
-- two-coordinate LocalizedAction.  Hence the finite source insertion selected
-- by varying only the Wilson coefficient is exactly the literal Wilson action
-- term.  No E/R/B/vacuum variation contaminates this direction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact as Canonical
import DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceEq223SectorProjectionExact as Selected

canonicalCoefficientShift :
  ∀ c delta w e r b v →
  Canonical.canonicalAssemble (c + delta) w e r b v
  ≡
  T4.addLocalizedAction
    (T4.scaleLocalizedAction delta w)
    (Canonical.canonicalAssemble c w e r b v)
canonicalCoefficientShift
    c delta
    (T4.localizedAction wc wr)
    (T4.localizedAction ec er)
    (T4.localizedAction rc rr)
    (T4.localizedAction bc br)
    (T4.localizedAction vc vr) =
  cong₂ T4.localizedAction
    (Ring.solve-∀ c delta wc ec rc bc vc)
    (Ring.solve-∀ c delta wr er rr br vr)

canonicalPlaquetteCoefficientShift :
  ∀ c delta e r b v →
  Canonical.canonicalAssemble
    (c + delta) T4.plaquetteBasisAction e r b v
  ≡
  T4.addLocalizedAction
    (T4.plaquetteRelevantAction delta)
    (Canonical.canonicalAssemble
      c T4.plaquetteBasisAction e r b v)
canonicalPlaquetteCoefficientShift c delta e r b v =
  canonicalCoefficientShift
    c delta T4.plaquetteBasisAction e r b v

module _
  {Density Background Fluctuation : Set}
  (source : CMP119.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  (meaning : Selected.SelectedEq223RationalActionInterpretation source)
  where

  sourceCoefficientShift :
    ∀ c delta w e r b v →
    CMP119.assemble (CMP119.actionAlgebra source)
      (c + delta) w e r b v
    ≡
    T4.addLocalizedAction
      (T4.scaleLocalizedAction delta w)
      (CMP119.assemble (CMP119.actionAlgebra source)
        c w e r b v)
  sourceCoefficientShift c delta w e r b v =
    trans
      (Selected.sourceAssemblyPreservesLocalizedAction meaning
        (c + delta) w e r b v)
      (trans
        (canonicalCoefficientShift c delta w e r b v)
        (cong
          (T4.addLocalizedAction (T4.scaleLocalizedAction delta w))
          (sym
            (Selected.sourceAssemblyPreservesLocalizedAction meaning
              c w e r b v))))

  selectedScaleWilsonCoefficientShift :
    ∀ scale delta →
    CMP119.assemble (CMP119.actionAlgebra source)
      (CMP119.wilsonCoefficient source scale + delta)
      (CMP119.wilsonActionTerm source scale)
      (CMP119.regularSmallFieldTerm source scale)
      (CMP119.rOperationTerm source scale)
      (CMP119.boundaryTerm source scale)
      (CMP119.vacuumEnergy source scale)
    ≡
    T4.addLocalizedAction
      (T4.scaleLocalizedAction delta
        (CMP119.wilsonActionTerm source scale))
      (CMP119.effectiveAction source scale)
  selectedScaleWilsonCoefficientShift scale delta =
    trans
      (sourceCoefficientShift
        (CMP119.wilsonCoefficient source scale)
        delta
        (CMP119.wilsonActionTerm source scale)
        (CMP119.regularSmallFieldTerm source scale)
        (CMP119.rOperationTerm source scale)
        (CMP119.boundaryTerm source scale)
        (CMP119.vacuumEnergy source scale))
      (cong
        (T4.addLocalizedAction
          (T4.scaleLocalizedAction delta
            (CMP119.wilsonActionTerm source scale)))
        (sym (CMP119.equation223 source scale)))

eq223WilsonCoefficientDirectionIsExact : Bool
eq223WilsonCoefficientDirectionIsExact = true

eq223CoefficientDirectionAddsNoERBVVariation : Bool
eq223CoefficientDirectionAddsNoERBVVariation = true

finiteWilsonInsertionNoLongerSemanticDebt : Bool
finiteWilsonInsertionNoLongerSemanticDebt = true
