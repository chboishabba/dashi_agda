module DASHI.Analysis.SetoidComplexQuotientWeldValidation where

open import Agda.Builtin.Equality using (_≡_)
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.ConcreteComplex as LegacyComplex
import DASHI.Analysis.SetoidComplexQuotientWeldExact as Weld

------------------------------------------------------------------------
-- RED contract for the generic representation seam used by Moonshine.
--
-- A propositional quotient of a setoid real must not merely exist: its
-- arithmetic must commute with the quotient map strongly enough that the
-- componentwise complex quotient preserves the literal ConcreteComplex
-- operations used by q/E4/E6.
------------------------------------------------------------------------

complexAdditionWeld :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : Weld.PropositionalQuotientOperationCompatibility R Q) →
  ∀ left right →
  Weld.legacyComplex Q (Weld.addSC R left right)
    ≡ LegacyComplex._+C_
        (Weld.legacyComplex Q left)
        (Weld.legacyComplex Q right)
complexAdditionWeld = Weld.legacyComplexAdd

complexMultiplicationWeld :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : Weld.PropositionalQuotientOperationCompatibility R Q) →
  ∀ left right →
  Weld.legacyComplex Q (Weld.mulSC R left right)
    ≡ LegacyComplex._*C_
        (Weld.legacyComplex Q left)
        (Weld.legacyComplex Q right)
complexMultiplicationWeld = Weld.legacyComplexMul

complexNormSquareWeld :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : Weld.PropositionalQuotientOperationCompatibility R Q) →
  ∀ value →
  Spine.quotient Q (Weld.normSqSC R value)
    ≡ LegacyComplex.normSqC (Weld.legacyComplex Q value)
complexNormSquareWeld = Weld.legacyNormSq

complexConjugationWeld :
  ∀ {R : Spine.SetoidOrderedCompleteReal}
    {Q : Spine.PropositionalQuotientRealization R} →
  (compat : Weld.PropositionalQuotientOperationCompatibility R Q) →
  ∀ value →
  Weld.legacyComplex Q (Weld.conjugateSC R value)
    ≡ LegacyComplex.conjugateC (Weld.legacyComplex Q value)
complexConjugationWeld = Weld.legacyComplexConjugate
