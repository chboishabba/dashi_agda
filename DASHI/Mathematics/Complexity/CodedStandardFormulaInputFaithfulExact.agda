module DASHI.Mathematics.Complexity.CodedStandardFormulaInputFaithfulExact where

------------------------------------------------------------------------
-- FAITHFUL CANONICAL FORMULA INPUT FOR CODED STANDARD MACHINES
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as CodedDecider
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

consHead :
  ∀ {A : Set} {x y : A} {xs ys : List A} →
  x ∷ xs ≡ y ∷ ys → x ≡ y
consHead refl = refl

consTail :
  ∀ {A : Set} {x y : A} {xs ys : List A} →
  x ∷ xs ≡ y ∷ ys → xs ≡ ys
consTail refl = refl

mapFormulaBitsInjective :
  ∀ {n : Nat}
    (zeroSymbol oneSymbol : Fin.Fin n) →
  (zeroSymbol ≡ oneSymbol → ⊥) →
  ∀ {left right : List Bool} →
  CodedDecider.mapFormulaBits zeroSymbol oneSymbol left
  ≡ CodedDecider.mapFormulaBits zeroSymbol oneSymbol right →
  left ≡ right
mapFormulaBitsInjective zeroSymbol oneSymbol distinct {[]} {[]} equality = refl
mapFormulaBitsInjective zeroSymbol oneSymbol distinct {[]} {false ∷ right} ()
mapFormulaBitsInjective zeroSymbol oneSymbol distinct {[]} {true ∷ right} ()
mapFormulaBitsInjective zeroSymbol oneSymbol distinct {false ∷ left} {[]} ()
mapFormulaBitsInjective zeroSymbol oneSymbol distinct {true ∷ left} {[]} ()
mapFormulaBitsInjective zeroSymbol oneSymbol distinct
    {false ∷ left} {false ∷ right} equality
    with mapFormulaBitsInjective zeroSymbol oneSymbol distinct
      (consTail equality)
... | refl = refl
mapFormulaBitsInjective zeroSymbol oneSymbol distinct
    {true ∷ left} {true ∷ right} equality
    with mapFormulaBitsInjective zeroSymbol oneSymbol distinct
      (consTail equality)
... | refl = refl
mapFormulaBitsInjective zeroSymbol oneSymbol distinct
    {false ∷ left} {true ∷ right} equality =
  ⊥-elim (distinct (consHead equality))
mapFormulaBitsInjective zeroSymbol oneSymbol distinct
    {true ∷ left} {false ∷ right} equality =
  ⊥-elim (distinct (sym (consHead equality)))

formulaInputInjective :
  (code : Coded.CodedFiniteStandardTM)
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount code)) →
  (distinct : zeroSymbol ≡ oneSymbol → ⊥) →
  ∀ {left right : Cook.BooleanFormula} →
  CodedDecider.formulaInput code zeroSymbol oneSymbol left
  ≡ CodedDecider.formulaInput code zeroSymbol oneSymbol right →
  left ≡ right
formulaInputInjective
    code zeroSymbol oneSymbol distinct {left} {right} inputEqual =
  trans
    (sym (Binary.decodeEncodeFormulaBits left))
    (trans decodedEqual (Binary.decodeEncodeFormulaBits right))
  where
    encodedEqual :
      Binary.encodeFormulaBits left ≡ Binary.encodeFormulaBits right
    encodedEqual =
      mapFormulaBitsInjective
        zeroSymbol oneSymbol distinct inputEqual

    decodedEqual :
      Binary.decodeFormulaBits (Binary.encodeFormulaBits left)
      ≡ Binary.decodeFormulaBits (Binary.encodeFormulaBits right)
    decodedEqual = cong Binary.decodeFormulaBits encodedEqual

witnessFormulaInputInjective :
  ∀ {decider : Cook.BooleanFormula → Bool}
    (witness : CodedDecider.CodedStandardPolynomialDecider decider)
    {left right : Cook.BooleanFormula} →
  CodedDecider.formulaInput
      (CodedDecider.code witness)
      (CodedDecider.zeroSymbol witness)
      (CodedDecider.oneSymbol witness)
      left
  ≡
  CodedDecider.formulaInput
      (CodedDecider.code witness)
      (CodedDecider.zeroSymbol witness)
      (CodedDecider.oneSymbol witness)
      right →
  left ≡ right
witnessFormulaInputInjective witness =
  formulaInputInjective
    (CodedDecider.code witness)
    (CodedDecider.zeroSymbol witness)
    (CodedDecider.oneSymbol witness)
    (CodedDecider.binarySymbolsDistinct witness)
