module DASHI.Analysis.MarxFiniteRiemannSumLaws where

open import Agda.Primitive using (Set₁)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPowerRuleNormalisation
open import DASHI.Analysis.MarxScalarFrechetBridge
open import DASHI.Analysis.MarxExteriorIntegration

------------------------------------------------------------------------
-- Additive interchange is the exact finite-sum normalization needed to collect
-- pointwise sums into two Riemann sums.

record RiemannSumAlgebraLaws
  (A : MarxAlgebra)
  : Set₁ where
  field
    scalarLaws : MarxScalarModuleLaws A
    addInterchange :
      ∀ a b c d →
      _+_ A (_+_ A a b) (_+_ A c d)
      ≡ _+_ A (_+_ A a c) (_+_ A b d)

open RiemannSumAlgebraLaws public

riemannSumCells :
  {A : MarxAlgebra} →
  Function A →
  List (RiemannCell A) →
  Carrier A
riemannSumCells {A} f [] = zero A
riemannSumCells {A} f (cell ∷ cells) =
  _+_ A (cellTerm f cell) (riemannSumCells f cells)

riemannSumMatchesCells :
  {A : MarxAlgebra} →
  (f : Function A) →
  (partition : TaggedPartition A) →
  riemannSum f partition
  ≡ riemannSumCells f (cells partition)
riemannSumMatchesCells f partition = refl

sumIntervalLengths :
  {A : MarxAlgebra} →
  List (RiemannCell A) →
  Carrier A
sumIntervalLengths {A} [] = zero A
sumIntervalLengths {A} (cell ∷ cells) =
  _+_ A
    (intervalLength (cellInterval cell))
    (sumIntervalLengths cells)

riemannSumCellsConstant :
  {A : MarxAlgebra} →
  (L : RiemannSumAlgebraLaws A) →
  (constant : Carrier A) →
  (cells : List (RiemannCell A)) →
  riemannSumCells (constantFunction constant) cells
  ≡ _*_ A constant (sumIntervalLengths cells)
riemannSumCellsConstant {A} L constant [] =
  sym (mulZeroRight A constant)
riemannSumCellsConstant {A} L constant (cell ∷ cells) =
  trans
    (cong
      (λ tail →
        _+_ A
          (_*_ A constant (intervalLength (cellInterval cell)))
          tail)
      (riemannSumCellsConstant L constant cells))
    (sym
      (MarxScalarModuleLaws.distribLeftLaw
        (scalarLaws L)
        constant
        (intervalLength (cellInterval cell))
        (sumIntervalLengths cells)))

riemannSumConstant :
  {A : MarxAlgebra} →
  (L : RiemannSumAlgebraLaws A) →
  (constant : Carrier A) →
  (partition : TaggedPartition A) →
  riemannSum (constantFunction constant) partition
  ≡ _*_ A constant (sumIntervalLengths (cells partition))
riemannSumConstant L constant partition =
  trans
    (riemannSumMatchesCells (constantFunction constant) partition)
    (riemannSumCellsConstant L constant (cells partition))

riemannSumCellsAdd :
  {A : MarxAlgebra} →
  (L : RiemannSumAlgebraLaws A) →
  (f g : Function A) →
  (cells : List (RiemannCell A)) →
  riemannSumCells (addFunctions f g) cells
  ≡ _+_ A (riemannSumCells f cells) (riemannSumCells g cells)
riemannSumCellsAdd {A} L f g [] =
  sym
    (MarxPowerAlgebraLaws.addZeroLeftLaw
      (MarxScalarModuleLaws.powerLaws (scalarLaws L))
      (zero A))
riemannSumCellsAdd {A} L f g (cell ∷ cells) =
  trans
    (cong₂ (_+_ A)
      (MarxPowerAlgebraLaws.distribRightLaw
        (MarxScalarModuleLaws.powerLaws (scalarLaws L))
        (f (tag cell))
        (g (tag cell))
        (intervalLength (cellInterval cell)))
      (riemannSumCellsAdd L f g cells))
    (addInterchange L
      (cellTerm f cell)
      (cellTerm g cell)
      (riemannSumCells f cells)
      (riemannSumCells g cells))

riemannSumAdd :
  {A : MarxAlgebra} →
  (L : RiemannSumAlgebraLaws A) →
  (f g : Function A) →
  (partition : TaggedPartition A) →
  riemannSum (addFunctions f g) partition
  ≡ _+_ A (riemannSum f partition) (riemannSum g partition)
riemannSumAdd L f g partition =
  trans
    (riemannSumMatchesCells (addFunctions f g) partition)
    (trans
      (riemannSumCellsAdd L f g (cells partition))
      (cong₂ (_+_ _)
        (sym (riemannSumMatchesCells f partition))
        (sym (riemannSumMatchesCells g partition))))

riemannSumCellsScale :
  {A : MarxAlgebra} →
  (L : RiemannSumAlgebraLaws A) →
  (scalar : Carrier A) →
  (f : Function A) →
  (cells : List (RiemannCell A)) →
  riemannSumCells (λ x → _*_ A scalar (f x)) cells
  ≡ _*_ A scalar (riemannSumCells f cells)
riemannSumCellsScale {A} L scalar f [] =
  sym (mulZeroRight A scalar)
riemannSumCellsScale {A} L scalar f (cell ∷ cells) =
  trans
    (cong₂ (_+_ A)
      (mulAssoc A scalar (f (tag cell))
        (intervalLength (cellInterval cell)))
      (riemannSumCellsScale L scalar f cells))
    (sym
      (MarxScalarModuleLaws.distribLeftLaw
        (scalarLaws L)
        scalar
        (cellTerm f cell)
        (riemannSumCells f cells)))

riemannSumScale :
  {A : MarxAlgebra} →
  (L : RiemannSumAlgebraLaws A) →
  (scalar : Carrier A) →
  (f : Function A) →
  (partition : TaggedPartition A) →
  riemannSum (λ x → _*_ A scalar (f x)) partition
  ≡ _*_ A scalar (riemannSum f partition)
riemannSumScale L scalar f partition =
  trans
    (riemannSumMatchesCells (λ x → _*_ _ scalar (f x)) partition)
    (trans
      (riemannSumCellsScale L scalar f (cells partition))
      (cong (λ total → _*_ _ scalar total)
        (sym (riemannSumMatchesCells f partition))))
