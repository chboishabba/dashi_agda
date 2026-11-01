module DASHI.Physics.Closure.NSTriadKNLiteralNestedRowEnumerationRound330Exact where

------------------------------------------------------------------------
-- ROUND330 / LITERAL FIXED-OUTPUT NESTED ROW ENUMERATION
--
-- The R329 cell has two physical incidences
--
--   inner : a+b=p,
--   outer : p+q=k.
--
-- For a fixed final output k, enumerate OUTER incidences first and then the
-- complete INNER output fibre at that outer forcing leg p.  This is the exact
-- row carrier required by R328.  No cardinality estimate is attached.
--
-- The important BIDI fact is visible in the data structure itself: a row is a
-- dependent sum of inner fibres over the outer output fibre.  Therefore a
-- naive row Cauchy estimate sees the sum of those fibre sizes.  Any uniform
-- Schur proof must beat/control that multiplicity using weights/shell geometry,
-- not hide it behind a generic finite-dimensional constant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.Product.Base using (_×_; _,_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output

NestedIncidence : Set
NestedIncidence = Physical.PhysicalTriadIncidence × Physical.PhysicalTriadIncidence

-- Pair every inner incidence with the outer incidence that requested its
-- output fibre.  Convention: (inner , outer).
pairInnerWithOuter :
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence →
  List NestedIncidence
pairInnerWithOuter outer [] = []
pairInnerWithOuter outer (inner ∷ rest) =
  (inner , outer) ∷ pairInnerWithOuter outer rest

nestedRowsFromOuters :
  Nat → List Physical.PhysicalTriadIncidence → List NestedIncidence
nestedRowsFromOuters cutoff [] = []
nestedRowsFromOuters cutoff (outer ∷ rest) =
  pairInnerWithOuter outer
    (Output.physicalOutputFiber cutoff (Physical.p outer))
  ++ nestedRowsFromOuters cutoff rest

literalNestedRow : Nat → Z3.FourierMode → List NestedIncidence
literalNestedRow cutoff finalOutput =
  nestedRowsFromOuters cutoff
    (Output.physicalOutputFiber cutoff finalOutput)

round330LiteralOuterThenInnerEnumerationClosed : Bool
round330LiteralOuterThenInnerEnumerationClosed = true

round330RowCarrierIsDependentSumOfInnerFibres : Bool
round330RowCarrierIsDependentSumOfInnerFibres = true

round330NaiveUniformRowCardinalityBoundClosed : Bool
round330NaiveUniformRowCardinalityBoundClosed = false

round330WeightedRowCauchyReceiptClosed : Bool
round330WeightedRowCauchyReceiptClosed = false

round330ColumnReceiptClosed : Bool
round330ColumnReceiptClosed = false

round330PackageAClosed : Bool
round330PackageAClosed = false

round330ClayPromotion : Bool
round330ClayPromotion = false
