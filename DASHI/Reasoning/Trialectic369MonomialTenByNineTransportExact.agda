module DASHI.Reasoning.Trialectic369MonomialTenByNineTransportExact where

------------------------------------------------------------------------
-- MONOMIAL BASIS TRANSPORT TO FINE10 x SECONDARY SHEET9
--
-- The existing 90 <-> 10x9 codec is used without treating the finite index
-- permutation as the full source representation. Each transported transition
-- retains its MONOMIAL scalar coefficient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Mixed
import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Reasoning.Trialectic369MonomialMultiplicityBasisSpecialisationExact as Monomial

TenByNine : Set
TenByNine = Pointed.Fine10 × Pointed.SecondarySheet9

indexActionOnTenByNine :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  Monomial.MonomialMultiplicityBasisSpecialisation route →
  Monomial.RouteGroup route →
  TenByNine → TenByNine
indexActionOnTenByNine route monomial g state =
  Mixed.fin90ToTenByNine
    (Monomial.indexAct monomial g
      (Mixed.tenByNineToFin90 state))

scalarOnTenByNine :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  Monomial.MonomialMultiplicityBasisSpecialisation route →
  Monomial.RouteGroup route →
  TenByNine →
  Linear.Scalar
    (WrongType.linearCarrier (WrongType.linearRepresentation route))
scalarOnTenByNine route monomial g state =
  Monomial.scalarAct monomial g (Mixed.tenByNineToFin90 state)

indexActionRecharts :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  (monomial : Monomial.MonomialMultiplicityBasisSpecialisation route) →
  (g : Monomial.RouteGroup route) →
  (index : Fin 90) →
  indexActionOnTenByNine route monomial g
    (Mixed.fin90ToTenByNine index)
  ≡ Mixed.fin90ToTenByNine (Monomial.indexAct monomial g index)
indexActionRecharts route monomial g index
  rewrite Mixed.tenByNineAfterFin90 index = refl

scalarActionRecharts :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  (monomial : Monomial.MonomialMultiplicityBasisSpecialisation route) →
  (g : Monomial.RouteGroup route) →
  (index : Fin 90) →
  scalarOnTenByNine route monomial g
    (Mixed.fin90ToTenByNine index)
  ≡ Monomial.scalarAct monomial g index
scalarActionRecharts route monomial g index
  rewrite Mixed.tenByNineAfterFin90 index = refl

inverseIndexActionOnTenByNine :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  Monomial.FullMonomialBasisReceipt route →
  Monomial.RouteGroup route →
  TenByNine → TenByNine
inverseIndexActionOnTenByNine route receipt g state =
  Mixed.fin90ToTenByNine
    (Monomial.inverseIndexAct receipt g
      (Mixed.tenByNineToFin90 state))

tenByNineIndexAfterInverse :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  (receipt : Monomial.FullMonomialBasisReceipt route) →
  (g : Monomial.RouteGroup route) →
  (state : TenByNine) →
  indexActionOnTenByNine route (Monomial.monomial receipt) g
    (inverseIndexActionOnTenByNine route receipt g state)
  ≡ state
tenByNineIndexAfterInverse route receipt g state
  rewrite Mixed.tenByNineAfterFin90
    (Monomial.inverseIndexAct receipt g (Mixed.tenByNineToFin90 state))
        | Monomial.indexActAfterInverse receipt g
            (Mixed.tenByNineToFin90 state)
        | Mixed.fin90AfterTenByNine state = refl

tenByNineInverseAfterIndex :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  (receipt : Monomial.FullMonomialBasisReceipt route) →
  (g : Monomial.RouteGroup route) →
  (state : TenByNine) →
  inverseIndexActionOnTenByNine route receipt g
    (indexActionOnTenByNine route (Monomial.monomial receipt) g state)
  ≡ state
tenByNineInverseAfterIndex route receipt g state
  rewrite Mixed.tenByNineAfterFin90
    (Monomial.indexAct (Monomial.monomial receipt) g
      (Mixed.tenByNineToFin90 state))
        | Monomial.inverseAfterIndexAct receipt g
            (Mixed.tenByNineToFin90 state)
        | Mixed.fin90AfterTenByNine state = refl

record Boundary : Set where
  constructor boundary
  field
    indexMotionTransportedWithoutLoss : Bool
    scalarCoefficientTransportedWithoutLoss : Bool
    inverseIndexTransported : Bool
    fullLinearActionReplacedByIndexAction : Bool
    actualMonomialBasisInhabitedHere : Bool

canonicalBoundary : Boundary
canonicalBoundary = boundary true true true false false
