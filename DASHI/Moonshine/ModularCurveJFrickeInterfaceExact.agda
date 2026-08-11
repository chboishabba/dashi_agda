module DASHI.Moonshine.ModularCurveJFrickeInterfaceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires", Séminaire Delange-Pisot-Poitou,
-- 1974/75, exp. 7.  No DOI assigned.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- State the exact type-theoretic interface linking a fine modular point
-- (E,C), its two coarse j-values, Fricke reversal, and a genus-zero quotient
-- coordinate.  This module constructs the interface and its derived laws;
-- it does not manufacture elliptic curves or a Hauptmodul.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import DASHI.Core.Prelude

import DASHI.Biology.ModularCoarseFineAddressFibrationExact as Address
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent

record ModularJFrickeSystem : Set₁ where
  field
    EllipticCurve : Set
    FinePoint : Set
    JValue : Set

    sourceCurve : FinePoint → EllipticCurve
    targetCurve : FinePoint → EllipticCurve
    jInvariant : EllipticCurve → JValue

    fricke : FinePoint → FinePoint
    frickeInvolutive :
      (point : FinePoint) →
      fricke (fricke point) ≡ point
    frickeSwapsSource :
      (point : FinePoint) →
      sourceCurve (fricke point) ≡ targetCurve point
    frickeSwapsTarget :
      (point : FinePoint) →
      targetCurve (fricke point) ≡ sourceCurve point

open ModularJFrickeSystem public

sourceJ :
  (system : ModularJFrickeSystem) →
  FinePoint system →
  JValue system
sourceJ system point =
  jInvariant system (sourceCurve system point)

targetJ :
  (system : ModularJFrickeSystem) →
  FinePoint system →
  JValue system
targetJ system point =
  jInvariant system (targetCurve system point)

sourceJAfterFricke :
  (system : ModularJFrickeSystem) →
  (point : FinePoint system) →
  sourceJ system (fricke system point) ≡ targetJ system point
sourceJAfterFricke system point =
  cong (jInvariant system) (frickeSwapsSource system point)

targetJAfterFricke :
  (system : ModularJFrickeSystem) →
  (point : FinePoint system) →
  targetJ system (fricke system point) ≡ sourceJ system point
targetJAfterFricke system point =
  cong (jInvariant system) (frickeSwapsTarget system point)

record SymmetricJObservation
  (system : ModularJFrickeSystem) : Set₁ where
  field
    Observation : Set
    combine :
      JValue system →
      JValue system →
      Observation
    combineSymmetric :
      (left right : JValue system) →
      combine left right ≡ combine right left

open SymmetricJObservation public

observeUnoriented :
  (system : ModularJFrickeSystem) →
  (observation : SymmetricJObservation system) →
  FinePoint system →
  Observation observation
observeUnoriented system observation point =
  combine observation (sourceJ system point) (targetJ system point)

observeUnorientedIsFrickeInvariant :
  (system : ModularJFrickeSystem) →
  (observation : SymmetricJObservation system) →
  (point : FinePoint system) →
  observeUnoriented system observation (fricke system point)
  ≡ observeUnoriented system observation point
observeUnorientedIsFrickeInvariant system observation point
  rewrite sourceJAfterFricke system point
        | targetJAfterFricke system point =
  combineSymmetric observation
    (targetJ system point)
    (sourceJ system point)

record GenusZeroQuotientCoordinate
  (system : ModularJFrickeSystem) : Set₁ where
  field
    Coordinate : Set
    hauptmodul : FinePoint system → Coordinate
    hauptmodulFrickeInvariant :
      (point : FinePoint system) →
      hauptmodul (fricke system point) ≡ hauptmodul point

open GenusZeroQuotientCoordinate public

record OggPrimeModularPackage
  (prime : Lane.MonsterPrimeLane) : Set₁ where
  field
    modularSystem : ModularJFrickeSystem
    quotientCoordinate :
      GenusZeroQuotientCoordinate modularSystem
    monsterExponent : Nat
    monsterExponentIsCorrect :
      monsterExponent ≡ Exponent.monsterOrderExponent prime

open OggPrimeModularPackage public

------------------------------------------------------------------------
-- Reuse the existing finite address model, but keep it honestly distinct
-- from a literal modular curve.
------------------------------------------------------------------------

finiteCoarseAddress : Set
finiteCoarseAddress = Address.CoarseAddress

finiteFineAddress : Set
finiteFineAddress = Address.FineAddress

finiteAbsoluteAddress : Set
finiteAbsoluteAddress = Address.AbsoluteAddress

finiteAddressForgetsFine :
  finiteAbsoluteAddress →
  finiteCoarseAddress
finiteAddressForgetsFine = Address.forgetFine

finiteSectionLaw :
  (coarse : finiteCoarseAddress) →
  (value : Address.CoarseAddress) →
  finiteAddressForgetsFine
    (Address.sectionAtFineValue coarse value)
  ≡ coarse
finiteSectionLaw = Address.sectionForgetsToBase

record ModularCurveBoundary : Set where
  constructor modularCurveBoundary
  field
    finiteAddressModelIsLiteralX0p : Bool
    finiteAddressModelIsLiteralX0pIsFalse :
      finiteAddressModelIsLiteralX0p ≡ false
    frickeInterfaceConstructsHauptmodul : Bool
    frickeInterfaceConstructsHauptmodulIsFalse :
      frickeInterfaceConstructsHauptmodul ≡ false
    genusZeroIsInternallyProved : Bool
    genusZeroIsInternallyProvedIsFalse :
      genusZeroIsInternallyProved ≡ false
    jIsOneCoordinateNotOneValue : Bool
    jIsOneCoordinateNotOneValueIsTrue :
      jIsOneCoordinateNotOneValue ≡ true

canonicalModularCurveBoundary : ModularCurveBoundary
canonicalModularCurveBoundary =
  modularCurveBoundary false refl false refl false refl true refl
