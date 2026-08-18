module DASHI.Moonshine.P11Level44FormalSameCoordinateComparisonExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Oldforms, degeneracy maps, and good-prime Hecke transport.
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
-- Hecke eigenforms and coefficient formulas.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Brandt modules / quaternionic modular forms and the basis problem context.
--
-- Hijikata, Pizer and Shemanske,
-- "The Basis Problem for Modular Forms on Gamma_0(N)",
-- Memoirs of the AMS 82 (1989), no. 418. No DOI asserted here.
--
-- DASHI CONTRIBUTION
--
-- Close the purely linear/formal part of the p=11 level-44 same-object cutset.
-- Both the analytic oldspace and the marked five-state oldspace are now
-- realized from ONE free integral coordinate module Old3.
--
-- Given the three genuine degeneracy targets b1,b2,b4 of a level-11 formal
-- q-series a, define
--
--   A(x1,x2,x4) = x1 b1 + x2 b2 + x4 b4
--
-- coefficientwise.  This realizes the three old-copy basis vectors exactly,
-- is Z-linear on arbitrary coordinates, and therefore inhabits the formal
-- Level44OldspaceSameObjectComparison interface already isolated in the repo.
--
-- We then lift the existing good-prime eigencharacter theorem from each basis
-- copy to the ENTIRE three-dimensional oldspace:
--
--   T_ell A(v) = lambda_ell A(v)
--
-- coefficientwise for arbitrary v : Old3, whenever ell is prime to the added
-- level and the source series has eigenvalue lambda_ell.
--
-- IMPORTANT BOUNDARY
-- This is a same-COORDINATE theorem, not the missing automorphic comparison.
-- It does not identify a formal q-series with a quaternionic modular form and
-- does not claim that the geometrically constructed marked T_ell is already
-- defined for every good prime.  The remaining Eichler/Jacquet--Langlands seam
-- is now exactly the assertion that the source-native analytic and quaternionic
-- objects are represented by this common coordinate module.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
import Data.Integer.Tactic.RingSolver as ℤRing

import DASHI.Moonshine.FormalQSeriesOldformDegeneracyHeckeExact as Deg
import DASHI.Moonshine.FormalQSeriesOldformEigencharacterTransportExact as Eig
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Marked
import DASHI.Moonshine.P11Level44OldspaceSameObjectCutsetExact as Cutset

------------------------------------------------------------------------
-- Three degeneracy copies sharing one level-11 source.
------------------------------------------------------------------------

record Level44DegeneracyTriple : Set where
  field
    level11Series : Deg.FormalQSeries
    copy1Series copy2Series copy4Series : Deg.FormalQSeries

    copy1Degeneracy :
      Deg.DegeneracyCoefficientLaw 1 level11Series copy1Series
    copy2Degeneracy :
      Deg.DegeneracyCoefficientLaw 2 level11Series copy2Series
    copy4Degeneracy :
      Deg.DegeneracyCoefficientLaw 4 level11Series copy4Series

open Level44DegeneracyTriple public

analyticRealize : Level44DegeneracyTriple → Marked.Old3 → Deg.FormalQSeries
analyticRealize D v n =
  (Marked.x1 v *ℤ copy1Series D n)
  +ℤ (Marked.x2 v *ℤ copy2Series D n)
  +ℤ (Marked.x4 v *ℤ copy4Series D n)

analyticBasis1 :
  (D : Level44DegeneracyTriple) → (n : Nat) →
  analyticRealize D Marked.oldBasis1 n ≡ copy1Series D n
analyticBasis1 D n = ℤRing.solve (copy1Series D n ∷ copy2Series D n ∷ copy4Series D n ∷ [])

analyticBasis2 :
  (D : Level44DegeneracyTriple) → (n : Nat) →
  analyticRealize D Marked.oldBasis2 n ≡ copy2Series D n
analyticBasis2 D n = ℤRing.solve (copy1Series D n ∷ copy2Series D n ∷ copy4Series D n ∷ [])

analyticBasis4 :
  (D : Level44DegeneracyTriple) → (n : Nat) →
  analyticRealize D Marked.oldBasis4 n ≡ copy4Series D n
analyticBasis4 D n = ℤRing.solve (copy1Series D n ∷ copy2Series D n ∷ copy4Series D n ∷ [])

analyticAdditive :
  (D : Level44DegeneracyTriple) →
  (u v : Marked.Old3) → (n : Nat) →
  analyticRealize D (Marked.addOld3 u v) n
  ≡ analyticRealize D u n +ℤ analyticRealize D v n
analyticAdditive D (Marked.old3 a b c) (Marked.old3 d e f) n =
  ℤRing.solve
    (a ∷ b ∷ c ∷ d ∷ e ∷ f
      ∷ copy1Series D n ∷ copy2Series D n ∷ copy4Series D n ∷ [])

analyticScalar :
  (D : Level44DegeneracyTriple) →
  (k : ℤ) → (v : Marked.Old3) → (n : Nat) →
  analyticRealize D (Marked.scaleOld3 k v) n
  ≡ k *ℤ analyticRealize D v n
analyticScalar D k (Marked.old3 a b c) n =
  ℤRing.solve
    (k ∷ a ∷ b ∷ c
      ∷ copy1Series D n ∷ copy2Series D n ∷ copy4Series D n ∷ [])

------------------------------------------------------------------------
-- The existing same-object cutset is now inhabited at the formal-coordinate
-- level for every genuine degeneracy triple.
------------------------------------------------------------------------

formalSameCoordinateComparison :
  Level44DegeneracyTriple → Cutset.Level44OldspaceSameObjectComparison
formalSameCoordinateComparison D = record
  { Cutset.level11Series = level11Series D
  ; Cutset.copy1Series = copy1Series D
  ; Cutset.copy2Series = copy2Series D
  ; Cutset.copy4Series = copy4Series D
  ; Cutset.copy1Degeneracy = copy1Degeneracy D
  ; Cutset.copy2Degeneracy = copy2Degeneracy D
  ; Cutset.copy4Degeneracy = copy4Degeneracy D
  ; Cutset.analyticRealize = analyticRealize D
  ; Cutset.analyticBasis1 = analyticBasis1 D
  ; Cutset.analyticBasis2 = analyticBasis2 D
  ; Cutset.analyticBasis4 = analyticBasis4 D
  ; Cutset.analyticAdditive = analyticAdditive D
  ; Cutset.analyticScalar = analyticScalar D
  }

------------------------------------------------------------------------
-- Good-prime Hecke data on the source and its three degeneracy copies.
------------------------------------------------------------------------

record Level44GoodPrimeEigenData
    (D : Level44DegeneracyTriple) (ell : Nat) : Set where
  field
    goodAuxiliary : Deg.PrimeToLevel44Auxiliary ell
    eigenvalue : ℤ

    sourceHecke : Deg.FormalQSeries
    copy1Hecke copy2Hecke copy4Hecke : Deg.FormalQSeries

    sourceHeckeLaw :
      Deg.Weight2PrimeHeckeCoefficientLaw ell (level11Series D) sourceHecke
    copy1HeckeLaw :
      Deg.Weight2PrimeHeckeCoefficientLaw ell (copy1Series D) copy1Hecke
    copy2HeckeLaw :
      Deg.Weight2PrimeHeckeCoefficientLaw ell (copy2Series D) copy2Hecke
    copy4HeckeLaw :
      Deg.Weight2PrimeHeckeCoefficientLaw ell (copy4Series D) copy4Hecke

    sourceEigen :
      (n : Nat) → sourceHecke n ≡ Eig.scaleSeries eigenvalue (level11Series D) n

open Level44GoodPrimeEigenData public

analyticHeckeRealize :
  {D : Level44DegeneracyTriple} {ell : Nat} →
  Level44GoodPrimeEigenData D ell → Marked.Old3 → Deg.FormalQSeries
analyticHeckeRealize H v n =
  (Marked.x1 v *ℤ copy1Hecke H n)
  +ℤ (Marked.x2 v *ℤ copy2Hecke H n)
  +ℤ (Marked.x4 v *ℤ copy4Hecke H n)

copy1GoodPrimeEigen :
  {D : Level44DegeneracyTriple} {ell : Nat} →
  (H : Level44GoodPrimeEigenData D ell) → (n : Nat) →
  copy1Hecke H n ≡ Eig.scaleSeries (eigenvalue H) (copy1Series D) n
copy1GoodPrimeEigen {D} {ell} H =
  Eig.degeneracy1PreservesEigencharacter
    ell (eigenvalue H)
    (level11Series D) (copy1Series D)
    (sourceHecke H) (copy1Hecke H)
    (copy1Degeneracy D)
    (sourceHeckeLaw H) (copy1HeckeLaw H) (sourceEigen H)

copy2GoodPrimeEigen :
  {D : Level44DegeneracyTriple} {ell : Nat} →
  (H : Level44GoodPrimeEigenData D ell) → (n : Nat) →
  copy2Hecke H n ≡ Eig.scaleSeries (eigenvalue H) (copy2Series D) n
copy2GoodPrimeEigen {D} {ell} H =
  Eig.degeneracy2PreservesEigencharacter
    ell (goodAuxiliary H) (eigenvalue H)
    (level11Series D) (copy2Series D)
    (sourceHecke H) (copy2Hecke H)
    (copy2Degeneracy D)
    (sourceHeckeLaw H) (copy2HeckeLaw H) (sourceEigen H)

copy4GoodPrimeEigen :
  {D : Level44DegeneracyTriple} {ell : Nat} →
  (H : Level44GoodPrimeEigenData D ell) → (n : Nat) →
  copy4Hecke H n ≡ Eig.scaleSeries (eigenvalue H) (copy4Series D) n
copy4GoodPrimeEigen {D} {ell} H =
  Eig.degeneracy4PreservesEigencharacter
    ell (goodAuxiliary H) (eigenvalue H)
    (level11Series D) (copy4Series D)
    (sourceHecke H) (copy4Hecke H)
    (copy4Degeneracy D)
    (sourceHeckeLaw H) (copy4HeckeLaw H) (sourceEigen H)

------------------------------------------------------------------------
-- WHOLE-OLDSPACE theorem: every integral linear combination inherits exactly
-- the same good-prime eigencharacter.
------------------------------------------------------------------------

wholeOldspaceGoodPrimeEigen :
  {D : Level44DegeneracyTriple} {ell : Nat} →
  (H : Level44GoodPrimeEigenData D ell) →
  (v : Marked.Old3) → (n : Nat) →
  analyticHeckeRealize H v n
  ≡ Eig.scaleSeries (eigenvalue H) (analyticRealize D v) n
wholeOldspaceGoodPrimeEigen {D} H (Marked.old3 a b c) n =
  trans
    (cong3
      (λ x y z → (a *ℤ x) +ℤ (b *ℤ y) +ℤ (c *ℤ z))
      (copy1GoodPrimeEigen H n)
      (copy2GoodPrimeEigen H n)
      (copy4GoodPrimeEigen H n))
    (ℤRing.solve
      (a ∷ b ∷ c ∷ eigenvalue H
        ∷ copy1Series D n ∷ copy2Series D n ∷ copy4Series D n ∷ []))
  where
  cong3 :
    {A B C R : Set} {x x' : A} {y y' : B} {z z' : C} →
    (f : A → B → C → R) →
    x ≡ x' → y ≡ y' → z ≡ z' →
    f x y z ≡ f x' y' z'
  cong3 f refl refl refl = refl

------------------------------------------------------------------------
-- Boundary: the linear/common-coordinate seam is closed; the actual
-- automorphic same-object identification remains source-facing.
------------------------------------------------------------------------

record P11Level44FormalSameCoordinateBoundary : Set where
  field
    commonOld3CoordinateModuleUsed : Bool
    formalAnalyticComparisonConstructed : Bool
    wholeOldspaceGoodPrimeEigenTransportProved : Bool
    markedRealizationUsesSameOld3Coordinates : Bool
    analyticQSeriesIdentifiedWithQuaternionicForm : Bool
    actualEichlerJacquetLanglandsComparisonConstructed : Bool

canonicalP11Level44FormalSameCoordinateBoundary :
  P11Level44FormalSameCoordinateBoundary
canonicalP11Level44FormalSameCoordinateBoundary = record
  { commonOld3CoordinateModuleUsed = true
  ; formalAnalyticComparisonConstructed = true
  ; wholeOldspaceGoodPrimeEigenTransportProved = true
  ; markedRealizationUsesSameOld3Coordinates = true
  ; analyticQSeriesIdentifiedWithQuaternionicForm = false
  ; actualEichlerJacquetLanglandsComparisonConstructed = false
  }
