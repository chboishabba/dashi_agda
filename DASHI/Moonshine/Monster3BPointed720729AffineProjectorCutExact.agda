module DASHI.Moonshine.Monster3BPointed720729AffineProjectorCutExact where

------------------------------------------------------------------------
-- PARETO/SNOWBALL: POINTED 720+9 VS ACTUAL FINITE HEISENBERG X6.
--
-- ORIGINAL MATHEMATICAL SOURCES (not new DASHI discoveries):
-- Serre, finite-group character/representation theory; Terras (1999),
-- finite Fourier analysis; Wilson (1988) 3B-local restriction;
-- Barraclough--Wilson (2007), DOI 10.1112/S1461157000001352.
--
-- PRE-EXISTING DASHI OWNERS:
-- Foundations.Base369PointedAppraisalFibreExact: (8*10*9)+9 = 729.
-- Moonshine.Base369Pointed729NestedNinetyBidiExact: 8*90+9 codec.
-- Moonshine.Monster3BFiniteHeisenbergGeneratorsExact: X6 = F3^6,
-- exact translation and modulation generators.
-- Moonshine.Monster3BFiniteSchrodingerPointProjectorExact: genuine
-- Heisenberg-generated point projectors and invariant-subspace closure.
-- Moonshine.Monster3BWilsonPublishedRestrictionReconciliationExact:
-- source-published 143+65520+(729+729')(12+78), distinct
-- from 53+3*65610 C3 character decomposition.
--
-- NEW TYPED CUT: in one CHOSEN basis identification, the shared
-- 9-sheet is a 2-dimensional affine coordinate plane in X6.
-- axis0, axis1 translations preserve its support, while axis2
-- EXPLICITLY moves the origin out of it. This rules out declaring
-- that coordinate-plane projector invariant under the full
-- unchanged Schrödinger/Heisenberg translation action.
--
-- The full affine 81-orbit and stabilizer orders are exhaustively
-- checked in the companion pure Python script; they are NOT
-- promoted to an Agda kernel-proof from this source-written file.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (zer; pos)

import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Base369Pointed729NestedNinetyBidiExact as Nested
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorExact as Projector
import DASHI.Moonshine.Monster3BWilsonPublishedRestrictionReconciliationExact as Wilson

chosenNinePlane : G.X6 → Set
chosenNinePlane x =
  ((G.x2 x ≡ zer) × (G.x3 x ≡ zer))
  × ((G.x4 x ≡ zer) × (G.x5 x ≡ zer))

origin : G.X6
origin = G.x6 zer zer zer zer zer zer

originInChosenNinePlane : chosenNinePlane origin
originInChosenNinePlane = ((refl , refl) , (refl , refl))

axis0PreservesChosenNinePlane :
  (x : G.X6) → chosenNinePlane x →
  chosenNinePlane (G.translate G.axis0 x)
axis0PreservesChosenNinePlane x member = member

axis1PreservesChosenNinePlane :
  (x : G.X6) → chosenNinePlane x →
  chosenNinePlane (G.translate G.axis1 x)
axis1PreservesChosenNinePlane x member = member

axis2TranslationLeavesChosenNinePlane :
  chosenNinePlane (G.translate G.axis2 origin) → ⊥
axis2TranslationLeavesChosenNinePlane ((() , _) , _)

chosenNinePlaneIsNotTranslationInvariant :
  ((x : G.X6) → chosenNinePlane x →
    chosenNinePlane (G.translate G.axis2 x)) → ⊥
chosenNinePlaneIsNotTranslationInvariant invariant =
  axis2TranslationLeavesChosenNinePlane
    (invariant origin originInChosenNinePlane)

-- Exact cardinal-arithmetic crosswalk; only same-number, not same-action.
pointed720Count : Pointed.noncentralAddressCount ≡ 720
pointed720Count = Pointed.noncentralAddressCountIs720

pointed729Count : Pointed.pointedAppraisalAddressCount ≡ 729
pointed729Count = Pointed.pointedAppraisalAddressCountIs729

nested729Count : Nested.nestedPointedDimension ≡ 729
nested729Count = Nested.nestedPointedDimensionIs729

wilsonHeisenberg729Count : Wilson.heisenbergDegree ≡ 729
wilsonHeisenberg729Count = refl

affineCosets81Times9 : 81 * 9 ≡ 729
affineCosets81Times9 = refl

noncentralCosets80Times9 : 80 * 9 ≡ 720
noncentralCosets80Times9 = refl

pointed720Plus9 : 720 + 9 ≡ 729
pointed720Plus9 = refl

pointed720Plus8Plus1 : (720 + 8) + 1 ≡ 729
pointed720Plus8Plus1 = refl

sourceWilsonOrbit728Times90 : 728 * 90 ≡ Wilson.linearOrbitMonomial
sourceWilsonOrbit728Times90 = refl

selected729Times90 : 729 * 90 ≡ 65610
selected729Times90 = refl

pointedFiltrationIntoWilsonArithmetic :
  720 * 90 + (8 * 90 + 90) ≡ Wilson.linearOrbitMonomial + 90
pointedFiltrationIntoWilsonArithmetic = refl

wilson143Plus65520StillIrreducibleNumericalReconciliation :
  Wilson.linearOrbitMonomial + Wilson.suzOneFortyThree
  ≡ 65610 + 53
wilson143Plus65520StillIrreducibleNumericalReconciliation = refl

-- Deliberate stop rule: the finite affine codec and rank-9 plane do NOT
-- supply an actual Monster-selected 6.Suz 78 character, an equivariant
-- embedding in W_zeta, an ATLAS D4-invariant chosen plane, or an Agda
-- typechecked Heisenberg-normalizer matrix. PR #1098 owns the latter.
