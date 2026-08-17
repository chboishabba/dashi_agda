module DASHI.Physics.Closure.NSTriadKNLiteralShellAtomListRound69Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND 69 / LITERAL LOCALIZED SOURCE LIST
--
-- The existing DynamicPhysicalShellBalance already has exactly seven signed
-- source values: HH, LH, HL, CC, Com, lower boundary and upper boundary.  This
-- module emits those seven values as one literal finite list and proves that its
-- signed fold is exactly the right-hand side of the physical shell identity.
--
-- This removes the need for later Duhamel quantities to be arbitrary scalar
-- selectors.  Any defect/generated/leakage/concentration quantity used by the
-- critical-barrier argument should be a proved projection/grouping of THIS
-- list (or a finer list refining its entries), preserving source identity and
-- sign until the estimate that needs positivity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell

data LiteralShellAtomKind : Set where
  hhAtom lhAtom hlAtom ccAtom comAtom lowerBoundaryAtom upperBoundaryAtom :
    LiteralShellAtomKind

record LiteralShellAtom : Set where
  constructor literal-shell-atom
  field
    kind : LiteralShellAtomKind
    signedValue : ℚ

open LiteralShellAtom public

literalShellAtoms : Shell.DynamicPhysicalShellBalance → List LiteralShellAtom
literalShellAtoms balance =
    literal-shell-atom hhAtom
      (Shell.hhValue (Shell.staticPairing balance))
  ∷ literal-shell-atom lhAtom
      (Shell.lhValue (Shell.staticPairing balance))
  ∷ literal-shell-atom hlAtom
      (Shell.hlValue (Shell.staticPairing balance))
  ∷ literal-shell-atom ccAtom
      (Shell.ccValue (Shell.staticPairing balance))
  ∷ literal-shell-atom comAtom
      (Shell.comValue (Shell.staticPairing balance))
  ∷ literal-shell-atom lowerBoundaryAtom
      (Shell.lowerBoundary balance)
  ∷ literal-shell-atom upperBoundaryAtom
      (Shell.upperBoundary balance)
  ∷ []

sumLiteralShellAtoms : List LiteralShellAtom → ℚ
sumLiteralShellAtoms [] = 0ℚ
sumLiteralShellAtoms (atom ∷ rest) =
  signedValue atom + sumLiteralShellAtoms rest

literalShellAtomFoldExact :
  (balance : Shell.DynamicPhysicalShellBalance) →
  sumLiteralShellAtoms (literalShellAtoms balance)
  ≡
    Shell.hhValue (Shell.staticPairing balance)
    + Shell.lhValue (Shell.staticPairing balance)
    + Shell.hlValue (Shell.staticPairing balance)
    + Shell.ccValue (Shell.staticPairing balance)
    + Shell.comValue (Shell.staticPairing balance)
    + Shell.lowerBoundary balance
    + Shell.upperBoundary balance
literalShellAtomFoldExact balance =
  solve
    ( Shell.hhValue (Shell.staticPairing balance)
    ∷ Shell.lhValue (Shell.staticPairing balance)
    ∷ Shell.hlValue (Shell.staticPairing balance)
    ∷ Shell.ccValue (Shell.staticPairing balance)
    ∷ Shell.comValue (Shell.staticPairing balance)
    ∷ Shell.lowerBoundary balance
    ∷ Shell.upperBoundary balance
    ∷ [])

physicalShellIdentityEmitsLiteralAtomList :
  (balance : Shell.DynamicPhysicalShellBalance) →
  Shell.energyDerivative balance + Shell.diffusion balance
  ≡ sumLiteralShellAtoms (literalShellAtoms balance)
physicalShellIdentityEmitsLiteralAtomList balance =
  trans
    (Shell.physicalShellBalanceExpandsOnce balance)
    (sym (literalShellAtomFoldExact balance))

-- Exact one-element projections are exposed without introducing any positivity
-- or owner decision.  HH-good versus HH-bad remains a later physical
-- classification; the source value itself is not duplicated.
hhProjection : Shell.DynamicPhysicalShellBalance → List LiteralShellAtom
hhProjection balance =
  literal-shell-atom hhAtom (Shell.hhValue (Shell.staticPairing balance)) ∷ []

comProjection : Shell.DynamicPhysicalShellBalance → List LiteralShellAtom
comProjection balance =
  literal-shell-atom comAtom (Shell.comValue (Shell.staticPairing balance)) ∷ []

boundaryProjection : Shell.DynamicPhysicalShellBalance → List LiteralShellAtom
boundaryProjection balance =
    literal-shell-atom lowerBoundaryAtom (Shell.lowerBoundary balance)
  ∷ literal-shell-atom upperBoundaryAtom (Shell.upperBoundary balance)
  ∷ []

hhProjectionMeaning : ∀ balance →
  sumLiteralShellAtoms (hhProjection balance)
  ≡ Shell.hhValue (Shell.staticPairing balance)
hhProjectionMeaning balance =
  Data.Rational.Properties.+-identityʳ
    (Shell.hhValue (Shell.staticPairing balance))

comProjectionMeaning : ∀ balance →
  sumLiteralShellAtoms (comProjection balance)
  ≡ Shell.comValue (Shell.staticPairing balance)
comProjectionMeaning balance =
  Data.Rational.Properties.+-identityʳ
    (Shell.comValue (Shell.staticPairing balance))

boundaryProjectionMeaning : ∀ balance →
  sumLiteralShellAtoms (boundaryProjection balance)
  ≡ Shell.lowerBoundary balance + Shell.upperBoundary balance
boundaryProjectionMeaning balance =
  solve (Shell.lowerBoundary balance ∷ Shell.upperBoundary balance ∷ [])

round69LiteralShellAtomListConstructed : Bool
round69LiteralShellAtomListConstructed = true

round69DuhamelScalarsMustBeLiteralProjections : Bool
round69DuhamelScalarsMustBeLiteralProjections = true

round69PhysicalConcentrationProjectionConstructed : Bool
round69PhysicalConcentrationProjectionConstructed = false

round69LiteralShellAtomListConstructedIsTrue :
  round69LiteralShellAtomListConstructed ≡ true
round69LiteralShellAtomListConstructedIsTrue = refl

round69PhysicalConcentrationProjectionConstructedIsFalse :
  round69PhysicalConcentrationProjectionConstructed ≡ false
round69PhysicalConcentrationProjectionConstructedIsFalse = refl
