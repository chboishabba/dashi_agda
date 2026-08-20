module DASHI.Physics.Closure.NSTriadKNHHGoodContinuumExtensionUnderdeterminedRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND 62 E1 FALSIFICATION RESULT
--
-- Round49 correctly separates the same-object lattice restriction from the
-- continuum Fourier theorem.  This file proves that the separation is not
-- merely bureaucratic: lattice restriction ALONE cannot determine the
-- continuum multiplier.
--
-- Enlarge the literal projection-mode carrier by one extra continuum point:
--
--     ContinuumMode = ProjectionMode + Unit.
--
-- Define two continuum extensions of the exact same Round48 lattice symbol.
-- On every embedded lattice mode they are definitionally identical to the
-- literal annular strain multiplier.  At the extra point, however, one is the
-- zero matrix and the other is the matrix with m_11=1 and every other entry
-- zero.  The two extensions are therefore provably distinct.
--
-- Consequently no theorem whose ONLY DASHI-specific input is
--
--     continuumSymbol(embed k) = literalSymbol(k)
--
-- can infer compact support, C^4 regularity, derivative mass, or inverse-
-- Fourier decay of the continuum object.  E1 must CONSTRUCT/SELECT the actual
-- smooth continuum annular multiplier (and its cutoff) before E2 can perform
-- four integrations by parts.  This prevents the Round55 numerical kernel
-- certificate from being misread as a construction of the continuum symbol.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Rational.Base using (1ℚ; 0ℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; cong)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNHHGoodLiteralAnnularStrainSymbolRound48Exact as Literal

ContinuumMode : Set
ContinuumMode = V.ProjectionMode ⊎ ⊤

embedProjectionMode : V.ProjectionMode → ContinuumMode
embedProjectionMode = inj₁

unit11Matrix : Matrix.Matrix3
unit11Matrix = Matrix.matrix3
  1ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ

unit11MatrixNotZero : unit11Matrix ≢ Matrix.zeroMatrix
unit11MatrixNotZero equality =
  oneNotZero (cong Matrix.m11 equality)
  where
  oneNotZero : 1ℚ ≢ 0ℚ
  oneNotZero ()

zeroOffLatticeExtension :
  Literal.LiteralAnnularStrainCutoff →
  ContinuumMode → V.Vector3 → Matrix.Matrix3
zeroOffLatticeExtension cutoff (inj₁ modeData) omega =
  Literal.literalAnnularStrainSymbol cutoff modeData omega
zeroOffLatticeExtension cutoff (inj₂ tt) omega = Matrix.zeroMatrix

unitOffLatticeExtension :
  Literal.LiteralAnnularStrainCutoff →
  ContinuumMode → V.Vector3 → Matrix.Matrix3
unitOffLatticeExtension cutoff (inj₁ modeData) omega =
  Literal.literalAnnularStrainSymbol cutoff modeData omega
unitOffLatticeExtension cutoff (inj₂ tt) omega = unit11Matrix

zeroExtensionRestrictsToLiteral :
  ∀ cutoff modeData omega →
  zeroOffLatticeExtension cutoff (embedProjectionMode modeData) omega
  ≡ Literal.literalAnnularStrainSymbol cutoff modeData omega
zeroExtensionRestrictsToLiteral cutoff modeData omega = refl

unitExtensionRestrictsToLiteral :
  ∀ cutoff modeData omega →
  unitOffLatticeExtension cutoff (embedProjectionMode modeData) omega
  ≡ Literal.literalAnnularStrainSymbol cutoff modeData omega
unitExtensionRestrictsToLiteral cutoff modeData omega = refl

extensionsAgreeOnEveryEmbeddedLatticeMode :
  ∀ cutoff modeData omega →
  zeroOffLatticeExtension cutoff (embedProjectionMode modeData) omega
  ≡ unitOffLatticeExtension cutoff (embedProjectionMode modeData) omega
extensionsAgreeOnEveryEmbeddedLatticeMode cutoff modeData omega = refl

extensionsDifferAtExtraContinuumPoint :
  ∀ cutoff omega →
  zeroOffLatticeExtension cutoff (inj₂ tt) omega
  ≢ unitOffLatticeExtension cutoff (inj₂ tt) omega
extensionsDifferAtExtraContinuumPoint cutoff omega equality =
  unit11MatrixNotZero
    (cong (λ matrix → matrix) (symmetry equality))
  where
  symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symmetry refl = refl

record TwoDistinctContinuumExtensionsWithSameLatticeRestriction
    (cutoff : Literal.LiteralAnnularStrainCutoff) : Set where
  field
    first second : ContinuumMode → V.Vector3 → Matrix.Matrix3
    firstRestricts : ∀ modeData omega →
      first (embedProjectionMode modeData) omega
      ≡ Literal.literalAnnularStrainSymbol cutoff modeData omega
    secondRestricts : ∀ modeData omega →
      second (embedProjectionMode modeData) omega
      ≡ Literal.literalAnnularStrainSymbol cutoff modeData omega
    offLatticeDifference : ∀ omega →
      first (inj₂ tt) omega ≢ second (inj₂ tt) omega

open TwoDistinctContinuumExtensionsWithSameLatticeRestriction public

explicitDistinctExtensions :
  (cutoff : Literal.LiteralAnnularStrainCutoff) →
  TwoDistinctContinuumExtensionsWithSameLatticeRestriction cutoff
explicitDistinctExtensions cutoff = record
  { first = zeroOffLatticeExtension cutoff
  ; second = unitOffLatticeExtension cutoff
  ; firstRestricts = zeroExtensionRestrictsToLiteral cutoff
  ; secondRestricts = unitExtensionRestrictsToLiteral cutoff
  ; offLatticeDifference = extensionsDifferAtExtraContinuumPoint cutoff
  }

latticeRestrictionDoesNotDetermineContinuumSymbol : Bool
latticeRestrictionDoesNotDetermineContinuumSymbol = true

e1MustConstructContinuumMultiplierBeforeFourierDecay : Bool
e1MustConstructContinuumMultiplierBeforeFourierDecay = true

latticeRestrictionDoesNotDetermineContinuumSymbolIsTrue :
  latticeRestrictionDoesNotDetermineContinuumSymbol ≡ true
latticeRestrictionDoesNotDetermineContinuumSymbolIsTrue = refl

e1MustConstructContinuumMultiplierBeforeFourierDecayIsTrue :
  e1MustConstructContinuumMultiplierBeforeFourierDecay ≡ true
e1MustConstructContinuumMultiplierBeforeFourierDecayIsTrue = refl
