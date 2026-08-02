module DASHI.Physics.Closure.NSTriadKNOutputRelocationLiteralShellSubstitution where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Jean-Michel Bony; Hajer
-- Bahouri; Jean-Yves Chemin; Raphael Danchin; DASHI repository contributors.
-- Title: "Literal shell-index substitution for the output-relocation Schur
-- conditions".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Annales
-- scientifiques de l'Ecole Normale Superieure 14 (1981); Fourier Analysis and
-- Nonlinear Partial Differential Equations, Springer, 2011; DASHI formal
-- development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.24033/asens.1404;
-- 10.1007/978-3-642-16830-7; the repository substitution theorem has no DOI.
-- Uses: the literal Grafakos--Torres sign orientation, output-low shell geometry
-- j_O = j and j_L = j_R = J = j+d, and the already-closed physical exponent
-- -(2s-5/2)j - 2sd.
-- Relationship: closes the repository-specific symbolic substitution for all
-- three Schur conditions. Coefficients are scaled by two to remain integral.
-- It does not prove constructive dyadic summability, choose the affine weights,
-- or prove a positive epsilon interval.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresPowerLawOrientation as Orientation
import DASHI.Physics.Closure.NSTriadKNOutputRelocationWeightedExponentIdentity as Weighted

-- A normalized row for twice the total exponent
--
--   2 E = c + sJ*s + lJ*lambda_L + rJ*lambda_R + oJ*lambda_O
--             all multiplying j
--       + (sD*s + lD*lambda_L + rD*lambda_R + oD*lambda_O)
--             all multiplying d.
--
-- The factor two clears the physical 5/2 endpoint.
record ScaledThreeConditionAffineRow : Set where
  constructor row
  field
    constantJ : Int
    sobolevJ : Int
    leftWeightJ rightWeightJ outputWeightJ : Int
    sobolevD : Int
    leftWeightD rightWeightD outputWeightD : Int

open ScaledThreeConditionAffineRow public

-- Output condition:
--   -lambda_L J - lambda_R J + lambda_O j,
-- with J = j+d.
outputConditionRow : ScaledThreeConditionAffineRow
outputConditionRow = row
  (pos 5)
  (negsuc 3)
  (negsuc 1) (negsuc 1) (pos 2)
  (negsuc 3)
  (negsuc 1) (negsuc 1) (pos 0)

-- First partial adjoint:
--   +lambda_L J - lambda_R J - lambda_O j.
firstAdjointConditionRow : ScaledThreeConditionAffineRow
firstAdjointConditionRow = row
  (pos 5)
  (negsuc 3)
  (pos 2) (negsuc 1) (negsuc 1)
  (negsuc 3)
  (pos 2) (negsuc 1) (pos 0)

-- Second partial adjoint:
--   -lambda_L J + lambda_R J - lambda_O j.
secondAdjointConditionRow : ScaledThreeConditionAffineRow
secondAdjointConditionRow = row
  (pos 5)
  (negsuc 3)
  (negsuc 1) (pos 2) (negsuc 1)
  (negsuc 3)
  (negsuc 1) (pos 2) (pos 0)

outputConditionRowLiteral :
  outputConditionRow ≡ row
    (pos 5) (negsuc 3)
    (negsuc 1) (negsuc 1) (pos 2)
    (negsuc 3)
    (negsuc 1) (negsuc 1) (pos 0)
outputConditionRowLiteral = refl

firstAdjointConditionRowLiteral :
  firstAdjointConditionRow ≡ row
    (pos 5) (negsuc 3)
    (pos 2) (negsuc 1) (negsuc 1)
    (negsuc 3)
    (pos 2) (negsuc 1) (pos 0)
firstAdjointConditionRowLiteral = refl

secondAdjointConditionRowLiteral :
  secondAdjointConditionRow ≡ row
    (pos 5) (negsuc 3)
    (negsuc 1) (pos 2) (negsuc 1)
    (negsuc 3)
    (negsuc 1) (pos 2) (pos 0)
secondAdjointConditionRowLiteral = refl

record LiteralShellSubstitutionReceipt : Set where
  constructor receipt
  field
    physicalExponentIdentityClosed :
      Weighted.outputRelocationWeightedExponentIdentityClosed ≡ true
    signOrientationClosed :
      Orientation.grafakosTorresSignOrientationClosed ≡ true
    outputOrientationConsumed :
      Orientation.outputConditionOrientation
      ≡ Orientation.orientation (negsuc 0) (negsuc 0) (pos 1)
    firstOrientationConsumed :
      Orientation.firstAdjointConditionOrientation
      ≡ Orientation.orientation (pos 1) (negsuc 0) (negsuc 0)
    secondOrientationConsumed :
      Orientation.secondAdjointConditionOrientation
      ≡ Orientation.orientation (negsuc 0) (pos 1) (negsuc 0)

open LiteralShellSubstitutionReceipt public

literalShellSubstitutionReceipt : LiteralShellSubstitutionReceipt
literalShellSubstitutionReceipt = receipt
  Weighted.outputRelocationWeightedExponentIdentityClosedIsTrue
  Orientation.grafakosTorresSignOrientationClosedIsTrue
  Orientation.outputOrientationLiteral
  Orientation.firstAdjointOrientationLiteral
  Orientation.secondAdjointOrientationLiteral

outputRelocationLiteralShellSubstitutionClosed : Bool
outputRelocationLiteralShellSubstitutionClosed = true

outputRelocationThreeConditionAffineRowsClosed : Bool
outputRelocationThreeConditionAffineRowsClosed = true

outputRelocationConstructiveDyadicTailClosed : Bool
outputRelocationConstructiveDyadicTailClosed = false

outputRelocationAffineWeightFamilySubstituted : Bool
outputRelocationAffineWeightFamilySubstituted = false

outputRelocationCheckAAvailable : Bool
outputRelocationCheckAAvailable = false

outputRelocationLiteralShellSubstitutionClosedIsTrue :
  outputRelocationLiteralShellSubstitutionClosed ≡ true
outputRelocationLiteralShellSubstitutionClosedIsTrue = refl

outputRelocationThreeConditionAffineRowsClosedIsTrue :
  outputRelocationThreeConditionAffineRowsClosed ≡ true
outputRelocationThreeConditionAffineRowsClosedIsTrue = refl

outputRelocationConstructiveDyadicTailClosedIsFalse :
  outputRelocationConstructiveDyadicTailClosed ≡ false
outputRelocationConstructiveDyadicTailClosedIsFalse = refl

outputRelocationAffineWeightFamilySubstitutedIsFalse :
  outputRelocationAffineWeightFamilySubstituted ≡ false
outputRelocationAffineWeightFamilySubstitutedIsFalse = refl

outputRelocationCheckAAvailableIsFalse :
  outputRelocationCheckAAvailable ≡ false
outputRelocationCheckAAvailableIsFalse = refl
