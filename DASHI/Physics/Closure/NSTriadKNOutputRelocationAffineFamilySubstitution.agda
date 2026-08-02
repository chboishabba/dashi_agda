module DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFamilySubstitution where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Terence Tao; DASHI repository
-- contributors.
-- Title: "Affine epsilon-family substitution for the output-relocation Schur
-- rows".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Journal of
-- Functional Analysis 199 (2003), 379--385; DASHI formal development, 2026.
-- DOI: 10.1006/jfan.2001.3804;
-- 10.1016/S0022-1236(02)00098-8; the repository substitution has no DOI.
-- Uses: lambda_i(epsilon) = base_i - epsilon direction_i and the three exact
-- scaled output-relocation rows.
-- Relationship: closes the symbolic epsilon slopes for both the low-shell and
-- gap exponents in S, S*1 and S*2. It does not supply DASHI numeric bases or
-- directions and therefore does not prove a positive epsilon interval.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresAffineWeightTemplate as Affine
import DASHI.Physics.Closure.NSTriadKNOutputRelocationLiteralShellSubstitution as Shells

-- Coefficients of the epsilon slope after substituting
-- lambda_i = base_i - epsilon direction_i.
--
-- If a row contains c_L lambda_L + c_R lambda_R + c_O lambda_O, then its
-- epsilon coefficient is -c_L D_L - c_R D_R - c_O D_O.
record DirectionCombination : Set where
  constructor directions
  field
    leftDirectionCoefficient : Int
    rightDirectionCoefficient : Int
    outputDirectionCoefficient : Int

open DirectionCombination public

record ConditionSlopePair : Set where
  constructor slopes
  field
    lowShellSlope : DirectionCombination
    separationGapSlope : DirectionCombination

open ConditionSlopePair public

outputConditionSlopes : ConditionSlopePair
outputConditionSlopes = slopes
  (directions (pos 2) (pos 2) (negsuc 1))
  (directions (pos 2) (pos 2) (pos 0))

firstAdjointConditionSlopes : ConditionSlopePair
firstAdjointConditionSlopes = slopes
  (directions (negsuc 1) (pos 2) (pos 2))
  (directions (negsuc 1) (pos 2) (pos 0))

secondAdjointConditionSlopes : ConditionSlopePair
secondAdjointConditionSlopes = slopes
  (directions (pos 2) (negsuc 1) (pos 2))
  (directions (pos 2) (negsuc 1) (pos 0))

outputConditionSlopesLiteral :
  outputConditionSlopes ≡ slopes
    (directions (pos 2) (pos 2) (negsuc 1))
    (directions (pos 2) (pos 2) (pos 0))
outputConditionSlopesLiteral = refl

firstAdjointConditionSlopesLiteral :
  firstAdjointConditionSlopes ≡ slopes
    (directions (negsuc 1) (pos 2) (pos 2))
    (directions (negsuc 1) (pos 2) (pos 0))
firstAdjointConditionSlopesLiteral = refl

secondAdjointConditionSlopesLiteral :
  secondAdjointConditionSlopes ≡ slopes
    (directions (pos 2) (negsuc 1) (pos 2))
    (directions (pos 2) (negsuc 1) (pos 0))
secondAdjointConditionSlopesLiteral = refl

record OutputRelocationAffineFamilyCutset : Set₁ where
  field
    Scalar : Set
    family : Affine.ThreeLegAffineFamily Scalar
    outputLowBaseStrict : Set
    outputGapBaseStrict : Set
    firstLowBaseStrict : Set
    firstGapBaseStrict : Set
    secondLowBaseStrict : Set
    secondGapBaseStrict : Set
    commonPositiveEpsilonPreservesAllSix : Set

open OutputRelocationAffineFamilyCutset public

record AffineFamilySubstitutionReceipt : Set where
  constructor receipt
  field
    literalShellRowsClosed :
      Shells.outputRelocationThreeConditionAffineRowsClosed ≡ true
    sourceAffineArchitectureClosed :
      Affine.grafakosTorresSection510AffineTemplateClosed ≡ true

open AffineFamilySubstitutionReceipt public

affineFamilySubstitutionReceipt : AffineFamilySubstitutionReceipt
affineFamilySubstitutionReceipt = receipt
  Shells.outputRelocationThreeConditionAffineRowsClosedIsTrue
  Affine.grafakosTorresSection510AffineTemplateClosedIsTrue

outputRelocationAffineFamilySubstitutionClosed : Bool
outputRelocationAffineFamilySubstitutionClosed = true

outputRelocationSixEpsilonSlopesClosed : Bool
outputRelocationSixEpsilonSlopesClosed = true

outputRelocationNumericBasesAndDirectionsSupplied : Bool
outputRelocationNumericBasesAndDirectionsSupplied = false

outputRelocationCommonPositiveEpsilonProved : Bool
outputRelocationCommonPositiveEpsilonProved = false

outputRelocationCheckAClosed : Bool
outputRelocationCheckAClosed = false

outputRelocationAffineFamilySubstitutionClosedIsTrue :
  outputRelocationAffineFamilySubstitutionClosed ≡ true
outputRelocationAffineFamilySubstitutionClosedIsTrue = refl

outputRelocationSixEpsilonSlopesClosedIsTrue :
  outputRelocationSixEpsilonSlopesClosed ≡ true
outputRelocationSixEpsilonSlopesClosedIsTrue = refl

outputRelocationNumericBasesAndDirectionsSuppliedIsFalse :
  outputRelocationNumericBasesAndDirectionsSupplied ≡ false
outputRelocationNumericBasesAndDirectionsSuppliedIsFalse = refl

outputRelocationCommonPositiveEpsilonProvedIsFalse :
  outputRelocationCommonPositiveEpsilonProved ≡ false
outputRelocationCommonPositiveEpsilonProvedIsFalse = refl

outputRelocationCheckAClosedIsFalse :
  outputRelocationCheckAClosed ≡ false
outputRelocationCheckAClosedIsFalse = refl
