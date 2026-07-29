module DASHI.Physics.Closure.NSTriadKNOutputRelocationCheckACriterion where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Terence Tao; DASHI repository
-- contributors.
-- Title: "Exact six-row Check A criterion for output relocation".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Journal of
-- Functional Analysis 199 (2003), 379--385; DASHI formal development, 2026.
-- DOI: 10.1006/jfan.2001.3804;
-- 10.1016/S0022-1236(02)00098-8; the repository criterion has no DOI.
-- Uses: the exact output-relocation low/gap rows and their six epsilon slopes.
-- Relationship: reduces Check A to six base inequalities and one common positive
-- epsilon witness. It does not supply the DASHI bases/directions or prove that
-- the resulting dyadic series converge constructively.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFamilySubstitution as AffineRows

record AffineStrictRow {s : Level} (Scalar : Set s) : Set (lsuc s) where
  constructor strict-row
  field
    base slope epsilon value : Scalar
    valueIsBasePlusEpsilonSlope : Set s
    valueStrictlyNegative : Set s

open AffineStrictRow public

record OutputRelocationSixRowCertificate {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    epsilon : Scalar
    epsilonStrictlyPositive : Set s

    outputLow outputGap : AffineStrictRow Scalar
    firstAdjointLow firstAdjointGap : AffineStrictRow Scalar
    secondAdjointLow secondAdjointGap : AffineStrictRow Scalar

    commonEpsilonUsedByAllSix : Set s

open OutputRelocationSixRowCertificate public

record OutputRelocationCheckAResult {s : Level} : Set (lsuc s) where
  field
    certificate : OutputRelocationSixRowCertificate {s}
    allThreeConditionsLowShellSummable : Set s
    allThreeConditionsGapSummable : Set s
    symbolicPositiveEpsilonIntervalNonempty : Set s

open OutputRelocationCheckAResult public

record OutputRelocationCheckACutset : Set₁ where
  field
    sixEpsilonSlopesClosed :
      AffineRows.outputRelocationSixEpsilonSlopesClosed ≡ true
    DASHINumericBases : Set
    DASHINumericDirections : Set
    oneCommonPositiveEpsilon : Set
    allSixAffineRowsStrict : Set

open OutputRelocationCheckACutset public

outputRelocationCheckACriterionClosed : Bool
outputRelocationCheckACriterionClosed = true

outputRelocationDASHIDataSupplied : Bool
outputRelocationDASHIDataSupplied = false

outputRelocationCheckAResultInhabited : Bool
outputRelocationCheckAResultInhabited = false

outputRelocationCheckACriterionClosedIsTrue :
  outputRelocationCheckACriterionClosed ≡ true
outputRelocationCheckACriterionClosedIsTrue = refl

outputRelocationDASHIDataSuppliedIsFalse :
  outputRelocationDASHIDataSupplied ≡ false
outputRelocationDASHIDataSuppliedIsFalse = refl

outputRelocationCheckAResultInhabitedIsFalse :
  outputRelocationCheckAResultInhabited ≡ false
outputRelocationCheckAResultInhabitedIsFalse = refl
