module DASHI.Core.NumberRoleProvenanceAtlasExact where

------------------------------------------------------------------------
-- NUMBER / ROLE PROVENANCE ATLAS
--
-- The supplied DASHI genealogy notes repeatedly warn that the same printed
-- number can acquire different mathematical and historical roles.  This module
-- makes that separation explicit and machine-visible.
--
-- Primary literature already owned by imported modules:
--
-- * Robert M. May, "Simple mathematical models with very complicated
--   dynamics", Nature 261 (1976), 459--467. DOI: 10.1038/261459a0.
-- * Theodore E. Harris, "The Theory of Branching Processes", Springer, 1963.
--   DOI: 10.1007/978-3-642-51866-9.
-- * Bernhard Riemann, "Ueber die Anzahl der Primzahlen unter einer gegebenen
--   Grösse" (1859), no DOI assigned.
-- * Enrico Bombieri, Clay Mathematics Institute RH problem description,
--   stable institutional source; no DOI assigned.
--
-- Historical DASHI-specific meanings are attributed to the supplied origin /
-- reconstruction notes rather than retroactively attributed to those sources.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.DecimalResidualRefinementExact as Decimal
import DASHI.Core.FiniteBranchingCriticalityExact as Branch
import DASHI.Core.LogisticFoldCriticalityExact as Logistic
import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as RH

------------------------------------------------------------------------
-- Typed roles.  Equal underlying scalars do not collapse these constructors.
------------------------------------------------------------------------

data NumberRole : Set where
  dyadicScreenCut
  historicalDecimalComparison
  branchingCriticalAvailability
  logisticFoldCriticalPoint
  riemannCriticalRealPart
  historicalAffineRefinementFixedPoint
  jCoarseFineFrequencyRole
  decimalStratificationRole
  triadicDepthRole
  : NumberRole

halfBranchingRoleDistinctFromLogisticRole :
  branchingCriticalAvailability ≡ logisticFoldCriticalPoint → ⊥
halfBranchingRoleDistinctFromLogisticRole ()

halfLogisticRoleDistinctFromRiemannRole :
  logisticFoldCriticalPoint ≡ riemannCriticalRealPart → ⊥
halfLogisticRoleDistinctFromRiemannRole ()

halfBranchingRoleDistinctFromRiemannRole :
  branchingCriticalAvailability ≡ riemannCriticalRealPart → ⊥
halfBranchingRoleDistinctFromRiemannRole ()

------------------------------------------------------------------------
-- Exact shared-scalar compatibility, without role identification.
------------------------------------------------------------------------

logisticHalfEqualsRiemannHalf : Logistic.half ≡ RH.half
logisticHalfEqualsRiemannHalf = refl

binaryHalfIsBranchingCritical :
  Branch.singleAxisRegime 2 1 2 ≡ Branch.critical
binaryHalfIsBranchingCritical = Branch.binaryHalfIsCritical

ternaryThirdIsBranchingCritical :
  Branch.singleAxisRegime 3 1 3 ≡ Branch.critical
ternaryThirdIsBranchingCritical = Branch.ternaryThirdIsCritical

quaternaryQuarterIsBranchingCritical :
  Branch.singleAxisRegime 4 1 4 ≡ Branch.critical
quaternaryQuarterIsBranchingCritical = Branch.quaternaryQuarterIsCritical

fiveEighteenthsHistoricalEquation :
  Branch.affineQuarterTenthFixedPointEquation 5 18
fiveEighteenthsHistoricalEquation =
  Branch.fiveEighteenthsSolvesAffineQuarterTenth

nineDecimalDepthTwo :
  Decimal.decimalRefinementNumerator Decimal.d9 2 ≡ 999
nineDecimalDepthTwo = Decimal.nineDepthTwo

------------------------------------------------------------------------
-- Provenance entries.  These are metadata carriers, not evidence that the
-- historical interpretation was derived from the later mathematical source.
------------------------------------------------------------------------

data EvidenceRelation : Set where
  exactTheorem
  historicalSourceMeaning
  retrospectiveAnalogy
  currentRepoOwner
  : EvidenceRelation

record NumberProvenanceEntry : Set where
  constructor number-provenance-entry
  field
    printedValue : String
    role : NumberRole
    firstSourceOrGenealogy : String
    meaning : String
    mathematicalRealisation : String
    repoOwner : String
    evidenceRelation : EvidenceRelation

open NumberProvenanceEntry public

quarterBranchingEntry : NumberProvenanceEntry
quarterBranchingEntry =
  number-provenance-entry
    "0.25 / 1/4"
    branchingCriticalAvailability
    "Harris branching-process criterion; DASHI historical notes separately use 0.25 as initial consideration"
    "critical availability for arity four"
    "4 * (1/4) = 1"
    "DASHI.Core.FiniteBranchingCriticalityExact"
    exactTheorem

thirdBranchingEntry : NumberProvenanceEntry
thirdBranchingEntry =
  number-provenance-entry
    "1/3"
    branchingCriticalAvailability
    "Harris branching-process criterion"
    "critical availability for arity three"
    "3 * (1/3) = 1"
    "DASHI.Core.FiniteBranchingCriticalityExact"
    exactTheorem

halfBranchingEntry : NumberProvenanceEntry
halfBranchingEntry =
  number-provenance-entry
    "0.5 / 1/2"
    branchingCriticalAvailability
    "Harris branching-process criterion"
    "critical availability for arity two"
    "2 * (1/2) = 1"
    "DASHI.Core.FiniteBranchingCriticalityExact"
    exactTheorem

halfLogisticEntry : NumberProvenanceEntry
halfLogisticEntry =
  number-provenance-entry
    "0.5 / 1/2"
    logisticFoldCriticalPoint
    "Robert M. May 1976; DOI 10.1038/261459a0"
    "critical/fold point of x |-> r*x*(1-x)"
    "formal derivative r*(1-2x) vanishes at x=1/2"
    "DASHI.Core.LogisticFoldCriticalityExact"
    exactTheorem

halfRiemannEntry : NumberProvenanceEntry
halfRiemannEntry =
  number-provenance-entry
    "0.5 / 1/2"
    riemannCriticalRealPart
    "Riemann 1859; Bombieri CMI RH problem description"
    "real coordinate of the RH critical line"
    "reflection s |-> 1-conjugate(s) fixes exactly Re(s)=1/2 in the repo rational model"
    "DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact"
    currentRepoOwner

fiveEighteenthsEntry : NumberProvenanceEntry
fiveEighteenthsEntry =
  number-provenance-entry
    "5/18 = 0.2777..."
    historicalAffineRefinementFixedPoint
    "supplied DASHI reconstruction notes"
    "actual fixed point of x = 1/4 + x/10"
    "40*5 = 10*18 + 4*5; separately ternary-subcritical"
    "DASHI.Core.FiniteBranchingCriticalityExact"
    exactTheorem

nineDecimalEntry : NumberProvenanceEntry
nineDecimalEntry =
  number-provenance-entry
    "9"
    decimalStratificationRole
    "supplied DASHI coarse/fine notes"
    "coarse digit under repeated decimal residual refinement"
    "9 -> 9.9 -> 9.99 is represented by exact Nat numerators"
    "DASHI.Core.DecimalResidualRefinementExact"
    historicalSourceMeaning

------------------------------------------------------------------------
-- Boundary: provenance records are intentionally plural.
------------------------------------------------------------------------

record NumberRoleProvenanceBoundary : Set where
  constructor number-role-provenance-boundary
  field
    samePrintedValueImpliesSameMathematicalRole : Bool
    samePrintedValueImpliesSameMathematicalRoleIsFalse :
      samePrintedValueImpliesSameMathematicalRole ≡ false
    laterRealisationIsClaimedAsHistoricalOrigin : Bool
    laterRealisationIsClaimedAsHistoricalOriginIsFalse :
      laterRealisationIsClaimedAsHistoricalOrigin ≡ false
    analogyPromotedToIdentity : Bool
    analogyPromotedToIdentityIsFalse :
      analogyPromotedToIdentity ≡ false

canonicalNumberRoleProvenanceBoundary : NumberRoleProvenanceBoundary
canonicalNumberRoleProvenanceBoundary =
  number-role-provenance-boundary
    false refl
    false refl
    false refl
