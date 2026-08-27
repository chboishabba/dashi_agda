module DASHI.Core.NumberRoleProvenanceAtlasExact where

------------------------------------------------------------------------
-- NUMBER / ROLE PROVENANCE ATLAS
--
-- The supplied DASHI genealogy notes repeatedly warn that the same printed
-- number can acquire different mathematical and historical roles.  This module
-- makes that separation explicit and machine-visible.
--
-- Primary literature already owned by referenced/imported modules:
--
-- * Robert M. May, "Simple mathematical models with very complicated
--   dynamics", Nature 261 (1976), 459--467. DOI: 10.1038/261459a0.
-- * Theodore E. Harris, "The Theory of Branching Processes", Springer, 1963.
--   DOI: 10.1007/978-3-642-51866-9.
-- * Fernando Q. Gouvea, "p-adic Numbers: An Introduction", 2nd ed., Springer,
--   1997. DOI: 10.1007/978-3-642-59058-0.
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
  decimalTenPercentPowerupRole
  branchingCriticalAvailability
  logisticFoldCriticalPoint
  riemannCriticalRealPart
  historicalAffineRefinementFixedPoint
  threeAdicMinusHalfRole
  tenAdicTwoFiveHistoryRole
  jCoarseFineFrequencyRole
  decimalStratificationRole
  decimalJRetentionRole
  triadicJDepthRole
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

halfRiemannRoleDistinctFromThreeAdicMinusHalfRole :
  riemannCriticalRealPart ≡ threeAdicMinusHalfRole → ⊥
halfRiemannRoleDistinctFromThreeAdicMinusHalfRole ()

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

fivePointFiveHistoricalNumerator :
  Decimal.decimalRefinementNumerator Decimal.d5 1 ≡ 55
fivePointFiveHistoricalNumerator = Decimal.fiveDepthOne

ninePointNineHistoricalNumerator :
  Decimal.decimalRefinementNumerator Decimal.d9 1 ≡ 99
ninePointNineHistoricalNumerator = Decimal.nineDepthOne

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

quarterHistoricalEntry : NumberProvenanceEntry
quarterHistoricalEntry =
  number-provenance-entry
    "0.25 / 1/4"
    historicalDecimalComparison
    "supplied DASHI origin/reconstruction notes"
    "initial consideration threshold in the historical notes"
    "historical role; not inferred from later branching theory"
    "DASHI genealogy notes / NumberRoleProvenanceAtlasExact"
    historicalSourceMeaning

quarterBranchingEntry : NumberProvenanceEntry
quarterBranchingEntry =
  number-provenance-entry
    "0.25 / 1/4"
    branchingCriticalAvailability
    "Harris branching-process criterion"
    "critical availability for arity four"
    "4 * (1/4) = 1"
    "DASHI.Core.FiniteBranchingCriticalityExact"
    exactTheorem

threeTenthsHistoricalEntry : NumberProvenanceEntry
threeTenthsHistoricalEntry =
  number-provenance-entry
    "0.3"
    historicalDecimalComparison
    "supplied DASHI origin/reconstruction notes"
    "decimal 3-side comparison / attempted next consideration level"
    "kept separate from exact 1/3 branching criticality"
    "DASHI genealogy notes / NumberRoleProvenanceAtlasExact"
    historicalSourceMeaning

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

halfHistoricalEntry : NumberProvenanceEntry
halfHistoricalEntry =
  number-provenance-entry
    "0.5 / 1/2"
    dyadicScreenCut
    "supplied DASHI origin/reconstruction notes"
    "binary screen split / commitment or hinge surface"
    "historical role preceding later logistic/RH comparisons"
    "DASHI genealogy notes / NumberRoleProvenanceAtlasExact"
    historicalSourceMeaning

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
    "critical reflection fixes exactly Re(s)=1/2 in the repo rational model"
    "DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact"
    currentRepoOwner

sixTenthsHistoricalEntry : NumberProvenanceEntry
sixTenthsHistoricalEntry =
  number-provenance-entry
    "0.6"
    historicalDecimalComparison
    "supplied DASHI origin/reconstruction notes"
    "reinforcement / comparison level in the historical threshold sequence"
    "historical decimal role; no canonical identification with stage 6"
    "DASHI genealogy notes / NumberRoleProvenanceAtlasExact"
    historicalSourceMeaning

nineTenthsHistoricalEntry : NumberProvenanceEntry
nineTenthsHistoricalEntry =
  number-provenance-entry
    "0.9"
    historicalDecimalComparison
    "supplied DASHI origin/reconstruction notes"
    "high decimal comparison level"
    "later three-axis toy arithmetic gives (3*9)^3/10^3 = 19683/1000, but that is retrospective"
    "DASHI.Biology.JCoarseFineBranchingCriticalityExact"
    retrospectiveAnalogy

fivePointFivePowerupEntry : NumberProvenanceEntry
fivePointFivePowerupEntry =
  number-provenance-entry
    "5.5"
    decimalTenPercentPowerupRole
    "supplied DASHI +10% / stage-refinement reconstruction notes"
    "first repeated-digit fine refinement of coarse 5"
    "decimalRefinementNumerator d5 1 = 55, interpreted over denominator 10"
    "DASHI.Core.DecimalResidualRefinementExact"
    historicalSourceMeaning

ninePointNinePowerupEntry : NumberProvenanceEntry
ninePointNinePowerupEntry =
  number-provenance-entry
    "9.9"
    decimalTenPercentPowerupRole
    "supplied DASHI +10% / coarse-fine reconstruction notes"
    "first repeated-digit fine refinement of coarse 9"
    "decimalRefinementNumerator d9 1 = 99, interpreted over denominator 10"
    "DASHI.Core.DecimalResidualRefinementExact"
    historicalSourceMeaning

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

threeAdicMinusHalfEntry : NumberProvenanceEntry
threeAdicMinusHalfEntry =
  number-provenance-entry
    "-1/2"
    threeAdicMinusHalfRole
    "standard 3-adic geometric-series identity; repo keeps convergence witness explicit"
    "candidate/sum for 1 + 3 + 3^2 + ... in the 3-adic metric"
    "not a real-series equality and not the same role as positive 1/2"
    "DASHI.Analysis.ThreeAdicGeometricSeries"
    currentRepoOwner

fiveTenAdicEntry : NumberProvenanceEntry
fiveTenAdicEntry =
  number-provenance-entry
    "5"
    tenAdicTwoFiveHistoryRole
    "Gouvea p-adic background; DOI 10.1007/978-3-642-59058-0"
    "5-adic factor in the compatible-history decomposition of the decimal 10-adic tower"
    "10 = 2*5 motivates the CRT product tower; ring-level claims stay separate"
    "DASHI.Biology.TenAdicInverseLimitBridge"
    currentRepoOwner

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

decimalJElevenEntry : NumberProvenanceEntry
decimalJElevenEntry =
  number-provenance-entry
    "11"
    decimalJRetentionRole
    "older supplied JCoarse/JFine stratification notes"
    "retain decimal strata j0=1 and j1=10 simultaneously"
    "1 + 10 = 11 is a decimal retained-resolution story"
    "DASHI decimal/J stratification lineage"
    historicalSourceMeaning

triadicJElevenEntry : NumberProvenanceEntry
triadicJElevenEntry =
  number-provenance-entry
    "11"
    triadicJDepthRole
    "current DASHI JCoarse/JFine triadic harmonic owner"
    "absolute depth obtained from coarse depth 2 plus relative fine depth 9"
    "3^11 = 3^2 * 3^9; this is not the same theorem as decimal 1+10=11"
    "DASHI.Biology.JFineCoarseRelativeScaleExact"
    currentRepoOwner

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
    decimalElevenIdentifiedWithTriadicEleven : Bool
    decimalElevenIdentifiedWithTriadicElevenIsFalse :
      decimalElevenIdentifiedWithTriadicEleven ≡ false
    positiveHalfIdentifiedWithThreeAdicMinusHalf : Bool
    positiveHalfIdentifiedWithThreeAdicMinusHalfIsFalse :
      positiveHalfIdentifiedWithThreeAdicMinusHalf ≡ false
    fivePointFiveIdentifiedWithHalfThreshold : Bool
    fivePointFiveIdentifiedWithHalfThresholdIsFalse :
      fivePointFiveIdentifiedWithHalfThreshold ≡ false

canonicalNumberRoleProvenanceBoundary : NumberRoleProvenanceBoundary
canonicalNumberRoleProvenanceBoundary =
  number-role-provenance-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
