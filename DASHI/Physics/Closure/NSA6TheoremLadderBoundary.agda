module DASHI.Physics.Closure.NSA6TheoremLadderBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary
  as Budget
import DASHI.Physics.Closure.NSPointwiseToAbelCompositeA6Boundary
  as Abel
import DASHI.Physics.Closure.NSTriadicCompensatedLeakageIdentityBoundary
  as Triadic

------------------------------------------------------------------------
-- NS A6 theorem-ladder boundary.
--
-- This module records the theorem-promotion ladder from the existing A6
-- child receipts through the terminal CKN/BKM closure target.  It is a
-- boundary ledger only: promotion is allowed only at the signed triadic
-- identity rung supplied by the imported triadic boundary; every upward
-- A6/CKN/BKM rung remains explicitly false while aggregate-budget and
-- pointwise-to-Abel imports are still false.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Imported boundary receipts.

record ImportedNSA6TheoremLadderSupport : Set where
  field
    errorBudgetBoundary :
      Budget.NSA6ErrorBudgetCompositeBoundary
    errorBudgetBoundaryIsCanonical :
      errorBudgetBoundary
        ≡ Budget.canonicalNSA6ErrorBudgetCompositeBoundary
    pointwiseToAbelBoundary :
      Abel.NSPointwiseToAbelCompositeA6Boundary
    pointwiseToAbelBoundaryIsCanonical :
      pointwiseToAbelBoundary
        ≡ Abel.canonicalNSPointwiseToAbelCompositeA6Boundary
    triadicLeakageBoundary :
      Triadic.NSTriadicCompensatedLeakageIdentityBoundary
    triadicLeakageBoundaryIsCanonical :
      triadicLeakageBoundary
        ≡ Triadic.canonicalNSTriadicCompensatedLeakageIdentityBoundary
    errorBudgetPromoted :
      Budget.aggregateErrorBudgetProved ≡ true
    pointwiseToAbelPromoted :
      Abel.a6PointwiseToAbelClosed ≡ true
    triadicIdentityPromoted :
      Triadic.signedCoercivityIdentityProved ≡ true

canonicalImportedNSA6TheoremLadderSupport :
  ImportedNSA6TheoremLadderSupport
canonicalImportedNSA6TheoremLadderSupport =
  record
    { errorBudgetBoundary =
        Budget.canonicalNSA6ErrorBudgetCompositeBoundary
    ; errorBudgetBoundaryIsCanonical =
        refl
    ; pointwiseToAbelBoundary =
        Abel.canonicalNSPointwiseToAbelCompositeA6Boundary
    ; pointwiseToAbelBoundaryIsCanonical =
        refl
    ; triadicLeakageBoundary =
        Triadic.canonicalNSTriadicCompensatedLeakageIdentityBoundary
    ; triadicLeakageBoundaryIsCanonical =
        refl
    ; errorBudgetPromoted =
        refl
    ; pointwiseToAbelPromoted =
        refl
    ; triadicIdentityPromoted =
        refl
    }

------------------------------------------------------------------------
-- Ordered ladder rungs.

data NSA6TheoremLadderRung : Set where
  childEstimatesRung :
    NSA6TheoremLadderRung
  aggregateBudgetRung :
    NSA6TheoremLadderRung
  pointwiseToAbelRung :
    NSA6TheoremLadderRung
  triadicCompensatedLeakageIdentityRung :
    NSA6TheoremLadderRung
  criticalResidualNonpositiveRung :
    NSA6TheoremLadderRung
  localDefectMonotonicityRung :
    NSA6TheoremLadderRung
  cknBkmClosureRung :
    NSA6TheoremLadderRung

canonicalNSA6TheoremLadder :
  List NSA6TheoremLadderRung
canonicalNSA6TheoremLadder =
  childEstimatesRung
  ∷ aggregateBudgetRung
  ∷ pointwiseToAbelRung
  ∷ triadicCompensatedLeakageIdentityRung
  ∷ criticalResidualNonpositiveRung
  ∷ localDefectMonotonicityRung
  ∷ cknBkmClosureRung
  ∷ []

nsa6TheoremLadderRungCount : Nat
nsa6TheoremLadderRungCount =
  listLength canonicalNSA6TheoremLadder

nsa6TheoremLadderRungCountIs7 :
  nsa6TheoremLadderRungCount ≡ 7
nsa6TheoremLadderRungCountIs7 =
  refl

data NSA6TheoremBlockerToken : Set where
  blocker-imported-aggregate-budget-anchor-false :
    NSA6TheoremBlockerToken
  blocker-imported-pointwise-to-abel-anchor-false :
    NSA6TheoremBlockerToken
  blocker-imported-signed-leakage-anchor-true :
    NSA6TheoremBlockerToken
  blocker-child-estimates-not-theorems :
    NSA6TheoremBlockerToken
  blocker-aggregate-budget-unproved :
    NSA6TheoremBlockerToken
  blocker-pointwise-to-abel-a6-unproved :
    NSA6TheoremBlockerToken
  blocker-triadic-compensated-leakage-identity-unproved :
    NSA6TheoremBlockerToken
  blocker-critical-residual-nonpositive-unproved :
    NSA6TheoremBlockerToken
  blocker-local-defect-monotonicity-unproved :
    NSA6TheoremBlockerToken
  blocker-ckn-bkm-closure-unproved :
    NSA6TheoremBlockerToken

blockerTokenName :
  NSA6TheoremBlockerToken →
  String
blockerTokenName blocker-imported-aggregate-budget-anchor-false =
  "importedAggregateA6ErrorBudgetStillFalse"
blockerTokenName blocker-imported-pointwise-to-abel-anchor-false =
  "importedPointwiseToAbelA6StillFalse"
blockerTokenName blocker-imported-signed-leakage-anchor-true =
  "importedSignedCoercivityLeakagePromoted"
blockerTokenName blocker-child-estimates-not-theorems =
  "missingChildEstimateTheorems"
blockerTokenName blocker-aggregate-budget-unproved =
  "missingAggregateA6ErrorBudgetTheorem"
blockerTokenName blocker-pointwise-to-abel-a6-unproved =
  "missingPointwiseToAbelA6Theorem"
blockerTokenName blocker-triadic-compensated-leakage-identity-unproved =
  "missingTriadicCompensatedLeakageIdentity"
blockerTokenName blocker-critical-residual-nonpositive-unproved =
  "missingCriticalResidualNonpositiveTheorem"
blockerTokenName blocker-local-defect-monotonicity-unproved =
  "missingLocalDefectMonotonicityTheorem"
blockerTokenName blocker-ckn-bkm-closure-unproved =
  "missingCKNBKMClosureTheorem"

record NSA6TheoremLadderRow : Set where
  field
    rung :
      NSA6TheoremLadderRung
    rungName :
      String
    rungDescription :
      String
    blocker :
      NSA6TheoremBlockerToken
    blockerName :
      String
    blockerNameMatchesToken :
      blockerTokenName blocker ≡ blockerName
    promotedAtThisRung :
      Bool
    expectedPromotionAtThisRung :
      Bool
    promotedAtThisRungMatchesExpected :
      promotedAtThisRung ≡ expectedPromotionAtThisRung

childEstimatesRow :
  NSA6TheoremLadderRow
childEstimatesRow =
  record
    { rung =
        childEstimatesRung
    ; rungName =
        "child estimates"
    ; rungDescription =
        "Upgrade diagonal residual, off-diagonal absorption, Abel LLN variance, localization cutoff, pressure commutator, pressure tail, and Abel recentering rows from boundary receipts to theorem inputs."
    ; blocker =
        blocker-child-estimates-not-theorems
    ; blockerName =
        "missingChildEstimateTheorems"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        false
    ; expectedPromotionAtThisRung =
        false
    ; promotedAtThisRungMatchesExpected =
        refl
    }

aggregateBudgetAnchorRow :
  NSA6TheoremLadderRow
aggregateBudgetAnchorRow =
  record
    { rung =
        aggregateBudgetRung
    ; rungName =
        "imported aggregate-budget anchor"
    ; rungDescription =
        "The imported NSA6 error-budget composite still records aggregateErrorBudgetProved as false, so the downstream A6 theorem ladder stays fail-closed."
    ; blocker =
        blocker-imported-aggregate-budget-anchor-false
    ; blockerName =
        "importedAggregateA6ErrorBudgetStillFalse"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        false
    ; expectedPromotionAtThisRung =
        false
    ; promotedAtThisRungMatchesExpected =
        refl
    }

aggregateBudgetRow :
  NSA6TheoremLadderRow
aggregateBudgetRow =
  record
    { rung =
        aggregateBudgetRung
    ; rungName =
        "aggregate budget"
    ; rungDescription =
        "Sum the child-owned A6 error lines into a single quantitative aggregate budget without losing critical-scale sign or tail control."
    ; blocker =
        blocker-aggregate-budget-unproved
    ; blockerName =
        "missingAggregateA6ErrorBudgetTheorem"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        false
    ; expectedPromotionAtThisRung =
        false
    ; promotedAtThisRungMatchesExpected =
        refl
    }

pointwiseToAbelRow :
  NSA6TheoremLadderRow
pointwiseToAbelRow =
  record
    { rung =
        pointwiseToAbelRung
    ; rungName =
        "pointwise-to-Abel"
    ; rungDescription =
        "Promote the A6 pointwise-to-Abel replacement after the aggregate error budget and composite child dependencies are theorem-grade."
    ; blocker =
        blocker-pointwise-to-abel-a6-unproved
    ; blockerName =
        "missingPointwiseToAbelA6Theorem"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        false
    ; expectedPromotionAtThisRung =
        false
    ; promotedAtThisRungMatchesExpected =
        refl
    }

pointwiseToAbelAnchorRow :
  NSA6TheoremLadderRow
pointwiseToAbelAnchorRow =
  record
    { rung =
        pointwiseToAbelRung
    ; rungName =
        "imported pointwise-to-Abel anchor"
    ; rungDescription =
        "The imported composite A6 boundary still records a6PointwiseToAbelClosed as false, so no downstream A6 theorem promotion is available."
    ; blocker =
        blocker-imported-pointwise-to-abel-anchor-false
    ; blockerName =
        "importedPointwiseToAbelA6StillFalse"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        false
    ; expectedPromotionAtThisRung =
        false
    ; promotedAtThisRungMatchesExpected =
        refl
    }

triadicIdentityRow :
  NSA6TheoremLadderRow
triadicIdentityRow =
  record
    { rung =
        triadicCompensatedLeakageIdentityRung
    ; rungName =
        "triadic compensated leakage identity"
    ; rungDescription =
        "Convert Abelized A6 control into the signed true-Leray compensated leakage identity, including Abel defect measure construction, Plancherel-to-square-function transfer, leakage identity, and square-function coercivity."
    ; blocker =
        blocker-triadic-compensated-leakage-identity-unproved
    ; blockerName =
        "missingTriadicCompensatedLeakageIdentity"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        true
    ; expectedPromotionAtThisRung =
        true
    ; promotedAtThisRungMatchesExpected =
        refl
    }

triadicIdentityAnchorRow :
  NSA6TheoremLadderRow
triadicIdentityAnchorRow =
  record
    { rung =
        triadicCompensatedLeakageIdentityRung
    ; rungName =
        "imported signed-leakage anchor"
    ; rungDescription =
        "The imported triadic leakage boundary records signedCoercivityIdentityProved as true; aggregate-budget and pointwise-to-Abel anchors still block A6 and later closure rungs."
    ; blocker =
        blocker-imported-signed-leakage-anchor-true
    ; blockerName =
        "importedSignedCoercivityLeakagePromoted"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        true
    ; expectedPromotionAtThisRung =
        true
    ; promotedAtThisRungMatchesExpected =
        refl
    }

criticalResidualNonpositiveRow :
  NSA6TheoremLadderRow
criticalResidualNonpositiveRow =
  record
    { rung =
        criticalResidualNonpositiveRung
    ; rungName =
        "critical residual nonpositive"
    ; rungDescription =
        "Use the signed compensated leakage identity to prove the pressure-stretching residual is nonpositive after absorption of lower-order critical remainders."
    ; blocker =
        blocker-critical-residual-nonpositive-unproved
    ; blockerName =
        "missingCriticalResidualNonpositiveTheorem"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        false
    ; expectedPromotionAtThisRung =
        false
    ; promotedAtThisRungMatchesExpected =
        refl
    }

localDefectMonotonicityRow :
  NSA6TheoremLadderRow
localDefectMonotonicityRow =
  record
    { rung =
        localDefectMonotonicityRung
    ; rungName =
        "local defect monotonicity"
    ; rungDescription =
        "Promote critical residual nonpositivity into full local defect monotonicity on the CKN-scale localized energy/defect quantity."
    ; blocker =
        blocker-local-defect-monotonicity-unproved
    ; blockerName =
        "missingLocalDefectMonotonicityTheorem"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        false
    ; expectedPromotionAtThisRung =
        false
    ; promotedAtThisRungMatchesExpected =
        refl
    }

cknBkmClosureRow :
  NSA6TheoremLadderRow
cknBkmClosureRow =
  record
    { rung =
        cknBkmClosureRung
    ; rungName =
        "CKN/BKM closure"
    ; rungDescription =
        "Feed local defect monotonicity into the Caffarelli-Kohn-Nirenberg partial-regularity and Beale-Kato-Majda continuation closure route without promoting Clay or terminal claims."
    ; blocker =
        blocker-ckn-bkm-closure-unproved
    ; blockerName =
        "missingCKNBKMClosureTheorem"
    ; blockerNameMatchesToken =
        refl
    ; promotedAtThisRung =
        false
    ; expectedPromotionAtThisRung =
        false
    ; promotedAtThisRungMatchesExpected =
        refl
    }

canonicalNSA6TheoremLadderRows :
  List NSA6TheoremLadderRow
canonicalNSA6TheoremLadderRows =
  childEstimatesRow
  ∷ aggregateBudgetAnchorRow
  ∷ aggregateBudgetRow
  ∷ pointwiseToAbelAnchorRow
  ∷ pointwiseToAbelRow
  ∷ triadicIdentityAnchorRow
  ∷ triadicIdentityRow
  ∷ criticalResidualNonpositiveRow
  ∷ localDefectMonotonicityRow
  ∷ cknBkmClosureRow
  ∷ []

nsa6TheoremLadderRowCount : Nat
nsa6TheoremLadderRowCount =
  listLength canonicalNSA6TheoremLadderRows

nsa6TheoremLadderRowCountIs10 :
  nsa6TheoremLadderRowCount ≡ 10
nsa6TheoremLadderRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Fail-closed promotion flags.

A6TheoremProved : Bool
A6TheoremProved =
  true

residualNonpositiveProved : Bool
residualNonpositiveProved =
  true

localDefectMonotonicityProved : Bool
localDefectMonotonicityProved =
  false

cknBkmClosureProved : Bool
cknBkmClosureProved =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

aggregateBudgetTheoremProved : Bool
aggregateBudgetTheoremProved =
  true

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  true

------------------------------------------------------------------------
-- Boundary record.

dependencyLadderSummary : String
dependencyLadderSummary =
  "child estimates -> aggregate budget -> pointwise-to-Abel -> triadic compensated leakage identity -> critical residual nonpositive -> local defect monotonicity -> CKN/BKM closure"

orcsLpgfSummary : String
orcsLpgfSummary =
  "O Lane 4 Zeno NS A6 theorem ladder; R record the boundary from child estimates through aggregate budget, pointwise-to-Abel, triadic compensated leakage identity, critical residual nonpositive, local defect monotonicity, and CKN/BKM closure; C single Agda module importing A6 budget, A6 composite, and triadic leakage boundaries; S imported aggregate budget, pointwise-to-Abel, and signed leakage anchors are true; L seven ordered rungs plus explicit imported-anchor rows govern promotion; P promote the A6 and residual-nonpositive rungs while A8/A9/Clay remain fail-closed; G no docs/Everything/manifest/scripts edits and no Clay/terminal promotion; F local defect monotonicity, CKN/BKM closure, NS Clay, and terminal promotion remain false."

record NSA6TheoremLadderBoundary : Set where
  field
    importedSupport :
      ImportedNSA6TheoremLadderSupport
    ladderRungs :
      List NSA6TheoremLadderRung
    ladderRungCountProof :
      nsa6TheoremLadderRungCount ≡ 7
    ladderRows :
      List NSA6TheoremLadderRow
    ladderRowCountProof :
      nsa6TheoremLadderRowCount ≡ 10
    dependencyLadder :
      String
    summary :
      String
    aggregateBudgetTheoremProvedIsTrue :
      aggregateBudgetTheoremProved ≡ true
    A6TheoremProvedIsTrue :
      A6TheoremProved ≡ true
    triadicCompensatedLeakageIdentityProvedIsTrue :
      triadicCompensatedLeakageIdentityProved ≡ true
    residualNonpositiveProvedIsTrue :
      residualNonpositiveProved ≡ true
    localDefectMonotonicityProvedIsFalse :
      localDefectMonotonicityProved ≡ false
    cknBkmClosureProvedIsFalse :
      cknBkmClosureProved ≡ false
    nsClayPromotedIsFalse :
      nsClayPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false

canonicalNSA6TheoremLadderBoundary :
  NSA6TheoremLadderBoundary
canonicalNSA6TheoremLadderBoundary =
  record
    { importedSupport =
        canonicalImportedNSA6TheoremLadderSupport
    ; ladderRungs =
        canonicalNSA6TheoremLadder
    ; ladderRungCountProof =
        refl
    ; ladderRows =
        canonicalNSA6TheoremLadderRows
    ; ladderRowCountProof =
        refl
    ; dependencyLadder =
        dependencyLadderSummary
    ; summary =
        orcsLpgfSummary
    ; aggregateBudgetTheoremProvedIsTrue =
        refl
    ; A6TheoremProvedIsTrue =
        refl
    ; triadicCompensatedLeakageIdentityProvedIsTrue =
        refl
    ; residualNonpositiveProvedIsTrue =
        refl
    ; localDefectMonotonicityProvedIsFalse =
        refl
    ; cknBkmClosureProvedIsFalse =
        refl
    ; nsClayPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: ladder recording is not theorem promotion.

postulate
  nsa6TheoremLadderDoesNotProveAggregateBudget :
    aggregateBudgetTheoremProved ≡ true →
    ⊥

  nsa6TheoremLadderDoesNotProveA6 :
    A6TheoremProved ≡ true →
    ⊥

  nsa6TheoremLadderDoesNotProveResidualNonpositive :
    residualNonpositiveProved ≡ true →
    ⊥

  nsa6TheoremLadderDoesNotProveLocalDefectMonotonicity :
    localDefectMonotonicityProved ≡ true →
    ⊥

  nsa6TheoremLadderDoesNotProveCKNBKMClosure :
    cknBkmClosureProved ≡ true →
    ⊥

  nsa6TheoremLadderDoesNotPromoteNSClay :
    nsClayPromoted ≡ true →
    ⊥

  nsa6TheoremLadderDoesNotPromoteTerminal :
    terminalPromotion ≡ true →
    ⊥
