module DASHI.Physics.Closure.NSNoTripleDangerBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Candidate-only, fail-closed no-triple-danger boundary.
--
-- The operator route is recorded as
--
--   K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)
--
-- and the boundary keeps the no-triple-danger claim in candidate mode.
-- The forbidden conjunction surface is made explicit so the module stays
-- fail-closed: no theorem promotion, no full-NS promotion, and no Clay
-- promotion are inferred from the boundary record.

operatorRouteStatement : String
operatorRouteStatement =
  "K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)"

tripleDangerTheoremShapeStatement : String
tripleDangerTheoremShapeStatement =
  "no-triple-danger theorem shape: the amplitude-weighted K_N(A) route excludes the triple-danger conjunction"

candidateOnlyStatement : String
candidateOnlyStatement =
  "candidate-only boundary: the no-triple-danger route is recorded, but no promotion is claimed"

failClosedStatement : String
failClosedStatement =
  "fail-closed boundary: the branch surface is explicit, and every promotion flag remains false"

forbiddenConjunctionStatement : String
forbiddenConjunctionStatement =
  "forbidden conjunction surface: candidate route, theorem-claim, and promotion may not be asserted together"

canonicalReceiptBoundary : List String
canonicalReceiptBoundary =
  "Amplitude-weighted operator route recorded: K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)"
  ∷ "Candidate no-triple-danger theorem shape recorded for the amplitude-weighted route"
  ∷ "Forbidden conjunction surface recorded explicitly and kept non-admissible"
  ∷ "All promotion flags remain false and the boundary stays fail-closed"
  ∷ []

data NSNoTripleDangerBoundaryStatus : Set where
  candidateOnlyNoTripleDangerRecorded :
    NSNoTripleDangerBoundaryStatus

data NSNoTripleDangerBranch : Set where
  amplitudeWeightedRouteBranch :
    NSNoTripleDangerBranch
  noTripleDangerCandidateBranch :
    NSNoTripleDangerBranch
  forbiddenConjunctionBranch :
    NSNoTripleDangerBranch
  failClosedBranch :
    NSNoTripleDangerBranch

canonicalNSNoTripleDangerBranchSurface :
  List NSNoTripleDangerBranch
canonicalNSNoTripleDangerBranchSurface =
  amplitudeWeightedRouteBranch
  ∷ noTripleDangerCandidateBranch
  ∷ forbiddenConjunctionBranch
  ∷ failClosedBranch
  ∷ []

data NSNoTripleDangerForbiddenConjunction : Set where
  routePlusTheoremClaimPlusPromotionBlocked :
    NSNoTripleDangerForbiddenConjunction
  routePlusTheoremClaimPlusFullNSPromotionBlocked :
    NSNoTripleDangerForbiddenConjunction
  routePlusTheoremClaimPlusClayPromotionBlocked :
    NSNoTripleDangerForbiddenConjunction

canonicalNSNoTripleDangerForbiddenConjunctions :
  List NSNoTripleDangerForbiddenConjunction
canonicalNSNoTripleDangerForbiddenConjunctions =
  routePlusTheoremClaimPlusPromotionBlocked
  ∷ routePlusTheoremClaimPlusFullNSPromotionBlocked
  ∷ routePlusTheoremClaimPlusClayPromotionBlocked
  ∷ []

data NSNoTripleDangerPromotion : Set where

nSNoTripleDangerPromotionImpossibleHere :
  NSNoTripleDangerPromotion → ⊥
nSNoTripleDangerPromotionImpossibleHere ()

organizationString : String
organizationString =
  "O: record the amplitude-weighted K_N(A) route as a candidate-only boundary."

requirementString : String
requirementString =
  "R: record the no-triple-danger theorem shape, the forbidden conjunction surface, and fail-closed status."

codeArtifactString : String
codeArtifactString =
  "C: export canonical strings, branch surface, forbidden conjunctions, false promotion flags, and an ORCSLPGF summary."

stateString : String
stateString =
  "S: the boundary is candidate-only; theorem, full-NS, Clay, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: the amplitude-weighted K_N(A) route conjugates L_neg(A) through L_abs(A)^(-1/2), and the theorem shape stays boundary-only."

proposalString : String
proposalString =
  "P: keep the no-triple-danger boundary in receipt mode until the forbidden conjunction is genuinely excluded."

governanceString : String
governanceString =
  "G: no theorem, full-NS, Clay, or terminal promotion may be inferred from this boundary."

failString : String
failString =
  "F: the missing evidence is a closed proof that the amplitude-weighted route excludes the triple-danger conjunction."

record NSNoTripleDangerBoundaryORCSLPGF : Set where
  constructor nsNoTripleDangerBoundaryORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ failString

open NSNoTripleDangerBoundaryORCSLPGF public

canonicalNSNoTripleDangerBoundaryORCSLPGF :
  NSNoTripleDangerBoundaryORCSLPGF
canonicalNSNoTripleDangerBoundaryORCSLPGF =
  nsNoTripleDangerBoundaryORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    failString
    refl

record NSNoTripleDangerBoundary : Setω where
  constructor mkNSNoTripleDangerBoundary
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSNoTripleDangerBoundary"

    status :
      NSNoTripleDangerBoundaryStatus
    statusIsCandidateOnly :
      status ≡ candidateOnlyNoTripleDangerRecorded

    amplitudeWeightedOperatorRoute :
      String
    amplitudeWeightedOperatorRouteIsCanonical :
      amplitudeWeightedOperatorRoute ≡ operatorRouteStatement

    noTripleDangerTheoremShape :
      String
    noTripleDangerTheoremShapeIsCanonical :
      noTripleDangerTheoremShape ≡ tripleDangerTheoremShapeStatement

    forbiddenConjunctionSurface :
      String
    forbiddenConjunctionSurfaceIsCanonical :
      forbiddenConjunctionSurface ≡ forbiddenConjunctionStatement

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted :
      Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool
    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    branchSurface :
      List NSNoTripleDangerBranch
    branchSurfaceIsCanonical :
      branchSurface ≡ canonicalNSNoTripleDangerBranchSurface

    forbiddenConjunctions :
      List NSNoTripleDangerForbiddenConjunction
    forbiddenConjunctionsAreCanonical :
      forbiddenConjunctions ≡ canonicalNSNoTripleDangerForbiddenConjunctions

    promotionFlags :
      List NSNoTripleDangerPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalReceiptBoundary

    orcslpgf :
      NSNoTripleDangerBoundaryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSNoTripleDangerBoundaryORCSLPGF

open NSNoTripleDangerBoundary public

canonicalNSNoTripleDangerBoundary :
  NSNoTripleDangerBoundary
canonicalNSNoTripleDangerBoundary =
  mkNSNoTripleDangerBoundary
    "NSNoTripleDangerBoundary"
    refl
    candidateOnlyNoTripleDangerRecorded
    refl
    operatorRouteStatement
    refl
    tripleDangerTheoremShapeStatement
    refl
    forbiddenConjunctionStatement
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    canonicalNSNoTripleDangerBranchSurface
    refl
    canonicalNSNoTripleDangerForbiddenConjunctions
    refl
    []
    refl
    canonicalReceiptBoundary
    refl
    canonicalNSNoTripleDangerBoundaryORCSLPGF
    refl

noTripleDangerBoundaryKeepsTheoremPromotedFalse :
  theoremPromoted canonicalNSNoTripleDangerBoundary ≡ false
noTripleDangerBoundaryKeepsTheoremPromotedFalse =
  refl

noTripleDangerBoundaryKeepsFullNSPromotedFalse :
  fullNSPromoted canonicalNSNoTripleDangerBoundary ≡ false
noTripleDangerBoundaryKeepsFullNSPromotedFalse =
  refl

noTripleDangerBoundaryKeepsClayPromotedFalse :
  clayPromoted canonicalNSNoTripleDangerBoundary ≡ false
noTripleDangerBoundaryKeepsClayPromotedFalse =
  refl

noTripleDangerBoundaryKeepsTerminalPromotedFalse :
  terminalPromoted canonicalNSNoTripleDangerBoundary ≡ false
noTripleDangerBoundaryKeepsTerminalPromotedFalse =
  refl
