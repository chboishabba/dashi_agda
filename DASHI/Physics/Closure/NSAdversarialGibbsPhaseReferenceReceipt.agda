module DASHI.Physics.Closure.NSAdversarialGibbsPhaseReferenceReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadFrustrationDefectBoundary
  as Boundary

------------------------------------------------------------------------
-- NS adversarial Gibbs phase-reference receipt.
--
-- This module records the regularized adversarial Gibbs reference
--
--   nu*_N,kappa
--
-- built from the phase-frustration energy.  It is candidate-only and
-- fail-closed.  The low-frustration ensemble and the frustration defect
-- remain diagnostic surfaces only; neither proves NS regularity or a
-- Sacasa bridge, and theorem/full-NS/Clay promotion stays false.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSAdversarialGibbsPhaseReferenceRow : Set where
  canonicalPhaseFrustrationEnergyRow :
    NSAdversarialGibbsPhaseReferenceRow
  canonicalRegularizedAdversarialWeightRow :
    NSAdversarialGibbsPhaseReferenceRow
  canonicalCandidateOnlyReferenceRow :
    NSAdversarialGibbsPhaseReferenceRow
  canonicalLowFrustrationDiagnosticRow :
    NSAdversarialGibbsPhaseReferenceRow
  canonicalSacasaBridgeBlockerRow :
    NSAdversarialGibbsPhaseReferenceRow
  canonicalFailClosedPromotionRow :
    NSAdversarialGibbsPhaseReferenceRow

canonicalNSAdversarialGibbsPhaseReferenceRows :
  List NSAdversarialGibbsPhaseReferenceRow
canonicalNSAdversarialGibbsPhaseReferenceRows =
  canonicalPhaseFrustrationEnergyRow
  ∷ canonicalRegularizedAdversarialWeightRow
  ∷ canonicalCandidateOnlyReferenceRow
  ∷ canonicalLowFrustrationDiagnosticRow
  ∷ canonicalSacasaBridgeBlockerRow
  ∷ canonicalFailClosedPromotionRow
  ∷ []

nSAdversarialGibbsPhaseReferenceRowCount : Nat
nSAdversarialGibbsPhaseReferenceRowCount =
  listLength canonicalNSAdversarialGibbsPhaseReferenceRows

nSAdversarialGibbsPhaseReferenceRowCountIs6 :
  nSAdversarialGibbsPhaseReferenceRowCount ≡ 6
nSAdversarialGibbsPhaseReferenceRowCountIs6 =
  refl

data NSAdversarialGibbsPhaseReferenceGap : Set where
  noLowFrustrationEnsembleProofOfNSRegularity :
    NSAdversarialGibbsPhaseReferenceGap
  noFrustrationDefectProofOfNSRegularity :
    NSAdversarialGibbsPhaseReferenceGap
  noLowFrustrationEnsembleSacasaBridge :
    NSAdversarialGibbsPhaseReferenceGap
  noFrustrationDefectSacasaBridge :
    NSAdversarialGibbsPhaseReferenceGap
  noTheoremFullNSOrClayPromotion :
    NSAdversarialGibbsPhaseReferenceGap

canonicalNSAdversarialGibbsPhaseReferenceGaps :
  List NSAdversarialGibbsPhaseReferenceGap
canonicalNSAdversarialGibbsPhaseReferenceGaps =
  noLowFrustrationEnsembleProofOfNSRegularity
  ∷ noFrustrationDefectProofOfNSRegularity
  ∷ noLowFrustrationEnsembleSacasaBridge
  ∷ noFrustrationDefectSacasaBridge
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSAdversarialGibbsPhaseReferenceGapCount : Nat
nSAdversarialGibbsPhaseReferenceGapCount =
  listLength canonicalNSAdversarialGibbsPhaseReferenceGaps

nSAdversarialGibbsPhaseReferenceGapCountIs5 :
  nSAdversarialGibbsPhaseReferenceGapCount ≡ 5
nSAdversarialGibbsPhaseReferenceGapCountIs5 =
  refl

record NSAdversarialGibbsPhaseReferenceORCSLPGF : Set where
  constructor nSAdversarialGibbsPhaseReferenceORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "Object: the regularized adversarial Gibbs reference nu*_N,kappa built from phase-frustration energy"
    R : String
    RIsCanonical : R ≡
      "Requirement: candidate-only, fail-closed reference data with no NS regularity or Sacasa bridge claim"
    C : String
    CIsCanonical : C ≡
      "Carrier rows, gap rows, and canonical refl witnesses are exported in this receipt"
    S : String
    SIsCanonical : S ≡
      "State: phase-frustration energy and its Gibbs weighting are recorded as diagnostics only"
    L : String
    LIsCanonical : L ≡
      "Lattice: phase-frustration energy -> regularized Gibbs weighting -> blocked NS regularity and Sacasa bridge claims"
    P : String
    PIsCanonical : P ≡
      "Proposal: treat nu*_N,kappa as a candidate reference surface, not as a theorem source"
    G : String
    GIsCanonical : G ≡
      "Governance: theorem, full-NS, and Clay promotion remain false"
    F : String
    FIsCanonical : F ≡
      "Gap: neither the low-frustration ensemble nor the frustration defect proves NS regularity or a Sacasa bridge"

open NSAdversarialGibbsPhaseReferenceORCSLPGF public

canonicalNSAdversarialGibbsPhaseReferenceORCSLPGF :
  NSAdversarialGibbsPhaseReferenceORCSLPGF
canonicalNSAdversarialGibbsPhaseReferenceORCSLPGF =
  nSAdversarialGibbsPhaseReferenceORCSLPGF
    "Object: the regularized adversarial Gibbs reference nu*_N,kappa built from phase-frustration energy"
    refl
    "Requirement: candidate-only, fail-closed reference data with no NS regularity or Sacasa bridge claim"
    refl
    "Carrier rows, gap rows, and canonical refl witnesses are exported in this receipt"
    refl
    "State: phase-frustration energy and its Gibbs weighting are recorded as diagnostics only"
    refl
    "Lattice: phase-frustration energy -> regularized Gibbs weighting -> blocked NS regularity and Sacasa bridge claims"
    refl
    "Proposal: treat nu*_N,kappa as a candidate reference surface, not as a theorem source"
    refl
    "Governance: theorem, full-NS, and Clay promotion remain false"
    refl
    "Gap: neither the low-frustration ensemble nor the frustration defect proves NS regularity or a Sacasa bridge"
    refl

record NSAdversarialGibbsPhaseReferenceReceipt : Set where
  constructor nSAdversarialGibbsPhaseReferenceReceipt
  field
    boundary :
      Boundary.NSTriadFrustrationDefectBoundary
    boundaryIsCanonical :
      boundary ≡ Boundary.canonicalNSTriadFrustrationDefectBoundary
    referenceFormula : String
    referenceFormulaIsCanonical :
      referenceFormula ≡ "nu*_N,kappa"
    candidateOnly : Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true
    failClosed : Bool
    failClosedIsTrue :
      failClosed ≡ true
    lowFrustrationEnsembleCandidateOnly : Bool
    lowFrustrationEnsembleCandidateOnlyIsTrue :
      lowFrustrationEnsembleCandidateOnly ≡ true
    lowFrustrationEnsembleProvesNSRegularity : Bool
    lowFrustrationEnsembleProvesNSRegularityIsFalse :
      lowFrustrationEnsembleProvesNSRegularity ≡ false
    frustrationDefectProvesNSRegularity : Bool
    frustrationDefectProvesNSRegularityIsFalse :
      frustrationDefectProvesNSRegularity ≡ false
    lowFrustrationEnsembleProvesSacasaBridge : Bool
    lowFrustrationEnsembleProvesSacasaBridgeIsFalse :
      lowFrustrationEnsembleProvesSacasaBridge ≡ false
    frustrationDefectProvesSacasaBridge : Bool
    frustrationDefectProvesSacasaBridgeIsFalse :
      frustrationDefectProvesSacasaBridge ≡ false
    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false
    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false
    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    orcslpgf :
      NSAdversarialGibbsPhaseReferenceORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSAdversarialGibbsPhaseReferenceORCSLPGF
    rows :
      List NSAdversarialGibbsPhaseReferenceRow
    rowsAreCanonical :
      rows ≡ canonicalNSAdversarialGibbsPhaseReferenceRows
    rowCount :
      Nat
    rowCountIs6 :
      rowCount ≡ 6
    gaps :
      List NSAdversarialGibbsPhaseReferenceGap
    gapsAreCanonical :
      gaps ≡ canonicalNSAdversarialGibbsPhaseReferenceGaps
    gapCount :
      Nat
    gapCountIs5 :
      gapCount ≡ 5
    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only adversarial Gibbs phase-reference receipt: nu*_N,kappa is built from the phase-frustration energy, but the low-frustration ensemble and the frustration defect remain diagnostic only; neither proves NS regularity or a Sacasa bridge; theorem/full-NS/Clay flags stay false."

open NSAdversarialGibbsPhaseReferenceReceipt public

canonicalNSAdversarialGibbsPhaseReferenceReceipt :
  NSAdversarialGibbsPhaseReferenceReceipt
canonicalNSAdversarialGibbsPhaseReferenceReceipt =
  nSAdversarialGibbsPhaseReferenceReceipt
    Boundary.canonicalNSTriadFrustrationDefectBoundary
    refl
    "nu*_N,kappa"
    refl
    true
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
    false
    refl
    false
    refl
    false
    refl
    canonicalNSAdversarialGibbsPhaseReferenceORCSLPGF
    refl
    canonicalNSAdversarialGibbsPhaseReferenceRows
    refl
    nSAdversarialGibbsPhaseReferenceRowCount
    refl
    canonicalNSAdversarialGibbsPhaseReferenceGaps
    refl
    nSAdversarialGibbsPhaseReferenceGapCount
    refl
    "Candidate-only adversarial Gibbs phase-reference receipt: nu*_N,kappa is built from the phase-frustration energy, but the low-frustration ensemble and the frustration defect remain diagnostic only; neither proves NS regularity or a Sacasa bridge; theorem/full-NS/Clay flags stay false."
    refl

candidateOnlyAdversarialGibbsReceipt :
  candidateOnly canonicalNSAdversarialGibbsPhaseReferenceReceipt ≡ true
candidateOnlyAdversarialGibbsReceipt =
  refl

failClosedAdversarialGibbsReceipt :
  failClosed canonicalNSAdversarialGibbsPhaseReferenceReceipt ≡ true
failClosedAdversarialGibbsReceipt =
  refl
