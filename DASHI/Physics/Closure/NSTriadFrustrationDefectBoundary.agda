module DASHI.Physics.Closure.NSTriadFrustrationDefectBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS triad frustration-defect boundary.
--
-- This module records the fail-closed carrier for the route
--
--   F_N(psi) = inf_phi ||B phi - psi||^2
--
-- in a candidate-only surface.  It keeps the low-frustration ensemble and
-- the frustration defect as diagnostic data only.  Neither of them proves
-- NS regularity or a Sacasa bridge, and no theorem/full-NS/Clay promotion
-- is made here.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSTriadFrustrationDefectBoundaryRow : Set where
  canonicalFrustrationCarrierFormulaRow :
    NSTriadFrustrationDefectBoundaryRow
  canonicalTriadicOperatorCarrierRow :
    NSTriadFrustrationDefectBoundaryRow
  canonicalLowFrustrationEnsembleRow :
    NSTriadFrustrationDefectBoundaryRow
  canonicalSacasaBridgeBlockerRow :
    NSTriadFrustrationDefectBoundaryRow
  canonicalFailClosedPromotionRow :
    NSTriadFrustrationDefectBoundaryRow

canonicalNSTriadFrustrationDefectBoundaryRows :
  List NSTriadFrustrationDefectBoundaryRow
canonicalNSTriadFrustrationDefectBoundaryRows =
  canonicalFrustrationCarrierFormulaRow
  ∷ canonicalTriadicOperatorCarrierRow
  ∷ canonicalLowFrustrationEnsembleRow
  ∷ canonicalSacasaBridgeBlockerRow
  ∷ canonicalFailClosedPromotionRow
  ∷ []

nSTriadFrustrationDefectBoundaryRowCount : Nat
nSTriadFrustrationDefectBoundaryRowCount =
  listLength canonicalNSTriadFrustrationDefectBoundaryRows

nSTriadFrustrationDefectBoundaryRowCountIs5 :
  nSTriadFrustrationDefectBoundaryRowCount ≡ 5
nSTriadFrustrationDefectBoundaryRowCountIs5 =
  refl

data NSTriadFrustrationDefectBoundaryGap : Set where
  noLowFrustrationEnsembleProofOfNSRegularity :
    NSTriadFrustrationDefectBoundaryGap
  noFrustrationDefectProofOfNSRegularity :
    NSTriadFrustrationDefectBoundaryGap
  noLowFrustrationEnsembleSacasaBridge :
    NSTriadFrustrationDefectBoundaryGap
  noFrustrationDefectSacasaBridge :
    NSTriadFrustrationDefectBoundaryGap
  noTheoremFullNSOrClayPromotion :
    NSTriadFrustrationDefectBoundaryGap

canonicalNSTriadFrustrationDefectBoundaryGaps :
  List NSTriadFrustrationDefectBoundaryGap
canonicalNSTriadFrustrationDefectBoundaryGaps =
  noLowFrustrationEnsembleProofOfNSRegularity
  ∷ noFrustrationDefectProofOfNSRegularity
  ∷ noLowFrustrationEnsembleSacasaBridge
  ∷ noFrustrationDefectSacasaBridge
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSTriadFrustrationDefectBoundaryGapCount : Nat
nSTriadFrustrationDefectBoundaryGapCount =
  listLength canonicalNSTriadFrustrationDefectBoundaryGaps

nSTriadFrustrationDefectBoundaryGapCountIs5 :
  nSTriadFrustrationDefectBoundaryGapCount ≡ 5
nSTriadFrustrationDefectBoundaryGapCountIs5 =
  refl

record NSTriadFrustrationDefectBoundaryORCSLPGF : Set where
  constructor nSTriadFrustrationDefectBoundaryORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "Object: the triad frustration defect carrier F_N(psi) = inf_phi ||B phi - psi||^2"
    R : String
    RIsCanonical : R ≡
      "Requirement: candidate-only, fail-closed boundary data with no NS regularity or Sacasa bridge claim"
    C : String
    CIsCanonical : C ≡
      "Carrier rows, gap rows, and canonical refl witnesses are exported without external proof imports"
    S : String
    SIsCanonical : S ≡
      "State: the low-frustration ensemble and the frustration defect are recorded as diagnostics only"
    L : String
    LIsCanonical : L ≡
      "Lattice: B operator carrier -> phase-frustration defect carrier -> blocked NS regularity and Sacasa bridge claims"
    P : String
    PIsCanonical : P ≡
      "Proposal: use the defect carrier as a target surface, not as a proof of a Navier-Stokes theorem"
    G : String
    GIsCanonical : G ≡
      "Governance: theorem, full-NS, and Clay promotion remain false"
    F : String
    FIsCanonical : F ≡
      "Gap: no low-frustration or defect implication proves NS regularity or a Sacasa bridge"

open NSTriadFrustrationDefectBoundaryORCSLPGF public

canonicalNSTriadFrustrationDefectBoundaryORCSLPGF :
  NSTriadFrustrationDefectBoundaryORCSLPGF
canonicalNSTriadFrustrationDefectBoundaryORCSLPGF =
  nSTriadFrustrationDefectBoundaryORCSLPGF
    "Object: the triad frustration defect carrier F_N(psi) = inf_phi ||B phi - psi||^2"
    refl
    "Requirement: candidate-only, fail-closed boundary data with no NS regularity or Sacasa bridge claim"
    refl
    "Carrier rows, gap rows, and canonical refl witnesses are exported without external proof imports"
    refl
    "State: the low-frustration ensemble and the frustration defect are recorded as diagnostics only"
    refl
    "Lattice: B operator carrier -> phase-frustration defect carrier -> blocked NS regularity and Sacasa bridge claims"
    refl
    "Proposal: use the defect carrier as a target surface, not as a proof of a Navier-Stokes theorem"
    refl
    "Governance: theorem, full-NS, and Clay promotion remain false"
    refl
    "Gap: no low-frustration or defect implication proves NS regularity or a Sacasa bridge"
    refl

record NSTriadFrustrationDefectBoundary : Set where
  constructor nSTriadFrustrationDefectBoundary
  field
    carrierFormula : String
    carrierFormulaIsCanonical :
      carrierFormula ≡ "F_N(psi) = inf_phi ||B phi - psi||^2"
    candidateOnly : Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true
    failClosed : Bool
    failClosedIsTrue :
      failClosed ≡ true
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
    orcslpgf : NSTriadFrustrationDefectBoundaryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadFrustrationDefectBoundaryORCSLPGF
    rows : List NSTriadFrustrationDefectBoundaryRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadFrustrationDefectBoundaryRows
    rowCount : Nat
    rowCountIs5 :
      rowCount ≡ 5
    gaps : List NSTriadFrustrationDefectBoundaryGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadFrustrationDefectBoundaryGaps
    gapCount : Nat
    gapCountIs5 :
      gapCount ≡ 5
    statement : String
    statementIsCanonical :
      statement ≡
      "Candidate-only triad frustration defect boundary: the low-frustration ensemble and the defect carrier are recorded, but neither proves NS regularity or a Sacasa bridge; theorem/full-NS/Clay flags stay false."

open NSTriadFrustrationDefectBoundary public

canonicalNSTriadFrustrationDefectBoundary :
  NSTriadFrustrationDefectBoundary
canonicalNSTriadFrustrationDefectBoundary =
  nSTriadFrustrationDefectBoundary
    "F_N(psi) = inf_phi ||B phi - psi||^2"
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
    canonicalNSTriadFrustrationDefectBoundaryORCSLPGF
    refl
    canonicalNSTriadFrustrationDefectBoundaryRows
    refl
    nSTriadFrustrationDefectBoundaryRowCount
    refl
    canonicalNSTriadFrustrationDefectBoundaryGaps
    refl
    nSTriadFrustrationDefectBoundaryGapCount
    refl
    "Candidate-only triad frustration defect boundary: the low-frustration ensemble and the defect carrier are recorded, but neither proves NS regularity or a Sacasa bridge; theorem/full-NS/Clay flags stay false."
    refl

candidateOnlyFrustrationBoundary :
  candidateOnly canonicalNSTriadFrustrationDefectBoundary ≡ true
candidateOnlyFrustrationBoundary =
  refl

failClosedFrustrationBoundary :
  failClosed canonicalNSTriadFrustrationDefectBoundary ≡ true
failClosedFrustrationBoundary =
  refl
