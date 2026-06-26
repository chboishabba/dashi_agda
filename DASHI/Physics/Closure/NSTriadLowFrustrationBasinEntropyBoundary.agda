module DASHI.Physics.Closure.NSTriadLowFrustrationBasinEntropyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed NS triad low-frustration basin / entropy boundary.
--
-- This receipt records the wall for the finite-dimensional low-frustration
-- basin
--
--   L_{N,delta}
--
-- and the entropy-volume obstruction
--
--   I_N(delta) = -log nu_0(L_{N,delta})
--
-- as candidate-only data.  The exponential-small basin theorem is not proved
-- here, and no theorem/full-NS/Clay promotion is made.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSTriadLowFrustrationBasinEntropyBoundaryRow : Set where
  canonicalLowFrustrationBasinCarrierRow :
    NSTriadLowFrustrationBasinEntropyBoundaryRow
  canonicalEntropyVolumeObstructionRow :
    NSTriadLowFrustrationBasinEntropyBoundaryRow
  canonicalExponentialSmallBasinTheoremOpenRow :
    NSTriadLowFrustrationBasinEntropyBoundaryRow
  canonicalCandidateOnlyWallRow :
    NSTriadLowFrustrationBasinEntropyBoundaryRow
  canonicalFailClosedPromotionRow :
    NSTriadLowFrustrationBasinEntropyBoundaryRow

canonicalNSTriadLowFrustrationBasinEntropyBoundaryRows :
  List NSTriadLowFrustrationBasinEntropyBoundaryRow
canonicalNSTriadLowFrustrationBasinEntropyBoundaryRows =
  canonicalLowFrustrationBasinCarrierRow
  ∷ canonicalEntropyVolumeObstructionRow
  ∷ canonicalExponentialSmallBasinTheoremOpenRow
  ∷ canonicalCandidateOnlyWallRow
  ∷ canonicalFailClosedPromotionRow
  ∷ []

nSTriadLowFrustrationBasinEntropyBoundaryRowCount : Nat
nSTriadLowFrustrationBasinEntropyBoundaryRowCount =
  listLength canonicalNSTriadLowFrustrationBasinEntropyBoundaryRows

nSTriadLowFrustrationBasinEntropyBoundaryRowCountIs5 :
  nSTriadLowFrustrationBasinEntropyBoundaryRowCount ≡ 5
nSTriadLowFrustrationBasinEntropyBoundaryRowCountIs5 =
  refl

data NSTriadLowFrustrationBasinEntropyBoundaryGap : Set where
  noLowFrustrationBasinProofOfNSRegularity :
    NSTriadLowFrustrationBasinEntropyBoundaryGap
  noEntropyVolumeObstructionProofOfNSRegularity :
    NSTriadLowFrustrationBasinEntropyBoundaryGap
  noExponentialSmallBasinTheorem :
    NSTriadLowFrustrationBasinEntropyBoundaryGap
  noLowFrustrationBasinToClayPromotion :
    NSTriadLowFrustrationBasinEntropyBoundaryGap
  noTheoremFullNSOrClayPromotion :
    NSTriadLowFrustrationBasinEntropyBoundaryGap

canonicalNSTriadLowFrustrationBasinEntropyBoundaryGaps :
  List NSTriadLowFrustrationBasinEntropyBoundaryGap
canonicalNSTriadLowFrustrationBasinEntropyBoundaryGaps =
  noLowFrustrationBasinProofOfNSRegularity
  ∷ noEntropyVolumeObstructionProofOfNSRegularity
  ∷ noExponentialSmallBasinTheorem
  ∷ noLowFrustrationBasinToClayPromotion
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSTriadLowFrustrationBasinEntropyBoundaryGapCount : Nat
nSTriadLowFrustrationBasinEntropyBoundaryGapCount =
  listLength canonicalNSTriadLowFrustrationBasinEntropyBoundaryGaps

nSTriadLowFrustrationBasinEntropyBoundaryGapCountIs5 :
  nSTriadLowFrustrationBasinEntropyBoundaryGapCount ≡ 5
nSTriadLowFrustrationBasinEntropyBoundaryGapCountIs5 =
  refl

record NSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF : Set where
  constructor nSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "Object: the low-frustration basin L_{N,delta} and entropy-volume obstruction I_N(delta) = -log nu_0(L_{N,delta})"
    R : String
    RIsCanonical : R ≡
      "Requirement: record the wall as candidate-only data, with the exponential-small basin theorem still open"
    C : String
    CIsCanonical : C ≡
      "Carrier: canonical rows, gaps, and refl witnesses are exported without extra proof imports"
    S : String
    SIsCanonical : S ≡
      "State: the low-frustration basin and entropy barrier are diagnostic surfaces, not a proof of NS regularity"
    L : String
    LIsCanonical : L ≡
      "Lattice: L_{N,delta} -> I_N(delta) -> open entropy barrier -> blocked theorem/full-NS/Clay promotion"
    P : String
    PIsCanonical : P ≡
      "Proposal: keep the basin and entropy obstruction as a fail-closed receipt, not as a promoted theorem"
    G : String
    GIsCanonical : G ≡
      "Governance: theorem, full-NS, and Clay promotion remain false"
    F : String
    FIsCanonical : F ≡
      "Gap: the analytic proof that L_{N,delta} is exponentially small is missing"

open NSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF public

canonicalNSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF :
  NSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF
canonicalNSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF =
  nSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF
    "Object: the low-frustration basin L_{N,delta} and entropy-volume obstruction I_N(delta) = -log nu_0(L_{N,delta})"
    refl
    "Requirement: record the wall as candidate-only data, with the exponential-small basin theorem still open"
    refl
    "Carrier: canonical rows, gaps, and refl witnesses are exported without extra proof imports"
    refl
    "State: the low-frustration basin and entropy barrier are diagnostic surfaces, not a proof of NS regularity"
    refl
    "Lattice: L_{N,delta} -> I_N(delta) -> open entropy barrier -> blocked theorem/full-NS/Clay promotion"
    refl
    "Proposal: keep the basin and entropy obstruction as a fail-closed receipt, not as a promoted theorem"
    refl
    "Governance: theorem, full-NS, and Clay promotion remain false"
    refl
    "Gap: the analytic proof that L_{N,delta} is exponentially small is missing"
    refl

data NSTriadLowFrustrationBasinEntropyBoundaryPromotion : Set where

record NSTriadLowFrustrationBasinEntropyBoundary : Set where
  constructor nSTriadLowFrustrationBasinEntropyBoundary
  field
    lowFrustrationBasinFormula : String
    lowFrustrationBasinFormulaIsCanonical :
      lowFrustrationBasinFormula ≡ "L_{N,delta}"
    entropyVolumeObstructionFormula : String
    entropyVolumeObstructionFormulaIsCanonical :
      entropyVolumeObstructionFormula ≡
      "I_N(delta) = -log nu_0(L_{N,delta})"
    candidateOnly : Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true
    failClosed : Bool
    failClosedIsTrue :
      failClosed ≡ true
    exponentialSmallBasinTheoremProved : Bool
    exponentialSmallBasinTheoremProvedIsFalse :
      exponentialSmallBasinTheoremProved ≡ false
    lowFrustrationBasinProvesNSRegularity : Bool
    lowFrustrationBasinProvesNSRegularityIsFalse :
      lowFrustrationBasinProvesNSRegularity ≡ false
    entropyVolumeObstructionProvesNSRegularity : Bool
    entropyVolumeObstructionProvesNSRegularityIsFalse :
      entropyVolumeObstructionProvesNSRegularity ≡ false
    lowFrustrationBasinProvesClay : Bool
    lowFrustrationBasinProvesClayIsFalse :
      lowFrustrationBasinProvesClay ≡ false
    entropyVolumeObstructionProvesClay : Bool
    entropyVolumeObstructionProvesClayIsFalse :
      entropyVolumeObstructionProvesClay ≡ false
    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false
    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false
    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    orcslpgf : NSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF
    rows : List NSTriadLowFrustrationBasinEntropyBoundaryRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadLowFrustrationBasinEntropyBoundaryRows
    rowCount : Nat
    rowCountIs5 :
      rowCount ≡ 5
    gaps : List NSTriadLowFrustrationBasinEntropyBoundaryGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadLowFrustrationBasinEntropyBoundaryGaps
    gapCount : Nat
    gapCountIs5 :
      gapCount ≡ 5
    statement : String
    statementIsCanonical :
      statement ≡
      "Candidate-only low-frustration basin receipt: L_{N,delta} and I_N(delta) = -log nu_0(L_{N,delta}) are recorded as a fail-closed entropy barrier wall, but the exponential-small basin theorem is not proved and theorem/full-NS/Clay flags stay false."

open NSTriadLowFrustrationBasinEntropyBoundary public

canonicalNSTriadLowFrustrationBasinEntropyBoundary :
  NSTriadLowFrustrationBasinEntropyBoundary
canonicalNSTriadLowFrustrationBasinEntropyBoundary =
  nSTriadLowFrustrationBasinEntropyBoundary
    "L_{N,delta}"
    refl
    "I_N(delta) = -log nu_0(L_{N,delta})"
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
    false
    refl
    canonicalNSTriadLowFrustrationBasinEntropyBoundaryORCSLPGF
    refl
    canonicalNSTriadLowFrustrationBasinEntropyBoundaryRows
    refl
    5
    refl
    canonicalNSTriadLowFrustrationBasinEntropyBoundaryGaps
    refl
    5
    refl
    "Candidate-only low-frustration basin receipt: L_{N,delta} and I_N(delta) = -log nu_0(L_{N,delta}) are recorded as a fail-closed entropy barrier wall, but the exponential-small basin theorem is not proved and theorem/full-NS/Clay flags stay false."
    refl
