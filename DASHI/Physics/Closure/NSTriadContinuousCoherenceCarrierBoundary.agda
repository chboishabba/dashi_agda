module DASHI.Physics.Closure.NSTriadContinuousCoherenceCarrierBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed Wall 1a continuous coherence carrier boundary.
--
-- This file records the positive Wall 1a route as a candidate-only
-- boundary.  The current signed-XOR carrier is retired as canonical here;
-- the continuous coherence carrier is the positive theorem target, but no
-- theorem, full-NS, or Clay promotion is claimed in this module.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadContinuousCoherenceCarrierBoundaryStatus : Set where
  wall1aContinuousCoherenceCarrierBoundaryRecorded :
    NSTriadContinuousCoherenceCarrierBoundaryStatus

data NSTriadContinuousCoherenceCarrierBoundaryRow : Set where
  positiveWall1aRouteRecorded :
    NSTriadContinuousCoherenceCarrierBoundaryRow
  signedXORCarrierRetiredAsCanonicalRecorded :
    NSTriadContinuousCoherenceCarrierBoundaryRow
  continuousCoherenceCarrierIsPositiveTheoremTargetRecorded :
    NSTriadContinuousCoherenceCarrierBoundaryRow
  theoremFullNSClayPromotionRemainFalseRecorded :
    NSTriadContinuousCoherenceCarrierBoundaryRow
  candidateOnlyFailClosedBoundaryRecorded :
    NSTriadContinuousCoherenceCarrierBoundaryRow

canonicalNSTriadContinuousCoherenceCarrierBoundaryRows :
  List NSTriadContinuousCoherenceCarrierBoundaryRow
canonicalNSTriadContinuousCoherenceCarrierBoundaryRows =
  positiveWall1aRouteRecorded
  ∷ signedXORCarrierRetiredAsCanonicalRecorded
  ∷ continuousCoherenceCarrierIsPositiveTheoremTargetRecorded
  ∷ theoremFullNSClayPromotionRemainFalseRecorded
  ∷ candidateOnlyFailClosedBoundaryRecorded
  ∷ []

nSTriadContinuousCoherenceCarrierBoundaryRowCount : Nat
nSTriadContinuousCoherenceCarrierBoundaryRowCount =
  listLength canonicalNSTriadContinuousCoherenceCarrierBoundaryRows

nSTriadContinuousCoherenceCarrierBoundaryRowCountIs5 :
  nSTriadContinuousCoherenceCarrierBoundaryRowCount ≡ 5
nSTriadContinuousCoherenceCarrierBoundaryRowCountIs5 = refl

data NSTriadContinuousCoherenceCarrierBoundaryGap : Set where
  signedXORCarrierNoLongerCanonical :
    NSTriadContinuousCoherenceCarrierBoundaryGap
  continuousCoherenceTargetStillCandidateOnly :
    NSTriadContinuousCoherenceCarrierBoundaryGap
  theoremPromotionNotYetDischarged :
    NSTriadContinuousCoherenceCarrierBoundaryGap
  fullNSPromotionRemainFalse :
    NSTriadContinuousCoherenceCarrierBoundaryGap
  clayPromotionRemainFalse :
    NSTriadContinuousCoherenceCarrierBoundaryGap

canonicalNSTriadContinuousCoherenceCarrierBoundaryGaps :
  List NSTriadContinuousCoherenceCarrierBoundaryGap
canonicalNSTriadContinuousCoherenceCarrierBoundaryGaps =
  signedXORCarrierNoLongerCanonical
  ∷ continuousCoherenceTargetStillCandidateOnly
  ∷ theoremPromotionNotYetDischarged
  ∷ fullNSPromotionRemainFalse
  ∷ clayPromotionRemainFalse
  ∷ []

nSTriadContinuousCoherenceCarrierBoundaryGapCount : Nat
nSTriadContinuousCoherenceCarrierBoundaryGapCount =
  listLength canonicalNSTriadContinuousCoherenceCarrierBoundaryGaps

nSTriadContinuousCoherenceCarrierBoundaryGapCountIs5 :
  nSTriadContinuousCoherenceCarrierBoundaryGapCount ≡ 5
nSTriadContinuousCoherenceCarrierBoundaryGapCountIs5 = refl

canonicalPositiveTheoremTargetText : String
canonicalPositiveTheoremTargetText =
  "continuous coherence carrier"

canonicalOText : String
canonicalOText =
  "O: record the Wall 1a continuous coherence carrier boundary as a fail-closed candidate-only receipt."

canonicalRText : String
canonicalRText =
  "R: retire the current signed-XOR carrier as canonical and keep the continuous coherence carrier as the positive theorem target."

canonicalCText : String
canonicalCText =
  "C: export canonical rows, gaps, and false-promotion gates with the continuous coherence carrier target in view."

canonicalSText : String
canonicalSText =
  "S: the route is candidate-only; the signed-XOR carrier is no longer canonical; the continuous coherence carrier is the positive theorem target."

canonicalLText : String
canonicalLText =
  "L: positive Wall 1a route -> signed-XOR carrier retired as canonical -> continuous coherence carrier as positive theorem target -> fail-closed boundary."

canonicalPText : String
canonicalPText =
  "P: keep the Wall 1a continuous coherence route candidate-only; do not promote theorem, full-NS, or Clay status."

canonicalGText : String
canonicalGText =
  "G: theorem, full-NS, and Clay promotion remain false."

canonicalFText : String
canonicalFText =
  "F: the missing evidence is a discharged positive Wall 1a theorem for the continuous coherence carrier."

record NSTriadContinuousCoherenceCarrierBoundaryORCSLPGF : Set where
  constructor mkNSTriadContinuousCoherenceCarrierBoundaryORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ canonicalOText
    R : String
    RIsCanonical : R ≡ canonicalRText
    C : String
    CIsCanonical : C ≡ canonicalCText
    S : String
    SIsCanonical : S ≡ canonicalSText
    L : String
    LIsCanonical : L ≡ canonicalLText
    P : String
    PIsCanonical : P ≡ canonicalPText
    G : String
    GIsCanonical : G ≡ canonicalGText
    F : String
    FIsCanonical : F ≡ canonicalFText

open NSTriadContinuousCoherenceCarrierBoundaryORCSLPGF public

canonicalNSTriadContinuousCoherenceCarrierBoundaryORCSLPGF :
  NSTriadContinuousCoherenceCarrierBoundaryORCSLPGF
canonicalNSTriadContinuousCoherenceCarrierBoundaryORCSLPGF =
  mkNSTriadContinuousCoherenceCarrierBoundaryORCSLPGF
    canonicalOText
    refl
    canonicalRText
    refl
    canonicalCText
    refl
    canonicalSText
    refl
    canonicalLText
    refl
    canonicalPText
    refl
    canonicalGText
    refl
    canonicalFText
    refl

data NSTriadContinuousCoherenceCarrierBoundaryPromotion : Set where

promotionImpossibleHere :
  NSTriadContinuousCoherenceCarrierBoundaryPromotion → ⊥
promotionImpossibleHere ()

record NSTriadContinuousCoherenceCarrierBoundary : Setω where
  constructor mkNSTriadContinuousCoherenceCarrierBoundary
  field
    status :
      NSTriadContinuousCoherenceCarrierBoundaryStatus
    statusIsCanonical :
      status ≡ wall1aContinuousCoherenceCarrierBoundaryRecorded

    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadContinuousCoherenceCarrierBoundary"

    targetTheorem :
      String
    targetTheoremIsCanonical :
      targetTheorem ≡ canonicalPositiveTheoremTargetText

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    signedXORCarrierRetiredAsCanonical :
      Bool
    signedXORCarrierRetiredAsCanonicalIsTrue :
      signedXORCarrierRetiredAsCanonical ≡ true

    continuousCoherenceCarrierIsPositiveTheoremTarget :
      Bool
    continuousCoherenceCarrierIsPositiveTheoremTargetIsTrue :
      continuousCoherenceCarrierIsPositiveTheoremTarget ≡ true

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

    promotionWitness :
      NSTriadContinuousCoherenceCarrierBoundaryPromotion → ⊥

    orcslpgf :
      NSTriadContinuousCoherenceCarrierBoundaryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadContinuousCoherenceCarrierBoundaryORCSLPGF

    rows :
      List NSTriadContinuousCoherenceCarrierBoundaryRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadContinuousCoherenceCarrierBoundaryRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nSTriadContinuousCoherenceCarrierBoundaryRowCount

    gaps :
      List NSTriadContinuousCoherenceCarrierBoundaryGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadContinuousCoherenceCarrierBoundaryGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nSTriadContinuousCoherenceCarrierBoundaryGapCount

    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only Wall 1a continuous coherence carrier boundary: the current signed-XOR carrier is retired as canonical, the continuous coherence carrier is the positive theorem target, and theorem/full-NS/Clay promotion stays false."

open NSTriadContinuousCoherenceCarrierBoundary public

canonicalNSTriadContinuousCoherenceCarrierBoundary :
  NSTriadContinuousCoherenceCarrierBoundary
canonicalNSTriadContinuousCoherenceCarrierBoundary =
  mkNSTriadContinuousCoherenceCarrierBoundary
    wall1aContinuousCoherenceCarrierBoundaryRecorded
    refl
    "NSTriadContinuousCoherenceCarrierBoundary"
    refl
    canonicalPositiveTheoremTargetText
    refl
    true
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
    promotionImpossibleHere
    canonicalNSTriadContinuousCoherenceCarrierBoundaryORCSLPGF
    refl
    canonicalNSTriadContinuousCoherenceCarrierBoundaryRows
    refl
    nSTriadContinuousCoherenceCarrierBoundaryRowCount
    refl
    canonicalNSTriadContinuousCoherenceCarrierBoundaryGaps
    refl
    nSTriadContinuousCoherenceCarrierBoundaryGapCount
    refl
    "Candidate-only Wall 1a continuous coherence carrier boundary: the current signed-XOR carrier is retired as canonical, the continuous coherence carrier is the positive theorem target, and theorem/full-NS/Clay promotion stays false."
    refl

------------------------------------------------------------------------
-- Contract witnesses.

targetTheoremProof :
  targetTheorem canonicalNSTriadContinuousCoherenceCarrierBoundary ≡
  canonicalPositiveTheoremTargetText
targetTheoremProof =
  refl

candidateOnlyProof :
  candidateOnly canonicalNSTriadContinuousCoherenceCarrierBoundary ≡ true
candidateOnlyProof =
  refl

failClosedProof :
  failClosed canonicalNSTriadContinuousCoherenceCarrierBoundary ≡ true
failClosedProof =
  refl

signedXORCarrierRetiredAsCanonicalProof :
  signedXORCarrierRetiredAsCanonical canonicalNSTriadContinuousCoherenceCarrierBoundary ≡ true
signedXORCarrierRetiredAsCanonicalProof =
  refl

continuousCoherenceCarrierIsPositiveTheoremTargetProof :
  continuousCoherenceCarrierIsPositiveTheoremTarget canonicalNSTriadContinuousCoherenceCarrierBoundary ≡ true
continuousCoherenceCarrierIsPositiveTheoremTargetProof =
  refl

theoremPromotedProof :
  theoremPromoted canonicalNSTriadContinuousCoherenceCarrierBoundary ≡ false
theoremPromotedProof =
  refl

fullNSPromotedProof :
  fullNSPromoted canonicalNSTriadContinuousCoherenceCarrierBoundary ≡ false
fullNSPromotedProof =
  refl

clayPromotedProof :
  clayPromoted canonicalNSTriadContinuousCoherenceCarrierBoundary ≡ false
clayPromotedProof =
  refl

rowsAreCanonicalProof :
  rows canonicalNSTriadContinuousCoherenceCarrierBoundary ≡
  canonicalNSTriadContinuousCoherenceCarrierBoundaryRows
rowsAreCanonicalProof =
  refl

gapsAreCanonicalProof :
  gaps canonicalNSTriadContinuousCoherenceCarrierBoundary ≡
  canonicalNSTriadContinuousCoherenceCarrierBoundaryGaps
gapsAreCanonicalProof =
  refl
