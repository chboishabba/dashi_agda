module DASHI.Physics.Closure.NSSchurComplementFrameGapBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed NS Wall 1 Schur-complement frame-gap boundary.
--
-- This receipt records the sharpened Wall 1b target:
--
--   S_N = (I - K11) - K10 (I - K00)^-1 K01
--
-- together with the diagonal shell-gap and cross-shell coupling roles.
-- It keeps the non-adversarial K01 / Schur bridge explicit and unproved, and
-- leaves theorem/full-NS/Clay promotion false.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSSchurComplementFrameGapRow : Set where
  schurTargetRecorded :
    NSSchurComplementFrameGapRow
  k00DiagonalGapRecorded :
    NSSchurComplementFrameGapRow
  k11DiagonalGapRecorded :
    NSSchurComplementFrameGapRow
  k01CrossShellCouplingRecorded :
    NSSchurComplementFrameGapRow
  nonAdversarialCrossShellBridgeRecorded :
    NSSchurComplementFrameGapRow
  frameGapTargetRecorded :
    NSSchurComplementFrameGapRow
  failClosedPromotionWallRecorded :
    NSSchurComplementFrameGapRow

canonicalNSSchurComplementFrameGapRows :
  List NSSchurComplementFrameGapRow
canonicalNSSchurComplementFrameGapRows =
  schurTargetRecorded
  ∷ k00DiagonalGapRecorded
  ∷ k11DiagonalGapRecorded
  ∷ k01CrossShellCouplingRecorded
  ∷ nonAdversarialCrossShellBridgeRecorded
  ∷ frameGapTargetRecorded
  ∷ failClosedPromotionWallRecorded
  ∷ []

nsschurComplementFrameGapRowCount : Nat
nsschurComplementFrameGapRowCount =
  listLength canonicalNSSchurComplementFrameGapRows

nsschurComplementFrameGapRowCountIs7 :
  nsschurComplementFrameGapRowCount ≡ 7
nsschurComplementFrameGapRowCountIs7 = refl

data NSSchurComplementFrameGapGap : Set where
  diagonalShellGapsOnlyNumerical :
    NSSchurComplementFrameGapGap
  crossShellCouplingOnlyNumerical :
    NSSchurComplementFrameGapGap
  naiveNormBoundInsufficient :
    NSSchurComplementFrameGapGap
  nonAdversarialCrossShellBridgeUnproved :
    NSSchurComplementFrameGapGap
  uniformSchurGapStillOpen :
    NSSchurComplementFrameGapGap
  theoremAndClayPromotionRemainFalse :
    NSSchurComplementFrameGapGap

canonicalNSSchurComplementFrameGapGaps :
  List NSSchurComplementFrameGapGap
canonicalNSSchurComplementFrameGapGaps =
  diagonalShellGapsOnlyNumerical
  ∷ crossShellCouplingOnlyNumerical
  ∷ naiveNormBoundInsufficient
  ∷ nonAdversarialCrossShellBridgeUnproved
  ∷ uniformSchurGapStillOpen
  ∷ theoremAndClayPromotionRemainFalse
  ∷ []

nsschurComplementFrameGapGapCount : Nat
nsschurComplementFrameGapGapCount =
  listLength canonicalNSSchurComplementFrameGapGaps

nsschurComplementFrameGapGapCountIs6 :
  nsschurComplementFrameGapGapCount ≡ 6
nsschurComplementFrameGapGapCountIs6 = refl

canonicalSchurTargetText : String
canonicalSchurTargetText =
  "Schur target: S_N = (I - K11) - K10 (I - K00)^-1 K01"

canonicalOText : String
canonicalOText =
  "O: record the sharpened Wall 1b Schur-complement frame-gap target on the active NS shell carrier."

canonicalRText : String
canonicalRText =
  "R: keep the Schur target, diagonal shell gaps, and cross-shell coupling bridge explicit without promoting them."

canonicalCText : String
canonicalCText =
  "C: expose canonical rows, gaps, the exact Schur-target string, and explicit false promotion gates."

canonicalSText : String
canonicalSText =
  "S: diagonal shell gaps and Schur telemetry exist numerically, but the non-adversarial K01 bridge is still unproved."

canonicalLText : String
canonicalLText =
  "L: diagonal shell gaps -> cross-shell coupling audit -> Schur-complement positivity target -> frame gap -> only then Wall 1 stability."

canonicalPText : String
canonicalPText =
  "P: treat the Schur-complement target as the live Wall 1b theorem boundary and promote nothing until the K01 bridge is proved."

canonicalGText : String
canonicalGText =
  "G: theorem, full-NS, and Clay promotion remain false."

canonicalFText : String
canonicalFText =
  "F: the missing evidence is a non-adversarial cross-shell coupling bound strong enough to keep the Schur complement positive uniformly."

record NSSchurComplementFrameGapORCSLPGF : Set where
  constructor mkNSSchurComplementFrameGapORCSLPGF
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

open NSSchurComplementFrameGapORCSLPGF public

canonicalNSSchurComplementFrameGapORCSLPGF :
  NSSchurComplementFrameGapORCSLPGF
canonicalNSSchurComplementFrameGapORCSLPGF =
  mkNSSchurComplementFrameGapORCSLPGF
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

record NSSchurComplementFrameGapBoundary : Setω where
  constructor mkNSSchurComplementFrameGapBoundary
  field
    rows :
      List NSSchurComplementFrameGapRow
    rowsAreCanonical :
      rows ≡ canonicalNSSchurComplementFrameGapRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nsschurComplementFrameGapRowCount

    gaps :
      List NSSchurComplementFrameGapGap
    gapsAreCanonical :
      gaps ≡ canonicalNSSchurComplementFrameGapGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nsschurComplementFrameGapGapCount

    schurTarget :
      String
    schurTargetIsCanonical :
      schurTarget ≡ canonicalSchurTargetText

    diagonalShellGapsProved :
      Bool
    diagonalShellGapsProvedIsFalse :
      diagonalShellGapsProved ≡ false

    crossShellCouplingBridgeProved :
      Bool
    crossShellCouplingBridgeProvedIsFalse :
      crossShellCouplingBridgeProved ≡ false

    schurComplementGapProved :
      Bool
    schurComplementGapProvedIsFalse :
      schurComplementGapProved ≡ false

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

    orcslpgf :
      NSSchurComplementFrameGapORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSSchurComplementFrameGapORCSLPGF

    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only Schur-complement frame-gap boundary: the target S_N = (I - K11) - K10 (I - K00)^-1 K01 is recorded, but the non-adversarial cross-shell bridge and the uniform frame gap remain unproved."

open NSSchurComplementFrameGapBoundary public

canonicalNSSchurComplementFrameGapBoundary :
  NSSchurComplementFrameGapBoundary
canonicalNSSchurComplementFrameGapBoundary =
  mkNSSchurComplementFrameGapBoundary
    canonicalNSSchurComplementFrameGapRows
    refl
    nsschurComplementFrameGapRowCount
    refl
    canonicalNSSchurComplementFrameGapGaps
    refl
    nsschurComplementFrameGapGapCount
    refl
    canonicalSchurTargetText
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
    canonicalNSSchurComplementFrameGapORCSLPGF
    refl
    "Candidate-only Schur-complement frame-gap boundary: the target S_N = (I - K11) - K10 (I - K00)^-1 K01 is recorded, but the non-adversarial cross-shell bridge and the uniform frame gap remain unproved."
    refl
