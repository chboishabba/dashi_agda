module DASHI.Physics.Closure.NSHardTheoremKornCollapseWallPostCalc11Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only receipt for the two remaining hard analytic walls after
-- Calc 11.
--
-- Canonical hard walls: KornLevelSet and collapseImpossible only.
-- BoundaryHB_Correct is closeable from pointwise kornBiaxialBound /
-- nondegeneracy and is not counted as a hard wall.
--
-- Calc 12 stays an optional, non-blocking statistical route selector for
-- |<omega,e2>|^2 ~ C*g12^beta: beta > 1 points toward delta = beta - 1,
-- beta < 1 marks a blowup-precursor candidate, and a CI straddling 1 is
-- inconclusive.
--
-- KornLevelSet still needs h_sd / h_omega_ctrl from NS, with
-- alpha_s empirically near 0.5 but unproved.
-- collapseImpossible still needs control of |<omega,e2>|^2 versus g12,
-- especially the estimate |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0,
-- with F123 = O(g12^delta) as the consequence if proved.
-- Calc 11 no_special_alignment is recorded as empirical only and
-- non-promoting.

data NSHardTheoremKornCollapseWallPostCalc11Status : Set where
  candidateOnlyFailClosed :
    NSHardTheoremKornCollapseWallPostCalc11Status

data NSHardTheoremKornCollapseWallPostCalc11Gate : Set where
  noKornLevelSetProof :
    NSHardTheoremKornCollapseWallPostCalc11Gate
  noCollapseImpossibleProof :
    NSHardTheoremKornCollapseWallPostCalc11Gate
  alphaSEmpiricalOnly :
    NSHardTheoremKornCollapseWallPostCalc11Gate
  calc11NoSpecialAlignmentOnly :
    NSHardTheoremKornCollapseWallPostCalc11Gate
  noClayPromotion :
    NSHardTheoremKornCollapseWallPostCalc11Gate

canonicalNSHardTheoremKornCollapseWallPostCalc11Gates :
  List NSHardTheoremKornCollapseWallPostCalc11Gate
canonicalNSHardTheoremKornCollapseWallPostCalc11Gates =
  noKornLevelSetProof
  ∷ noCollapseImpossibleProof
  ∷ alphaSEmpiricalOnly
  ∷ calc11NoSpecialAlignmentOnly
  ∷ noClayPromotion
  ∷ []

record NSHardTheoremKornCollapseWallPostCalc11ORCSLPGF : Set where
  constructor mkNSHardTheoremKornCollapseWallPostCalc11ORCSLPGF
  field
    O :
      String
    OIsCanonical :
      O ≡
      "Post-Calc-11 worker lane 2 owns the KornLevelSet and collapseImpossible wall receipt only; BoundaryHB_Correct is closeable and not a hard wall."

    R :
      String
    RIsCanonical :
      R ≡
      "Record the exact wall variables, the empirical Calc 11 signal, and keep every promotion flag false."

    C :
      String
    CIsCanonical :
      C ≡
      "This is a local receipt surface only; it does not discharge the analytic walls."

    S :
      String
    SIsCanonical :
      S ≡
      "KornLevelSet needs h_sd and h_omega_ctrl from NS with alpha_s ~ 0.5 empirical-only; collapseImpossible needs |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0, with F123 = O(g12^delta) if proved. BoundaryHB_Correct closes from pointwise kornBiaxialBound / nondegeneracy and is not a hard wall."

    L :
      String
    LIsCanonical :
      L ≡
      "h_sd -> h_omega_ctrl -> alpha_s; omega -> e2 -> g12 -> F123 -> no_special_alignment; BoundaryHB_Correct -> pointwise kornBiaxialBound / nondegeneracy."

    P :
      String
    PIsCanonical :
      P ≡
      "Track KornLevelSet and collapseImpossible as the only hard walls, keep BoundaryHB_Correct closeable, keep Calc 12 optional and non-blocking, and keep promotion false."

    G :
      String
    GIsCanonical :
      G ≡
      "Fail closed on KornLevelSet, collapseImpossible, theorem_authority, Clay, and terminal promotion; do not count BoundaryHB_Correct as a hard wall."

    F :
      String
    FIsCanonical :
      F ≡
      "Missing analytic proof of KornLevelSet and of |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0, with F123 = O(g12^delta) still unproved; BoundaryHB_Correct is only a closeable boundary case."

open NSHardTheoremKornCollapseWallPostCalc11ORCSLPGF public

kornLevelSetExactVariablesText : List String
kornLevelSetExactVariablesText =
  "h_sd"
  ∷ "h_omega_ctrl"
  ∷ "alpha_s"
  ∷ []

kornLevelSetWallTextValue : String
kornLevelSetWallTextValue =
      "KornLevelSet needs h_sd and h_omega_ctrl from NS; alpha_s is empirically ~0.5 and remains empirical-only."

collapseImpossibleExactVariablesText : List String
collapseImpossibleExactVariablesText =
  "u"
  ∷ "T*"
  ∷ "∂Ω_K"
  ∷ "component C"
  ∷ "g12"
  ∷ "e2"
  ∷ "omega = curl u"
  ∷ "F123"
  ∷ "C"
  ∷ "delta"
  ∷ "no_special_alignment"
  ∷ []

collapseImpossibleWallTextValue : String
collapseImpossibleWallTextValue =
      "collapseImpossible needs control of |<omega,e2>|^2 versus g12, especially |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0, with F123 = O(g12^delta) if proved; Calc 11 no_special_alignment is empirical only and non-promoting."

combinedWallOrderText : List String
combinedWallOrderText =
  "KornLevelSet"
  ∷ "collapseImpossible"
  ∷ []

candidateOnlyReceiptStatementValue : String
candidateOnlyReceiptStatementValue =
      "Candidate-only post-Calc-11 receipt for the two hard walls KornLevelSet and collapseImpossible: the first wall still needs h_sd / h_omega_ctrl and only has empirical alpha_s ~ 0.5 support, while the second wall still needs |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0, with F123 = O(g12^delta) if proved. Calc 12 remains an optional non-blocking route selector: beta > 1 suggests delta = beta - 1, beta < 1 marks a blowup-precursor candidate, and a CI straddling 1 is inconclusive. BoundaryHB_Correct is closeable and not counted as a hard wall."

canonicalNSHardTheoremKornCollapseWallPostCalc11ORCSLPGF :
  NSHardTheoremKornCollapseWallPostCalc11ORCSLPGF
canonicalNSHardTheoremKornCollapseWallPostCalc11ORCSLPGF =
  mkNSHardTheoremKornCollapseWallPostCalc11ORCSLPGF
    "Post-Calc-11 worker lane 2 owns the KornLevelSet and collapseImpossible wall receipt only; BoundaryHB_Correct is closeable and not a hard wall."
    refl
    "Record the exact wall variables, the empirical Calc 11 signal, and keep every promotion flag false."
    refl
    "This is a local receipt surface only; it does not discharge the analytic walls."
    refl
    "KornLevelSet needs h_sd and h_omega_ctrl from NS with alpha_s ~ 0.5 empirical-only; collapseImpossible needs |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0, with F123 = O(g12^delta) if proved. BoundaryHB_Correct closes from pointwise kornBiaxialBound / nondegeneracy and is not a hard wall."
    refl
    "h_sd -> h_omega_ctrl -> alpha_s; omega -> e2 -> g12 -> F123 -> no_special_alignment; BoundaryHB_Correct -> pointwise kornBiaxialBound / nondegeneracy."
    refl
    "Track KornLevelSet and collapseImpossible as the only hard walls, keep BoundaryHB_Correct closeable, keep Calc 12 optional and non-blocking, and keep promotion false."
    refl
    "Fail closed on KornLevelSet, collapseImpossible, theorem_authority, Clay, and terminal promotion; do not count BoundaryHB_Correct as a hard wall."
    refl
    "Missing analytic proof of KornLevelSet and of |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0, with F123 = O(g12^delta) still unproved; BoundaryHB_Correct is only a closeable boundary case."
    refl

record NSHardTheoremKornCollapseWallPostCalc11Receipt : Setω where
  field
    status :
      NSHardTheoremKornCollapseWallPostCalc11Status

    statusIsCanonical :
      status ≡ candidateOnlyFailClosed

    kornLevelSetExactVariables :
      List String

    kornLevelSetExactVariablesAreCanonical :
      kornLevelSetExactVariables ≡ kornLevelSetExactVariablesText

    kornLevelSetWallText :
      String

    kornLevelSetWallTextIsCanonical :
      kornLevelSetWallText ≡ kornLevelSetWallTextValue

    collapseImpossibleExactVariables :
      List String

    collapseImpossibleExactVariablesAreCanonical :
      collapseImpossibleExactVariables ≡ collapseImpossibleExactVariablesText

    collapseImpossibleWallText :
      String

    collapseImpossibleWallTextIsCanonical :
      collapseImpossibleWallText ≡ collapseImpossibleWallTextValue

    combinedWallOrder :
      List String

    combinedWallOrderIsCanonical :
      combinedWallOrder ≡ combinedWallOrderText

    candidateOnlyReceiptStatement :
      String

    candidateOnlyReceiptStatementIsCanonical :
      candidateOnlyReceiptStatement ≡ candidateOnlyReceiptStatementValue

    promotion :
      Bool

    promotionIsFalse :
      promotion ≡ false

    kornLevelSetPromoted :
      Bool

    kornLevelSetPromotedIsFalse :
      kornLevelSetPromoted ≡ false

    collapseImpossiblePromoted :
      Bool

    collapseImpossiblePromotedIsFalse :
      collapseImpossiblePromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    gates :
      List NSHardTheoremKornCollapseWallPostCalc11Gate

    gatesAreCanonical :
      gates ≡ canonicalNSHardTheoremKornCollapseWallPostCalc11Gates

    orcslpgf :
      NSHardTheoremKornCollapseWallPostCalc11ORCSLPGF

    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSHardTheoremKornCollapseWallPostCalc11ORCSLPGF

    receiptBoundary :
      List String

open NSHardTheoremKornCollapseWallPostCalc11Receipt public

canonicalNSHardTheoremKornCollapseWallPostCalc11Receipt :
  NSHardTheoremKornCollapseWallPostCalc11Receipt
canonicalNSHardTheoremKornCollapseWallPostCalc11Receipt =
  record
    { status =
        candidateOnlyFailClosed
    ; statusIsCanonical =
        refl
    ; kornLevelSetExactVariables =
        kornLevelSetExactVariablesText
    ; kornLevelSetExactVariablesAreCanonical =
        refl
    ; kornLevelSetWallText =
        kornLevelSetWallTextValue
    ; kornLevelSetWallTextIsCanonical =
        refl
    ; collapseImpossibleExactVariables =
        collapseImpossibleExactVariablesText
    ; collapseImpossibleExactVariablesAreCanonical =
        refl
    ; collapseImpossibleWallText =
        collapseImpossibleWallTextValue
    ; collapseImpossibleWallTextIsCanonical =
        refl
    ; combinedWallOrder =
        combinedWallOrderText
    ; combinedWallOrderIsCanonical =
        refl
    ; candidateOnlyReceiptStatement =
        candidateOnlyReceiptStatementValue
    ; candidateOnlyReceiptStatementIsCanonical =
        refl
    ; promotion =
        false
    ; promotionIsFalse =
        refl
    ; kornLevelSetPromoted =
        false
    ; kornLevelSetPromotedIsFalse =
        refl
    ; collapseImpossiblePromoted =
        false
    ; collapseImpossiblePromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; gates =
        canonicalNSHardTheoremKornCollapseWallPostCalc11Gates
    ; gatesAreCanonical =
        refl
    ; orcslpgf =
        canonicalNSHardTheoremKornCollapseWallPostCalc11ORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; receiptBoundary =
        "Candidate-only post-Calc-11 receipt for the two remaining hard analytic walls"
        ∷ "KornLevelSet keeps h_sd and h_omega_ctrl explicit"
        ∷ "alpha_s is empirical near 0.5 and stays empirical-only"
        ∷ "collapseImpossible keeps |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0, explicit"
        ∷ "Calc 11 no_special_alignment remains empirical only and non-promoting"
        ∷ "Calc 12 is an optional non-blocking route selector: beta > 1 -> delta = beta - 1; beta < 1 -> blowup precursor candidate; CI straddling 1 -> inconclusive"
        ∷ "BoundaryHB_Correct closes from pointwise kornBiaxialBound / nondegeneracy and is not a hard wall"
        ∷ "KornLevelSet, collapseImpossible, theorem_authority, Clay, and terminal promotion remain false"
        ∷ []
    }

nsHardTheoremKornCollapseWallPostCalc11Promoted :
  promotion canonicalNSHardTheoremKornCollapseWallPostCalc11Receipt ≡ false
nsHardTheoremKornCollapseWallPostCalc11Promoted =
  refl
