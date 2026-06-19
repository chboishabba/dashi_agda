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
-- KornLevelSet still needs h_strain_dom / h_omega_ctrl from NS, with
-- alpha_s empirically near 0.5 but unproved.
-- collapseImpossible still needs control of |<omega,e2>|^2 versus g12,
-- especially the estimate |<omega,e2>|^2 <= C*g12^(1+delta), while the
-- F123/g12 term remains dangerous.
-- Calc 11 no_special_alignment is recorded as empirical only.

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
      "Post-Calc-11 worker lane 4 owns the KornLevelSet and collapseImpossible wall receipt only."

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
      "KornLevelSet needs h_strain_dom and h_omega_ctrl from NS with alpha_s ~ 0.5 unproved; collapseImpossible needs |<omega,e2>|^2 control versus g12."

    L :
      String
    LIsCanonical :
      L ≡
      "h_strain_dom -> h_omega_ctrl -> alpha_s; omega -> e2 -> g12 -> F123 -> no_special_alignment."

    P :
      String
    PIsCanonical :
      P ≡
      "Track both walls as candidate-only and keep promotion false."

    G :
      String
    GIsCanonical :
      G ≡
      "Fail closed on KornLevelSet, collapseImpossible, Clay, and terminal promotion."

    F :
      String
    FIsCanonical :
      F ≡
      "Missing analytic proof of KornLevelSet and of |<omega,e2>|^2 <= C*g12^(1+delta), with F123/g12 still dangerous."

open NSHardTheoremKornCollapseWallPostCalc11ORCSLPGF public

kornLevelSetExactVariablesText : List String
kornLevelSetExactVariablesText =
  "h_strain_dom"
  ∷ "h_omega_ctrl"
  ∷ "alpha_s"
  ∷ []

kornLevelSetWallTextValue : String
kornLevelSetWallTextValue =
  "KornLevelSet needs h_strain_dom and h_omega_ctrl from NS; alpha_s is empirically ~0.5 but remains unproved."

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
  "collapseImpossible needs control of |<omega,e2>|^2 versus g12, especially |<omega,e2>|^2 <= C*g12^(1+delta); the F123/g12 term remains dangerous, and Calc 11 no_special_alignment is empirical only."

combinedWallOrderText : List String
combinedWallOrderText =
  "KornLevelSet"
  ∷ "collapseImpossible"
  ∷ []

candidateOnlyReceiptStatementValue : String
candidateOnlyReceiptStatementValue =
  "Candidate-only post-Calc-11 receipt for KornLevelSet and collapseImpossible: the first wall still needs h_strain_dom / h_omega_ctrl and only has empirical alpha_s ~ 0.5 support, while the second wall still needs |<omega,e2>|^2 control against g12 and keeps the F123/g12 hazard open."

canonicalNSHardTheoremKornCollapseWallPostCalc11ORCSLPGF :
  NSHardTheoremKornCollapseWallPostCalc11ORCSLPGF
canonicalNSHardTheoremKornCollapseWallPostCalc11ORCSLPGF =
  mkNSHardTheoremKornCollapseWallPostCalc11ORCSLPGF
    "Post-Calc-11 worker lane 4 owns the KornLevelSet and collapseImpossible wall receipt only."
    refl
    "Record the exact wall variables, the empirical Calc 11 signal, and keep every promotion flag false."
    refl
    "This is a local receipt surface only; it does not discharge the analytic walls."
    refl
    "KornLevelSet needs h_strain_dom and h_omega_ctrl from NS with alpha_s ~ 0.5 unproved; collapseImpossible needs |<omega,e2>|^2 control versus g12."
    refl
    "h_strain_dom -> h_omega_ctrl -> alpha_s; omega -> e2 -> g12 -> F123 -> no_special_alignment."
    refl
    "Track both walls as candidate-only and keep promotion false."
    refl
    "Fail closed on KornLevelSet, collapseImpossible, Clay, and terminal promotion."
    refl
    "Missing analytic proof of KornLevelSet and of |<omega,e2>|^2 <= C*g12^(1+delta), with F123/g12 still dangerous."
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
        ∷ "KornLevelSet keeps h_strain_dom and h_omega_ctrl explicit"
        ∷ "alpha_s is empirical near 0.5 but unproved"
        ∷ "collapseImpossible keeps |<omega,e2>|^2 versus g12 explicit"
        ∷ "|<omega,e2>|^2 <= C*g12^(1+delta) is the missing estimate"
        ∷ "Calc 11 no_special_alignment remains empirical only"
        ∷ "KornLevelSet, collapseImpossible, Clay, and terminal promotion remain false"
        ∷ []
    }

nsHardTheoremKornCollapseWallPostCalc11Promoted :
  promotion canonicalNSHardTheoremKornCollapseWallPostCalc11Receipt ≡ false
nsHardTheoremKornCollapseWallPostCalc11Promoted =
  refl
