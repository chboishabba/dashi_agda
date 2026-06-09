module DASHI.Physics.Closure.UltrametricInsightClarificationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Ultrametric insight clarification receipt.
--
-- This C1 receipt records the component split missing from the prior
-- hyperbolic flat-limit receipt: the p-adic boundary is ultrametric as a
-- theorem, while the archimedean boundary is not ultrametric.  The
-- ultrametric insight therefore resolves the p-adic flat-limit issue only;
-- it does not resolve the archimedean flat-limit issue.

data UltrametricClarificationStatus : Set where
  ultrametricInsightClarifiesComponentSplit :
    UltrametricClarificationStatus

data BoundaryComponent : Set where
  pAdicBoundary :
    BoundaryComponent

  archimedeanBoundary :
    BoundaryComponent

canonicalBoundaryComponents :
  List BoundaryComponent
canonicalBoundaryComponents =
  pAdicBoundary
  ∷ archimedeanBoundary
  ∷ []

data BoundaryUltrametricVerdict : Set where
  ultrametricTheorem :
    BoundaryUltrametricVerdict

  notUltrametric :
    BoundaryUltrametricVerdict

data FlatLimitComponent : Set where
  pAdicFlatLimit :
    FlatLimitComponent

  archimedeanFlatLimit :
    FlatLimitComponent

canonicalFlatLimitComponents :
  List FlatLimitComponent
canonicalFlatLimitComponents =
  pAdicFlatLimit
  ∷ archimedeanFlatLimit
  ∷ []

data FlatLimitResolutionVerdict : Set where
  resolvedByUltrametricInsight :
    FlatLimitResolutionVerdict

  notResolvedByUltrametricInsight :
    FlatLimitResolutionVerdict

data PriorReceiptClarification : Set where
  supersedesAndClarifiesHyperbolicFlatLimitReceipt :
    PriorReceiptClarification

pAdicBoundaryUltrametricStatement : String
pAdicBoundaryUltrametricStatement =
  "The p-adic boundary ultrametric is theorem."

archimedeanBoundaryNotUltrametricStatement : String
archimedeanBoundaryNotUltrametricStatement =
  "The archimedean boundary is not ultrametric."

pAdicFlatLimitResolvedStatement : String
pAdicFlatLimitResolvedStatement =
  "The ultrametric insight resolves the p-adic flat limit."

archimedeanFlatLimitNotResolvedStatement : String
archimedeanFlatLimitNotResolvedStatement =
  "The ultrametric insight does not resolve the archimedean flat limit."

priorHyperbolicReceiptClarificationStatement : String
priorHyperbolicReceiptClarificationStatement =
  "This receipt supersedes and clarifies the prior hyperbolic flat limit receipt because it did not distinguish archimedean from p-adic components."

ultrametricInsightClarificationStatement : String
ultrametricInsightClarificationStatement =
  "Ultrametric insight is component-specific: p-adic boundary ultrametric is theorem and resolves the p-adic flat limit; archimedean boundary is not ultrametric and remains unresolved by that insight."

record UltrametricInsightClarificationReceipt : Setω where
  field
    status :
      UltrametricClarificationStatus

    boundaryComponents :
      List BoundaryComponent

    boundaryComponentsAreCanonical :
      boundaryComponents ≡ canonicalBoundaryComponents

    pAdicBoundaryVerdict :
      BoundaryUltrametricVerdict

    pAdicBoundaryVerdictIsTheorem :
      pAdicBoundaryVerdict ≡ ultrametricTheorem

    pAdicBoundaryUltrametric :
      Bool

    pAdicBoundaryUltrametricIsTrue :
      pAdicBoundaryUltrametric ≡ true

    archimedeanBoundaryVerdict :
      BoundaryUltrametricVerdict

    archimedeanBoundaryVerdictIsNotUltrametric :
      archimedeanBoundaryVerdict ≡ notUltrametric

    archimedeanBoundaryUltrametric :
      Bool

    archimedeanBoundaryUltrametricIsFalse :
      archimedeanBoundaryUltrametric ≡ false

    flatLimitComponents :
      List FlatLimitComponent

    flatLimitComponentsAreCanonical :
      flatLimitComponents ≡ canonicalFlatLimitComponents

    pAdicFlatLimitResolution :
      FlatLimitResolutionVerdict

    pAdicFlatLimitResolutionIsResolvedByUltrametricInsight :
      pAdicFlatLimitResolution ≡ resolvedByUltrametricInsight

    pAdicFlatLimitResolvedByUltrametricInsight :
      Bool

    pAdicFlatLimitResolvedByUltrametricInsightIsTrue :
      pAdicFlatLimitResolvedByUltrametricInsight ≡ true

    archimedeanFlatLimitResolution :
      FlatLimitResolutionVerdict

    archimedeanFlatLimitResolutionIsNotResolvedByUltrametricInsight :
      archimedeanFlatLimitResolution ≡ notResolvedByUltrametricInsight

    archimedeanFlatLimitResolvedByUltrametricInsight :
      Bool

    archimedeanFlatLimitResolvedByUltrametricInsightIsFalse :
      archimedeanFlatLimitResolvedByUltrametricInsight ≡ false

    priorReceiptClarification :
      PriorReceiptClarification

    priorReceiptClarificationIsCanonical :
      priorReceiptClarification
      ≡
      supersedesAndClarifiesHyperbolicFlatLimitReceipt

    priorHyperbolicReceiptDidNotDistinguishComponents :
      Bool

    priorHyperbolicReceiptDidNotDistinguishComponentsIsTrue :
      priorHyperbolicReceiptDidNotDistinguishComponents ≡ true

    supersedesPriorHyperbolicFlatLimitReceipt :
      Bool

    supersedesPriorHyperbolicFlatLimitReceiptIsTrue :
      supersedesPriorHyperbolicFlatLimitReceipt ≡ true

    clarifiesPriorHyperbolicFlatLimitReceipt :
      Bool

    clarifiesPriorHyperbolicFlatLimitReceiptIsTrue :
      clarifiesPriorHyperbolicFlatLimitReceipt ≡ true

    pAdicBoundaryStatement :
      String

    pAdicBoundaryStatementIsCanonical :
      pAdicBoundaryStatement ≡ pAdicBoundaryUltrametricStatement

    archimedeanBoundaryStatement :
      String

    archimedeanBoundaryStatementIsCanonical :
      archimedeanBoundaryStatement ≡ archimedeanBoundaryNotUltrametricStatement

    pAdicFlatLimitStatement :
      String

    pAdicFlatLimitStatementIsCanonical :
      pAdicFlatLimitStatement ≡ pAdicFlatLimitResolvedStatement

    archimedeanFlatLimitStatement :
      String

    archimedeanFlatLimitStatementIsCanonical :
      archimedeanFlatLimitStatement ≡ archimedeanFlatLimitNotResolvedStatement

    priorClarificationStatement :
      String

    priorClarificationStatementIsCanonical :
      priorClarificationStatement ≡ priorHyperbolicReceiptClarificationStatement

    statement :
      String

    statementIsCanonical :
      statement ≡ ultrametricInsightClarificationStatement

    receiptBoundary :
      List String

open UltrametricInsightClarificationReceipt public

canonicalUltrametricInsightClarificationReceipt :
  UltrametricInsightClarificationReceipt
canonicalUltrametricInsightClarificationReceipt =
  record
    { status =
        ultrametricInsightClarifiesComponentSplit
    ; boundaryComponents =
        canonicalBoundaryComponents
    ; boundaryComponentsAreCanonical =
        refl
    ; pAdicBoundaryVerdict =
        ultrametricTheorem
    ; pAdicBoundaryVerdictIsTheorem =
        refl
    ; pAdicBoundaryUltrametric =
        true
    ; pAdicBoundaryUltrametricIsTrue =
        refl
    ; archimedeanBoundaryVerdict =
        notUltrametric
    ; archimedeanBoundaryVerdictIsNotUltrametric =
        refl
    ; archimedeanBoundaryUltrametric =
        false
    ; archimedeanBoundaryUltrametricIsFalse =
        refl
    ; flatLimitComponents =
        canonicalFlatLimitComponents
    ; flatLimitComponentsAreCanonical =
        refl
    ; pAdicFlatLimitResolution =
        resolvedByUltrametricInsight
    ; pAdicFlatLimitResolutionIsResolvedByUltrametricInsight =
        refl
    ; pAdicFlatLimitResolvedByUltrametricInsight =
        true
    ; pAdicFlatLimitResolvedByUltrametricInsightIsTrue =
        refl
    ; archimedeanFlatLimitResolution =
        notResolvedByUltrametricInsight
    ; archimedeanFlatLimitResolutionIsNotResolvedByUltrametricInsight =
        refl
    ; archimedeanFlatLimitResolvedByUltrametricInsight =
        false
    ; archimedeanFlatLimitResolvedByUltrametricInsightIsFalse =
        refl
    ; priorReceiptClarification =
        supersedesAndClarifiesHyperbolicFlatLimitReceipt
    ; priorReceiptClarificationIsCanonical =
        refl
    ; priorHyperbolicReceiptDidNotDistinguishComponents =
        true
    ; priorHyperbolicReceiptDidNotDistinguishComponentsIsTrue =
        refl
    ; supersedesPriorHyperbolicFlatLimitReceipt =
        true
    ; supersedesPriorHyperbolicFlatLimitReceiptIsTrue =
        refl
    ; clarifiesPriorHyperbolicFlatLimitReceipt =
        true
    ; clarifiesPriorHyperbolicFlatLimitReceiptIsTrue =
        refl
    ; pAdicBoundaryStatement =
        pAdicBoundaryUltrametricStatement
    ; pAdicBoundaryStatementIsCanonical =
        refl
    ; archimedeanBoundaryStatement =
        archimedeanBoundaryNotUltrametricStatement
    ; archimedeanBoundaryStatementIsCanonical =
        refl
    ; pAdicFlatLimitStatement =
        pAdicFlatLimitResolvedStatement
    ; pAdicFlatLimitStatementIsCanonical =
        refl
    ; archimedeanFlatLimitStatement =
        archimedeanFlatLimitNotResolvedStatement
    ; archimedeanFlatLimitStatementIsCanonical =
        refl
    ; priorClarificationStatement =
        priorHyperbolicReceiptClarificationStatement
    ; priorClarificationStatementIsCanonical =
        refl
    ; statement =
        ultrametricInsightClarificationStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        pAdicBoundaryUltrametricStatement
        ∷ archimedeanBoundaryNotUltrametricStatement
        ∷ pAdicFlatLimitResolvedStatement
        ∷ archimedeanFlatLimitNotResolvedStatement
        ∷ priorHyperbolicReceiptClarificationStatement
        ∷ ultrametricInsightClarificationStatement
        ∷ []
    }

pAdicBoundaryUltrametricIsTheorem :
  pAdicBoundaryVerdict canonicalUltrametricInsightClarificationReceipt
  ≡
  ultrametricTheorem
pAdicBoundaryUltrametricIsTheorem =
  refl

archimedeanBoundaryIsNotUltrametric :
  archimedeanBoundaryVerdict canonicalUltrametricInsightClarificationReceipt
  ≡
  notUltrametric
archimedeanBoundaryIsNotUltrametric =
  refl

pAdicFlatLimitResolvedByInsight :
  pAdicFlatLimitResolution canonicalUltrametricInsightClarificationReceipt
  ≡
  resolvedByUltrametricInsight
pAdicFlatLimitResolvedByInsight =
  refl

archimedeanFlatLimitNotResolvedByInsight :
  archimedeanFlatLimitResolution canonicalUltrametricInsightClarificationReceipt
  ≡
  notResolvedByUltrametricInsight
archimedeanFlatLimitNotResolvedByInsight =
  refl

priorHyperbolicFlatLimitReceiptClarified :
  priorReceiptClarification canonicalUltrametricInsightClarificationReceipt
  ≡
  supersedesAndClarifiesHyperbolicFlatLimitReceipt
priorHyperbolicFlatLimitReceiptClarified =
  refl
