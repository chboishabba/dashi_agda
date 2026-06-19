module DASHI.Physics.Closure.NSQ3ExtensionalThresholdReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- NS Q3 extensional threshold hard-wall receipt.
--
-- O/R/C/S/L/P/G/F surface:
-- This module records the new Q3 hard wall in fail-closed form.  The
-- surface is the boundary integral
--
--   Q3 = ∫_{∂Ω_K} |<omega,e3>|^2 / g12^2 dH2.
--
-- On the biaxial carrier with λ1 = -g12, λ2 = 0, λ3 = g12 > 0, the
-- projected term <S omega,e3> = g12 <omega,e3> is not cancelled.  The
-- associated differential inequality is recorded as
--
--   dQ3/dt <= Q3 * (2 - 2*g12*(1 - C_CZ) + 2*Cnu) + RK + viscous.
--
-- The negative coefficient only appears once
--
--   g12 > (1 + Cnu) / (1 - C_CZ),
--
-- which is the empirical hard wall at about 1.03.  The current analytic GD1
-- lower bound is only about 0.031, so this receipt remains closed unless a
-- bypass theorem is supplied elsewhere.

data NSQ3ExtensionalThresholdStatus : Set where
  q3ExtensionalThresholdHardWallRecorded :
    NSQ3ExtensionalThresholdStatus

data NSQ3ExtensionalThresholdComponent : Set where
  q3BoundaryIntegralRecorded :
    NSQ3ExtensionalThresholdComponent

  biaxialCarrierRecorded :
    NSQ3ExtensionalThresholdComponent

  projectedStretchingNotCancelled :
    NSQ3ExtensionalThresholdComponent

  differentialInequalityRecorded :
    NSQ3ExtensionalThresholdComponent

  empiricalThresholdHardWallRecorded :
    NSQ3ExtensionalThresholdComponent

  analyticGD1LowerBoundStillTooSmall :
    NSQ3ExtensionalThresholdComponent

  promotionKeptClosed :
    NSQ3ExtensionalThresholdComponent

canonicalNSQ3ExtensionalThresholdComponents :
  List NSQ3ExtensionalThresholdComponent
canonicalNSQ3ExtensionalThresholdComponents =
  q3BoundaryIntegralRecorded
  ∷ biaxialCarrierRecorded
  ∷ projectedStretchingNotCancelled
  ∷ differentialInequalityRecorded
  ∷ empiricalThresholdHardWallRecorded
  ∷ analyticGD1LowerBoundStillTooSmall
  ∷ promotionKeptClosed
  ∷ []

data NSQ3ExtensionalThresholdBlocker : Set where
  hardWallRequiresStrongEnoughG12 :
    NSQ3ExtensionalThresholdBlocker

  empiricalThresholdStillAboveCurrentAnalyticBound :
    NSQ3ExtensionalThresholdBlocker

  biaxialStretchingProjectionSurvives :
    NSQ3ExtensionalThresholdBlocker

  rkAndViscousTermsRemain :
    NSQ3ExtensionalThresholdBlocker

  noPromotionByThisReceipt :
    NSQ3ExtensionalThresholdBlocker

canonicalNSQ3ExtensionalThresholdBlockers :
  List NSQ3ExtensionalThresholdBlocker
canonicalNSQ3ExtensionalThresholdBlockers =
  hardWallRequiresStrongEnoughG12
  ∷ empiricalThresholdStillAboveCurrentAnalyticBound
  ∷ biaxialStretchingProjectionSurvives
  ∷ rkAndViscousTermsRemain
  ∷ noPromotionByThisReceipt
  ∷ []

data NSQ3ExtensionalThresholdPromotion : Set where

nsQ3ExtensionalThresholdPromotionImpossibleHere :
  NSQ3ExtensionalThresholdPromotion →
  ⊥
nsQ3ExtensionalThresholdPromotionImpossibleHere ()

q3BoundaryIntegralStatement : String
q3BoundaryIntegralStatement =
  "Q3 is the boundary integral ∫_{∂Ω_K} |<omega,e3>|^2 / g12^2 dH2."

biaxialCarrierStatement : String
biaxialCarrierStatement =
  "On the biaxial carrier λ1 = -g12, λ2 = 0, λ3 = g12 > 0, the projection <S omega,e3> = g12 <omega,e3> is not cancelled."

differentialInequalityStatement : String
differentialInequalityStatement =
  "dQ3/dt <= Q3 * (2 - 2*g12*(1 - C_CZ) + 2*Cnu) + RK + viscous."

hardWallThresholdStatement : String
hardWallThresholdStatement =
  "Negative coefficient only if g12 > (1 + Cnu) / (1 - C_CZ); the empirical threshold is about 1.03."

analyticGD1BoundStatement : String
analyticGD1BoundStatement =
  "The current analytic GD1 lower bound is about 0.031, so the threshold remains a hard wall without a bypass theorem."

boundaryStatement : String
boundaryStatement =
  "This receipt is fail-closed: it records the Q3 hard wall, keeps authority false, keeps promotion empty, and does not prove the bypass."

authorityStatement : String
authorityStatement =
  "Authority is intentionally false for this receipt."

promotionStatement : String
promotionStatement =
  "Promotion remains closed and the promotion type is empty."

oStatement : String
oStatement =
  "O: Q3 is recorded as the boundary integral over ∂Ω_K of |<omega,e3>|^2 / g12^2 dH2."

rStatement : String
rStatement =
  "R: On the biaxial carrier λ1 = -g12, λ2 = 0, λ3 = g12 > 0, the e3 projection survives without cancellation."

cStatement : String
cStatement =
  "C: The differential inequality is recorded in the exact ledger shape dQ3/dt <= Q3*(2 - 2*g12*(1 - C_CZ) + 2*Cnu) + RK + viscous."

sStatement : String
sStatement =
  "S: The hard-wall threshold is g12 > (1 + Cnu) / (1 - C_CZ), with the empirical wall at about 1.03."

lStatement : String
lStatement =
  "L: The analytic GD1 lower bound remains about 0.031, far below the empirical wall."

pStatement : String
pStatement =
  "P: Promotion is kept empty and false; no bypass theorem is constructed here."

gStatement : String
gStatement =
  "G: Fail closed: this receipt records the threshold wall, authority false, and the open gap between analytic and empirical bounds."

fStatement : String
fStatement =
  "F: The file is a canonical receipt only, with projection lemmas and an empty promotion type."

record NSQ3ExtensionalThresholdReceipt : Set where
  field
    status :
      NSQ3ExtensionalThresholdStatus

    statusIsRecorded :
      status ≡ q3ExtensionalThresholdHardWallRecorded

    canonicalComponents :
      List NSQ3ExtensionalThresholdComponent

    canonicalComponentsAreExact :
      canonicalComponents ≡ canonicalNSQ3ExtensionalThresholdComponents

    q3BoundaryIntegral :
      String

    q3BoundaryIntegralIsCanonical :
      q3BoundaryIntegral ≡ q3BoundaryIntegralStatement

    biaxialCarrier :
      String

    biaxialCarrierIsCanonical :
      biaxialCarrier ≡ biaxialCarrierStatement

    differentialInequality :
      String

    differentialInequalityIsCanonical :
      differentialInequality ≡ differentialInequalityStatement

    hardWallThreshold :
      String

    hardWallThresholdIsCanonical :
      hardWallThreshold ≡ hardWallThresholdStatement

    analyticGD1LowerBound :
      String

    analyticGD1LowerBoundIsCanonical :
      analyticGD1LowerBound ≡ analyticGD1BoundStatement

    authority :
      Bool

    authorityIsFalse :
      authority ≡ false

    promotionClosed :
      Bool

    promotionClosedIsFalse :
      promotionClosed ≡ false

    promotionFlags :
      List NSQ3ExtensionalThresholdPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ boundaryStatement

    authorityBoundary :
      String

    authorityBoundaryIsCanonical :
      authorityBoundary ≡ authorityStatement

    promotionBoundary :
      String

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ promotionStatement

    oString :
      String

    oStringIsCanonical :
      oString ≡ oStatement

    rString :
      String

    rStringIsCanonical :
      rString ≡ rStatement

    cString :
      String

    cStringIsCanonical :
      cString ≡ cStatement

    sString :
      String

    sStringIsCanonical :
      sString ≡ sStatement

    lString :
      String

    lStringIsCanonical :
      lString ≡ lStatement

    pString :
      String

    pStringIsCanonical :
      pString ≡ pStatement

    gString :
      String

    gStringIsCanonical :
      gString ≡ gStatement

    fString :
      String

    fStringIsCanonical :
      fString ≡ fStatement

    blockers :
      List NSQ3ExtensionalThresholdBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSQ3ExtensionalThresholdBlockers

open NSQ3ExtensionalThresholdReceipt public

canonicalNSQ3ExtensionalThresholdReceipt :
  NSQ3ExtensionalThresholdReceipt
canonicalNSQ3ExtensionalThresholdReceipt =
  record
    { status =
        q3ExtensionalThresholdHardWallRecorded
    ; statusIsRecorded =
        refl
    ; canonicalComponents =
        canonicalNSQ3ExtensionalThresholdComponents
    ; canonicalComponentsAreExact =
        refl
    ; q3BoundaryIntegral =
        q3BoundaryIntegralStatement
    ; q3BoundaryIntegralIsCanonical =
        refl
    ; biaxialCarrier =
        biaxialCarrierStatement
    ; biaxialCarrierIsCanonical =
        refl
    ; differentialInequality =
        differentialInequalityStatement
    ; differentialInequalityIsCanonical =
        refl
    ; hardWallThreshold =
        hardWallThresholdStatement
    ; hardWallThresholdIsCanonical =
        refl
    ; analyticGD1LowerBound =
        analyticGD1BoundStatement
    ; analyticGD1LowerBoundIsCanonical =
        refl
    ; authority =
        false
    ; authorityIsFalse =
        refl
    ; promotionClosed =
        false
    ; promotionClosedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        boundaryStatement
    ; receiptBoundaryIsCanonical =
        refl
    ; authorityBoundary =
        authorityStatement
    ; authorityBoundaryIsCanonical =
        refl
    ; promotionBoundary =
        promotionStatement
    ; promotionBoundaryIsCanonical =
        refl
    ; oString =
        oStatement
    ; oStringIsCanonical =
        refl
    ; rString =
        rStatement
    ; rStringIsCanonical =
        refl
    ; cString =
        cStatement
    ; cStringIsCanonical =
        refl
    ; sString =
        sStatement
    ; sStringIsCanonical =
        refl
    ; lString =
        lStatement
    ; lStringIsCanonical =
        refl
    ; pString =
        pStatement
    ; pStringIsCanonical =
        refl
    ; gString =
        gStatement
    ; gStringIsCanonical =
        refl
    ; fString =
        fStatement
    ; fStringIsCanonical =
        refl
    ; blockers =
        canonicalNSQ3ExtensionalThresholdBlockers
    ; blockersAreCanonical =
        refl
    }

canonicalNSQ3ExtensionalThresholdStatusIsRecorded :
  status canonicalNSQ3ExtensionalThresholdReceipt
  ≡ q3ExtensionalThresholdHardWallRecorded
canonicalNSQ3ExtensionalThresholdStatusIsRecorded =
  refl

canonicalNSQ3ExtensionalThresholdAuthorityIsFalse :
  authority canonicalNSQ3ExtensionalThresholdReceipt ≡ false
canonicalNSQ3ExtensionalThresholdAuthorityIsFalse =
  refl

canonicalNSQ3ExtensionalThresholdPromotionClosedIsFalse :
  promotionClosed canonicalNSQ3ExtensionalThresholdReceipt ≡ false
canonicalNSQ3ExtensionalThresholdPromotionClosedIsFalse =
  refl

canonicalNSQ3ExtensionalThresholdPromotionFlagsAreEmpty :
  promotionFlags canonicalNSQ3ExtensionalThresholdReceipt ≡ []
canonicalNSQ3ExtensionalThresholdPromotionFlagsAreEmpty =
  refl

canonicalNSQ3ExtensionalThresholdBoundaryIsCanonical :
  receiptBoundary canonicalNSQ3ExtensionalThresholdReceipt
  ≡ boundaryStatement
canonicalNSQ3ExtensionalThresholdBoundaryIsCanonical =
  refl
