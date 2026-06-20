module DASHI.Physics.Closure.NSSardBoundaryRegularityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS Sard boundary regularity receipt.
--
-- This is a fail-closed, self-contained receipt for the lambda2 = 0
-- boundary carrier.  It records the regular-value / regular-point framing,
-- the nonvanishing gradient condition at regular points, the boundary
-- tracelessness identity delta1 = |lambda1|, and the a.e. delta1 > 0
-- partial closure.
--
-- The quantitative delta1 >= 1 gate is kept explicitly open.  No Clay
-- promotion or theorem promotion is claimed here.

data Void : Set where

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Local carriers for the boundary-regularity receipt.

data BoundaryCarrier : Set where
  lambda2EqualsZeroBoundaryCarrier :
    BoundaryCarrier

data RegularityFraming : Set where
  regularValueRegularPointFraming :
    RegularityFraming

data GradientCertificate : Set where
  gradientNonvanishingAtRegularPoints :
    RegularityFraming →
    GradientCertificate

data BoundaryTracelessnessCertificate : Set where
  delta1EqualsAbsLambda1OnBoundaryViaTracelessness :
    BoundaryCarrier →
    BoundaryTracelessnessCertificate

data AlmostEverywherePositivePartialClosure : Set where
  delta1AlmostEverywherePositivePartialClosure :
    BoundaryTracelessnessCertificate →
    AlmostEverywherePositivePartialClosure

data NSSardBoundaryRegularityPromotion : Set where

nssardBoundaryRegularityPromotionImpossibleHere :
  NSSardBoundaryRegularityPromotion →
  Void
nssardBoundaryRegularityPromotionImpossibleHere ()

data NSSardBoundaryRegularityStatusRow : Set where
  lambda2ZeroBoundaryCarrierRecorded :
    NSSardBoundaryRegularityStatusRow
  regularValueRegularPointFramingRecorded :
    NSSardBoundaryRegularityStatusRow
  gradientNonvanishingAtRegularPointsRecorded :
    NSSardBoundaryRegularityStatusRow
  delta1EqualsAbsLambda1OnBoundaryViaTracelessnessRecorded :
    NSSardBoundaryRegularityStatusRow
  delta1AlmostEverywherePositivePartialClosureRecorded :
    NSSardBoundaryRegularityStatusRow
  quantitativeDelta1Ge1GateLeftOpenRecorded :
    NSSardBoundaryRegularityStatusRow
  clayPromotionBlockedRecorded :
    NSSardBoundaryRegularityStatusRow

canonicalNSSardBoundaryRegularityStatusRows :
  List NSSardBoundaryRegularityStatusRow
canonicalNSSardBoundaryRegularityStatusRows =
  lambda2ZeroBoundaryCarrierRecorded
  ∷ regularValueRegularPointFramingRecorded
  ∷ gradientNonvanishingAtRegularPointsRecorded
  ∷ delta1EqualsAbsLambda1OnBoundaryViaTracelessnessRecorded
  ∷ delta1AlmostEverywherePositivePartialClosureRecorded
  ∷ quantitativeDelta1Ge1GateLeftOpenRecorded
  ∷ clayPromotionBlockedRecorded
  ∷ []

NSSardBoundaryRegularityStatusRowCount : Nat
NSSardBoundaryRegularityStatusRowCount =
  listLength canonicalNSSardBoundaryRegularityStatusRows

NSSardBoundaryRegularityStatusRowCountIs7 :
  NSSardBoundaryRegularityStatusRowCount ≡ 7
NSSardBoundaryRegularityStatusRowCountIs7 =
  refl

------------------------------------------------------------------------
-- Canonical labels.

organizationString : String
organizationString =
  "O: Worker lane 5 records a boundary-regularity receipt for the lambda2 = 0 Sard boundary carrier."

requirementString : String
requirementString =
  "R: Record the regular-value / regular-point framing, gradient nonvanishing at regular points, boundary tracelessness delta1 = |lambda1|, and the a.e. delta1 > 0 partial closure."

codeArtifactString : String
codeArtifactString =
  "C: This standalone Agda receipt owns only the local boundary carriers, canonical status rows, open quantitative gate, fail-closed promotion guard, and O/R/C/S/L/P/G/F contract strings."

stateString : String
stateString =
  "S: The boundary carrier is lambda2 = 0; the regularity framing and nonvanishing gradient are recorded; delta1 = |lambda1| is recorded on the boundary via tracelessness; a.e. delta1 > 0 is recorded as a partial closure; delta1 >= 1 remains explicitly open; Clay promotion stays false."

latticeString : String
latticeString =
  "L: lambda2 = 0 boundary carrier -> regular-value / regular-point framing -> gradient nonvanishing at regular points -> traceless boundary identity delta1 = |lambda1| -> a.e. delta1 > 0 partial closure -> open quantitative delta1 >= 1 gate -> fail-closed promotion guard."

proposalString : String
proposalString =
  "P: Treat this module as the nearby receipt surface for the Sard boundary-regularity partial closure, but keep the quantitative delta1 >= 1 gate open until an external proof binds it."

governanceString : String
governanceString =
  "G: The receipt is fail-closed: it records the lambda2 = 0 boundary, the regular-point framing, the gradient condition, the tracelessness-derived boundary identity, and the partial closure without claiming Clay or theorem promotion."

gapString : String
gapString =
  "F: Remaining gap is the quantitative delta1 >= 1 closure; the a.e. delta1 > 0 statement is only partial, so promotion remains blocked."

record NSSardBoundaryRegularityORCSLPGF : Set where
  constructor nssardBoundaryRegularityORCSLPGF
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
    FIsCanonical : F ≡ gapString

canonicalNSSardBoundaryRegularityORCSLPGF :
  NSSardBoundaryRegularityORCSLPGF
canonicalNSSardBoundaryRegularityORCSLPGF =
  nssardBoundaryRegularityORCSLPGF
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
    gapString
    refl

------------------------------------------------------------------------
-- Receipt statements and canonical witnesses.

boundaryCarrierStatement : String
boundaryCarrierStatement =
  "lambda2 = 0 boundary carrier recorded"

regularityFramingStatement : String
regularityFramingStatement =
  "regular-value / regular-point framing recorded"

gradientStatement : String
gradientStatement =
  "gradient nonvanishing at regular points recorded"

boundaryTracelessnessStatement : String
boundaryTracelessnessStatement =
  "tracelessness records delta1 = |lambda1| on the boundary"

partialClosureStatement : String
partialClosureStatement =
  "a.e. delta1 > 0 partial closure recorded"

openQuantitativeGateStatement : String
openQuantitativeGateStatement =
  "quantitative delta1 >= 1 gate left open"

nssardBoundaryRegularityStatement : String
nssardBoundaryRegularityStatement =
  "lambda2 = 0 boundary regularity is recorded as a fail-closed receipt: regular-value / regular-point framing, gradient nonvanishing at regular points, boundary tracelessness delta1 = |lambda1|, and a.e. delta1 > 0 partial closure are present; the quantitative delta1 >= 1 gate stays open and Clay promotion stays false."

canonicalBoundaryCarrier :
  BoundaryCarrier
canonicalBoundaryCarrier =
  lambda2EqualsZeroBoundaryCarrier

canonicalRegularityFraming :
  RegularityFraming
canonicalRegularityFraming =
  regularValueRegularPointFraming

canonicalGradientCertificate :
  GradientCertificate
canonicalGradientCertificate =
  gradientNonvanishingAtRegularPoints canonicalRegularityFraming

canonicalBoundaryTracelessnessCertificate :
  BoundaryTracelessnessCertificate
canonicalBoundaryTracelessnessCertificate =
  delta1EqualsAbsLambda1OnBoundaryViaTracelessness canonicalBoundaryCarrier

canonicalAlmostEverywherePositivePartialClosure :
  AlmostEverywherePositivePartialClosure
canonicalAlmostEverywherePositivePartialClosure =
  delta1AlmostEverywherePositivePartialClosure
    canonicalBoundaryTracelessnessCertificate

canonicalQuantitativeDelta1Ge1GateThreshold : Nat
canonicalQuantitativeDelta1Ge1GateThreshold =
  suc zero

canonicalQuantitativeDelta1Ge1GateOpen : Bool
canonicalQuantitativeDelta1Ge1GateOpen =
  true

canonicalDelta1AlmostEverywherePositivePartialClosureRecorded : Bool
canonicalDelta1AlmostEverywherePositivePartialClosureRecorded =
  true

canonicalFullQuantitativeClosureRecorded : Bool
canonicalFullQuantitativeClosureRecorded =
  false

canonicalClayPromotion : Bool
canonicalClayPromotion =
  false

record NSSardBoundaryRegularityReceipt : Setω where
  field
    statusRows :
      List NSSardBoundaryRegularityStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalNSSardBoundaryRegularityStatusRows
    statusRowCountIsCanonical :
      NSSardBoundaryRegularityStatusRowCount ≡ 7
    boundaryCarrier :
      BoundaryCarrier
    boundaryCarrierIsCanonical :
      boundaryCarrier ≡ canonicalBoundaryCarrier
    regularityFraming :
      RegularityFraming
    regularityFramingIsCanonical :
      regularityFraming ≡ canonicalRegularityFraming
    gradientCertificate :
      GradientCertificate
    gradientCertificateIsCanonical :
      gradientCertificate ≡ canonicalGradientCertificate
    boundaryTracelessnessCertificate :
      BoundaryTracelessnessCertificate
    boundaryTracelessnessCertificateIsCanonical :
      boundaryTracelessnessCertificate
        ≡ canonicalBoundaryTracelessnessCertificate
    almostEverywherePositivePartialClosure :
      AlmostEverywherePositivePartialClosure
    almostEverywherePositivePartialClosureIsCanonical :
      almostEverywherePositivePartialClosure
        ≡ canonicalAlmostEverywherePositivePartialClosure
    quantitativeDelta1Ge1GateThreshold :
      Nat
    quantitativeDelta1Ge1GateThresholdIsOne :
      quantitativeDelta1Ge1GateThreshold ≡ suc zero
    quantitativeDelta1Ge1GateOpen :
      Bool
    quantitativeDelta1Ge1GateOpenIsTrue :
      quantitativeDelta1Ge1GateOpen ≡ true
    delta1AlmostEverywherePositivePartialClosureFlag :
      Bool
    delta1AlmostEverywherePositivePartialClosureFlagIsTrue :
      delta1AlmostEverywherePositivePartialClosureFlag ≡ true
    fullQuantitativeClosureRecorded :
      Bool
    fullQuantitativeClosureRecordedIsFalse :
      fullQuantitativeClosureRecorded ≡ false
    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false
    orcslpgf :
      NSSardBoundaryRegularityORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSSardBoundaryRegularityORCSLPGF
    statement :
      String
    statementIsCanonical :
      statement ≡ nssardBoundaryRegularityStatement
    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡
        boundaryCarrierStatement
        ∷ regularityFramingStatement
        ∷ gradientStatement
        ∷ boundaryTracelessnessStatement
        ∷ partialClosureStatement
        ∷ openQuantitativeGateStatement
        ∷ "Clay promotion stays false"
        ∷ []
    promotionFlags :
      List NSSardBoundaryRegularityPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open NSSardBoundaryRegularityReceipt public

canonicalNSSardBoundaryRegularityReceipt :
  NSSardBoundaryRegularityReceipt
canonicalNSSardBoundaryRegularityReceipt =
  record
    { statusRows =
        canonicalNSSardBoundaryRegularityStatusRows
    ; statusRowsAreCanonical =
        refl
    ; statusRowCountIsCanonical =
        refl
    ; boundaryCarrier =
        canonicalBoundaryCarrier
    ; boundaryCarrierIsCanonical =
        refl
    ; regularityFraming =
        canonicalRegularityFraming
    ; regularityFramingIsCanonical =
        refl
    ; gradientCertificate =
        canonicalGradientCertificate
    ; gradientCertificateIsCanonical =
        refl
    ; boundaryTracelessnessCertificate =
        canonicalBoundaryTracelessnessCertificate
    ; boundaryTracelessnessCertificateIsCanonical =
        refl
    ; almostEverywherePositivePartialClosure =
        canonicalAlmostEverywherePositivePartialClosure
    ; almostEverywherePositivePartialClosureIsCanonical =
        refl
    ; quantitativeDelta1Ge1GateThreshold =
        canonicalQuantitativeDelta1Ge1GateThreshold
    ; quantitativeDelta1Ge1GateThresholdIsOne =
        refl
    ; quantitativeDelta1Ge1GateOpen =
        canonicalQuantitativeDelta1Ge1GateOpen
    ; quantitativeDelta1Ge1GateOpenIsTrue =
        refl
    ; delta1AlmostEverywherePositivePartialClosureFlag =
        canonicalDelta1AlmostEverywherePositivePartialClosureRecorded
    ; delta1AlmostEverywherePositivePartialClosureFlagIsTrue =
        refl
    ; fullQuantitativeClosureRecorded =
        canonicalFullQuantitativeClosureRecorded
    ; fullQuantitativeClosureRecordedIsFalse =
        refl
    ; clayPromotion =
        canonicalClayPromotion
    ; clayPromotionIsFalse =
        refl
    ; orcslpgf =
        canonicalNSSardBoundaryRegularityORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; statement =
        nssardBoundaryRegularityStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        boundaryCarrierStatement
        ∷ regularityFramingStatement
        ∷ gradientStatement
        ∷ boundaryTracelessnessStatement
        ∷ partialClosureStatement
        ∷ openQuantitativeGateStatement
        ∷ "Clay promotion stays false"
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

recordsBoundaryCarrier :
  boundaryCarrier canonicalNSSardBoundaryRegularityReceipt
  ≡ canonicalBoundaryCarrier
recordsBoundaryCarrier =
  refl

recordsRegularityFraming :
  regularityFraming canonicalNSSardBoundaryRegularityReceipt
  ≡ canonicalRegularityFraming
recordsRegularityFraming =
  refl

recordsGradientCertificate :
  gradientCertificate canonicalNSSardBoundaryRegularityReceipt
  ≡ canonicalGradientCertificate
recordsGradientCertificate =
  refl

recordsBoundaryTracelessnessCertificate :
  boundaryTracelessnessCertificate canonicalNSSardBoundaryRegularityReceipt
  ≡ canonicalBoundaryTracelessnessCertificate
recordsBoundaryTracelessnessCertificate =
  refl

recordsPartialClosure :
  almostEverywherePositivePartialClosure canonicalNSSardBoundaryRegularityReceipt
  ≡ canonicalAlmostEverywherePositivePartialClosure
recordsPartialClosure =
  refl

recordsQuantitativeDelta1Ge1GateOpen :
  quantitativeDelta1Ge1GateOpen canonicalNSSardBoundaryRegularityReceipt
  ≡ true
recordsQuantitativeDelta1Ge1GateOpen =
  refl

recordsClayPromotionFalse :
  clayPromotion canonicalNSSardBoundaryRegularityReceipt ≡ false
recordsClayPromotionFalse =
  refl

recordsFullQuantitativeClosureFalse :
  fullQuantitativeClosureRecorded canonicalNSSardBoundaryRegularityReceipt
  ≡ false
recordsFullQuantitativeClosureFalse =
  refl

NSSardBoundaryRegularityReceiptRecorded : Bool
NSSardBoundaryRegularityReceiptRecorded =
  true

recordsNSSardBoundaryRegularityReceipt :
  NSSardBoundaryRegularityReceiptRecorded ≡ true
recordsNSSardBoundaryRegularityReceipt =
  refl
