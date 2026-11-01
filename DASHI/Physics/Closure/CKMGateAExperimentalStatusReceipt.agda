module DASHI.Physics.Closure.CKMGateAExperimentalStatusReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM Gate-A experimental-status addendum.
--
-- CKMGateAPartialCloseReceipt records a clean number-theory fact: the
-- D=-7 CM point on X0(7) is mathematically well-defined.  This addendum
-- records the harder empirical and architectural boundary.  The pure
-- gamma = arctan(sqrt(7)) formula is experimentally disfavoured against
-- HFLAV 2023, the earlier (1-alpha1) correction is not carrier-derived,
-- and the finite class-number route leaves two carrier-prime survivors.
-- Therefore Gate A remains blocked and no CKM promotion is available.

data GateASubclaim : Set where
  p7UniqueCKMLane :
    GateASubclaim

  cpPhaseAtClassOneCMPointOfX07 :
    GateASubclaim

  reconcilePureCMFormulaWithExperiment :
    GateASubclaim

data GateASubclaimStatus : Set where
  internalCarrierArchitectureOpen :
    GateASubclaimStatus

  dependsOnCKMLaneSelection :
    GateASubclaimStatus

  experimentallyFailingAtFivePointFourSigma :
    GateASubclaimStatus

data GateAClassNumberSurvivor : Set where
  survivorD=-3 :
    GateAClassNumberSurvivor

  survivorD=-7 :
    GateAClassNumberSurvivor

canonicalClassNumberRouteSurvivors :
  List GateAClassNumberSurvivor
canonicalClassNumberRouteSurvivors =
  survivorD=-3
  ∷ survivorD=-7
  ∷ []

data GateAStatusComponent : Set where
  partialNumberTheoryComplete :
    GateAStatusComponent

  architectureOpen :
    GateAStatusComponent

  formulaDisfavouredAt5Point4Sigma :
    GateAStatusComponent

canonicalGateAStatus :
  List GateAStatusComponent
canonicalGateAStatus =
  partialNumberTheoryComplete
  ∷ architectureOpen
  ∷ formulaDisfavouredAt5Point4Sigma
  ∷ []

data GateAExperimentalConclusion : Set where
  pureCMGammaFormulaExperimentallyDisfavoured :
    GateAExperimentalConclusion

data GateACorrectionStatus : Set where
  oneMinusAlphaOneCorrectionUngrounded :
    GateACorrectionStatus

data G7PromotionToken : Set where

g7PromotionImpossibleHere :
  G7PromotionToken →
  ⊥
g7PromotionImpossibleHere ()

gammaCarrierPureDegrees :
  Float
gammaCarrierPureDegrees =
  69.3

gammaHFLAV2023Degrees :
  Float
gammaHFLAV2023Degrees =
  65.5

gammaHFLAV2023SigmaDegrees :
  Float
gammaHFLAV2023SigmaDegrees =
  0.7

tensionWithHFLAVSigma :
  Float
tensionWithHFLAVSigma =
  5.4

gammaD=-3Degrees :
  Float
gammaD=-3Degrees =
  60.0

tensionD=-3WithHFLAVSigma :
  Float
tensionD=-3WithHFLAVSigma =
  7.9

gateAExperimentalStatement :
  String
gateAExperimentalStatement =
  "The pure gamma=arctan(sqrt(7)) formula gives 69.3 degrees, 5.4 sigma above HFLAV 2023 gamma=65.5+-0.7 degrees. The earlier (1-alpha1) correction is not carrier-derived and is not allowed as a promotion mechanism. The finite class-number route leaves D=-3 and D=-7; selecting D=-7 requires the internal p=7 CKM-lane claim and is circular until that claim is proved."

record GateASubclaimReceipt : Set where
  field
    subclaim :
      GateASubclaim

    status :
      GateASubclaimStatus

    closed :
      Bool

    closedIsFalse :
      closed ≡ false

    statement :
      String

open GateASubclaimReceipt public

gateASubclaimA :
  GateASubclaimReceipt
gateASubclaimA =
  record
    { subclaim =
        p7UniqueCKMLane
    ; status =
        internalCarrierArchitectureOpen
    ; closed =
        false
    ; closedIsFalse =
        refl
    ; statement =
        "Gate A(a): prove p=7 is the unique CKM lane in the carrier. This is an internal carrier-architecture claim."
    }

gateASubclaimB :
  GateASubclaimReceipt
gateASubclaimB =
  record
    { subclaim =
        cpPhaseAtClassOneCMPointOfX07
    ; status =
        dependsOnCKMLaneSelection
    ; closed =
        false
    ; closedIsFalse =
        refl
    ; statement =
        "Gate A(b): prove the CP phase lives at the class-1 CM point of X0(7). This depends on Gate A(a)."
    }

gateASubclaimC :
  GateASubclaimReceipt
gateASubclaimC =
  record
    { subclaim =
        reconcilePureCMFormulaWithExperiment
    ; status =
        experimentallyFailingAtFivePointFourSigma
    ; closed =
        false
    ; closedIsFalse =
        refl
    ; statement =
        "Gate A(c): reconcile arctan(sqrt(7))=69.3 degrees with experiment, or accept the pure CM formula as disfavoured."
    }

canonicalGateASubclaims :
  List GateASubclaimReceipt
canonicalGateASubclaims =
  gateASubclaimA
  ∷ gateASubclaimB
  ∷ gateASubclaimC
  ∷ []

record CKMGateAExperimentalStatusReceipt : Set where
  field
    gammaCarrierPure :
      Float

    gammaCarrierPureIs69Point3Degrees :
      gammaCarrierPure ≡ gammaCarrierPureDegrees

    gammaHFLAV2023 :
      Float

    gammaHFLAV2023Is65Point5Degrees :
      gammaHFLAV2023 ≡ gammaHFLAV2023Degrees

    gammaHFLAV2023Sigma :
      Float

    gammaHFLAV2023SigmaIs0Point7Degrees :
      gammaHFLAV2023Sigma ≡ gammaHFLAV2023SigmaDegrees

    tensionWithHFLAV :
      Float

    tensionWithHFLAVIs5Point4Sigma :
      tensionWithHFLAV ≡ tensionWithHFLAVSigma

    gammaFormulaExperimentallyDisfavoured :
      Bool

    gammaFormulaExperimentallyDisfavouredIsTrue :
      gammaFormulaExperimentallyDisfavoured ≡ true

    oneMinusAlphaOneCorrectionIsUngrounded :
      Bool

    oneMinusAlphaOneCorrectionIsUngroundedIsTrue :
      oneMinusAlphaOneCorrectionIsUngrounded ≡ true

    classNumberRouteSurvivors :
      List GateAClassNumberSurvivor

    classNumberRouteSurvivorsAreCanonical :
      classNumberRouteSurvivors ≡ canonicalClassNumberRouteSurvivors

    selectingD=-7OverD=-3IsCircular :
      Bool

    selectingD=-7OverD=-3IsCircularIsTrue :
      selectingD=-7OverD=-3IsCircular ≡ true

    D=-3FormulaAlsoExperimentallyDisfavoured :
      Bool

    D=-3FormulaAlsoExperimentallyDisfavouredIsTrue :
      D=-3FormulaAlsoExperimentallyDisfavoured ≡ true

    gateASubclaims :
      List GateASubclaimReceipt

    gateASubclaimsAreCanonical :
      gateASubclaims ≡ canonicalGateASubclaims

    gateAStatus :
      List GateAStatusComponent

    gateAStatusIsCanonical :
      gateAStatus ≡ canonicalGateAStatus

    gateAExperimentalConclusion :
      GateAExperimentalConclusion

    gateAExperimentalConclusionIsDisfavoured :
      gateAExperimentalConclusion ≡ pureCMGammaFormulaExperimentallyDisfavoured

    priorCorrectionStatus :
      GateACorrectionStatus

    priorCorrectionStatusIsUngrounded :
      priorCorrectionStatus ≡ oneMinusAlphaOneCorrectionUngrounded

    G7Blocked :
      Bool

    G7BlockedIsTrue :
      G7Blocked ≡ true

    noCKMPromotion :
      Bool

    noCKMPromotionIsTrue :
      noCKMPromotion ≡ true

    statement :
      String

    statementIsCanonical :
      statement ≡ gateAExperimentalStatement

open CKMGateAExperimentalStatusReceipt public

canonicalCKMGateAExperimentalStatusReceipt :
  CKMGateAExperimentalStatusReceipt
canonicalCKMGateAExperimentalStatusReceipt =
  record
    { gammaCarrierPure =
        gammaCarrierPureDegrees
    ; gammaCarrierPureIs69Point3Degrees =
        refl
    ; gammaHFLAV2023 =
        gammaHFLAV2023Degrees
    ; gammaHFLAV2023Is65Point5Degrees =
        refl
    ; gammaHFLAV2023Sigma =
        gammaHFLAV2023SigmaDegrees
    ; gammaHFLAV2023SigmaIs0Point7Degrees =
        refl
    ; tensionWithHFLAV =
        tensionWithHFLAVSigma
    ; tensionWithHFLAVIs5Point4Sigma =
        refl
    ; gammaFormulaExperimentallyDisfavoured =
        true
    ; gammaFormulaExperimentallyDisfavouredIsTrue =
        refl
    ; oneMinusAlphaOneCorrectionIsUngrounded =
        true
    ; oneMinusAlphaOneCorrectionIsUngroundedIsTrue =
        refl
    ; classNumberRouteSurvivors =
        canonicalClassNumberRouteSurvivors
    ; classNumberRouteSurvivorsAreCanonical =
        refl
    ; selectingD=-7OverD=-3IsCircular =
        true
    ; selectingD=-7OverD=-3IsCircularIsTrue =
        refl
    ; D=-3FormulaAlsoExperimentallyDisfavoured =
        true
    ; D=-3FormulaAlsoExperimentallyDisfavouredIsTrue =
        refl
    ; gateASubclaims =
        canonicalGateASubclaims
    ; gateASubclaimsAreCanonical =
        refl
    ; gateAStatus =
        canonicalGateAStatus
    ; gateAStatusIsCanonical =
        refl
    ; gateAExperimentalConclusion =
        pureCMGammaFormulaExperimentallyDisfavoured
    ; gateAExperimentalConclusionIsDisfavoured =
        refl
    ; priorCorrectionStatus =
        oneMinusAlphaOneCorrectionUngrounded
    ; priorCorrectionStatusIsUngrounded =
        refl
    ; G7Blocked =
        true
    ; G7BlockedIsTrue =
        refl
    ; noCKMPromotion =
        true
    ; noCKMPromotionIsTrue =
        refl
    ; statement =
        gateAExperimentalStatement
    ; statementIsCanonical =
        refl
    }
