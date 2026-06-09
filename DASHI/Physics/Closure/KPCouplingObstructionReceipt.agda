module DASHI.Physics.Closure.KPCouplingObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- KP coupling obstruction receipt.
--
-- This receipt records the corrected carrier-side coupling arithmetic for
-- the Bruhat-Tits-tree KP estimate.  The earlier flat-lattice beta reading
-- near 0.33 is not promoted here.  Once tree branching is included, the
-- single-prime path count contributes a log p term:
--
--   betaMin(p) = (a + log p) / cMin(p).
--
-- This is only the geometric-series convergence threshold.  The stricter
-- activity-absorption / KP-margin gate asks for the local KP sum to be
-- below one:
--
--   r / (1 - r) < 1, where r = p * exp (-(beta*cMin(p) - a)).
--
-- Equivalently beta*cMin(p) - a > log(2p).  At p = 7 this records the
-- stricter betaKPMargin(7) ~= 13.64.  The 10.13 number is therefore a
-- convergence boundary, not a KP-pass / absorption boundary.
--
-- At p = 7, using the narrow a bookkeeping 0.06 and
-- cMin(7) ~= Re(1 - exp(2 pi i / 7)) ~= 0.198, the recorded threshold is
-- betaMin(7) ~= 10.13, while the stricter margin threshold is ~= 13.64.
-- A one-loop physical beta 6 fails this carrier KP
-- test directly, and the carrier-scale one-loop translation records only
-- betaCarrier ~= 7.69, not 16.7.  The two-loop correction surface remains
-- below the same threshold.  Any betaCarrier ~= 16.7 reading is recorded only
-- as a conditional/nonperturbative RG input, requiring a Balaban bridge that
-- is not supplied here.
--
-- No continuum KP theorem, no Balaban RG proof, no Yang-Mills construction,
-- and no Clay promotion are claimed.

data KPCouplingObstructionStatus : Set where
  btBranchingBetaObstructionRecorded :
    KPCouplingObstructionStatus

data BetaThresholdFormulaStatus : Set where
  betaMinIncludesTreeBranchingLogP :
    BetaThresholdFormulaStatus

data KPMarginThresholdFormulaStatus : Set where
  kpMarginIncludesLogTwoP :
    KPMarginThresholdFormulaStatus

data FlatLatticeBetaVerdict : Set where
  flatBetaPointThreeThreeRejectedForBTTreeKP :
    FlatLatticeBetaVerdict

data PhysicalCouplingVerdict : Set where
  physicalFineLatticeBetaFailsP7Threshold :
    PhysicalCouplingVerdict

data RGCarrierCouplingVerdict : Set where
  oneLoopCarrierBetaStillFailsThreshold :
    RGCarrierCouplingVerdict

  twoLoopCarrierBetaStillFailsThreshold :
    RGCarrierCouplingVerdict

  nonperturbativeCarrierBetaPassesConditionally :
    RGCarrierCouplingVerdict

data KPRequiresRGFlowStatus : Set where
  balabanRGFlowIsNecessaryInput :
    KPRequiresRGFlowStatus

data KPCouplingOpenObligation : Set where
  proveBalabanRGScaleTransfer :
    KPCouplingOpenObligation

  justifyCarrierScaleBetaValue :
    KPCouplingOpenObligation

  proveTwoLoopCarrierScaleStillBelowThreshold :
    KPCouplingOpenObligation

  proveNonperturbativeCarrierBetaSixteenSevenBridge :
    KPCouplingOpenObligation

  proveSinglePrimeBTKPBoundAtCarrierScale :
    KPCouplingOpenObligation

  proveStrictKPMarginBelowOneAtCarrierScale :
    KPCouplingOpenObligation

  connectCarrierKPToContinuumOnlyAfterGate3 :
    KPCouplingOpenObligation

canonicalKPCouplingOpenObligations :
  List KPCouplingOpenObligation
canonicalKPCouplingOpenObligations =
  proveBalabanRGScaleTransfer
  ∷ justifyCarrierScaleBetaValue
  ∷ proveTwoLoopCarrierScaleStillBelowThreshold
  ∷ proveNonperturbativeCarrierBetaSixteenSevenBridge
  ∷ proveSinglePrimeBTKPBoundAtCarrierScale
  ∷ proveStrictKPMarginBelowOneAtCarrierScale
  ∷ connectCarrierKPToContinuumOnlyAfterGate3
  ∷ []

data KPCouplingNonClaim : Set where
  noFlatLatticeBetaKPClaim :
    KPCouplingNonClaim

  noPhysicalBetaDirectPassClaim :
    KPCouplingNonClaim

  noBalabanRGProof :
    KPCouplingNonClaim

  noPerturbativeCarrierBetaPassClaim :
    KPCouplingNonClaim

  noUnconditionalBetaSixteenSevenClaim :
    KPCouplingNonClaim

  noContinuumKPTheorem :
    KPCouplingNonClaim

  noYangMillsMassGapClaim :
    KPCouplingNonClaim

  noClayPromotion :
    KPCouplingNonClaim

canonicalKPCouplingNonClaims :
  List KPCouplingNonClaim
canonicalKPCouplingNonClaims =
  noFlatLatticeBetaKPClaim
  ∷ noPhysicalBetaDirectPassClaim
  ∷ noBalabanRGProof
  ∷ noPerturbativeCarrierBetaPassClaim
  ∷ noUnconditionalBetaSixteenSevenClaim
  ∷ noContinuumKPTheorem
  ∷ noYangMillsMassGapClaim
  ∷ noClayPromotion
  ∷ []

data KPCouplingPromotion : Set where

kpCouplingPromotionImpossibleHere :
  KPCouplingPromotion →
  ⊥
kpCouplingPromotionImpossibleHere ()

p7Prime :
  Nat
p7Prime =
  7

aBookkeepingNumerator :
  Nat
aBookkeepingNumerator =
  6

aBookkeepingDenominator :
  Nat
aBookkeepingDenominator =
  100

cMinP7ApproxNumerator :
  Nat
cMinP7ApproxNumerator =
  198

cMinP7ApproxDenominator :
  Nat
cMinP7ApproxDenominator =
  1000

betaMinP7ApproxNumerator :
  Nat
betaMinP7ApproxNumerator =
  1013

betaMinP7ApproxDenominator :
  Nat
betaMinP7ApproxDenominator =
  100

kpMarginP7ApproxNumerator :
  Nat
kpMarginP7ApproxNumerator =
  1364

kpMarginP7ApproxDenominator :
  Nat
kpMarginP7ApproxDenominator =
  100

physicalFineLatticeBetaApproxNumerator :
  Nat
physicalFineLatticeBetaApproxNumerator =
  6

physicalFineLatticeBetaApproxDenominator :
  Nat
physicalFineLatticeBetaApproxDenominator =
  1

rgFlowedCarrierBetaApproxNumerator :
  Nat
rgFlowedCarrierBetaApproxNumerator =
  769

rgFlowedCarrierBetaApproxDenominator :
  Nat
rgFlowedCarrierBetaApproxDenominator =
  100

twoLoopCarrierBetaApproxNumerator :
  Nat
twoLoopCarrierBetaApproxNumerator =
  800

twoLoopCarrierBetaApproxDenominator :
  Nat
twoLoopCarrierBetaApproxDenominator =
  100

conditionalNonperturbativeCarrierBetaNumerator :
  Nat
conditionalNonperturbativeCarrierBetaNumerator =
  167

conditionalNonperturbativeCarrierBetaDenominator :
  Nat
conditionalNonperturbativeCarrierBetaDenominator =
  10

betaFormulaSummary :
  String
betaFormulaSummary =
  "Corrected BT-tree KP threshold records betaMin(p) = (a + log p) / cMin(p), so tree branching contributes log p."

p7ObstructionSummary :
  String
p7ObstructionSummary =
  "At p=7, with a approximately 0.06 and cMin approximately 0.198, betaMin convergence is approximately 10.13, while the stricter KP margin threshold beta*cMin-a>log(2p) is approximately 13.64."

rgBoundarySummary :
  String
rgBoundarySummary =
  "Physical one-loop beta 6 gives carrier beta approximately 7.69, not 16.7, and still fails the p=7 threshold; the two-loop surface is still below threshold, while betaCarrier approximately 16.7 is conditional on a Balaban/nonperturbative RG bridge."

record KPCouplingObstructionReceipt : Setω where
  field
    status :
      KPCouplingObstructionStatus

    statusIsCanonical :
      status ≡ btBranchingBetaObstructionRecorded

    betaThresholdFormula :
      BetaThresholdFormulaStatus

    betaThresholdFormulaIsBTBranching :
      betaThresholdFormula ≡ betaMinIncludesTreeBranchingLogP

    kpMarginThresholdFormula :
      KPMarginThresholdFormulaStatus

    kpMarginThresholdFormulaIsLogTwoP :
      kpMarginThresholdFormula ≡ kpMarginIncludesLogTwoP

    flatLatticeBetaVerdict :
      FlatLatticeBetaVerdict

    flatLatticeBetaRejected :
      flatLatticeBetaVerdict ≡
      flatBetaPointThreeThreeRejectedForBTTreeKP

    p7PrimeRecorded :
      Nat

    p7PrimeRecordedIsCanonical :
      p7PrimeRecorded ≡ p7Prime

    aNumeratorRecorded :
      Nat

    aNumeratorRecordedIsCanonical :
      aNumeratorRecorded ≡ aBookkeepingNumerator

    aDenominatorRecorded :
      Nat

    aDenominatorRecordedIsCanonical :
      aDenominatorRecorded ≡ aBookkeepingDenominator

    cMinP7NumeratorRecorded :
      Nat

    cMinP7NumeratorRecordedIsCanonical :
      cMinP7NumeratorRecorded ≡ cMinP7ApproxNumerator

    cMinP7DenominatorRecorded :
      Nat

    cMinP7DenominatorRecordedIsCanonical :
      cMinP7DenominatorRecorded ≡ cMinP7ApproxDenominator

    betaMinP7NumeratorRecorded :
      Nat

    betaMinP7NumeratorRecordedIsCanonical :
      betaMinP7NumeratorRecorded ≡ betaMinP7ApproxNumerator

    betaMinP7DenominatorRecorded :
      Nat

    betaMinP7DenominatorRecordedIsCanonical :
      betaMinP7DenominatorRecorded ≡ betaMinP7ApproxDenominator

    kpMarginP7NumeratorRecorded :
      Nat

    kpMarginP7NumeratorRecordedIsCanonical :
      kpMarginP7NumeratorRecorded ≡ kpMarginP7ApproxNumerator

    kpMarginP7DenominatorRecorded :
      Nat

    kpMarginP7DenominatorRecordedIsCanonical :
      kpMarginP7DenominatorRecorded ≡ kpMarginP7ApproxDenominator

    physicalCouplingVerdict :
      PhysicalCouplingVerdict

    physicalCouplingFailsDirectly :
      physicalCouplingVerdict ≡ physicalFineLatticeBetaFailsP7Threshold

    physicalBetaNumeratorRecorded :
      Nat

    physicalBetaNumeratorRecordedIsCanonical :
      physicalBetaNumeratorRecorded ≡
      physicalFineLatticeBetaApproxNumerator

    physicalBetaDenominatorRecorded :
      Nat

    physicalBetaDenominatorRecordedIsCanonical :
      physicalBetaDenominatorRecorded ≡
      physicalFineLatticeBetaApproxDenominator

    rgCarrierCouplingVerdict :
      RGCarrierCouplingVerdict

    rgCarrierCouplingStillFails :
      rgCarrierCouplingVerdict ≡ oneLoopCarrierBetaStillFailsThreshold

    rgCarrierBetaNumeratorRecorded :
      Nat

    rgCarrierBetaNumeratorRecordedIsCanonical :
      rgCarrierBetaNumeratorRecorded ≡ rgFlowedCarrierBetaApproxNumerator

    rgCarrierBetaDenominatorRecorded :
      Nat

    rgCarrierBetaDenominatorRecordedIsCanonical :
      rgCarrierBetaDenominatorRecorded ≡ rgFlowedCarrierBetaApproxDenominator

    twoLoopCarrierCouplingVerdict :
      RGCarrierCouplingVerdict

    twoLoopCarrierCouplingStillFails :
      twoLoopCarrierCouplingVerdict ≡ twoLoopCarrierBetaStillFailsThreshold

    twoLoopCarrierBetaNumeratorRecorded :
      Nat

    twoLoopCarrierBetaNumeratorRecordedIsCanonical :
      twoLoopCarrierBetaNumeratorRecorded ≡ twoLoopCarrierBetaApproxNumerator

    twoLoopCarrierBetaDenominatorRecorded :
      Nat

    twoLoopCarrierBetaDenominatorRecordedIsCanonical :
      twoLoopCarrierBetaDenominatorRecorded ≡ twoLoopCarrierBetaApproxDenominator

    conditionalNonperturbativeCarrierCouplingVerdict :
      RGCarrierCouplingVerdict

    conditionalNonperturbativeCarrierPassesOnlyConditionally :
      conditionalNonperturbativeCarrierCouplingVerdict
      ≡
      nonperturbativeCarrierBetaPassesConditionally

    conditionalNonperturbativeCarrierBetaNumeratorRecorded :
      Nat

    conditionalNonperturbativeCarrierBetaNumeratorRecordedIsCanonical :
      conditionalNonperturbativeCarrierBetaNumeratorRecorded
      ≡
      conditionalNonperturbativeCarrierBetaNumerator

    conditionalNonperturbativeCarrierBetaDenominatorRecorded :
      Nat

    conditionalNonperturbativeCarrierBetaDenominatorRecordedIsCanonical :
      conditionalNonperturbativeCarrierBetaDenominatorRecorded
      ≡
      conditionalNonperturbativeCarrierBetaDenominator

    kpRequiresRGFlow :
      KPRequiresRGFlowStatus

    kpRequiresRGFlowIsCanonical :
      kpRequiresRGFlow ≡ balabanRGFlowIsNecessaryInput

    directPhysicalKPClaim :
      Bool

    directPhysicalKPClaimIsFalse :
      directPhysicalKPClaim ≡ false

    carrierScaleKPPassPromotedUnconditionally :
      Bool

    carrierScaleKPPassPromotedUnconditionallyIsFalse :
      carrierScaleKPPassPromotedUnconditionally ≡ false

    balabanRGProofPresent :
      Bool

    balabanRGProofPresentIsFalse :
      balabanRGProofPresent ≡ false

    nonperturbativeBalabanBridgePresent :
      Bool

    nonperturbativeBalabanBridgePresentIsFalse :
      nonperturbativeBalabanBridgePresent ≡ false

    continuumKPProved :
      Bool

    continuumKPProvedIsFalse :
      continuumKPProved ≡ false

    clayPromotionMade :
      Bool

    clayPromotionMadeIsFalse :
      clayPromotionMade ≡ false

    openObligations :
      List KPCouplingOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalKPCouplingOpenObligations

    nonClaims :
      List KPCouplingNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalKPCouplingNonClaims

    promotionFlags :
      List KPCouplingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    betaFormulaReading :
      String

    betaFormulaReadingIsCanonical :
      betaFormulaReading ≡ betaFormulaSummary

    p7ObstructionReading :
      String

    p7ObstructionReadingIsCanonical :
      p7ObstructionReading ≡ p7ObstructionSummary

    rgBoundaryReading :
      String

    rgBoundaryReadingIsCanonical :
      rgBoundaryReading ≡ rgBoundarySummary

    receiptBoundary :
      List String

open KPCouplingObstructionReceipt public

canonicalKPCouplingObstructionReceipt :
  KPCouplingObstructionReceipt
canonicalKPCouplingObstructionReceipt =
  record
    { status =
        btBranchingBetaObstructionRecorded
    ; statusIsCanonical =
        refl
    ; betaThresholdFormula =
        betaMinIncludesTreeBranchingLogP
    ; betaThresholdFormulaIsBTBranching =
        refl
    ; kpMarginThresholdFormula =
        kpMarginIncludesLogTwoP
    ; kpMarginThresholdFormulaIsLogTwoP =
        refl
    ; flatLatticeBetaVerdict =
        flatBetaPointThreeThreeRejectedForBTTreeKP
    ; flatLatticeBetaRejected =
        refl
    ; p7PrimeRecorded =
        p7Prime
    ; p7PrimeRecordedIsCanonical =
        refl
    ; aNumeratorRecorded =
        aBookkeepingNumerator
    ; aNumeratorRecordedIsCanonical =
        refl
    ; aDenominatorRecorded =
        aBookkeepingDenominator
    ; aDenominatorRecordedIsCanonical =
        refl
    ; cMinP7NumeratorRecorded =
        cMinP7ApproxNumerator
    ; cMinP7NumeratorRecordedIsCanonical =
        refl
    ; cMinP7DenominatorRecorded =
        cMinP7ApproxDenominator
    ; cMinP7DenominatorRecordedIsCanonical =
        refl
    ; betaMinP7NumeratorRecorded =
        betaMinP7ApproxNumerator
    ; betaMinP7NumeratorRecordedIsCanonical =
        refl
    ; betaMinP7DenominatorRecorded =
        betaMinP7ApproxDenominator
    ; betaMinP7DenominatorRecordedIsCanonical =
        refl
    ; kpMarginP7NumeratorRecorded =
        kpMarginP7ApproxNumerator
    ; kpMarginP7NumeratorRecordedIsCanonical =
        refl
    ; kpMarginP7DenominatorRecorded =
        kpMarginP7ApproxDenominator
    ; kpMarginP7DenominatorRecordedIsCanonical =
        refl
    ; physicalCouplingVerdict =
        physicalFineLatticeBetaFailsP7Threshold
    ; physicalCouplingFailsDirectly =
        refl
    ; physicalBetaNumeratorRecorded =
        physicalFineLatticeBetaApproxNumerator
    ; physicalBetaNumeratorRecordedIsCanonical =
        refl
    ; physicalBetaDenominatorRecorded =
        physicalFineLatticeBetaApproxDenominator
    ; physicalBetaDenominatorRecordedIsCanonical =
        refl
    ; rgCarrierCouplingVerdict =
        oneLoopCarrierBetaStillFailsThreshold
    ; rgCarrierCouplingStillFails =
        refl
    ; rgCarrierBetaNumeratorRecorded =
        rgFlowedCarrierBetaApproxNumerator
    ; rgCarrierBetaNumeratorRecordedIsCanonical =
        refl
    ; rgCarrierBetaDenominatorRecorded =
        rgFlowedCarrierBetaApproxDenominator
    ; rgCarrierBetaDenominatorRecordedIsCanonical =
        refl
    ; twoLoopCarrierCouplingVerdict =
        twoLoopCarrierBetaStillFailsThreshold
    ; twoLoopCarrierCouplingStillFails =
        refl
    ; twoLoopCarrierBetaNumeratorRecorded =
        twoLoopCarrierBetaApproxNumerator
    ; twoLoopCarrierBetaNumeratorRecordedIsCanonical =
        refl
    ; twoLoopCarrierBetaDenominatorRecorded =
        twoLoopCarrierBetaApproxDenominator
    ; twoLoopCarrierBetaDenominatorRecordedIsCanonical =
        refl
    ; conditionalNonperturbativeCarrierCouplingVerdict =
        nonperturbativeCarrierBetaPassesConditionally
    ; conditionalNonperturbativeCarrierPassesOnlyConditionally =
        refl
    ; conditionalNonperturbativeCarrierBetaNumeratorRecorded =
        conditionalNonperturbativeCarrierBetaNumerator
    ; conditionalNonperturbativeCarrierBetaNumeratorRecordedIsCanonical =
        refl
    ; conditionalNonperturbativeCarrierBetaDenominatorRecorded =
        conditionalNonperturbativeCarrierBetaDenominator
    ; conditionalNonperturbativeCarrierBetaDenominatorRecordedIsCanonical =
        refl
    ; kpRequiresRGFlow =
        balabanRGFlowIsNecessaryInput
    ; kpRequiresRGFlowIsCanonical =
        refl
    ; directPhysicalKPClaim =
        false
    ; directPhysicalKPClaimIsFalse =
        refl
    ; carrierScaleKPPassPromotedUnconditionally =
        false
    ; carrierScaleKPPassPromotedUnconditionallyIsFalse =
        refl
    ; balabanRGProofPresent =
        false
    ; balabanRGProofPresentIsFalse =
        refl
    ; nonperturbativeBalabanBridgePresent =
        false
    ; nonperturbativeBalabanBridgePresentIsFalse =
        refl
    ; continuumKPProved =
        false
    ; continuumKPProvedIsFalse =
        refl
    ; clayPromotionMade =
        false
    ; clayPromotionMadeIsFalse =
        refl
    ; openObligations =
        canonicalKPCouplingOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; nonClaims =
        canonicalKPCouplingNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; betaFormulaReading =
        betaFormulaSummary
    ; betaFormulaReadingIsCanonical =
        refl
    ; p7ObstructionReading =
        p7ObstructionSummary
    ; p7ObstructionReadingIsCanonical =
        refl
    ; rgBoundaryReading =
        rgBoundarySummary
    ; rgBoundaryReadingIsCanonical =
        refl
    ; receiptBoundary =
        "Records corrected BT-tree KP threshold betaMin(p) = (a + log p) / cMin(p)"
        ∷ "Records p=7 convergence threshold approximately 10.13, correcting the earlier flat-lattice 0.33 optimism"
        ∷ "Records stricter p=7 KP activity-absorption threshold approximately 13.64 from beta*cMin-a > log(2p)"
        ∷ "Records one-loop physical beta 6 as failing the direct p=7 tree threshold"
        ∷ "Records one-loop carrier-scale beta approximately 7.69, not 16.7, as still below the p=7 threshold"
        ∷ "Records the two-loop carrier-scale surface as still below threshold"
        ∷ "Records betaCarrier approximately 16.7 only as conditional/nonperturbative input requiring a Balaban RG bridge"
        ∷ "Makes Balaban/nonperturbative RG scale transfer a necessary obligation before any carrier KP claim is promoted"
        ∷ "No continuum KP theorem, Yang-Mills mass gap, or Clay promotion follows"
        ∷ []
    }

canonicalKPCouplingNeedsRG :
  kpRequiresRGFlow canonicalKPCouplingObstructionReceipt
  ≡
  balabanRGFlowIsNecessaryInput
canonicalKPCouplingNeedsRG =
  refl

canonicalKPCouplingNoDirectPhysicalKP :
  directPhysicalKPClaim canonicalKPCouplingObstructionReceipt ≡ false
canonicalKPCouplingNoDirectPhysicalKP =
  refl

canonicalKPCouplingNoClayPromotion :
  clayPromotionMade canonicalKPCouplingObstructionReceipt ≡ false
canonicalKPCouplingNoClayPromotion =
  refl
