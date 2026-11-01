module DASHI.Physics.Closure.BraidGroupedKPReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Braid-grouped KP bookkeeping receipt.
--
-- This receipt records a structural reorganization of the single p = 7
-- Bruhat-Tits KP polymer sum.  The p = 7 tree is 8-regular, while the
-- no-backtracking path count branches by p = 7 after an oriented edge is
-- fixed.  Braid/Yang-Baxter equivalence is used only to group path polymers
-- into braid/Lyndon-word classes.
--
-- The Lyndon 1/n grouping improves constants and logarithmic bookkeeping,
-- but it does not change the convergence radius or the retained beta_min
-- threshold.  The receipt is therefore structural, with only a small
-- candidate numerical improvement and no Clay promotion.

data BraidGroupedKPStatus : Set where
  btTreeBraidClassKPOrganizerRecorded :
    BraidGroupedKPStatus

data BTTreeOrganization : Set where
  p7BTTreeEightRegular :
    BTTreeOrganization

data NoBacktrackingBranching : Set where
  p7NoBacktrackingBranchingSeven :
    NoBacktrackingBranching

data PolymerOrganization : Set where
  pathPolymersOrganizedByBTTreeAndBraidClasses :
    PolymerOrganization

data BraidYangBaxterGrouping : Set where
  braidYangBaxterEquivalenceGroupsPathPolymers :
    BraidYangBaxterGrouping

data LyndonWordGrouping : Set where
  braidClassesIndexedByLyndonWordRepresentatives :
    LyndonWordGrouping

data LyndonFactor : Set where
  oneOverLengthLyndonGroupingRecorded :
    LyndonFactor

data ConvergenceRadiusVerdict : Set where
  lyndonGroupingDoesNotChangeConvergenceRadius :
    ConvergenceRadiusVerdict

data BetaMinVerdict : Set where
  betaMinThresholdRetained :
    BetaMinVerdict

data NumericalImprovementStatus : Set where
  smallCandidateConstantImprovementOnly :
    NumericalImprovementStatus

data BraidGroupedKPClaim : Set where
  recordsP7EightRegularBTTree :
    BraidGroupedKPClaim

  recordsP7NoBacktrackingBranching :
    BraidGroupedKPClaim

  recordsPathPolymerBraidClassOrganization :
    BraidGroupedKPClaim

  recordsYangBaxterEquivalenceAsGrouping :
    BraidGroupedKPClaim

  recordsLyndonOneOverNBookkeeping :
    BraidGroupedKPClaim

  recordsBetaMinRetained :
    BraidGroupedKPClaim

canonicalBraidGroupedKPClaims :
  List BraidGroupedKPClaim
canonicalBraidGroupedKPClaims =
  recordsP7EightRegularBTTree
  ∷ recordsP7NoBacktrackingBranching
  ∷ recordsPathPolymerBraidClassOrganization
  ∷ recordsYangBaxterEquivalenceAsGrouping
  ∷ recordsLyndonOneOverNBookkeeping
  ∷ recordsBetaMinRetained
  ∷ []

data BraidGroupedKPNonClaim : Set where
  noImprovedConvergenceRadius :
    BraidGroupedKPNonClaim

  noLoweredBetaMin :
    BraidGroupedKPNonClaim

  noYangBaxterKPProof :
    BraidGroupedKPNonClaim

  noContinuumKPTheorem :
    BraidGroupedKPNonClaim

  noBalabanRGConvergenceTheorem :
    BraidGroupedKPNonClaim

  noClayPromotion :
    BraidGroupedKPNonClaim

canonicalBraidGroupedKPNonClaims :
  List BraidGroupedKPNonClaim
canonicalBraidGroupedKPNonClaims =
  noImprovedConvergenceRadius
  ∷ noLoweredBetaMin
  ∷ noYangBaxterKPProof
  ∷ noContinuumKPTheorem
  ∷ noBalabanRGConvergenceTheorem
  ∷ noClayPromotion
  ∷ []

data BraidGroupedKPObligation : Set where
  proveConcreteBraidEquivalenceRelationOnCarrierPaths :
    BraidGroupedKPObligation

  proveYangBaxterMovesPreserveKPActivity :
    BraidGroupedKPObligation

  quantifyLyndonConstantGainForP7 :
    BraidGroupedKPObligation

  keepBetaMinComparisonAgainstUngroupedTreeTail :
    BraidGroupedKPObligation

canonicalBraidGroupedKPObligations :
  List BraidGroupedKPObligation
canonicalBraidGroupedKPObligations =
  proveConcreteBraidEquivalenceRelationOnCarrierPaths
  ∷ proveYangBaxterMovesPreserveKPActivity
  ∷ quantifyLyndonConstantGainForP7
  ∷ keepBetaMinComparisonAgainstUngroupedTreeTail
  ∷ []

data ClayPromotion : Set where

clayPromotionImpossibleHere :
  ClayPromotion →
  ⊥
clayPromotionImpossibleHere ()

p7Prime :
  Nat
p7Prime =
  7

p7BTValency :
  Nat
p7BTValency =
  8

p7NoBacktrackingBranchingFactor :
  Nat
p7NoBacktrackingBranchingFactor =
  7

lyndonGroupingNumerator :
  Nat
lyndonGroupingNumerator =
  1

lyndonGroupingDenominatorSymbolicLength :
  String
lyndonGroupingDenominatorSymbolicLength =
  "n"

p7BetaMinNumerator :
  Nat
p7BetaMinNumerator =
  1013

p7BetaMinDenominator :
  Nat
p7BetaMinDenominator =
  100

btTreeBraidClassSummary :
  String
btTreeBraidClassSummary =
  "The p=7 Bruhat-Tits tree is 8-regular; no-backtracking path polymers branch by 7 after an oriented edge is fixed."

braidYangBaxterSummary :
  String
braidYangBaxterSummary =
  "Braid/Yang-Baxter equivalence is used as a class-grouping of path polymers by braid and Lyndon-word representatives."

lyndonBookkeepingSummary :
  String
lyndonBookkeepingSummary =
  "The Lyndon 1/n grouping improves constants and log bookkeeping but leaves the convergence radius and beta_min unchanged."

promotionBoundarySummary :
  String
promotionBoundarySummary =
  "This is a structural organizer with only a small candidate numerical improvement; no Clay promotion is made."

record BraidGroupedKPReceipt : Setω where
  field
    status :
      BraidGroupedKPStatus

    statusIsCanonical :
      status ≡ btTreeBraidClassKPOrganizerRecorded

    btTreeOrganization :
      BTTreeOrganization

    btTreeOrganizationIsP7EightRegular :
      btTreeOrganization ≡ p7BTTreeEightRegular

    p7PrimeRecorded :
      Nat

    p7PrimeRecordedIsCanonical :
      p7PrimeRecorded ≡ p7Prime

    p7ValencyRecorded :
      Nat

    p7ValencyRecordedIsCanonical :
      p7ValencyRecorded ≡ p7BTValency

    noBacktrackingBranching :
      NoBacktrackingBranching

    noBacktrackingBranchingIsP7 :
      noBacktrackingBranching ≡ p7NoBacktrackingBranchingSeven

    p7NoBacktrackingBranchingRecorded :
      Nat

    p7NoBacktrackingBranchingRecordedIsCanonical :
      p7NoBacktrackingBranchingRecorded
      ≡
      p7NoBacktrackingBranchingFactor

    polymerOrganization :
      PolymerOrganization

    polymerOrganizationIsBTTreeBraidClass :
      polymerOrganization
      ≡
      pathPolymersOrganizedByBTTreeAndBraidClasses

    braidYangBaxterGrouping :
      BraidYangBaxterGrouping

    braidYangBaxterGroupingIsPathClassGrouping :
      braidYangBaxterGrouping
      ≡
      braidYangBaxterEquivalenceGroupsPathPolymers

    lyndonWordGrouping :
      LyndonWordGrouping

    lyndonWordGroupingIsRepresentativeIndexing :
      lyndonWordGrouping
      ≡
      braidClassesIndexedByLyndonWordRepresentatives

    lyndonFactor :
      LyndonFactor

    lyndonFactorIsOneOverLength :
      lyndonFactor ≡ oneOverLengthLyndonGroupingRecorded

    lyndonGroupingNumeratorRecorded :
      Nat

    lyndonGroupingNumeratorRecordedIsCanonical :
      lyndonGroupingNumeratorRecorded ≡ lyndonGroupingNumerator

    lyndonGroupingDenominatorRecorded :
      String

    lyndonGroupingDenominatorRecordedIsLength :
      lyndonGroupingDenominatorRecorded
      ≡
      lyndonGroupingDenominatorSymbolicLength

    convergenceRadiusVerdict :
      ConvergenceRadiusVerdict

    convergenceRadiusVerdictIsUnchanged :
      convergenceRadiusVerdict
      ≡
      lyndonGroupingDoesNotChangeConvergenceRadius

    betaMinVerdict :
      BetaMinVerdict

    betaMinVerdictIsRetained :
      betaMinVerdict ≡ betaMinThresholdRetained

    p7BetaMinNumeratorRecorded :
      Nat

    p7BetaMinNumeratorRecordedIsCanonical :
      p7BetaMinNumeratorRecorded ≡ p7BetaMinNumerator

    p7BetaMinDenominatorRecorded :
      Nat

    p7BetaMinDenominatorRecordedIsCanonical :
      p7BetaMinDenominatorRecorded ≡ p7BetaMinDenominator

    structuralOrganizer :
      Bool

    structuralOrganizerIsTrue :
      structuralOrganizer ≡ true

    constantsAndLogBookkeepingImproved :
      Bool

    constantsAndLogBookkeepingImprovedIsTrue :
      constantsAndLogBookkeepingImproved ≡ true

    numericalImprovementStatus :
      NumericalImprovementStatus

    numericalImprovementStatusIsSmallCandidate :
      numericalImprovementStatus
      ≡
      smallCandidateConstantImprovementOnly

    convergenceRadiusImproved :
      Bool

    convergenceRadiusImprovedIsFalse :
      convergenceRadiusImproved ≡ false

    betaMinLowered :
      Bool

    betaMinLoweredIsFalse :
      betaMinLowered ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    claims :
      List BraidGroupedKPClaim

    claimsAreCanonical :
      claims ≡ canonicalBraidGroupedKPClaims

    nonClaims :
      List BraidGroupedKPNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalBraidGroupedKPNonClaims

    obligations :
      List BraidGroupedKPObligation

    obligationsAreCanonical :
      obligations ≡ canonicalBraidGroupedKPObligations

    promotionFlags :
      List ClayPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    btTreeBraidClassReading :
      String

    btTreeBraidClassReadingIsCanonical :
      btTreeBraidClassReading ≡ btTreeBraidClassSummary

    braidYangBaxterReading :
      String

    braidYangBaxterReadingIsCanonical :
      braidYangBaxterReading ≡ braidYangBaxterSummary

    lyndonBookkeepingReading :
      String

    lyndonBookkeepingReadingIsCanonical :
      lyndonBookkeepingReading ≡ lyndonBookkeepingSummary

    promotionBoundaryReading :
      String

    promotionBoundaryReadingIsCanonical :
      promotionBoundaryReading ≡ promotionBoundarySummary

    receiptBoundary :
      List String

open BraidGroupedKPReceipt public

canonicalBraidGroupedKPReceipt :
  BraidGroupedKPReceipt
canonicalBraidGroupedKPReceipt =
  record
    { status =
        btTreeBraidClassKPOrganizerRecorded
    ; statusIsCanonical =
        refl
    ; btTreeOrganization =
        p7BTTreeEightRegular
    ; btTreeOrganizationIsP7EightRegular =
        refl
    ; p7PrimeRecorded =
        p7Prime
    ; p7PrimeRecordedIsCanonical =
        refl
    ; p7ValencyRecorded =
        p7BTValency
    ; p7ValencyRecordedIsCanonical =
        refl
    ; noBacktrackingBranching =
        p7NoBacktrackingBranchingSeven
    ; noBacktrackingBranchingIsP7 =
        refl
    ; p7NoBacktrackingBranchingRecorded =
        p7NoBacktrackingBranchingFactor
    ; p7NoBacktrackingBranchingRecordedIsCanonical =
        refl
    ; polymerOrganization =
        pathPolymersOrganizedByBTTreeAndBraidClasses
    ; polymerOrganizationIsBTTreeBraidClass =
        refl
    ; braidYangBaxterGrouping =
        braidYangBaxterEquivalenceGroupsPathPolymers
    ; braidYangBaxterGroupingIsPathClassGrouping =
        refl
    ; lyndonWordGrouping =
        braidClassesIndexedByLyndonWordRepresentatives
    ; lyndonWordGroupingIsRepresentativeIndexing =
        refl
    ; lyndonFactor =
        oneOverLengthLyndonGroupingRecorded
    ; lyndonFactorIsOneOverLength =
        refl
    ; lyndonGroupingNumeratorRecorded =
        lyndonGroupingNumerator
    ; lyndonGroupingNumeratorRecordedIsCanonical =
        refl
    ; lyndonGroupingDenominatorRecorded =
        lyndonGroupingDenominatorSymbolicLength
    ; lyndonGroupingDenominatorRecordedIsLength =
        refl
    ; convergenceRadiusVerdict =
        lyndonGroupingDoesNotChangeConvergenceRadius
    ; convergenceRadiusVerdictIsUnchanged =
        refl
    ; betaMinVerdict =
        betaMinThresholdRetained
    ; betaMinVerdictIsRetained =
        refl
    ; p7BetaMinNumeratorRecorded =
        p7BetaMinNumerator
    ; p7BetaMinNumeratorRecordedIsCanonical =
        refl
    ; p7BetaMinDenominatorRecorded =
        p7BetaMinDenominator
    ; p7BetaMinDenominatorRecordedIsCanonical =
        refl
    ; structuralOrganizer =
        true
    ; structuralOrganizerIsTrue =
        refl
    ; constantsAndLogBookkeepingImproved =
        true
    ; constantsAndLogBookkeepingImprovedIsTrue =
        refl
    ; numericalImprovementStatus =
        smallCandidateConstantImprovementOnly
    ; numericalImprovementStatusIsSmallCandidate =
        refl
    ; convergenceRadiusImproved =
        false
    ; convergenceRadiusImprovedIsFalse =
        refl
    ; betaMinLowered =
        false
    ; betaMinLoweredIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; claims =
        canonicalBraidGroupedKPClaims
    ; claimsAreCanonical =
        refl
    ; nonClaims =
        canonicalBraidGroupedKPNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; obligations =
        canonicalBraidGroupedKPObligations
    ; obligationsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; btTreeBraidClassReading =
        btTreeBraidClassSummary
    ; btTreeBraidClassReadingIsCanonical =
        refl
    ; braidYangBaxterReading =
        braidYangBaxterSummary
    ; braidYangBaxterReadingIsCanonical =
        refl
    ; lyndonBookkeepingReading =
        lyndonBookkeepingSummary
    ; lyndonBookkeepingReadingIsCanonical =
        refl
    ; promotionBoundaryReading =
        promotionBoundarySummary
    ; promotionBoundaryReadingIsCanonical =
        refl
    ; receiptBoundary =
        btTreeBraidClassSummary
        ∷ braidYangBaxterSummary
        ∷ lyndonBookkeepingSummary
        ∷ promotionBoundarySummary
        ∷ []
    }

canonicalBraidGroupedKPStructuralOrganizer :
  structuralOrganizer canonicalBraidGroupedKPReceipt ≡ true
canonicalBraidGroupedKPStructuralOrganizer =
  refl

canonicalBraidGroupedKPBetaMinRetained :
  betaMinLowered canonicalBraidGroupedKPReceipt ≡ false
canonicalBraidGroupedKPBetaMinRetained =
  refl

canonicalBraidGroupedKPNoClayPromotion :
  clayPromoted canonicalBraidGroupedKPReceipt ≡ false
canonicalBraidGroupedKPNoClayPromotion =
  refl
