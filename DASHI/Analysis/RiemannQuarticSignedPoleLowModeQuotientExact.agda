module DASHI.Analysis.RiemannQuarticSignedPoleLowModeQuotientExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH G3 LOW-MODE QUOTIENT DIAGNOSTIC
--
-- Lean companion:
--
--   Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourthOrderQuotient.lean
--
-- The centered quartic jet is local information.  It does not by itself
-- imply that the global/symmetric Abel consumer is invariant under every
-- centered polynomial of degree <= 3.
--
-- The exact symmetric consumer does factor through the even low-mode
-- quotient
--
--   E ~ E + a0 + a2 (x-t)^2
--
-- because Psi_t' is odd about t.  A full cubic quotient additionally
-- requires the centered-linear and centered-cubic mode defects to vanish.
-- Those are retained as explicit analytic obstructions, not silently
-- promoted from the local jet.
------------------------------------------------------------------------

data LowModeQuotientCoordinate : Set where
  centeredDerivativeOdd : LowModeQuotientCoordinate
  constantModeInvisible : LowModeQuotientCoordinate
  quadraticModeInvisible : LowModeQuotientCoordinate
  evenLowModeFactorisation : LowModeQuotientCoordinate
  c4CarrierRegularity : LowModeQuotientCoordinate
  inverseFourthPsiDecay : LowModeQuotientCoordinate
  globalOddDefectsWellPosed : LowModeQuotientCoordinate
  globalLinearDefectZero : LowModeQuotientCoordinate
  globalCubicDefectZero : LowModeQuotientCoordinate
  linearModeDefect : LowModeQuotientCoordinate
  cubicModeDefect : LowModeQuotientCoordinate
  fullCubicFactorisation : LowModeQuotientCoordinate
  localJetImpliesGlobalCubicFactorisation : LowModeQuotientCoordinate

data LowModeQuotientStatus : Set where
  theoremOwned : LowModeQuotientStatus
  openAnalyticObstruction : LowModeQuotientStatus
  rejectedPromotion : LowModeQuotientStatus

lowModeQuotientStatus :
  LowModeQuotientCoordinate -> LowModeQuotientStatus
lowModeQuotientStatus centeredDerivativeOdd = theoremOwned
lowModeQuotientStatus constantModeInvisible = theoremOwned
lowModeQuotientStatus quadraticModeInvisible = theoremOwned
lowModeQuotientStatus evenLowModeFactorisation = theoremOwned
lowModeQuotientStatus c4CarrierRegularity = theoremOwned
lowModeQuotientStatus inverseFourthPsiDecay = theoremOwned
lowModeQuotientStatus globalOddDefectsWellPosed = theoremOwned
lowModeQuotientStatus globalLinearDefectZero = openAnalyticObstruction
lowModeQuotientStatus globalCubicDefectZero = openAnalyticObstruction
lowModeQuotientStatus linearModeDefect = openAnalyticObstruction
lowModeQuotientStatus cubicModeDefect = openAnalyticObstruction
lowModeQuotientStatus fullCubicFactorisation = openAnalyticObstruction
lowModeQuotientStatus localJetImpliesGlobalCubicFactorisation = rejectedPromotion

record QuarticSignedPoleLowModeQuotientBoundary : Set where
  constructor quartic-signed-pole-low-mode-quotient-boundary
  field
    signedPsiDerivativeOddAboutTargetPaid : Bool
    constantDiscrepancyModeInvisiblePaid : Bool
    centeredQuadraticDiscrepancyModeInvisiblePaid : Bool
    evenLowModeQuotientFactorisationPaid : Bool
    c4CarrierRegularityPaid : Bool
    inverseFourthPsiDecayPaid : Bool
    globalOddDefectsWellPosedPaid : Bool
    globalLinearDefectZeroPaid : Bool
    globalCubicDefectZeroPaid : Bool

    centeredLinearModeDefectPaid : Bool
    centeredCubicModeDefectPaid : Bool
    fullCenteredCubicQuotientPaid : Bool

    localCenteredJetAloneProvesGlobalCubicQuotient : Bool
    fullCubicQuotientReducesToOddModeDefects : Bool

    signedPsiDerivativeOddAboutTargetPaidIsTrue :
      signedPsiDerivativeOddAboutTargetPaid ≡ true
    constantDiscrepancyModeInvisiblePaidIsTrue :
      constantDiscrepancyModeInvisiblePaid ≡ true
    centeredQuadraticDiscrepancyModeInvisiblePaidIsTrue :
      centeredQuadraticDiscrepancyModeInvisiblePaid ≡ true
    evenLowModeQuotientFactorisationPaidIsTrue :
      evenLowModeQuotientFactorisationPaid ≡ true
    c4CarrierRegularityPaidIsTrue :
      c4CarrierRegularityPaid ≡ true
    inverseFourthPsiDecayPaidIsTrue :
      inverseFourthPsiDecayPaid ≡ true
    globalOddDefectsWellPosedPaidIsTrue :
      globalOddDefectsWellPosedPaid ≡ true
    globalLinearDefectZeroPaidIsFalse :
      globalLinearDefectZeroPaid ≡ false
    globalCubicDefectZeroPaidIsFalse :
      globalCubicDefectZeroPaid ≡ false

    centeredLinearModeDefectPaidIsFalse :
      centeredLinearModeDefectPaid ≡ false
    centeredCubicModeDefectPaidIsFalse :
      centeredCubicModeDefectPaid ≡ false
    fullCenteredCubicQuotientPaidIsFalse :
      fullCenteredCubicQuotientPaid ≡ false

    localCenteredJetAloneProvesGlobalCubicQuotientIsFalse :
      localCenteredJetAloneProvesGlobalCubicQuotient ≡ false
    fullCubicQuotientReducesToOddModeDefectsIsTrue :
      fullCubicQuotientReducesToOddModeDefects ≡ true

    interpretation : String
    nextResearchCut : String

canonicalQuarticSignedPoleLowModeQuotientBoundary :
  QuarticSignedPoleLowModeQuotientBoundary
canonicalQuarticSignedPoleLowModeQuotientBoundary =
  quartic-signed-pole-low-mode-quotient-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    true
    refl refl refl refl refl refl refl
    refl refl
    refl refl refl
    refl refl
    "The preferred symmetric Abel consumer is exactly invariant under adding a constant plus a centered quadratic discrepancy mode.  This is a genuine FactorsThrough result supplied by target-centred parity.  The local vanishing jet of Psi_t at t must not be promoted to invariance under arbitrary centered cubics.  The Lean companion now lifts the smooth bump carrier to C4, proves inverse-fourth decay for the actual Psi_t, makes the weighted cubic Psi moment globally integrable, and proves that the finite odd mode defects converge to concrete global Psi moments.  Their existence is paid; their vanishing is not."
    "The full global cubic quotient is now equivalent to two exact global equations: the global linear defect -integral Psi_t must vanish and the global cubic defect -3*integral Psi_t(x)*(x-t)^2 must vanish.  Investigate whether either equation follows from a same-object Fourier-inversion/profile identity, or whether cancellation only appears after coupling these obstruction coordinates to H_comb.  Do not infer either equation from the centered jet."

evenLowModeFactorisationIsPaid :
  lowModeQuotientStatus evenLowModeFactorisation ≡ theoremOwned
evenLowModeFactorisationIsPaid = refl

linearModeRemainsOpen :
  lowModeQuotientStatus linearModeDefect ≡ openAnalyticObstruction
linearModeRemainsOpen = refl

cubicModeRemainsOpen :
  lowModeQuotientStatus cubicModeDefect ≡ openAnalyticObstruction
cubicModeRemainsOpen = refl

localJetToGlobalCubicPromotionRejected :
  lowModeQuotientStatus localJetImpliesGlobalCubicFactorisation ≡ rejectedPromotion
localJetToGlobalCubicPromotionRejected = refl


------------------------------------------------------------------------
-- FOURIER-DUAL PROFILE OBSTRUCTION OWNER
--
-- The Lean companion now identifies the two global odd defects with local
-- coordinates of the exact signed combined projective profile:
--
--   D1∞ = -(2π/(t/16)) * Pcomb(0)
--   D3∞ =  6π(t/16)   * Pcomb''(0)
--
-- Hence the proposed full cubic quotient exists iff both local profile
-- coordinates vanish.  The first coordinate factors further through a
-- distinct on-line-response determinant because all off-centre taper windows
-- vanish at u=0 for R<1.  None of these vanishings is supplied by the paid
-- pole determinant.
------------------------------------------------------------------------

data ProfileObstructionCoordinate : Set where
  linearFourierDualIdentity : ProfileObstructionCoordinate
  cubicFourierDualIdentity : ProfileObstructionCoordinate
  fullCubicIffProfileCoordinatesZero : ProfileObstructionCoordinate
  explicitLinearProfileDeterminant : ProfileObstructionCoordinate
  explicitCubicProfileDeterminant : ProfileObstructionCoordinate
  centralWindowLinearFactorisation : ProfileObstructionCoordinate
  linearOnLineObstructionZero : ProfileObstructionCoordinate
  cubicProfileObstructionZero : ProfileObstructionCoordinate
  poleDeterminantForcesProfileObstructions : ProfileObstructionCoordinate

data ProfileObstructionStatus : Set where
  theoremOwned : ProfileObstructionStatus
  openAnalyticObstruction : ProfileObstructionStatus
  rejectedImplication : ProfileObstructionStatus

profileObstructionStatus :
  ProfileObstructionCoordinate -> ProfileObstructionStatus
profileObstructionStatus linearFourierDualIdentity = theoremOwned
profileObstructionStatus cubicFourierDualIdentity = theoremOwned
profileObstructionStatus fullCubicIffProfileCoordinatesZero = theoremOwned
profileObstructionStatus explicitLinearProfileDeterminant = theoremOwned
profileObstructionStatus explicitCubicProfileDeterminant = theoremOwned
profileObstructionStatus centralWindowLinearFactorisation = theoremOwned
profileObstructionStatus linearOnLineObstructionZero = openAnalyticObstruction
profileObstructionStatus cubicProfileObstructionZero = openAnalyticObstruction
profileObstructionStatus poleDeterminantForcesProfileObstructions = rejectedImplication

record QuarticSignedPoleProfileObstructionBoundary : Set where
  constructor quartic-signed-pole-profile-obstruction-boundary
  field
    linearFourierDualIdentityPaid : Bool
    cubicFourierDualIdentityPaid : Bool
    fullCubicIffProfileCoordinatesZeroPaid : Bool
    explicitLinearProfileDeterminantPaid : Bool
    explicitCubicProfileDeterminantPaid : Bool
    centralWindowLinearFactorisationPaid : Bool

    linearOnLineObstructionZeroPaid : Bool
    cubicProfileObstructionZeroPaid : Bool
    poleDeterminantAloneForcesBothProfileObstructions : Bool

    linearFourierDualIdentityPaidIsTrue :
      linearFourierDualIdentityPaid ≡ true
    cubicFourierDualIdentityPaidIsTrue :
      cubicFourierDualIdentityPaid ≡ true
    fullCubicIffProfileCoordinatesZeroPaidIsTrue :
      fullCubicIffProfileCoordinatesZeroPaid ≡ true
    explicitLinearProfileDeterminantPaidIsTrue :
      explicitLinearProfileDeterminantPaid ≡ true
    explicitCubicProfileDeterminantPaidIsTrue :
      explicitCubicProfileDeterminantPaid ≡ true
    centralWindowLinearFactorisationPaidIsTrue :
      centralWindowLinearFactorisationPaid ≡ true

    linearOnLineObstructionZeroPaidIsFalse :
      linearOnLineObstructionZeroPaid ≡ false
    cubicProfileObstructionZeroPaidIsFalse :
      cubicProfileObstructionZeroPaid ≡ false
    poleDeterminantAloneForcesBothProfileObstructionsIsFalse :
      poleDeterminantAloneForcesBothProfileObstructions ≡ false

    interpretation : String
    nextResearchCut : String

canonicalQuarticSignedPoleProfileObstructionBoundary :
  QuarticSignedPoleProfileObstructionBoundary
canonicalQuarticSignedPoleProfileObstructionBoundary =
  quartic-signed-pole-profile-obstruction-boundary
    true true true true true true
    false false false
    refl refl refl refl refl refl
    refl refl refl
    "The global odd quotient defects are now exact Fourier-dual local coordinates of the signed combined profile.  Full cubic factorisation is equivalent to Pcomb(0)=0 and Pcomb''(0)=0.  The linear coordinate factors further through a separate on-line-response determinant because the endpoint tapers share the same positive central-window value for R<1.  The paid pole cancellation is a different determinant and must not be promoted to either profile-coordinate vanishing."
    "Investigate the two remaining local obstruction determinants themselves, especially the cubic endpoint curvature coordinate, and only then ask whether a coupled completed-residual mechanism can use them.  Do not treat the fourth-order quotient as paid unless both obstruction determinants vanish."

profileObstructionCriterionIsPaid :
  profileObstructionStatus fullCubicIffProfileCoordinatesZero ≡ theoremOwned
profileObstructionCriterionIsPaid = refl

linearOnLineObstructionRemainsOpen :
  profileObstructionStatus linearOnLineObstructionZero ≡ openAnalyticObstruction
linearOnLineObstructionRemainsOpen = refl

cubicProfileObstructionRemainsOpen :
  profileObstructionStatus cubicProfileObstructionZero ≡ openAnalyticObstruction
cubicProfileObstructionRemainsOpen = refl

poleToProfilePromotionRejected :
  profileObstructionStatus poleDeterminantForcesProfileObstructions ≡ rejectedImplication
poleToProfilePromotionRejected = refl


------------------------------------------------------------------------
-- ATOMIC QUOTIENT OBSTRUCTION RECEIPT
--
-- On the exact J2-null atomic endpoints the Lean companion proves, for every
-- t>=200,
--
--   linearOnLineAtomic(t) < 0
--   cubicOnLineAtomic(t)  > 0.
--
-- Hence the full cubic quotient is not an identity of the present atomic
-- signed-pole architecture.  This is a structural diagnostic, not an RH
-- theorem: smoothing/coupling may still introduce different mechanisms.
------------------------------------------------------------------------

data AtomicQuotientCoordinate : Set where
  atomicLinearObstructionNegative : AtomicQuotientCoordinate
  atomicCubicObstructionPositive : AtomicQuotientCoordinate
  atomicFullCubicQuotientHolds : AtomicQuotientCoordinate
  paidPoleAndMomentConstraintsImplyAtomicFullCubicQuotient :
    AtomicQuotientCoordinate

data AtomicQuotientStatus : Set where
  theoremOwned : AtomicQuotientStatus
  rejectedIdentity : AtomicQuotientStatus
  rejectedImplication : AtomicQuotientStatus

atomicQuotientStatus :
  AtomicQuotientCoordinate -> AtomicQuotientStatus
atomicQuotientStatus atomicLinearObstructionNegative = theoremOwned
atomicQuotientStatus atomicCubicObstructionPositive = theoremOwned
atomicQuotientStatus atomicFullCubicQuotientHolds = rejectedIdentity
atomicQuotientStatus
  paidPoleAndMomentConstraintsImplyAtomicFullCubicQuotient =
  rejectedImplication

record QuarticSignedPoleAtomicQuotientBoundary : Set where
  constructor quartic-signed-pole-atomic-quotient-boundary
  field
    atomicLinearObstructionNegativePaid : Bool
    atomicCubicObstructionPositivePaid : Bool
    atomicFullCubicQuotientHolds : Bool
    paidPoleAndMomentConstraintsImplyAtomicFullCubicQuotient : Bool

    atomicLinearObstructionNegativePaidIsTrue :
      atomicLinearObstructionNegativePaid ≡ true
    atomicCubicObstructionPositivePaidIsTrue :
      atomicCubicObstructionPositivePaid ≡ true
    atomicFullCubicQuotientHoldsIsFalse :
      atomicFullCubicQuotientHolds ≡ false
    paidPoleAndMomentConstraintsImplyAtomicFullCubicQuotientIsFalse :
      paidPoleAndMomentConstraintsImplyAtomicFullCubicQuotient ≡ false

    interpretation : String
    nextResearchCut : String

canonicalQuarticSignedPoleAtomicQuotientBoundary :
  QuarticSignedPoleAtomicQuotientBoundary
canonicalQuarticSignedPoleAtomicQuotientBoundary =
  quartic-signed-pole-atomic-quotient-boundary
    true true false false
    refl refl refl refl
    "At the exact atomic J2-null endpoints, the two Fourier-dual odd quotient coordinates are separated from zero with opposite signs throughout t>=200.  Therefore the full centered-cubic quotient is not an identity already encoded by the paid J2/J4/pole constraints."
    "Transport the sign separation to sufficiently narrow smooth endpoints.  If that survives on the actual G1 witness corridor, retire full cubic factorisation as a proof mechanism for the present signed-pole lane and investigate only genuinely coupled cancellation with the horizontal remainder or a modified witness family."

atomicLinearSignPaid :
  atomicQuotientStatus atomicLinearObstructionNegative ≡ theoremOwned
atomicLinearSignPaid = refl

atomicCubicSignPaid :
  atomicQuotientStatus atomicCubicObstructionPositive ≡ theoremOwned
atomicCubicSignPaid = refl

atomicFullCubicIdentityRejected :
  atomicQuotientStatus atomicFullCubicQuotientHolds ≡ rejectedIdentity
atomicFullCubicIdentityRejected = refl



------------------------------------------------------------------------
-- NARROW SMOOTH CORRIDOR OBSTRUCTION RECEIPT
--
-- Lean companion now transports the atomic linear obstruction through:
--
--   atomic mu-corridor robustness
--   + smooth pole localization
--   + smooth on-line pairing localization.
--
-- For every t>=200 there is a radius d(t)>0 such that every sufficiently
-- narrow endpoint pair in the witness corridors has
--
--   linearOnLineObstruction < -1/100.
--
-- It then constructs a genuine strength-floor signed-pole witness inside
-- that radius and proves that witness does not satisfy the full cubic
-- quotient.
------------------------------------------------------------------------

data SmoothQuotientDiagnosticCoordinate : Set where
  atomicLinearSignStableOnMuCorridor : SmoothQuotientDiagnosticCoordinate
  smoothLinearSignStableForSmallRadius : SmoothQuotientDiagnosticCoordinate
  strengthFloorWitnessWithLinearObstruction : SmoothQuotientDiagnosticCoordinate
  strengthFloorWitnessHasFullCubicQuotient : SmoothQuotientDiagnosticCoordinate

data SmoothQuotientDiagnosticStatus : Set where
  theoremOwned : SmoothQuotientDiagnosticStatus
  rejectedExistentialIdentity : SmoothQuotientDiagnosticStatus

smoothQuotientDiagnosticStatus :
  SmoothQuotientDiagnosticCoordinate -> SmoothQuotientDiagnosticStatus
smoothQuotientDiagnosticStatus atomicLinearSignStableOnMuCorridor =
  theoremOwned
smoothQuotientDiagnosticStatus smoothLinearSignStableForSmallRadius =
  theoremOwned
smoothQuotientDiagnosticStatus strengthFloorWitnessWithLinearObstruction =
  theoremOwned
smoothQuotientDiagnosticStatus strengthFloorWitnessHasFullCubicQuotient =
  rejectedExistentialIdentity

record QuarticSignedPoleSmoothQuotientDiagnosticBoundary : Set where
  constructor quartic-signed-pole-smooth-quotient-diagnostic-boundary
  field
    atomicLinearSignStableOnMuCorridorPaid : Bool
    smoothLinearSignStableForSmallRadiusPaid : Bool
    strengthFloorWitnessWithLinearObstructionPaid : Bool
    everyStrengthFloorWitnessHasFullCubicQuotient : Bool

    atomicLinearSignStableOnMuCorridorPaidIsTrue :
      atomicLinearSignStableOnMuCorridorPaid ≡ true
    smoothLinearSignStableForSmallRadiusPaidIsTrue :
      smoothLinearSignStableForSmallRadiusPaid ≡ true
    strengthFloorWitnessWithLinearObstructionPaidIsTrue :
      strengthFloorWitnessWithLinearObstructionPaid ≡ true
    everyStrengthFloorWitnessHasFullCubicQuotientIsFalse :
      everyStrengthFloorWitnessHasFullCubicQuotient ≡ false

    interpretation : String
    nextResearchCut : String

canonicalQuarticSignedPoleSmoothQuotientDiagnosticBoundary :
  QuarticSignedPoleSmoothQuotientDiagnosticBoundary
canonicalQuarticSignedPoleSmoothQuotientDiagnosticBoundary =
  quartic-signed-pole-smooth-quotient-diagnostic-boundary
    true true true false
    refl refl refl refl
    "The linear odd-mode obstruction is not an artifact of the atomic idealisation.  It remains strictly negative throughout a sufficiently narrow smooth witness corridor, and one can choose a genuine target-strength-floor G1 witness inside that corridor.  That witness provably does not satisfy the proposed full centered-cubic quotient."
    "Retire full cubic quotient factorisation as an automatic cancellation mechanism for the present narrow signed-pole lane.  Preserve the exact odd obstruction coordinates and investigate whether they participate in a joint cancellation with the horizontal remainder, or whether a modified witness family must impose the two on-line determinant equations as additional design constraints."

smoothLinearObstructionTransportPaid :
  smoothQuotientDiagnosticStatus smoothLinearSignStableForSmallRadius
    ≡ theoremOwned
smoothLinearObstructionTransportPaid = refl

strengthFloorCounterexampleToFullCubicQuotientPaid :
  smoothQuotientDiagnosticStatus strengthFloorWitnessHasFullCubicQuotient
    ≡ rejectedExistentialIdentity
strengthFloorCounterexampleToFullCubicQuotientPaid = refl

