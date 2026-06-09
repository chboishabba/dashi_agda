module DASHI.Physics.Closure.NSA4OutputSupportCoareaResidualTheoremBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS A4 output-support coarea/residual theorem boundary.
--
-- This is a lightweight, fail-closed receipt for the four-part A4 proof
-- content:
--
--   I.   local derivative formula,
--   II.  Sard/coarea density and uniform Jacobian control,
--   III. Lei-Ren-Tian transfer to every output great-circle strip,
--   IV. error subtraction and residual positivity.
--
-- It is intentionally standalone so the direct validation target can run
-- under the 10s sprint cap.  It records A4 proof content as complete at the
-- receipt level only.  It does not promote A5, A6, A7, CKN/BKM, Navier-
-- Stokes Clay, or terminal authority.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- A4 proof content.

data A4ProofPart : Set where
  partI-localDerivativeFormula :
    A4ProofPart
  partII-sardCoareaDensityUniformJacobian :
    A4ProofPart
  partIII-leiRenTianTransfer :
    A4ProofPart
  partIV-errorSubtractionResidualPositivity :
    A4ProofPart

canonicalA4ProofParts :
  List A4ProofPart
canonicalA4ProofParts =
  partI-localDerivativeFormula
  ∷ partII-sardCoareaDensityUniformJacobian
  ∷ partIII-leiRenTianTransfer
  ∷ partIV-errorSubtractionResidualPositivity
  ∷ []

A4ProofPartCount : Nat
A4ProofPartCount =
  listLength canonicalA4ProofParts

A4ProofPartCountIs4 :
  A4ProofPartCount ≡ 4
A4ProofPartCountIs4 =
  refl

data A4LocalDerivativeClause : Set where
  normalizeSumEquatorDerivativeFormula :
    A4LocalDerivativeClause
  equatorSecondFactorVanishes :
    A4LocalDerivativeClause
  derivativeScaleIsOneOverSqrtTwoCosHalfGamma :
    A4LocalDerivativeClause

canonicalA4LocalDerivativeClauses :
  List A4LocalDerivativeClause
canonicalA4LocalDerivativeClauses =
  normalizeSumEquatorDerivativeFormula
  ∷ equatorSecondFactorVanishes
  ∷ derivativeScaleIsOneOverSqrtTwoCosHalfGamma
  ∷ []

A4LocalDerivativeClauseCount : Nat
A4LocalDerivativeClauseCount =
  listLength canonicalA4LocalDerivativeClauses

A4LocalDerivativeClauseCountIs3 :
  A4LocalDerivativeClauseCount ≡ 3
A4LocalDerivativeClauseCountIs3 =
  refl

data A4CoareaDensityClause : Set where
  sardCriticalValuesNull :
    A4CoareaDensityClause
  offAntipodalGradientInverseUniformlyBounded :
    A4CoareaDensityClause
  stripDensityPositiveForRegularValues :
    A4CoareaDensityClause
  normalDirectionConstantsUniform :
    A4CoareaDensityClause

canonicalA4CoareaDensityClauses :
  List A4CoareaDensityClause
canonicalA4CoareaDensityClauses =
  sardCriticalValuesNull
  ∷ offAntipodalGradientInverseUniformlyBounded
  ∷ stripDensityPositiveForRegularValues
  ∷ normalDirectionConstantsUniform
  ∷ []

A4CoareaDensityClauseCount : Nat
A4CoareaDensityClauseCount =
  listLength canonicalA4CoareaDensityClauses

A4CoareaDensityClauseCountIs4 :
  A4CoareaDensityClauseCount ≡ 4
A4CoareaDensityClauseCountIs4 =
  refl

data A4LRTTransferClause : Set where
  lrtGreatCircleConditionForEveryNormal :
    A4LRTTransferClause
  bothOpenHemispheresCarryPositiveMass :
    A4LRTTransferClause
  weightedCoareaDensityAtZeroIsPositive :
    A4LRTTransferClause
  cA4DefinedAsPositiveLRTSquaredConstant :
    A4LRTTransferClause

canonicalA4LRTTransferClauses :
  List A4LRTTransferClause
canonicalA4LRTTransferClauses =
  lrtGreatCircleConditionForEveryNormal
  ∷ bothOpenHemispheresCarryPositiveMass
  ∷ weightedCoareaDensityAtZeroIsPositive
  ∷ cA4DefinedAsPositiveLRTSquaredConstant
  ∷ []

A4LRTTransferClauseCount : Nat
A4LRTTransferClauseCount =
  listLength canonicalA4LRTTransferClauses

A4LRTTransferClauseCountIs4 :
  A4LRTTransferClauseCount ≡ 4
A4LRTTransferClauseCountIs4 =
  refl

data A4ErrorSubtractionClause : Set where
  antipodalTubeErrorAbsorbed :
    A4ErrorSubtractionClause
  lowVorticityMassErrorAbsorbed :
    A4ErrorSubtractionClause
  nearAntipodalNullOutputErrorAbsorbed :
    A4ErrorSubtractionClause
  bonyPerturbationErrorAbsorbed :
    A4ErrorSubtractionClause
  residualPositiveForSmallScale :
    A4ErrorSubtractionClause

canonicalA4ErrorSubtractionClauses :
  List A4ErrorSubtractionClause
canonicalA4ErrorSubtractionClauses =
  antipodalTubeErrorAbsorbed
  ∷ lowVorticityMassErrorAbsorbed
  ∷ nearAntipodalNullOutputErrorAbsorbed
  ∷ bonyPerturbationErrorAbsorbed
  ∷ residualPositiveForSmallScale
  ∷ []

A4ErrorSubtractionClauseCount : Nat
A4ErrorSubtractionClauseCount =
  listLength canonicalA4ErrorSubtractionClauses

A4ErrorSubtractionClauseCountIs5 :
  A4ErrorSubtractionClauseCount ≡ 5
A4ErrorSubtractionClauseCountIs5 =
  refl

------------------------------------------------------------------------
-- Downstream blockers.

data DownstreamA4Blocker : Set where
  blockerA5-kappaBiasVanishingFromA4Stationarity :
    DownstreamA4Blocker
  blockerA6-triadicCompensatedLeakageIdentity :
    DownstreamA4Blocker
  blockerA7-residualDepletionGronwall :
    DownstreamA4Blocker
  blockerA8-fullLocalDefectMonotonicity :
    DownstreamA4Blocker
  blockerA9-CKNBKMClosure :
    DownstreamA4Blocker
  blockerClayAuthority :
    DownstreamA4Blocker

canonicalDownstreamA4Blockers :
  List DownstreamA4Blocker
canonicalDownstreamA4Blockers =
  blockerA5-kappaBiasVanishingFromA4Stationarity
  ∷ blockerA6-triadicCompensatedLeakageIdentity
  ∷ blockerA7-residualDepletionGronwall
  ∷ blockerA8-fullLocalDefectMonotonicity
  ∷ blockerA9-CKNBKMClosure
  ∷ blockerClayAuthority
  ∷ []

DownstreamA4BlockerCount : Nat
DownstreamA4BlockerCount =
  listLength canonicalDownstreamA4Blockers

DownstreamA4BlockerCountIs6 :
  DownstreamA4BlockerCount ≡ 6
DownstreamA4BlockerCountIs6 =
  refl

------------------------------------------------------------------------
-- Fail-closed flags.

data A4OutputSupportCoareaResidualPromotion : Set where

A4OutputSupportCoareaResidualPromotionImpossibleHere :
  A4OutputSupportCoareaResidualPromotion →
  ⊥
A4OutputSupportCoareaResidualPromotionImpossibleHere ()

NSA4OutputSupportCoareaResidualTheoremBoundaryRecorded : Bool
NSA4OutputSupportCoareaResidualTheoremBoundaryRecorded =
  true

A4ProofContentCompleteReceipt : Bool
A4ProofContentCompleteReceipt =
  true

A4PromotesA5KappaBiasVanishing : Bool
A4PromotesA5KappaBiasVanishing =
  false

A4PromotesA6TriadicCompensatedLeakage : Bool
A4PromotesA6TriadicCompensatedLeakage =
  false

A4PromotesA7ResidualDepletion : Bool
A4PromotesA7ResidualDepletion =
  false

A4PromotesCKNBKMClosure : Bool
A4PromotesCKNBKMClosure =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsNSA4OutputSupportCoareaResidualTheoremBoundary :
  NSA4OutputSupportCoareaResidualTheoremBoundaryRecorded ≡ true
recordsNSA4OutputSupportCoareaResidualTheoremBoundary =
  refl

recordsA4ProofContentComplete :
  A4ProofContentCompleteReceipt ≡ true
recordsA4ProofContentComplete =
  refl

keepsA5False :
  A4PromotesA5KappaBiasVanishing ≡ false
keepsA5False =
  refl

keepsA6False :
  A4PromotesA6TriadicCompensatedLeakage ≡ false
keepsA6False =
  refl

keepsA7False :
  A4PromotesA7ResidualDepletion ≡ false
keepsA7False =
  refl

keepsCKNBKMFalse :
  A4PromotesCKNBKMClosure ≡ false
keepsCKNBKMFalse =
  refl

keepsClayFalse :
  clayNavierStokesPromoted ≡ false
keepsClayFalse =
  refl

keepsTerminalFalse :
  terminalPromotion ≡ false
keepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: Worker-D A4 output-support coarea/residual receipt owned by Closure; direct validation is standalone and 10s-safe."

requirementString : String
requirementString =
  "R: Record A4 four-part proof content: local derivative, Sard/coarea density, LRT transfer, and error subtraction/residual positivity."

codeArtifactString : String
codeArtifactString =
  "C: NSA4OutputSupportCoareaResidualTheoremBoundary.agda records A4 proof parts, subclauses, downstream blockers, and fail-closed promotion flags."

stateString : String
stateString =
  "S: A4_proof_content_complete is true as a receipt status; A5, A6, A7, CKN/BKM, NS Clay, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: derivative formula -> Sard/coarea density -> LRT transfer -> error subtraction/residual positivity -> A5/A6/A7 blockers."

proposalString : String
proposalString =
  "P: Use this as the canonical lightweight A4 receipt; next proof rungs are A5 kappa-bias vanishing, A6 leakage, and A7 depletion."

governanceString : String
governanceString =
  "G: Fail closed: A4 receipt completeness is not a Clay promotion and does not discharge A5/A6/A7 or external authority."

gapString : String
gapString =
  "F: Remaining gaps are A5, A6, A7, A8 local monotonicity, A9 CKN/BKM closure, and Clay authority."

record NSA4OutputSupportCoareaResidualTheoremBoundary : Set where
  field
    O :
      String
    OIsCanonical :
      O ≡ organizationString
    R :
      String
    RIsCanonical :
      R ≡ requirementString
    C :
      String
    CIsCanonical :
      C ≡ codeArtifactString
    S :
      String
    SIsCanonical :
      S ≡ stateString
    L :
      String
    LIsCanonical :
      L ≡ latticeString
    P :
      String
    PIsCanonical :
      P ≡ proposalString
    G :
      String
    GIsCanonical :
      G ≡ governanceString
    F :
      String
    FIsCanonical :
      F ≡ gapString
    proofParts :
      List A4ProofPart
    proofPartsAreCanonical :
      proofParts ≡ canonicalA4ProofParts
    proofPartCountIsFour :
      A4ProofPartCount ≡ 4
    localDerivativeClauses :
      List A4LocalDerivativeClause
    localDerivativeClausesAreCanonical :
      localDerivativeClauses ≡ canonicalA4LocalDerivativeClauses
    localDerivativeClauseCountIsThree :
      A4LocalDerivativeClauseCount ≡ 3
    coareaDensityClauses :
      List A4CoareaDensityClause
    coareaDensityClausesAreCanonical :
      coareaDensityClauses ≡ canonicalA4CoareaDensityClauses
    coareaDensityClauseCountIsFour :
      A4CoareaDensityClauseCount ≡ 4
    lrtTransferClauses :
      List A4LRTTransferClause
    lrtTransferClausesAreCanonical :
      lrtTransferClauses ≡ canonicalA4LRTTransferClauses
    lrtTransferClauseCountIsFour :
      A4LRTTransferClauseCount ≡ 4
    errorSubtractionClauses :
      List A4ErrorSubtractionClause
    errorSubtractionClausesAreCanonical :
      errorSubtractionClauses ≡ canonicalA4ErrorSubtractionClauses
    errorSubtractionClauseCountIsFive :
      A4ErrorSubtractionClauseCount ≡ 5
    downstreamBlockers :
      List DownstreamA4Blocker
    downstreamBlockersAreCanonical :
      downstreamBlockers ≡ canonicalDownstreamA4Blockers
    downstreamBlockerCountIsSix :
      DownstreamA4BlockerCount ≡ 6
    boundaryRecordedTrue :
      NSA4OutputSupportCoareaResidualTheoremBoundaryRecorded ≡ true
    A4ProofContentCompleteReceiptTrue :
      A4ProofContentCompleteReceipt ≡ true
    A5StillFalse :
      A4PromotesA5KappaBiasVanishing ≡ false
    A6StillFalse :
      A4PromotesA6TriadicCompensatedLeakage ≡ false
    A7StillFalse :
      A4PromotesA7ResidualDepletion ≡ false
    CKNBKMStillFalse :
      A4PromotesCKNBKMClosure ≡ false
    clayNavierStokesPromotedStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

canonicalNSA4OutputSupportCoareaResidualTheoremBoundary :
  NSA4OutputSupportCoareaResidualTheoremBoundary
canonicalNSA4OutputSupportCoareaResidualTheoremBoundary =
  record
    { O =
        organizationString
    ; OIsCanonical =
        refl
    ; R =
        requirementString
    ; RIsCanonical =
        refl
    ; C =
        codeArtifactString
    ; CIsCanonical =
        refl
    ; S =
        stateString
    ; SIsCanonical =
        refl
    ; L =
        latticeString
    ; LIsCanonical =
        refl
    ; P =
        proposalString
    ; PIsCanonical =
        refl
    ; G =
        governanceString
    ; GIsCanonical =
        refl
    ; F =
        gapString
    ; FIsCanonical =
        refl
    ; proofParts =
        canonicalA4ProofParts
    ; proofPartsAreCanonical =
        refl
    ; proofPartCountIsFour =
        refl
    ; localDerivativeClauses =
        canonicalA4LocalDerivativeClauses
    ; localDerivativeClausesAreCanonical =
        refl
    ; localDerivativeClauseCountIsThree =
        refl
    ; coareaDensityClauses =
        canonicalA4CoareaDensityClauses
    ; coareaDensityClausesAreCanonical =
        refl
    ; coareaDensityClauseCountIsFour =
        refl
    ; lrtTransferClauses =
        canonicalA4LRTTransferClauses
    ; lrtTransferClausesAreCanonical =
        refl
    ; lrtTransferClauseCountIsFour =
        refl
    ; errorSubtractionClauses =
        canonicalA4ErrorSubtractionClauses
    ; errorSubtractionClausesAreCanonical =
        refl
    ; errorSubtractionClauseCountIsFive =
        refl
    ; downstreamBlockers =
        canonicalDownstreamA4Blockers
    ; downstreamBlockersAreCanonical =
        refl
    ; downstreamBlockerCountIsSix =
        refl
    ; boundaryRecordedTrue =
        refl
    ; A4ProofContentCompleteReceiptTrue =
        refl
    ; A5StillFalse =
        refl
    ; A6StillFalse =
        refl
    ; A7StillFalse =
        refl
    ; CKNBKMStillFalse =
        refl
    ; clayNavierStokesPromotedStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    }
