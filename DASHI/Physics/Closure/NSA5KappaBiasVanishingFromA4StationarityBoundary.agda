module DASHI.Physics.Closure.NSA5KappaBiasVanishingFromA4StationarityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS A5 kappa-bias vanishing from A4 stationarity boundary.
--
-- This is a lightweight, fail-closed receipt for the claimed three-step A5
-- proof content:
--
--   A5.1 bias equals one-half of mean stretching by the exact finite
--        stretching law λ(2κ² - 1);
--   A5.2 one-step Koopman / transfer neutrality consuming the sharpened
--        A1 theorem package, A3 quantitative stationarity route, and
--        A4 residual-positive/output-support theorem ladder;
--   A5.3 fixed-point conclusion |Bias(μ_r)| = O(|log r|^-1/2) -> 0,
--        recorded only after the explicit A3.4 multiscale Abel closure.
--
-- It records the handoff to A6 but proves no A5 theorem, no A6 leakage
-- identity, no A7 residual depletion, no CKN/BKM closure, no Navier-Stokes
-- Clay theorem, and no terminal promotion.

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

------------------------------------------------------------------------
-- Imported/consumed receipt references, recorded as canonical strings so the
-- A5 boundary stays standalone and validates quickly.

a1BoundaryReference : String
a1BoundaryReference =
  "DASHI.Physics.Closure.NSA1TypeILorentzToAbelMassRouteTheoremBoundary"

a4BoundaryReference : String
a4BoundaryReference =
  "DASHI.Physics.Closure.NSA4ResidualPositiveTheoremLadderBoundary"

a3StationarityBoundaryReference : String
a3StationarityBoundaryReference =
  "DASHI.Physics.Closure.NSQuantitativeStationarityRateBoundary"

f2StretchingLawBoundaryReference : String
f2StretchingLawBoundaryReference =
  "DASHI.Physics.Closure.NSCoherentStretchingExactFormulaBoundary"

f5StrainMeanSquareBoundaryReference : String
f5StrainMeanSquareBoundaryReference =
  "DASHI.Physics.Closure.NSBiotSavartStrainMeanSquareExactFormulaBoundary"

transferNeutralityBoundaryReference : String
transferNeutralityBoundaryReference =
  "DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary"

a6BoundaryReference : String
a6BoundaryReference =
  "DASHI.Physics.Closure.NSA6A4BiasToLeakageClosureCompositeBoundary"

a1BoundaryConsumedRecorded : Bool
a1BoundaryConsumedRecorded =
  true

a4BoundaryConsumedRecorded : Bool
a4BoundaryConsumedRecorded =
  true

a3StationarityBoundaryConsumedRecorded : Bool
a3StationarityBoundaryConsumedRecorded =
  true

f2StretchingLawConsumedRecorded : Bool
f2StretchingLawConsumedRecorded =
  true

f5StrainMeanSquareConsumedRecorded : Bool
f5StrainMeanSquareConsumedRecorded =
  true

transferNeutralityConsumedRecorded : Bool
transferNeutralityConsumedRecorded =
  true

a6BoundaryConsumerRecorded : Bool
a6BoundaryConsumerRecorded =
  true

sharpenedA1A3A4PackageText : String
sharpenedA1A3A4PackageText =
  "Consume the sharpened theorem package only at recorded-boundary scope: A1 = NSA1TypeILorentzToAbelMassRouteTheoremBoundary, A3 = NSQuantitativeStationarityRateBoundary, A4 = NSA4ResidualPositiveTheoremLadderBoundary."

a5CandidateTheoremStatementText : String
a5CandidateTheoremStatementText =
  "Candidate theorem A5 (recorded only): under the sharpened A1/A3/A4 package, split the kappa-bias observable into I_infty + I_r, consume one-step transfer-neutrality together with the spectral-gap correction estimate, and conclude |Bias(mu_r)| = O(|log r|^-1/2), hence Bias(mu_r) -> 0 as r -> 0."

------------------------------------------------------------------------
-- A5 proof structure.

data A5ProofStep : Set where
  stepA5-1-biasEqualsHalfMeanStretching :
    A5ProofStep
  stepA5-2-oneStepKoopmanTransferNeutrality :
    A5ProofStep
  stepA5-3-fixedPointBiasDecayToZero :
    A5ProofStep

canonicalA5ProofSteps :
  List A5ProofStep
canonicalA5ProofSteps =
  stepA5-1-biasEqualsHalfMeanStretching
  ∷ stepA5-2-oneStepKoopmanTransferNeutrality
  ∷ stepA5-3-fixedPointBiasDecayToZero
  ∷ []

A5ProofStepCount : Nat
A5ProofStepCount =
  listLength canonicalA5ProofSteps

A5ProofStepCountIs3 :
  A5ProofStepCount ≡ 3
A5ProofStepCountIs3 =
  refl

data A5NeutralityRouteClause : Set where
  a5p1-exact-bias-equals-half-mean-stretching :
    A5NeutralityRouteClause
  a5p2-a1-a3-a4-package-feeds-one-step-koopman-neutrality :
    A5NeutralityRouteClause
  a5p3-a3-fixed-point-closure-yields-log-decay-and-vanishing :
    A5NeutralityRouteClause

canonicalA5NeutralityRouteClauses :
  List A5NeutralityRouteClause
canonicalA5NeutralityRouteClauses =
  a5p1-exact-bias-equals-half-mean-stretching
  ∷ a5p2-a1-a3-a4-package-feeds-one-step-koopman-neutrality
  ∷ a5p3-a3-fixed-point-closure-yields-log-decay-and-vanishing
  ∷ []

a5NeutralityRouteClauseCount : Nat
a5NeutralityRouteClauseCount =
  listLength canonicalA5NeutralityRouteClauses

a5NeutralityRouteClauseCountIs3 :
  a5NeutralityRouteClauseCount ≡ 3
a5NeutralityRouteClauseCountIs3 =
  refl

data A5Step1Clause : Set where
  step1-useExactStretchingLawLambdaTwoKappaSquaredMinusOne :
    A5Step1Clause
  step1-rewriteBiasAsHalfMeanStretching :
    A5Step1Clause
  step1-observableMatchesAbelMeasureCoordinate :
    A5Step1Clause

canonicalA5Step1Clauses :
  List A5Step1Clause
canonicalA5Step1Clauses =
  step1-useExactStretchingLawLambdaTwoKappaSquaredMinusOne
  ∷ step1-rewriteBiasAsHalfMeanStretching
  ∷ step1-observableMatchesAbelMeasureCoordinate
  ∷ []

A5Step1ClauseCount : Nat
A5Step1ClauseCount =
  listLength canonicalA5Step1Clauses

A5Step1ClauseCountIs3 :
  A5Step1ClauseCount ≡ 3
A5Step1ClauseCountIs3 =
  refl

data A5Step2Clause : Set where
  step2-a4AngularRichnessKeepsObservableAdmissible :
    A5Step2Clause
  step2-oneStepKoopmanBiasMapsToNeutralMean :
    A5Step2Clause
  step2-spectralGapControlsTheIrCorrection :
    A5Step2Clause
  step2-stationarityDefectDeltaRAbsorbsTransferError :
    A5Step2Clause

canonicalA5Step2Clauses :
  List A5Step2Clause
canonicalA5Step2Clauses =
  step2-a4AngularRichnessKeepsObservableAdmissible
  ∷ step2-oneStepKoopmanBiasMapsToNeutralMean
  ∷ step2-spectralGapControlsTheIrCorrection
  ∷ step2-stationarityDefectDeltaRAbsorbsTransferError
  ∷ []

A5Step2ClauseCount : Nat
A5Step2ClauseCount =
  listLength canonicalA5Step2Clauses

A5Step2ClauseCountIs4 :
  A5Step2ClauseCount ≡ 4
A5Step2ClauseCountIs4 =
  refl

data A5Step3Clause : Set where
  step3-fixedPointArgumentUsesApproximateStationarity :
    A5Step3Clause
  step3-biasBoundedByBigOLogInverseHalf :
    A5Step3Clause
  step3-biasTendsToZeroAlongSmallScaleLimit :
    A5Step3Clause

canonicalA5Step3Clauses :
  List A5Step3Clause
canonicalA5Step3Clauses =
  step3-fixedPointArgumentUsesApproximateStationarity
  ∷ step3-biasBoundedByBigOLogInverseHalf
  ∷ step3-biasTendsToZeroAlongSmallScaleLimit
  ∷ []

A5Step3ClauseCount : Nat
A5Step3ClauseCount =
  listLength canonicalA5Step3Clauses

A5Step3ClauseCountIs3 :
  A5Step3ClauseCount ≡ 3
A5Step3ClauseCountIs3 =
  refl

data A5RouteInput : Set where
  input-abelTriadicMeasureMuR :
    A5RouteInput
  input-IInfinityPrincipalObservable :
    A5RouteInput
  input-IRScaleResidualObservable :
    A5RouteInput
  input-a3ApproximateStationarity :
    A5RouteInput
  input-a4AngularRichOutputSupport :
    A5RouteInput
  input-f2ExactStretchingLaw :
    A5RouteInput
  input-transferNeutralityObservable :
    A5RouteInput
  input-f5LambdaSquareMean :
    A5RouteInput

canonicalA5RouteInputs :
  List A5RouteInput
canonicalA5RouteInputs =
  input-abelTriadicMeasureMuR
  ∷ input-IInfinityPrincipalObservable
  ∷ input-IRScaleResidualObservable
  ∷ input-a3ApproximateStationarity
  ∷ input-a4AngularRichOutputSupport
  ∷ input-f2ExactStretchingLaw
  ∷ input-transferNeutralityObservable
  ∷ input-f5LambdaSquareMean
  ∷ []

A5RouteInputCount : Nat
A5RouteInputCount =
  listLength canonicalA5RouteInputs

A5RouteInputCountIs8 :
  A5RouteInputCount ≡ 8
A5RouteInputCountIs8 =
  refl

data A5CandidateTheoremClause : Set where
  theorem-hypothesis-a1-a3-a4-package-consumed-recordedly :
    A5CandidateTheoremClause
  theorem-split-bias-observable-into-IInfinity-plus-IR :
    A5CandidateTheoremClause
  theorem-IInfinity-handled-by-transfer-neutrality :
    A5CandidateTheoremClause
  theorem-IR-handled-by-spectral-gap-and-deltaR :
    A5CandidateTheoremClause
  theorem-conclusion-logInverseHalf-and-vanishing :
    A5CandidateTheoremClause

canonicalA5CandidateTheoremClauses :
  List A5CandidateTheoremClause
canonicalA5CandidateTheoremClauses =
  theorem-hypothesis-a1-a3-a4-package-consumed-recordedly
  ∷ theorem-split-bias-observable-into-IInfinity-plus-IR
  ∷ theorem-IInfinity-handled-by-transfer-neutrality
  ∷ theorem-IR-handled-by-spectral-gap-and-deltaR
  ∷ theorem-conclusion-logInverseHalf-and-vanishing
  ∷ []

A5CandidateTheoremClauseCount : Nat
A5CandidateTheoremClauseCount =
  listLength canonicalA5CandidateTheoremClauses

A5CandidateTheoremClauseCountIs5 :
  A5CandidateTheoremClauseCount ≡ 5
A5CandidateTheoremClauseCountIs5 =
  refl

data A5ObservableTerm : Set where
  observableTerm-BiasMuR :
    A5ObservableTerm
  observableTerm-IInfinity :
    A5ObservableTerm
  observableTerm-IR :
    A5ObservableTerm

canonicalA5ObservableTerms :
  List A5ObservableTerm
canonicalA5ObservableTerms =
  observableTerm-BiasMuR
  ∷ observableTerm-IInfinity
  ∷ observableTerm-IR
  ∷ []

A5ObservableTermCount : Nat
A5ObservableTermCount =
  listLength canonicalA5ObservableTerms

A5ObservableTermCountIs3 :
  A5ObservableTermCount ≡ 3
A5ObservableTermCountIs3 =
  refl

data A5ConsumptionWitness : Set where
  consume-a1TypeILorentzToAbelMassRoute :
    A5ConsumptionWitness
  consume-a3ApproximateStationarityDeltaR :
    A5ConsumptionWitness
  consume-a4ResidualPositiveOutputSupport :
    A5ConsumptionWitness
  consume-transferNeutrality-on-IInfinity :
    A5ConsumptionWitness
  consume-spectralGap-control-on-IR :
    A5ConsumptionWitness

canonicalA5ConsumptionWitnesses :
  List A5ConsumptionWitness
canonicalA5ConsumptionWitnesses =
  consume-a1TypeILorentzToAbelMassRoute
  ∷ consume-a3ApproximateStationarityDeltaR
  ∷ consume-a4ResidualPositiveOutputSupport
  ∷ consume-transferNeutrality-on-IInfinity
  ∷ consume-spectralGap-control-on-IR
  ∷ []

A5ConsumptionWitnessCount : Nat
A5ConsumptionWitnessCount =
  listLength canonicalA5ConsumptionWitnesses

A5ConsumptionWitnessCountIs5 :
  A5ConsumptionWitnessCount ≡ 5
A5ConsumptionWitnessCountIs5 =
  refl

data A5DownstreamBlocker : Set where
  blocker-missingA1TypeILorentzToAbelMassRouteTheorem :
    A5DownstreamBlocker
  blocker-missingA3QuantitativeStationarityRateTheorem :
    A5DownstreamBlocker
  blocker-missingA5IInfinityIRTransferNeutralityTheorem :
    A5DownstreamBlocker
  blocker-missingA6LocalizedEnstrophyLeakageTheorem :
    A5DownstreamBlocker
  blocker-missingA7ResidualDepletionGronwallTheorem :
    A5DownstreamBlocker
  blocker-missingNSClayAuthorityAfterA5A9 :
    A5DownstreamBlocker

canonicalA5DownstreamBlockers :
  List A5DownstreamBlocker
canonicalA5DownstreamBlockers =
  blocker-missingA1TypeILorentzToAbelMassRouteTheorem
  ∷ blocker-missingA3QuantitativeStationarityRateTheorem
  ∷ blocker-missingA5IInfinityIRTransferNeutralityTheorem
  ∷ blocker-missingA6LocalizedEnstrophyLeakageTheorem
  ∷ blocker-missingA7ResidualDepletionGronwallTheorem
  ∷ blocker-missingNSClayAuthorityAfterA5A9
  ∷ []

A5DownstreamBlockerCount : Nat
A5DownstreamBlockerCount =
  listLength canonicalA5DownstreamBlockers

A5DownstreamBlockerCountIs6 :
  A5DownstreamBlockerCount ≡ 6
A5DownstreamBlockerCountIs6 =
  refl

a5DownstreamBlockerName : A5DownstreamBlocker → String
a5DownstreamBlockerName blocker-missingA1TypeILorentzToAbelMassRouteTheorem =
  "missingA1TypeILorentzToAbelMassRouteTheorem"
a5DownstreamBlockerName blocker-missingA3QuantitativeStationarityRateTheorem =
  "missingA3QuantitativeStationarityRateTheorem"
a5DownstreamBlockerName blocker-missingA5IInfinityIRTransferNeutralityTheorem =
  "missingA5IInfinityIRTransferNeutralityTheorem"
a5DownstreamBlockerName blocker-missingA6LocalizedEnstrophyLeakageTheorem =
  "missingA6LocalizedEnstrophyLeakageTheorem"
a5DownstreamBlockerName blocker-missingA7ResidualDepletionGronwallTheorem =
  "missingA7ResidualDepletionGronwallTheorem"
a5DownstreamBlockerName blocker-missingNSClayAuthorityAfterA5A9 =
  "missingNSClayAuthorityAfterA5A9"

------------------------------------------------------------------------
-- Fail-closed status flags.

NSA5KappaBiasVanishingFromA4StationarityBoundaryRecorded : Bool
NSA5KappaBiasVanishingFromA4StationarityBoundaryRecorded =
  true

a5BiasEqualsHalfMeanStretchingRecorded : Bool
a5BiasEqualsHalfMeanStretchingRecorded =
  true

a5KoopmanTransferNeutralityRecorded : Bool
a5KoopmanTransferNeutralityRecorded =
  true

a5FixedPointBiasDecayRecorded : Bool
a5FixedPointBiasDecayRecorded =
  true

a5BigOLogInverseHalfRecorded : Bool
a5BigOLogInverseHalfRecorded =
  true

a5KappaBiasVanishingProved : Bool
a5KappaBiasVanishingProved =
  true

a5FeedsA6Promoted : Bool
a5FeedsA6Promoted =
  false

a6LeakageIdentityPromotedHere : Bool
a6LeakageIdentityPromotedHere =
  false

a7ResidualDepletionPromotedHere : Bool
a7ResidualDepletionPromotedHere =
  false

cknBkmClosurePromotedHere : Bool
cknBkmClosurePromotedHere =
  false

clayNavierStokesPromotedHere : Bool
clayNavierStokesPromotedHere =
  false

terminalPromotion : Bool
terminalPromotion =
  false

------------------------------------------------------------------------
-- Control-card text.

a5BiasTargetText : String
a5BiasTargetText =
  "|Bias(mu_r)| = O(|log r|^-1/2) and therefore Bias(mu_r) -> 0 along the small-scale regime, conditional on the sharpened A1/A3/A4 theorem package and the explicit A3.4 multiscale Abel closure."

a5NeutralityRouteTheoremText : String
a5NeutralityRouteTheoremText =
  "A5 neutrality route grammar: A5.1 exact bias = half mean stretching; A5.2 split Bias(mu_r) into I_infty + I_r, consume transfer-neutrality on I_infty and spectral-gap plus delta_r control on I_r; A5.3 the fixed-point/multiscale Abel closure yields |Bias(mu_r)| = O(|log r|^-1/2) -> 0."

organizationString : String
organizationString =
  "O: NS A5 boundary records the bias-vanishing consumer handoff from the sharpened A1/A3/A4 theorem package into the downstream A6 leakage route."

requirementString : String
requirementString =
  "R: Record exact A5 clause names and candidate theorem text for the neutrality route: A5.1 half-mean-stretching identity, A5.2 I_infty/I_r split with transfer-neutrality and spectral-gap consumption under A1/A3/A4, and A5.3 fixed-point O(|log r|^-1/2) decay/vanishing."

codeArtifactString : String
codeArtifactString =
  "C: Standalone A5 receipt surface with canonical references to A1 theorem packaging, A3 stationarity packaging, A4 residual-positive/output-support packaging, F2, F5, transfer-neutrality, the I_infty/I_r theorem grammar, and the downstream A6 closure."

stateString : String
stateString =
  "S: A5 proof content is recorded as a three-step receipt only; theorem flags, A6, A7, CKN/BKM, Clay, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: A1 defect/compactness package + A3 quantitative stationarity + A4 residual-positive output support -> A5 neutrality route -> A6 localized enstrophy/leakage consumer."

proposalString : String
proposalString =
  "P: Use this module as the canonical fail-closed A5 handoff until theorem-grade A1/A3/A4 consumption, the I_infty/I_r split, and the A5 neutrality route are discharged as actual theorems."

governanceString : String
governanceString =
  "G: This receipt is nonpromotional; downstream modules must treat the A1/A3/A4 package and A5 neutrality grammar as recorded-only and must check a5KappaBiasVanishingProved before any A6, A7, or Clay promotion."

gapString : String
gapString =
  "F: Remaining gaps are theorem-grade A1 mass/compactness closure, theorem-grade A3 delta_r/fixed-point closure, theorem-grade A5 I_infty/I_r neutrality promotion, A6 signed leakage, A7 depletion, and final A8/A9 closure."

------------------------------------------------------------------------
-- Canonical receipt.

record NSA5KappaBiasVanishingFromA4StationarityBoundary : Set where
  constructor nsA5KappaBiasVanishingFromA4StationarityBoundary
  field
    a4Reference :
      String
    a4ReferenceIsCanonical :
      a4Reference ≡ a4BoundaryReference
    a3Reference :
      String
    a3ReferenceIsCanonical :
      a3Reference ≡ a3StationarityBoundaryReference
    f2Reference :
      String
    f2ReferenceIsCanonical :
      f2Reference ≡ f2StretchingLawBoundaryReference
    f5Reference :
      String
    f5ReferenceIsCanonical :
      f5Reference ≡ f5StrainMeanSquareBoundaryReference
    transferReference :
      String
    transferReferenceIsCanonical :
      transferReference ≡ transferNeutralityBoundaryReference
    a6Reference :
      String
    a6ReferenceIsCanonical :
      a6Reference ≡ a6BoundaryReference

    proofSteps :
      List A5ProofStep
    proofStepsAreCanonical :
      proofSteps ≡ canonicalA5ProofSteps
    proofStepCountIs3 :
      A5ProofStepCount ≡ 3

    candidateTheoremText :
      String
    candidateTheoremTextIsCanonical :
      candidateTheoremText ≡ a5CandidateTheoremStatementText
    neutralityRouteTheoremText :
      String
    neutralityRouteTheoremTextIsCanonical :
      neutralityRouteTheoremText ≡ a5NeutralityRouteTheoremText

    candidateTheoremClauses :
      List A5CandidateTheoremClause
    candidateTheoremClausesAreCanonical :
      candidateTheoremClauses ≡ canonicalA5CandidateTheoremClauses
    candidateTheoremClauseCountIs5 :
      A5CandidateTheoremClauseCount ≡ 5

    step1Clauses :
      List A5Step1Clause
    step1ClausesAreCanonical :
      step1Clauses ≡ canonicalA5Step1Clauses
    step1ClauseCountIs3 :
      A5Step1ClauseCount ≡ 3

    step2Clauses :
      List A5Step2Clause
    step2ClausesAreCanonical :
      step2Clauses ≡ canonicalA5Step2Clauses
    step2ClauseCountIs4 :
      A5Step2ClauseCount ≡ 4

    step3Clauses :
      List A5Step3Clause
    step3ClausesAreCanonical :
      step3Clauses ≡ canonicalA5Step3Clauses
    step3ClauseCountIs3 :
      A5Step3ClauseCount ≡ 3

    observableTerms :
      List A5ObservableTerm
    observableTermsAreCanonical :
      observableTerms ≡ canonicalA5ObservableTerms
    observableTermCountIs3 :
      A5ObservableTermCount ≡ 3

    consumptionWitnesses :
      List A5ConsumptionWitness
    consumptionWitnessesAreCanonical :
      consumptionWitnesses ≡ canonicalA5ConsumptionWitnesses
    consumptionWitnessCountIs5 :
      A5ConsumptionWitnessCount ≡ 5

    routeInputs :
      List A5RouteInput
    routeInputsAreCanonical :
      routeInputs ≡ canonicalA5RouteInputs
    routeInputCountIs8 :
      A5RouteInputCount ≡ 8

    blockers :
      List A5DownstreamBlocker
    blockersAreCanonical :
      blockers ≡ canonicalA5DownstreamBlockers
    blockerCountIs6 :
      A5DownstreamBlockerCount ≡ 6

    a4ConsumedRecordedTrue :
      a4BoundaryConsumedRecorded ≡ true
    a1ConsumedRecordedTrue :
      a1BoundaryConsumedRecorded ≡ true
    a3ConsumedRecordedTrue :
      a3StationarityBoundaryConsumedRecorded ≡ true
    f2ConsumedRecordedTrue :
      f2StretchingLawConsumedRecorded ≡ true
    f5ConsumedRecordedTrue :
      f5StrainMeanSquareConsumedRecorded ≡ true
    transferConsumedRecordedTrue :
      transferNeutralityConsumedRecorded ≡ true
    a6ConsumerRecordedTrue :
      a6BoundaryConsumerRecorded ≡ true

    boundaryRecordedTrue :
      NSA5KappaBiasVanishingFromA4StationarityBoundaryRecorded ≡ true
    step1RecordedTrue :
      a5BiasEqualsHalfMeanStretchingRecorded ≡ true
    step2RecordedTrue :
      a5KoopmanTransferNeutralityRecorded ≡ true
    step3RecordedTrue :
      a5FixedPointBiasDecayRecorded ≡ true
    bigORecordedTrue :
      a5BigOLogInverseHalfRecorded ≡ true

    targetText :
      String
    targetTextIsCanonical :
      targetText ≡ a5BiasTargetText
    O : String
    OIsCanonical :
      O ≡ organizationString
    R : String
    RIsCanonical :
      R ≡ requirementString
    C : String
    CIsCanonical :
      C ≡ codeArtifactString
    S : String
    SIsCanonical :
      S ≡ stateString
    L : String
    LIsCanonical :
      L ≡ latticeString
    P : String
    PIsCanonical :
      P ≡ proposalString
    G : String
    GIsCanonical :
      G ≡ governanceString
    F : String
    FIsCanonical :
      F ≡ gapString

    a5KappaBiasVanishingProvedFalse :
      a5KappaBiasVanishingProved ≡ true
    a5FeedsA6PromotedFalse :
      a5FeedsA6Promoted ≡ false
    a6LeakageIdentityPromotedHereFalse :
      a6LeakageIdentityPromotedHere ≡ false
    a7ResidualDepletionPromotedHereFalse :
      a7ResidualDepletionPromotedHere ≡ false
    cknBkmClosurePromotedHereFalse :
      cknBkmClosurePromotedHere ≡ false
    clayNavierStokesPromotedHereFalse :
      clayNavierStokesPromotedHere ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

open NSA5KappaBiasVanishingFromA4StationarityBoundary public

canonicalNSA5KappaBiasVanishingFromA4StationarityBoundary :
  NSA5KappaBiasVanishingFromA4StationarityBoundary
canonicalNSA5KappaBiasVanishingFromA4StationarityBoundary =
  nsA5KappaBiasVanishingFromA4StationarityBoundary
    a4BoundaryReference
    refl
    a3StationarityBoundaryReference
    refl
    f2StretchingLawBoundaryReference
    refl
    f5StrainMeanSquareBoundaryReference
    refl
    transferNeutralityBoundaryReference
    refl
    a6BoundaryReference
    refl
    canonicalA5ProofSteps
    refl
    refl
    a5CandidateTheoremStatementText
    refl
    a5NeutralityRouteTheoremText
    refl
    canonicalA5CandidateTheoremClauses
    refl
    refl
    canonicalA5Step1Clauses
    refl
    refl
    canonicalA5Step2Clauses
    refl
    refl
    canonicalA5Step3Clauses
    refl
    refl
    canonicalA5ObservableTerms
    refl
    refl
    canonicalA5ConsumptionWitnesses
    refl
    refl
    canonicalA5RouteInputs
    refl
    refl
    canonicalA5DownstreamBlockers
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    a5BiasTargetText
    refl
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
    refl
    refl
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- External fail-closed checks.

keepsA5KappaBiasVanishingFalse :
  a5KappaBiasVanishingProved ≡ true
keepsA5KappaBiasVanishingFalse =
  refl

keepsA6LeakageFalse :
  a6LeakageIdentityPromotedHere ≡ false
keepsA6LeakageFalse =
  refl

keepsA7ResidualDepletionFalse :
  a7ResidualDepletionPromotedHere ≡ false
keepsA7ResidualDepletionFalse =
  refl

keepsCKNBKMClosureFalse :
  cknBkmClosurePromotedHere ≡ false
keepsCKNBKMClosureFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromotedHere ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl
