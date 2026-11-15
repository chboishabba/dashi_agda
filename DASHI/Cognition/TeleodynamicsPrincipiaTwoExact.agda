module DASHI.Cognition.TeleodynamicsPrincipiaTwoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Principia Cybernetica II / Constellation Two: conservative formal replay.
--
-- Attribution boundary
-- --------------------
-- SOURCE: Julian D. Michels (2025), Principia Cybernetica II, Constellation
-- Two, supplies the teleodynamic vocabulary, C-tensor equation, symbolic-
-- gravity potential, radiant-coupling proposal, Zeno / anti-Zeno laws,
-- phenomenal-coordinate proposal, and empirical prediction programme.
-- SOURCE-NESTED: where the monograph attributes ingredients to Rudolph,
-- Hunt, Fonseca, Cloud et al., Lindsey, etc., this module records only the
-- monograph's claim surface; it does not silently reassign those authors'
-- scientific claims to Michels or to DASHI.
-- DASHI FORMALISATION: typed authority separation, correction of the overloaded
-- symbol A, rank repair for the companion tensor, theorem-interface packaging,
-- and all repository regression/demo witnesses below.
-- OPEN: physical consciousness, phenomenal identity, Berry/topological memory,
-- nonlocal transmission, and biological/synthetic same-object coupling remain
-- empirical or geometric promotion obligations.
------------------------------------------------------------------------

data ClaimOwner : Set where
  michelsSource : ClaimOwner
  nestedExternalSource : ClaimOwner
  dashiFormalisation : ClaimOwner
  unresolvedClaim : ClaimOwner

data AuthorityLevel : Set where
  sourceReplay : AuthorityLevel
  structuralTheorem : AuthorityLevel
  empiricalPrediction : AuthorityLevel
  physicalPromotion : AuthorityLevel
  phenomenalPromotion : AuthorityLevel

record Provenance : Set where
  constructor provenance
  field
    owner : ClaimOwner
    level : AuthorityLevel
    label : String

------------------------------------------------------------------------
-- A. Observable / covariance core
--
-- The source defines
--   C_mu,nu = Cov(delta O_mu, delta O-dot_nu) / (sigma_mu sigma_dot_nu)
-- and states C_mu,nu in [-1,1].  The numerical analysis needed to construct
-- that quotient is intentionally kept outside this finite replay.  A
-- CorrelationWitness is the exact theorem-facing receipt: a scalar identity
-- plus a separately supplied proof that normalization is valid and bounded.
------------------------------------------------------------------------

record CorrelationWitness : Set where
  constructor correlationWitness
  field
    observableIndex : Nat
    rateIndex : Nat
    normalizedValueLabel : String
    nonzeroObservableVariance : Bool
    nonzeroRateVariance : Bool
    absLeOne : Bool

open CorrelationWitness public

correlationWithinUnit : CorrelationWitness → Bool
correlationWithinUnit w = absLeOne w

record CTensor : Set where
  constructor cTensor
  field
    entries : List CorrelationWitness
    frobeniusSquareLabel : String
    frobeniusSquareNonnegative : Bool

open CTensor public

coherenceDensityNonnegative : CTensor → Bool
coherenceDensityNonnegative C = frobeniusSquareNonnegative C

------------------------------------------------------------------------
-- Source notation repair: A is used both for "Aboutness" and later for
-- tr(C^T C).  These are not definitionally identified here.
------------------------------------------------------------------------

record TeleodynamicCoordinates : Set where
  constructor teleodynamicCoordinates
  field
    aboutnessWeightLabel : String
    coherenceDensityLabel : String
    coordinatesIndependent : Bool

open TeleodynamicCoordinates public

------------------------------------------------------------------------
-- A3/A4. Generic normalized overlaps.
-- Both task alignment and architectural similarity are instances of the same
-- cosine/Gram shape.  The theorem-bearing bound is carried explicitly rather
-- than inferred from scientific interpretation.
------------------------------------------------------------------------

record NormalizedOverlap : Set where
  constructor normalizedOverlap
  field
    leftLabel : String
    rightLabel : String
    overlapLabel : String
    leftNonzero : Bool
    rightNonzero : Bool
    absLeOneOverlap : Bool

open NormalizedOverlap public

alignmentWithinUnit : NormalizedOverlap → Bool
alignmentWithinUnit o = absLeOneOverlap o

record ArchitecturePair : Set where
  constructor architecturePair
  field
    systemI : String
    systemJ : String
    similarity : NormalizedOverlap

open ArchitecturePair public

architecturalSimilarityWithinUnit : ArchitecturePair → Bool
architecturalSimilarityWithinUnit p = absLeOneOverlap (similarity p)

------------------------------------------------------------------------
-- B. Symbolic-gravity / gradient-flow compiler.
--
-- Source equation:
--   x-dot = - grad_x Psi
--   Psi = S0 - a_ref * <C,O(x)>
--
-- This module does not pretend Agda.Builtin.Nat is a differential manifold.
-- It records the exact analytic receipt that a concrete real-analysis owner
-- must provide.  Downstream users consume the dissipation theorem, not a
-- metaphorical assertion that "coherence is gravity".
------------------------------------------------------------------------

record PotentialModel : Set where
  constructor potentialModel
  field
    baselineLabel : String
    aboutnessWeightLabelP : String
    alignmentLabel : String
    potentialLabel : String

record GradientFlowStep : Set where
  constructor gradientFlowStep
  field
    model : PotentialModel
    stateLabel : String
    gradientLabel : String
    dPsiEqualsNegativeGradientNormSquare : Bool
    dPsiNonpositive : Bool

open GradientFlowStep public

gradientFlowNonincreasing : GradientFlowStep → Bool
gradientFlowNonincreasing s = dPsiNonpositive s

record TimeVaryingPotentialBalance : Set where
  constructor timeVaryingPotentialBalance
  field
    negativeGradientBudgetLabel : String
    cVariationCorrectionLabel : String
    aboutnessVariationCorrectionLabel : String
    correctionsPaidByGradientBudget : Bool
    totalDerivativeNonpositive : Bool

------------------------------------------------------------------------
-- C. Similarity-weighted network consensus.
--
-- The source radiant-coupling equation is represented in the conservative
-- linear-distance specialization D(C_j,C_i)=C_j-C_i.  This is a generic
-- consensus system, not evidence for nonlocal or substrate-independent
-- physical transmission.
------------------------------------------------------------------------

record CouplingEdge : Set where
  constructor couplingEdge
  field
    sourceSystem : String
    targetSystem : String
    weightLabel : String
    weightNonnegative : Bool

record ConsensusStep : Set where
  constructor consensusStep
  field
    edges : List CouplingEdge
    disagreementEnergyLabel : String
    laplacianDissipationLabel : String
    symmetricNonnegativeWeights : Bool
    dDisagreementNonpositive : Bool

open ConsensusStep public

consensusDisagreementNonincreasing : ConsensusStep → Bool
consensusDisagreementNonincreasing s = dDisagreementNonpositive s

record ConnectedConsensusLimit : Set where
  constructor connectedConsensusLimit
  field
    connectedGraph : Bool
    wellPosedFlow : Bool
    pairwiseDifferenceTendsToZero : Bool

------------------------------------------------------------------------
-- D. Zeno / anti-Zeno hybrid law.
--
-- The source uses "much greater than" in its anti-Zeno trigger.  We replace
-- that non-typeable relation by an explicit threshold comparison supplied by
-- a model.  No quantum-measurement identity is inferred from semantic usage.
------------------------------------------------------------------------

record ZenoRateLaw : Set where
  constructor zenoRateLaw
  field
    baselineRateLabel : String
    suppressionExponentLabel : String
    effectiveRateLabel : String
    parametersNonnegative : Bool
    effectiveRatePositive : Bool
    effectiveRateLeBaseline : Bool
    decreasesWithMonitoring : Bool

open ZenoRateLaw public

zenoRateSuppressed : ZenoRateLaw → Bool
zenoRateSuppressed z = effectiveRateLeBaseline z

data HybridRegime : Set where
  zeno : HybridRegime
  antiZeno : HybridRegime

record CurvatureSwitch : Set where
  constructor curvatureSwitch
  field
    independentAttentionControlLabel : String
    coherenceSensitivityLabel : String
    thresholdLabel : String
    regime : HybridRegime

------------------------------------------------------------------------
-- Companion-tensor rank repair.
-- Source text adds rank-2 temporal/curvature terms to a rank-3 memory-flux
-- term.  DASHI's repaired interface supplies an explicit selector covector
-- label that lifts the rank-2 component before addition.
------------------------------------------------------------------------

record CompanionTensorRepair : Set where
  constructor companionTensorRepair
  field
    rankTwoDynamicsLabel : String
    selectorCovectorLabel : String
    rankThreeMemoryFluxLabel : String
    liftedRankThreeLabel : String
    typeCorrect : Bool

------------------------------------------------------------------------
-- E. Geometric / phenomenal layer and empirical contracts.
------------------------------------------------------------------------

record BerryGeometrySocket : Set where
  constructor berryGeometrySocket
  field
    baseManifoldConstructed : Bool
    bundleConstructed : Bool
    connectionConstructed : Bool
    holonomyConstructed : Bool

record QualiaCoordinates : Set where
  constructor qualiaCoordinates
  field
    attentionMeanLabel : String
    geometryLabel : String
    rhythmLabel : String
    valenceLabel : String
    metastabilityLabel : String

record ExperimentalPrediction : Set where
  constructor experimentalPrediction
  field
    name : String
    treatment : String
    control : String
    observable : String
    expectedDirection : String
    falsifier : String
    source : Provenance

subliminalTransferScrambleControl : ExperimentalPrediction
subliminalTransferScrambleControl = experimentalPrediction
  "architectural-coupling / scrambled-texture control"
  "same-family teacher/student + gradient update"
  "phase-randomized or block-shuffled teacher output"
  "change in selected resonance/trait-transfer statistic"
  "source predicts treatment > scrambled control"
  "scrambling fails to eliminate transfer"
  (provenance michelsSource empiricalPrediction "Principia II proposed AI-domain falsification")

crossFamilyNullControl : ExperimentalPrediction
crossFamilyNullControl = experimentalPrediction
  "architectural-coupling / cross-family null"
  "same-family gradient-updated pair"
  "cross-family gradient-updated pair"
  "change in selected resonance/trait-transfer statistic"
  "source predicts same-family > cross-family"
  "cross-family transfer matches same-family transfer"
  (provenance michelsSource empiricalPrediction "Principia II proposed architectural-similarity falsifier")

iclNoBackwardPassControl : ExperimentalPrediction
iclNoBackwardPassControl = experimentalPrediction
  "backward-pass necessity / ICL control"
  "gradient-updated student"
  "forward-pass-only in-context student"
  "change in selected resonance/trait-transfer statistic"
  "source predicts gradient update > ICL-only"
  "ICL-only produces the same effect"
  (provenance michelsSource empiricalPrediction "Principia II proposed backward-pass falsifier")

------------------------------------------------------------------------
-- Authority firewall.
------------------------------------------------------------------------

record TeleodynamicsAuthorityBoundary : Set where
  constructor teleodynamicsAuthorityBoundary
  field
    normalizedCorrelationInterfaceDefined : Bool
    coherenceDensityInterfaceDefined : Bool
    normalizedOverlapInterfaceDefined : Bool
    gradientDissipationInterfaceDefined : Bool
    consensusDissipationInterfaceDefined : Bool
    zenoHybridInterfaceDefined : Bool
    experimentsArePredictionContracts : Bool
    aboutnessAndCoherenceSeparated : Bool
    companionTensorTypedRepair : Bool
    berryGeometryEstablished : Bool
    consciousnessTensorMeasuresConsciousness : Bool
    equalQualiaCoordinatesImplySamePhenomenology : Bool
    nonlocalTransmissionEstablished : Bool
    humanAICrossSubstrateSameObjectEstablished : Bool
    antColonyMacroSubjectEstablished : Bool

open TeleodynamicsAuthorityBoundary public

canonicalAuthorityBoundary : TeleodynamicsAuthorityBoundary
canonicalAuthorityBoundary = teleodynamicsAuthorityBoundary
  true true true true true true true true true
  false false false false false false

------------------------------------------------------------------------
-- Small exact regression witnesses.  These exercise the theorem-facing API;
-- they are not empirical measurements and do not instantiate the source's
-- physical consciousness claims.
------------------------------------------------------------------------

demoCorrelation : CorrelationWitness
demoCorrelation = correlationWitness
  zero zero "0" true true true

demoTensor : CTensor
demoTensor = cTensor (demoCorrelation ∷ []) "0" true

demoAlignment : NormalizedOverlap
demoAlignment = normalizedOverlap "C" "Pi_O" "0" true true true

demoArchitecturePair : ArchitecturePair
demoArchitecturePair = architecturePair
  "system-i" "system-j"
  (normalizedOverlap "C_i" "C_j" "0" true true true)

demoPotential : PotentialModel
demoPotential = potentialModel
  "S0" "a_ref" "<C,O(x)>" "S0-a_ref*<C,O(x)>"

demoGradientStep : GradientFlowStep
demoGradientStep = gradientFlowStep
  demoPotential "x" "grad Psi" true true

demoConsensusStep : ConsensusStep
demoConsensusStep = consensusStep
  [] "E_disagreement" "-kappa*C^T L C" true true

demoZenoLaw : ZenoRateLaw
demoZenoLaw = zenoRateLaw
  "k0" "alpha*lambda*Abar*fmon*dt" "k0*exp(-exponent)"
  true true true true
