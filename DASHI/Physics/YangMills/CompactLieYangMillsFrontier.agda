module DASHI.Physics.YangMills.CompactLieYangMillsFrontier where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBackgroundFieldClosure

------------------------------------------------------------------------
-- Proof-level ledger for the compact-group Yang--Mills route.
------------------------------------------------------------------------

data CompactLieYMClaim : Set where
  groupLawsDerived                  : CompactLieYMClaim
  su2QuaternionGroup               : CompactLieYMClaim
  su2LieBracketAndJacobi           : CompactLieYMClaim
  su2AdjointRealizesGenericAd      : CompactLieYMClaim
  pathHolonomyGaugeCovariance      : CompactLieYMClaim
  blockAverageStructuralCovariance : CompactLieYMClaim
  weightedColumnImpliesDecay       : CompactLieYMClaim
  localLipschitzImpliesContraction : CompactLieYMClaim

  uniformProductBridge             : CompactLieYMClaim
  oneStepPolymerBudgetBridge       : CompactLieYMClaim
  concreteStepVBridge              : CompactLieYMClaim
  quantitativeAllScaleBridge       : CompactLieYMClaim
  continuumOSLimitBridge           : CompactLieYMClaim
  uniformGapSurvivalBridge         : CompactLieYMClaim

  compactInvariantMetric          : CompactLieYMClaim
  localExponentialChart           : CompactLieYMClaim
  quantitativeBCH                 : CompactLieYMClaim
  normalizedHaar                  : CompactLieYMClaim
  peterWeylCharacters             : CompactLieYMClaim
  cartanKillingClassification     : CompactLieYMClaim

  concreteAllPatchGreenEstimate   : CompactLieYMClaim
  concreteNonlinearResidualBound  : CompactLieYMClaim
  hessianCoercivity               : CompactLieYMClaim
  gaugeFixingContraction          : CompactLieYMClaim
  backgroundFieldClosure          : CompactLieYMClaim

  strictUniformResidualContraction : CompactLieYMClaim
  fourDimensionalLargeFieldStepV   : CompactLieYMClaim
  allScaleFourDimensionalRG         : CompactLieYMClaim
  continuumOSAxioms                 : CompactLieYMClaim
  positivePhysicalMassGap           : CompactLieYMClaim

claimLevel : CompactLieYMClaim → ProofLevel
claimLevel groupLawsDerived = machineChecked
claimLevel su2QuaternionGroup = machineChecked
claimLevel su2LieBracketAndJacobi = machineChecked
claimLevel su2AdjointRealizesGenericAd = machineChecked
claimLevel pathHolonomyGaugeCovariance = machineChecked
claimLevel blockAverageStructuralCovariance = machineChecked
claimLevel weightedColumnImpliesDecay = machineChecked
claimLevel localLipschitzImpliesContraction = machineChecked

claimLevel uniformProductBridge = machineChecked
claimLevel oneStepPolymerBudgetBridge = machineChecked
claimLevel concreteStepVBridge = machineChecked
claimLevel quantitativeAllScaleBridge = machineChecked
claimLevel continuumOSLimitBridge = machineChecked
claimLevel uniformGapSurvivalBridge = machineChecked

claimLevel compactInvariantMetric = standardImported
claimLevel localExponentialChart = standardImported
claimLevel quantitativeBCH = standardImported
claimLevel normalizedHaar = standardImported
claimLevel peterWeylCharacters = standardImported
claimLevel cartanKillingClassification = standardImported

claimLevel concreteAllPatchGreenEstimate = conditional
claimLevel concreteNonlinearResidualBound = conditional
claimLevel hessianCoercivity = conditional
claimLevel gaugeFixingContraction = conditional
claimLevel backgroundFieldClosure = conditional

claimLevel strictUniformResidualContraction = conjectural
claimLevel fourDimensionalLargeFieldStepV = conjectural
claimLevel allScaleFourDimensionalRG = conjectural
claimLevel continuumOSAxioms = conjectural
claimLevel positivePhysicalMassGap = conjectural

claimLocallyPromotable : CompactLieYMClaim → Bool
claimLocallyPromotable claim = promotable (claimLevel claim)

massGapDoesNotSelfPromote :
  claimLocallyPromotable positivePhysicalMassGap ≡ false
massGapDoesNotSelfPromote = refl

uniformGapBridgeDoesPromote :
  claimLocallyPromotable uniformGapSurvivalBridge ≡ true
uniformGapBridgeDoesPromote = refl

su2AdjointIsLocallyPromotable :
  claimLocallyPromotable su2AdjointRealizesGenericAd ≡ true
su2AdjointIsLocallyPromotable = refl

------------------------------------------------------------------------
-- Conjectured theorem objects are represented as exact target types.  No
-- constructor is supplied by this module, so naming the frontier never proves
-- it.  A future proof may inhabit these records without changing downstream IO.
------------------------------------------------------------------------

record UniformResidualContractionTarget
    (Index State Bound : Set) : Set₁ where
  field
    residual : Index → State → State
    norm : State → Bound
    rho : Bound
    StrictlyBelowOne : Bound → Set
    LessEqual : Bound → Bound → Set
    multiply : Bound → Bound → Bound
    rhoStrict : StrictlyBelowOne rho
    uniformContraction : ∀ index state →
      LessEqual (norm (residual index state)) (multiply rho (norm state))

record LargeFieldStepVTarget (Polymer Bound : Set) : Set₁ where
  field
    activity : Polymer → Bound
    DiameterEntropyControlled : Set
    LargeFieldSuppressed : Set
    KoteckyPreissSummable : Set
    diameterEntropyControlled : DiameterEntropyControlled
    largeFieldSuppressed : LargeFieldSuppressed
    koteckyPreissSummable : KoteckyPreissSummable

record AllScaleRGTarget (Scale EffectiveTheory : Set) : Set₁ where
  field
    renormalize : Scale → EffectiveTheory → EffectiveTheory
    InvariantDomain : Scale → EffectiveTheory → Set
    invariantUnderEveryStep : ∀ scale theory →
      InvariantDomain scale theory → InvariantDomain scale (renormalize scale theory)
    SummableErrors : Set
    summableErrors : SummableErrors

record ContinuumOSTarget (SchwingerFamily : Set) : Set₁ where
  field
    continuumSchwingerFunctions : SchwingerFamily
    OS0 OS1 OS2 OS3 OS4 OS5 : SchwingerFamily → Set
    os0 : OS0 continuumSchwingerFunctions
    os1 : OS1 continuumSchwingerFunctions
    os2 : OS2 continuumSchwingerFunctions
    os3 : OS3 continuumSchwingerFunctions
    os4 : OS4 continuumSchwingerFunctions
    os5 : OS5 continuumSchwingerFunctions

record PhysicalMassGapTarget (Hamiltonian Gap : Set) : Set₁ where
  field
    reconstructedHamiltonian : Hamiltonian
    gap : Gap
    Positive : Gap → Set
    SpectrumSeparatedBy : Hamiltonian → Gap → Set
    positiveGap : Positive gap
    spectrumSeparated : SpectrumSeparatedBy reconstructedHamiltonian gap

record FullCompactLieYangMillsClosure
    (Coarse State Gauge Index Bound Polymer Scale EffectiveTheory
     SchwingerFamily Hamiltonian Gap : Set)
    (criticalMap : State → State)
    (Critical Minimizer : State → Set) : Set₁ where
  field
    background :
      BackgroundFieldClosure Coarse State Gauge criticalMap Critical Minimizer
    residualContraction : UniformResidualContractionTarget Index State Bound
    largeFieldStepV : LargeFieldStepVTarget Polymer Bound
    allScaleRG : AllScaleRGTarget Scale EffectiveTheory
    continuumOS : ContinuumOSTarget SchwingerFamily
    physicalMassGap : PhysicalMassGapTarget Hamiltonian Gap

open FullCompactLieYangMillsClosure public
