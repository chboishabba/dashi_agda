module DASHI.Physics.Closure.PenguinDecayResidualComparisonLaw where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
import Data.Nat.Properties as NatP
  using (_≤?_)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Physics.Closure.ResidualComparisonLaw as Residual
import DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt as Projection
import DASHI.Physics.Closure.PenguinDecayObservableContract as Contract
import DASHI.Physics.Closure.PenguinDecayProjectionArtifact as Artifact
import DASHI.Physics.Closure.PenguinDecaySMBaselineAuthority as Baseline

------------------------------------------------------------------------
-- Penguin empirical-contact residual comparison law.
--
-- This is a concrete diagnostic request surface.  It consumes the finite
-- penguin projection-defect receipt when present, names the comparison modes
-- a provider must bind, and fails closed until an accepted authority route,
-- complete dataset binding, covariance calibration, and theory-uncertainty
-- budget are supplied.  The accepted law is intentionally empty here.

open Residual public
  using
    ( UniversalResidualComparisonOutcome
    ; acceptedResidualCandidate
    ; borderlineCandidate
    ; rejectedResidualCandidate
    ; insufficientAuthority
    ; theoryUncertaintyDominates
    ; freezeMissing
    ; dataMissing
    )

PenguinResidualComparisonDiagnosticOutcome : Set
PenguinResidualComparisonDiagnosticOutcome =
  UniversalResidualComparisonOutcome

canonicalPenguinResidualComparisonDiagnosticOutcomes :
  List PenguinResidualComparisonDiagnosticOutcome
canonicalPenguinResidualComparisonDiagnosticOutcomes =
  acceptedResidualCandidate
  ∷ borderlineCandidate
  ∷ rejectedResidualCandidate
  ∷ insufficientAuthority
  ∷ theoryUncertaintyDominates
  ∷ freezeMissing
  ∷ dataMissing
  ∷ []

data PenguinResidualComparisonMode : Set where
  normalizedPull :
    PenguinResidualComparisonMode
  covarianceWhitenedResidual :
    PenguinResidualComparisonMode
  angularAnomalyPattern :
    PenguinResidualComparisonMode
  theoryUncertaintyDominatesComparisonMode :
    PenguinResidualComparisonMode

canonicalPenguinResidualComparisonModes :
  List PenguinResidualComparisonMode
canonicalPenguinResidualComparisonModes =
  normalizedPull
  ∷ covarianceWhitenedResidual
  ∷ angularAnomalyPattern
  ∷ theoryUncertaintyDominatesComparisonMode
  ∷ []

data PenguinEmpiricalContact : Set where
  bToSLeptonPairAngularContact :
    PenguinEmpiricalContact
  bToSLeptonPairBranchingRatioContact :
    PenguinEmpiricalContact
  bToDPhotonBranchingRatioContact :
    PenguinEmpiricalContact
  cToULeptonPairNullSearchContact :
    PenguinEmpiricalContact

canonicalPenguinEmpiricalContacts :
  List PenguinEmpiricalContact
canonicalPenguinEmpiricalContacts =
  bToSLeptonPairAngularContact
  ∷ bToSLeptonPairBranchingRatioContact
  ∷ bToDPhotonBranchingRatioContact
  ∷ cToULeptonPairNullSearchContact
  ∷ []

contactDecay :
  PenguinEmpiricalContact →
  Projection.RarePenguinDecay
contactDecay bToSLeptonPairAngularContact =
  Projection.bToSLeptonPair
contactDecay bToSLeptonPairBranchingRatioContact =
  Projection.bToSLeptonPair
contactDecay bToDPhotonBranchingRatioContact =
  Projection.bToDPhoton
contactDecay cToULeptonPairNullSearchContact =
  Projection.cToULeptonPair

contactObservable :
  PenguinEmpiricalContact →
  Projection.IndirectObservable
contactObservable bToSLeptonPairAngularContact =
  Projection.angularCoefficientDeviation
contactObservable bToSLeptonPairBranchingRatioContact =
  Projection.branchingRatioDeviation
contactObservable bToDPhotonBranchingRatioContact =
  Projection.branchingRatioDeviation
contactObservable cToULeptonPairNullSearchContact =
  Projection.branchingRatioDeviation

record PenguinResidualComparisonCandidate : Set where
  constructor mkPenguinResidualComparisonCandidate
  field
    contact :
      PenguinEmpiricalContact

    mode :
      PenguinResidualComparisonMode

    decay :
      Projection.RarePenguinDecay

    observable :
      Projection.IndirectObservable

    indirectWitness :
      Projection.IndirectWitness

    decayMatchesContact :
      decay ≡ contactDecay contact

    observableMatchesContact :
      observable ≡ contactObservable contact

    witnessIsIndirect :
      Projection.extractionMode indirectWitness
      ≡
      Projection.indirectProjectionDefectExtraction

    witnessDefectIsResidual :
      Projection.extractedDefect indirectWitness
      ≡
      Projection.residualDefectSurface

open PenguinResidualComparisonCandidate public

candidateFor :
  PenguinEmpiricalContact →
  PenguinResidualComparisonMode →
  PenguinResidualComparisonCandidate
candidateFor contact mode =
  mkPenguinResidualComparisonCandidate
    contact
    mode
    (contactDecay contact)
    (contactObservable contact)
    (Projection.extractIndirectWitness
      (contactDecay contact)
      (contactObservable contact))
    refl
    refl
    refl
    refl

data PenguinResidualComparisonRequiredBinding : Set where
  requiresExactDatasetAuthority :
    PenguinResidualComparisonRequiredBinding
  requiresChecksumBoundObservableSelection :
    PenguinResidualComparisonRequiredBinding
  requiresNormalizedPullDefinition :
    PenguinResidualComparisonRequiredBinding
  requiresFullCovarianceWhitening :
    PenguinResidualComparisonRequiredBinding
  requiresAngularAnomalyPatternDefinition :
    PenguinResidualComparisonRequiredBinding
  requiresTheoryUncertaintyBudget :
    PenguinResidualComparisonRequiredBinding
  requiresProjectionDefectReceiptBinding :
    PenguinResidualComparisonRequiredBinding
  requiresAcceptedAuthorityRoute :
    PenguinResidualComparisonRequiredBinding

canonicalPenguinResidualComparisonRequiredBindings :
  List PenguinResidualComparisonRequiredBinding
canonicalPenguinResidualComparisonRequiredBindings =
  requiresExactDatasetAuthority
  ∷ requiresChecksumBoundObservableSelection
  ∷ requiresNormalizedPullDefinition
  ∷ requiresFullCovarianceWhitening
  ∷ requiresAngularAnomalyPatternDefinition
  ∷ requiresTheoryUncertaintyBudget
  ∷ requiresProjectionDefectReceiptBinding
  ∷ requiresAcceptedAuthorityRoute
  ∷ []

modeOutcomeWithoutAuthority :
  PenguinResidualComparisonMode →
  PenguinResidualComparisonDiagnosticOutcome
modeOutcomeWithoutAuthority normalizedPull =
  insufficientAuthority
modeOutcomeWithoutAuthority covarianceWhitenedResidual =
  insufficientAuthority
modeOutcomeWithoutAuthority angularAnomalyPattern =
  insufficientAuthority
modeOutcomeWithoutAuthority theoryUncertaintyDominatesComparisonMode =
  theoryUncertaintyDominates

twentyFive twentyEight : Nat
twentyFive =
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))
twentyEight =
  suc (suc (suc twentyFive))

data PenguinResidualSigmaSign : Set where
  negativeSigma :
    PenguinResidualSigmaSign
  positiveSigma :
    PenguinResidualSigmaSign

data P5PrimeResidualQ2Bin : Set where
  q2Bin4To6 :
    P5PrimeResidualQ2Bin
  q2Bin6To8 :
    P5PrimeResidualQ2Bin

canonicalP5PrimeResidualQ2Bins :
  List P5PrimeResidualQ2Bin
canonicalP5PrimeResidualQ2Bins =
  q2Bin4To6
  ∷ q2Bin6To8
  ∷ []

data P5PrimeResidualVectorStatus : Set where
  p5PrimeBorderlineAnomalyCandidate :
    P5PrimeResidualVectorStatus
  p5PrimeAcceptedResidualNotClaimed :
    P5PrimeResidualVectorStatus
  p5PrimeResidualVectorAuthorityGated :
    P5PrimeResidualVectorStatus

p5PrimePullFormula :
  String
p5PrimePullFormula =
  "r = (obs - SM) / sqrt(stat^2 + syst^2 + th^2)"

p5PrimeTenthsExceedsTwoPointFive :
  Nat →
  Bool
p5PrimeTenthsExceedsTwoPointFive sigmaTenths with twentyFive NatP.≤? sigmaTenths
... | yes _ =
  true
... | no _ =
  false

boolAnd :
  Bool →
  Bool →
  Bool
boolAnd true value =
  value
boolAnd false _ =
  false

record P5PrimeResidualBinComparison : Set where
  constructor mkP5PrimeResidualBinComparison
  field
    q2Bin :
      P5PrimeResidualQ2Bin

    residualFormula :
      String

    residualFormulaIsCanonical :
      residualFormula
      ≡
      p5PrimePullFormula

    sigmaSign :
      PenguinResidualSigmaSign

    sigmaMagnitudeTenths :
      Nat

    sigmaBand :
      Residual.SigmaBand

    sigmaBandIsBorderline :
      sigmaBand
      ≡
      Residual.sigmaAtMostThree

    sigmaBandMatchesMagnitude :
      Residual.classifyTenthSigmaBand sigmaMagnitudeTenths
      ≡
      sigmaBand

    exceedsTwoPointFiveSigma :
      Bool

    exceedsTwoPointFiveSigmaIsTrue :
      exceedsTwoPointFiveSigma
      ≡
      true

    binOutcome :
      PenguinResidualComparisonDiagnosticOutcome

    binOutcomeIsBorderline :
      binOutcome
      ≡
      borderlineCandidate

    binOutcomeMatchesBand :
      Residual.sigmaBandOutcome sigmaBand
      ≡
      binOutcome

open P5PrimeResidualBinComparison public

p5Prime4To6ResidualBinComparison :
  P5PrimeResidualBinComparison
p5Prime4To6ResidualBinComparison =
  mkP5PrimeResidualBinComparison
    q2Bin4To6
    p5PrimePullFormula
    refl
    negativeSigma
    twentyEight
    Residual.sigmaAtMostThree
    refl
    refl
    (p5PrimeTenthsExceedsTwoPointFive twentyEight)
    refl
    borderlineCandidate
    refl
    refl

p5Prime6To8ResidualBinComparison :
  P5PrimeResidualBinComparison
p5Prime6To8ResidualBinComparison =
  mkP5PrimeResidualBinComparison
    q2Bin6To8
    p5PrimePullFormula
    refl
    negativeSigma
    Residual.thirty
    Residual.sigmaAtMostThree
    refl
    refl
    (p5PrimeTenthsExceedsTwoPointFive Residual.thirty)
    refl
    borderlineCandidate
    refl
    refl

record P5PrimeResidualVectorComparison : Set where
  constructor mkP5PrimeResidualVectorComparison
  field
    bins :
      List P5PrimeResidualQ2Bin

    binsAreCanonical :
      bins
      ≡
      canonicalP5PrimeResidualQ2Bins

    residualFormula :
      String

    residualFormulaIsCanonical :
      residualFormula
      ≡
      p5PrimePullFormula

    bin4To6Comparison :
      P5PrimeResidualBinComparison

    bin4To6ComparisonIsCanonical :
      bin4To6Comparison
      ≡
      p5Prime4To6ResidualBinComparison

    bin6To8Comparison :
      P5PrimeResidualBinComparison

    bin6To8ComparisonIsCanonical :
      bin6To8Comparison
      ≡
      p5Prime6To8ResidualBinComparison

    bothSelectedBinsExceedTwoPointFiveSigma :
      Bool

    bothSelectedBinsExceedTwoPointFiveSigmaIsTrue :
      bothSelectedBinsExceedTwoPointFiveSigma
      ≡
      true

    vectorStatus :
      P5PrimeResidualVectorStatus

    vectorStatusIsBorderlineAnomalyCandidate :
      vectorStatus
      ≡
      p5PrimeBorderlineAnomalyCandidate

    acceptedResidualCandidateConstructedHere :
      Bool

    acceptedResidualCandidateConstructedHereIsFalse :
      acceptedResidualCandidateConstructedHere
      ≡
      false

open P5PrimeResidualVectorComparison public

canonicalP5PrimeResidualVectorComparison :
  P5PrimeResidualVectorComparison
canonicalP5PrimeResidualVectorComparison =
  mkP5PrimeResidualVectorComparison
    canonicalP5PrimeResidualQ2Bins
    refl
    p5PrimePullFormula
    refl
    p5Prime4To6ResidualBinComparison
    refl
    p5Prime6To8ResidualBinComparison
    refl
    (boolAnd
      (p5PrimeTenthsExceedsTwoPointFive twentyEight)
      (p5PrimeTenthsExceedsTwoPointFive Residual.thirty))
    refl
    p5PrimeBorderlineAnomalyCandidate
    refl
    false
    refl

canonicalP5Prime4To6ResidualIsMinusTwoPointEight :
  sigmaSign p5Prime4To6ResidualBinComparison
  ≡
  negativeSigma
canonicalP5Prime4To6ResidualIsMinusTwoPointEight =
  refl

canonicalP5Prime4To6ResidualMagnitudeTenths :
  sigmaMagnitudeTenths p5Prime4To6ResidualBinComparison
  ≡
  twentyEight
canonicalP5Prime4To6ResidualMagnitudeTenths =
  refl

canonicalP5Prime4To6ResidualClassifiesBorderline :
  binOutcome p5Prime4To6ResidualBinComparison
  ≡
  borderlineCandidate
canonicalP5Prime4To6ResidualClassifiesBorderline =
  refl

canonicalP5Prime6To8ResidualIsMinusThreePointZero :
  sigmaSign p5Prime6To8ResidualBinComparison
  ≡
  negativeSigma
canonicalP5Prime6To8ResidualIsMinusThreePointZero =
  refl

canonicalP5Prime6To8ResidualMagnitudeTenths :
  sigmaMagnitudeTenths p5Prime6To8ResidualBinComparison
  ≡
  Residual.thirty
canonicalP5Prime6To8ResidualMagnitudeTenths =
  refl

canonicalP5Prime6To8ResidualClassifiesBorderline :
  binOutcome p5Prime6To8ResidualBinComparison
  ≡
  borderlineCandidate
canonicalP5Prime6To8ResidualClassifiesBorderline =
  refl

canonicalP5PrimeResidualVectorStatusIsBorderline :
  vectorStatus canonicalP5PrimeResidualVectorComparison
  ≡
  p5PrimeBorderlineAnomalyCandidate
canonicalP5PrimeResidualVectorStatusIsBorderline =
  refl

canonicalP5PrimeResidualVectorNotAcceptedHere :
  acceptedResidualCandidateConstructedHere
    canonicalP5PrimeResidualVectorComparison
  ≡
  false
canonicalP5PrimeResidualVectorNotAcceptedHere =
  refl

p5PrimeBorderlineOutcomeNotAccepted :
  borderlineCandidate
  ≡
  acceptedResidualCandidate →
  ⊥
p5PrimeBorderlineOutcomeNotAccepted ()

record P5PrimeResidualVectorBaselineCheckReceipt : Set where
  field
    baselineAuthorityChain :
      Baseline.P5PrimeSMBaselineAuthorityChain

    baselineAuthorityChainIsCanonical :
      baselineAuthorityChain
      ≡
      Baseline.canonicalP5PrimeSMBaselineAuthorityChain

    baselineArtifactPath :
      String

    baselineArtifactPathIsCanonical :
      baselineArtifactPath
      ≡
      "scripts/data/hepdata/penguin_gate5_p5prime_sm_baseline_flavio_2_7_0.json"

    baselineArtifactName :
      String

    baselineArtifactNameIsCanonical :
      baselineArtifactName
      ≡
      "penguin_gate5_p5prime_sm_baseline_flavio_2_7_0"

    flavioVersion :
      String

    flavioVersionIs270 :
      flavioVersion
      ≡
      "2.7.0"

    p5PrimeObservableKey :
      String

    p5PrimeObservableKeyIsCanonical :
      p5PrimeObservableKey
      ≡
      "<P5p>(B0->K*mumu)"

    bin4To6TheoryAuthority :
      Baseline.P5PrimeBinTheoryAuthority

    bin4To6TheoryAuthorityIsCanonical :
      bin4To6TheoryAuthority
      ≡
      Baseline.p5Prime4To6TheoryAuthority

    bin4To6SMCentralValue :
      Baseline.centralValue bin4To6TheoryAuthority
      ≡
      "-0.7583138786902011"

    bin4To6SMOneSigmaTheoryUncertainty :
      Baseline.oneSigmaTheoryUncertainty bin4To6TheoryAuthority
      ≡
      "0.07524646089051247"

    bin4To6SignedResidual :
      P5PrimeResidualBinComparison

    bin4To6SignedResidualIsCanonical :
      bin4To6SignedResidual
      ≡
      p5Prime4To6ResidualBinComparison

    bin4To6SignedResidualIsMinusTwoPointEightSigma :
      sigmaSign bin4To6SignedResidual
      ≡
      negativeSigma

    bin4To6SignedResidualMagnitudeIsTwentyEightTenths :
      sigmaMagnitudeTenths bin4To6SignedResidual
      ≡
      twentyEight

    bin6To8TheoryAuthority :
      Baseline.P5PrimeBinTheoryAuthority

    bin6To8TheoryAuthorityIsCanonical :
      bin6To8TheoryAuthority
      ≡
      Baseline.p5Prime6To8TheoryAuthority

    bin6To8SMCentralValue :
      Baseline.centralValue bin6To8TheoryAuthority
      ≡
      "-0.8342430145843444"

    bin6To8SMOneSigmaTheoryUncertainty :
      Baseline.oneSigmaTheoryUncertainty bin6To8TheoryAuthority
      ≡
      "0.06092804199708315"

    bin6To8SignedResidual :
      P5PrimeResidualBinComparison

    bin6To8SignedResidualIsCanonical :
      bin6To8SignedResidual
      ≡
      p5Prime6To8ResidualBinComparison

    bin6To8SignedResidualIsMinusThreePointZeroSigma :
      sigmaSign bin6To8SignedResidual
      ≡
      negativeSigma

    bin6To8SignedResidualMagnitudeIsThirtyTenths :
      sigmaMagnitudeTenths bin6To8SignedResidual
      ≡
      Residual.thirty

    residualVectorComparison :
      P5PrimeResidualVectorComparison

    residualVectorComparisonIsCanonical :
      residualVectorComparison
      ≡
      canonicalP5PrimeResidualVectorComparison

    residualVectorStatusIsBorderline :
      vectorStatus residualVectorComparison
      ≡
      p5PrimeBorderlineAnomalyCandidate

    acceptedResidualCandidateConstructedHereIsFalse :
      acceptedResidualCandidateConstructedHere residualVectorComparison
      ≡
      false

    localHEPDataBoundary :
      List String

open P5PrimeResidualVectorBaselineCheckReceipt public

canonicalP5PrimeResidualVectorBaselineCheckReceipt :
  P5PrimeResidualVectorBaselineCheckReceipt
canonicalP5PrimeResidualVectorBaselineCheckReceipt =
  record
    { baselineAuthorityChain =
        Baseline.canonicalP5PrimeSMBaselineAuthorityChain
    ; baselineAuthorityChainIsCanonical =
        refl
    ; baselineArtifactPath =
        "scripts/data/hepdata/penguin_gate5_p5prime_sm_baseline_flavio_2_7_0.json"
    ; baselineArtifactPathIsCanonical =
        refl
    ; baselineArtifactName =
        "penguin_gate5_p5prime_sm_baseline_flavio_2_7_0"
    ; baselineArtifactNameIsCanonical =
        refl
    ; flavioVersion =
        "2.7.0"
    ; flavioVersionIs270 =
        refl
    ; p5PrimeObservableKey =
        "<P5p>(B0->K*mumu)"
    ; p5PrimeObservableKeyIsCanonical =
        refl
    ; bin4To6TheoryAuthority =
        Baseline.p5Prime4To6TheoryAuthority
    ; bin4To6TheoryAuthorityIsCanonical =
        refl
    ; bin4To6SMCentralValue =
        refl
    ; bin4To6SMOneSigmaTheoryUncertainty =
        refl
    ; bin4To6SignedResidual =
        p5Prime4To6ResidualBinComparison
    ; bin4To6SignedResidualIsCanonical =
        refl
    ; bin4To6SignedResidualIsMinusTwoPointEightSigma =
        refl
    ; bin4To6SignedResidualMagnitudeIsTwentyEightTenths =
        refl
    ; bin6To8TheoryAuthority =
        Baseline.p5Prime6To8TheoryAuthority
    ; bin6To8TheoryAuthorityIsCanonical =
        refl
    ; bin6To8SMCentralValue =
        refl
    ; bin6To8SMOneSigmaTheoryUncertainty =
        refl
    ; bin6To8SignedResidual =
        p5Prime6To8ResidualBinComparison
    ; bin6To8SignedResidualIsCanonical =
        refl
    ; bin6To8SignedResidualIsMinusThreePointZeroSigma =
        refl
    ; bin6To8SignedResidualMagnitudeIsThirtyTenths =
        refl
    ; residualVectorComparison =
        canonicalP5PrimeResidualVectorComparison
    ; residualVectorComparisonIsCanonical =
        refl
    ; residualVectorStatusIsBorderline =
        refl
    ; acceptedResidualCandidateConstructedHereIsFalse =
        refl
    ; localHEPDataBoundary =
        "Checked against scripts/data/hepdata/penguin_gate5_p5prime_sm_baseline_flavio_2_7_0.json"
        ∷ "Baseline JSON is flavio 2.7.0 for <P5p>(B0->K*mumu), not the separate Bs->mumu baseline"
        ∷ "The local ins1486676 HEPData table present here is a normalised-moment covariance surface, not an accepted P5' [4,6]/[6,8] residual-vector authority"
        ∷ "This receipt records the published signed pulls as -2.8 sigma and -3.0 sigma over the checked SM central values and uncertainties"
        ∷ "No acceptedResidualCandidate is constructed from this P5' vector receipt"
        ∷ []
    }

canonicalP5PrimeResidualVectorBaselineCheckStatus :
  vectorStatus
    (residualVectorComparison
      canonicalP5PrimeResidualVectorBaselineCheckReceipt)
  ≡
  p5PrimeBorderlineAnomalyCandidate
canonicalP5PrimeResidualVectorBaselineCheckStatus =
  refl

canonicalP5PrimeResidualVectorBaselineCheckNotAccepted :
  acceptedResidualCandidateConstructedHere
    (residualVectorComparison
      canonicalP5PrimeResidualVectorBaselineCheckReceipt)
  ≡
  false
canonicalP5PrimeResidualVectorBaselineCheckNotAccepted =
  refl

record PenguinExpectedResidualComparison : Set where
  constructor mkPenguinExpectedResidualComparison
  field
    candidate :
      PenguinResidualComparisonCandidate

    sigmaSign :
      PenguinResidualSigmaSign

    sigmaMagnitudeTenths :
      Nat

    sigmaMagnitudeIsArtifactBoundOnly :
      sigmaMagnitudeTenths ≡ zero

    sigmaBand :
      Residual.SigmaBand

    sigmaBandIsAtMostTwo :
      sigmaBand ≡ Residual.sigmaAtMostTwo

    sigmaBandMatchesMagnitude :
      Residual.classifyTenthSigmaBand sigmaMagnitudeTenths
      ≡
      sigmaBand

    authorityGatedOutcome :
      PenguinResidualComparisonDiagnosticOutcome

    authorityGatedOutcomeIsInsufficientAuthority :
      authorityGatedOutcome ≡ insufficientAuthority

    authorityGatedOutcomeMatchesMissingAuthority :
      Residual.classifyResidualCandidate
        Residual.authorityMissing
        Residual.freezeAbsent
        Residual.dataAbsent
        Residual.theoryUncertaintyDominant
        sigmaBand
      ≡
      authorityGatedOutcome

open PenguinExpectedResidualComparison public

artifactBoundAtMostTwoSigmaPenguinResidualComparison :
  PenguinExpectedResidualComparison
artifactBoundAtMostTwoSigmaPenguinResidualComparison =
  mkPenguinExpectedResidualComparison
    (candidateFor bToSLeptonPairAngularContact normalizedPull)
    negativeSigma
    zero
    refl
    Residual.sigmaAtMostTwo
    refl
    refl
    insufficientAuthority
    refl
    refl

record PenguinResidualAcceptedCandidatePrerequisites : Set where
  constructor mkPenguinResidualAcceptedCandidatePrerequisites
  field
    datasetChecksumAuthority :
      Artifact.SuppliedPenguinDatasetChecksumAuthority

    datasetChecksumAuthorityUsesSHA256 :
      Artifact.digestAlgorithm datasetChecksumAuthority
      ≡
      "sha256"

    datasetChecksumAuthorityIsForSelectedThread :
      Artifact.sourceCandidate datasetChecksumAuthority
      ≡
      Contract.lhcbPRD105012010CDS2779103

    selectedThreadChecksumAuthorityPresent :
      Bool

    selectedThreadChecksumAuthorityPresentIsTrue :
      selectedThreadChecksumAuthorityPresent ≡ true

    acceptedAuthorityState :
      Residual.ResidualAuthorityState

    acceptedAuthorityStateIsPresent :
      acceptedAuthorityState ≡ Residual.authorityPresent

    freezeState :
      Residual.ResidualFreezeState

    freezeStateIsPresent :
      freezeState ≡ Residual.freezePresent

    freezeTuple :
      Artifact.PenguinFreezeHashPreRegistrationTuple

    freezeTupleFieldsAreCanonical :
      Artifact.tupleFields freezeTuple
      ≡
      Artifact.canonicalPenguinPreRegistrationTupleFields

    noPosteriorTuningBlockers :
      List Artifact.PenguinNoPosteriorTuningBlocker

    noPosteriorTuningBlockersAreCanonical :
      noPosteriorTuningBlockers
      ≡
      Artifact.canonicalPenguinNoPosteriorTuningBlockers

    dataState :
      Residual.ResidualDataState

    dataStateIsPresent :
      dataState ≡ Residual.dataPresent

    theoryUncertaintyState :
      Residual.ResidualTheoryUncertaintyState

    theoryUncertaintyStateIsControlled :
      theoryUncertaintyState ≡ Residual.theoryUncertaintyControlled

open PenguinResidualAcceptedCandidatePrerequisites public

acceptedResidualCandidateForArtifactBoundAtMostTwoSigma :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  Residual.classifyResidualCandidate
    (acceptedAuthorityState prerequisites)
    (freezeState prerequisites)
    (dataState prerequisites)
    (theoryUncertaintyState prerequisites)
    Residual.sigmaAtMostTwo
  ≡
  acceptedResidualCandidate
acceptedResidualCandidateForArtifactBoundAtMostTwoSigma prerequisites
  rewrite acceptedAuthorityStateIsPresent prerequisites
        | freezeStateIsPresent prerequisites
        | dataStateIsPresent prerequisites
        | theoryUncertaintyStateIsControlled prerequisites =
  refl

artifactBoundAtMostTwoSigmaOutcomeWithMissingAuthority :
  (freeze : Residual.ResidualFreezeState) →
  (dataState : Residual.ResidualDataState) →
  (theory : Residual.ResidualTheoryUncertaintyState) →
  Residual.classifyResidualCandidate
    Residual.authorityMissing
    freeze
    dataState
    theory
    Residual.sigmaAtMostTwo
  ≡
  insufficientAuthority
artifactBoundAtMostTwoSigmaOutcomeWithMissingAuthority freeze dataState theory =
  Residual.authorityMissingPrecedesDataMissing
    freeze
    dataState
    theory
    Residual.sigmaAtMostTwo

acceptedResidualCandidateBridgeForFrozenPenguinTuple :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  Artifact.tupleFields (freezeTuple prerequisites)
  ≡
  Artifact.canonicalPenguinPreRegistrationTupleFields
acceptedResidualCandidateBridgeForFrozenPenguinTuple prerequisites =
  freezeTupleFieldsAreCanonical prerequisites

acceptedResidualCandidateBridgeNoPosteriorTuningBlockers :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  noPosteriorTuningBlockers prerequisites
  ≡
  Artifact.canonicalPenguinNoPosteriorTuningBlockers
acceptedResidualCandidateBridgeNoPosteriorTuningBlockers prerequisites =
  noPosteriorTuningBlockersAreCanonical prerequisites

acceptedResidualCandidateBridgeUsesSuppliedChecksumCanonical :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  Artifact.digestAlgorithm (datasetChecksumAuthority prerequisites)
  ≡
  "sha256"
acceptedResidualCandidateBridgeUsesSuppliedChecksumCanonical prerequisites =
  datasetChecksumAuthorityUsesSHA256 prerequisites

data AcceptedPenguinResidualComparisonLaw : Set where

acceptedPenguinResidualComparisonLawImpossibleHere :
  AcceptedPenguinResidualComparisonLaw →
  ⊥
acceptedPenguinResidualComparisonLawImpossibleHere ()

record PenguinDecayResidualComparisonLaw : Set where
  field
    projectionReceipt :
      Projection.PenguinDecayProjectionDefectReceipt

    currentOutcome :
      PenguinResidualComparisonDiagnosticOutcome

    currentOutcomeIsInsufficientAuthority :
      currentOutcome ≡ insufficientAuthority

    diagnosticOutcomes :
      List PenguinResidualComparisonDiagnosticOutcome

    diagnosticOutcomesAreCanonical :
      diagnosticOutcomes
      ≡
      canonicalPenguinResidualComparisonDiagnosticOutcomes

    comparisonModes :
      List PenguinResidualComparisonMode

    comparisonModesAreCanonical :
      comparisonModes
      ≡
      canonicalPenguinResidualComparisonModes

    empiricalContacts :
      List PenguinEmpiricalContact

    empiricalContactsAreCanonical :
      empiricalContacts
      ≡
      canonicalPenguinEmpiricalContacts

    candidate :
      PenguinEmpiricalContact →
      PenguinResidualComparisonMode →
      PenguinResidualComparisonCandidate

    candidateUsesProjectionDefectReceipt :
      (contact : PenguinEmpiricalContact) →
      (mode : PenguinResidualComparisonMode) →
      Projection.extractedDefect
        (indirectWitness (candidate contact mode))
      ≡
      Projection.residualDefectSurface

    outcomeWithoutAuthority :
      PenguinResidualComparisonMode →
      PenguinResidualComparisonDiagnosticOutcome

    outcomeWithoutAuthorityMatchesModeLaw :
      (mode : PenguinResidualComparisonMode) →
      outcomeWithoutAuthority mode ≡ modeOutcomeWithoutAuthority mode

    requiredBindings :
      List PenguinResidualComparisonRequiredBinding

    requiredBindingsAreCanonical :
      requiredBindings
      ≡
      canonicalPenguinResidualComparisonRequiredBindings

    datasetBindingComplete :
      Bool

    datasetBindingCompleteIsFalse :
      datasetBindingComplete ≡ false

    acceptedAuthorityAvailable :
      Bool

    acceptedAuthorityAvailableIsFalse :
      acceptedAuthorityAvailable ≡ false

    acceptedLawConstructedHere :
      Bool

    acceptedLawConstructedHereIsFalse :
      acceptedLawConstructedHere ≡ false

    acceptedLawImpossibleHere :
      AcceptedPenguinResidualComparisonLaw →
      ⊥

    expectedResidualComparison :
      PenguinExpectedResidualComparison

    expectedResidualComparisonIsArtifactBoundAtMostTwoSigma :
      expectedResidualComparison
      ≡
      artifactBoundAtMostTwoSigmaPenguinResidualComparison

    acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent :
      (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
      Residual.classifyResidualCandidate
        (acceptedAuthorityState prerequisites)
        (freezeState prerequisites)
        (dataState prerequisites)
        (theoryUncertaintyState prerequisites)
        Residual.sigmaAtMostTwo
      ≡
      acceptedResidualCandidate

    acceptedResidualCandidateBridgeUsesFrozenTuple :
      (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
      Artifact.tupleFields (freezeTuple prerequisites)
      ≡
      Artifact.canonicalPenguinPreRegistrationTupleFields

    acceptedResidualCandidateBridgeUsesNoPosteriorTuningBlockers :
      (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
      noPosteriorTuningBlockers prerequisites
      ≡
      Artifact.canonicalPenguinNoPosteriorTuningBlockers

    acceptedResidualCandidateBridgeUsesSuppliedChecksum :
      (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
      Artifact.digestAlgorithm (datasetChecksumAuthority prerequisites)
      ≡
      "sha256"

    artifactBoundAtMostTwoSigmaStillInsufficientWithoutAuthority :
      (freeze : Residual.ResidualFreezeState) →
      (dataState : Residual.ResidualDataState) →
      (theory : Residual.ResidualTheoryUncertaintyState) →
      Residual.classifyResidualCandidate
        Residual.authorityMissing
        freeze
        dataState
        theory
        Residual.sigmaAtMostTwo
      ≡
      insufficientAuthority

    p5PrimeResidualVectorComparison :
      P5PrimeResidualVectorComparison

    p5PrimeResidualVectorComparisonIsCanonical :
      p5PrimeResidualVectorComparison
      ≡
      canonicalP5PrimeResidualVectorComparison

    p5PrimeResidualVectorStatus :
      P5PrimeResidualVectorStatus

    p5PrimeResidualVectorStatusIsBorderlineAnomalyCandidate :
      p5PrimeResidualVectorStatus
      ≡
      p5PrimeBorderlineAnomalyCandidate

    p5PrimeResidualVectorAcceptedCandidateConstructedHere :
      Bool

    p5PrimeResidualVectorAcceptedCandidateConstructedHereIsFalse :
      p5PrimeResidualVectorAcceptedCandidateConstructedHere
      ≡
      false

    requestBoundary :
      List String

open PenguinDecayResidualComparisonLaw public

canonicalPenguinDecayResidualComparisonLaw :
  PenguinDecayResidualComparisonLaw
canonicalPenguinDecayResidualComparisonLaw =
  record
    { projectionReceipt =
        Projection.canonicalPenguinDecayProjectionDefectReceipt
    ; currentOutcome =
        insufficientAuthority
    ; currentOutcomeIsInsufficientAuthority =
        refl
    ; diagnosticOutcomes =
        canonicalPenguinResidualComparisonDiagnosticOutcomes
    ; diagnosticOutcomesAreCanonical =
        refl
    ; comparisonModes =
        canonicalPenguinResidualComparisonModes
    ; comparisonModesAreCanonical =
        refl
    ; empiricalContacts =
        canonicalPenguinEmpiricalContacts
    ; empiricalContactsAreCanonical =
        refl
    ; candidate =
        candidateFor
    ; candidateUsesProjectionDefectReceipt =
        λ _ _ → refl
    ; outcomeWithoutAuthority =
        modeOutcomeWithoutAuthority
    ; outcomeWithoutAuthorityMatchesModeLaw =
        λ _ → refl
    ; requiredBindings =
        canonicalPenguinResidualComparisonRequiredBindings
    ; requiredBindingsAreCanonical =
        refl
    ; datasetBindingComplete =
        false
    ; datasetBindingCompleteIsFalse =
        refl
    ; acceptedAuthorityAvailable =
        false
    ; acceptedAuthorityAvailableIsFalse =
        refl
    ; acceptedLawConstructedHere =
        false
    ; acceptedLawConstructedHereIsFalse =
        refl
    ; acceptedLawImpossibleHere =
        acceptedPenguinResidualComparisonLawImpossibleHere
    ; expectedResidualComparison =
        artifactBoundAtMostTwoSigmaPenguinResidualComparison
    ; expectedResidualComparisonIsArtifactBoundAtMostTwoSigma =
        refl
    ; acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent =
        acceptedResidualCandidateForArtifactBoundAtMostTwoSigma
    ; acceptedResidualCandidateBridgeUsesFrozenTuple =
        acceptedResidualCandidateBridgeForFrozenPenguinTuple
    ; acceptedResidualCandidateBridgeUsesNoPosteriorTuningBlockers =
        acceptedResidualCandidateBridgeNoPosteriorTuningBlockers
    ; acceptedResidualCandidateBridgeUsesSuppliedChecksum =
        acceptedResidualCandidateBridgeUsesSuppliedChecksumCanonical
    ; artifactBoundAtMostTwoSigmaStillInsufficientWithoutAuthority =
        artifactBoundAtMostTwoSigmaOutcomeWithMissingAuthority
    ; p5PrimeResidualVectorComparison =
        canonicalP5PrimeResidualVectorComparison
    ; p5PrimeResidualVectorComparisonIsCanonical =
        refl
    ; p5PrimeResidualVectorStatus =
        p5PrimeBorderlineAnomalyCandidate
    ; p5PrimeResidualVectorStatusIsBorderlineAnomalyCandidate =
        refl
    ; p5PrimeResidualVectorAcceptedCandidateConstructedHere =
        false
    ; p5PrimeResidualVectorAcceptedCandidateConstructedHereIsFalse =
        refl
    ; requestBoundary =
        "Diagnostic request for penguin empirical-contact residual comparison"
        ∷ "Consumes the finite projection-defect receipt for rare penguin decays"
        ∷ "Comparison modes are normalized pull, covariance-whitened residual, angular anomaly pattern, and theory-uncertainty-dominates"
        ∷ "Fail-closed outcomes use ResidualComparisonLaw: acceptedResidualCandidate, borderlineCandidate, rejectedResidualCandidate, insufficientAuthority, theoryUncertaintyDominates, freezeMissing, and dataMissing"
        ∷ "Gate 5 P5' residual vector uses r = (obs - SM) / sqrt(stat^2 + syst^2 + th^2) in q2 bins [4,6] and [6,8]"
        ∷ "Published LHCb per-bin deviations are recorded as signed pulls: [4,6] = -2.8 sigma and [6,8] = -3.0 sigma"
        ∷ "Because both selected bins exceed 2.5 sigma and remain within the <=3 sigma band, the vector status is borderline/anomaly candidate rather than accepted residual"
        ∷ "Artifact-bound sub-2-sigma b -> s lepton-pair residual comparisons can classify as acceptedResidualCandidate only when a selected-thread sha256 dataset checksum authority, accepted authority, freeze, data, and controlled-theory prerequisites are present"
        ∷ "No canonical acceptedResidualCandidate prerequisite is fabricated here; the live diagnostic remains insufficientAuthority until all selected-thread checksum, authority, freeze, data, and controlled-theory prerequisites are supplied"
        ∷ "Canonical current outcome is insufficientAuthority"
        ∷ "Dataset binding and accepted authority route are absent here"
        ∷ "No accepted residual comparison law or empirical promotion is constructed here"
        ∷ []
    }

canonicalPenguinResidualComparisonCurrentOutcome :
  currentOutcome canonicalPenguinDecayResidualComparisonLaw
  ≡
  insufficientAuthority
canonicalPenguinResidualComparisonCurrentOutcome =
  refl

canonicalPenguinResidualComparisonAcceptedLawImpossible :
  AcceptedPenguinResidualComparisonLaw →
  ⊥
canonicalPenguinResidualComparisonAcceptedLawImpossible =
  acceptedLawImpossibleHere canonicalPenguinDecayResidualComparisonLaw

canonicalPenguinArtifactBoundAtMostTwoSigmaAcceptedWhenPrerequisitesPresent :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  Residual.classifyResidualCandidate
    (acceptedAuthorityState prerequisites)
    (freezeState prerequisites)
    (dataState prerequisites)
    (theoryUncertaintyState prerequisites)
    Residual.sigmaAtMostTwo
  ≡
  acceptedResidualCandidate
canonicalPenguinArtifactBoundAtMostTwoSigmaAcceptedWhenPrerequisitesPresent =
  acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent
    canonicalPenguinDecayResidualComparisonLaw

canonicalPenguinArtifactBoundAtMostTwoSigmaStillInsufficientWithoutAuthority :
  (freeze : Residual.ResidualFreezeState) →
  (dataState : Residual.ResidualDataState) →
  (theory : Residual.ResidualTheoryUncertaintyState) →
  Residual.classifyResidualCandidate
    Residual.authorityMissing
    freeze
    dataState
    theory
    Residual.sigmaAtMostTwo
  ≡
  insufficientAuthority
canonicalPenguinArtifactBoundAtMostTwoSigmaStillInsufficientWithoutAuthority =
  artifactBoundAtMostTwoSigmaStillInsufficientWithoutAuthority
    canonicalPenguinDecayResidualComparisonLaw
