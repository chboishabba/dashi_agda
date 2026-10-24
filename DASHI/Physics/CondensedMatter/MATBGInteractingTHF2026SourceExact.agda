module DASHI.Physics.CondensedMatter.MATBGInteractingTHF2026SourceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.CondensedMatter.MATBG2026VerticalSliceExact as MATBG

------------------------------------------------------------------------
-- 2026 INTERACTING / TOPLOGICAL-HEAVY-FERMION SOURCE RECEIPTS
--
-- Xiao et al. give an explicit THF/Hubbard-I calculation used to reproduce
-- Dirac-revival phenomenology. Zhang et al. use a zero-hybridization THF
-- combinatorial model to interpret the entropy plateaus. These are different
-- experiments/samples. DASHI records the source-owned parameters and model
-- obligations without manufacturing a same-sample or solved-model receipt.
------------------------------------------------------------------------

record SignedMagnitude : Set where
  constructor signed-magnitude
  field
    negative : Bool
    magnitude : Nat

open SignedMagnitude public

record XiaoTHFParameters : Set where
  constructor xiao-thf-parameters
  field
    vStarMeVNm : SignedMagnitude
    vStarPrimeMeVNm : SignedMagnitude
    gammaMeV : SignedMagnitude
    mTenthsMeV : SignedMagnitude
    uMeV : Nat
    wMeV : Nat
    yMeV : Nat
    inverseLifetimeMeV : Nat
    fStateCount : Nat
    sourceReference : String

open XiaoTHFParameters public

xiao2026THFParameters : XiaoTHFParameters
xiao2026THFParameters =
  xiao-thf-parameters
    (signed-magnitude true 1000)
    (signed-magnitude false 366)
    (signed-magnitude true 70)
    (signed-magnitude false 37)
    60
    45
    45
    1
    8
    "Xiao et al. Nature 653 (2026), Methods: THF model reproducing the Dirac revivals; v*=-1 eV nm, v*'=366 meV nm, gamma=-70 meV, M=3.7 meV, U=60 meV, W=45 meV, Y=45 meV, tau^-1=1 meV, N=8"

record HubbardIForwardContract : Set where
  constructor hubbard-i-forward-contract
  field
    fPropagatorHasUpperAndLowerHubbardPoles : Bool
    cPropagatorUsesSingleParticleHc : Bool
    fcHybridizationBlockRequired : Bool
    spectralFunctionIsMinusImagTraceOverPi : Bool
    cAndFDensitiesRequireMomentumFrequencyIntegration : Bool
    densityAndChemicalPotentialSolvedSelfConsistently : Bool
    spinValleyFactorFourUsedInSource : Bool
    sourceReference : String

open HubbardIForwardContract public

xiao2026HubbardIContract : HubbardIForwardContract
xiao2026HubbardIContract =
  hubbard-i-forward-contract
    true true true true true true true
    "Xiao et al. Nature 653 (2026), Methods equations for G_f^0, G_c^0, coupled Hubbard-I Green function, spectral function and self-consistent densities"

record ZhangEntropyTHFReceipt : Set where
  constructor zhang-entropy-thf-receipt
  field
    lowPlateauTemperatureKelvin : Nat
    highPlateauTemperatureKelvin : Nat
    lowTemperatureDegeneracy : Nat
    highTemperatureDegeneracy : Nat
    zeroHybridizationLimitUsed : Bool
    localizedFAtAASites : Bool
    itinerantCHalfFilledAtIntegerFFilling : Bool
    combinatorialLocalMomentModelUsed : Bool
    strainLiftsEightToFourInterpretation : Bool
    finiteTemperaturePlateausQuantitativelyCompared : Bool
    lowTemperatureEntropyFailureAcknowledged : Bool
    omittedHybridizationAndInterSiteCorrelationsAcknowledged : Bool
    sourceReference : String

open ZhangEntropyTHFReceipt public

zhang2026EntropyTHFReceipt : ZhangEntropyTHFReceipt
zhang2026EntropyTHFReceipt =
  zhang-entropy-thf-receipt
    10 20 4 8
    true true true true true true true true
    "Zhang et al. Nature Communications 17, 9785 (2026): zero-hybridization THF combinatorial entropy model with strain; source states the simplification omits f-c hybridization and inter-AA-site correlations"

record MATBGInteractingTHF2026Boundary : Set where
  constructor matbg-interacting-thf-2026-boundary
  field
    qtmTHFParameterSetSourcePaid : Bool
    qtmHubbardIFormulaStructureSourcePaid : Bool
    entropyTHFCombinatorialInterpretationSourcePaid : Bool
    qtmAndEntropyShareMaterialClass : Bool
    sameSampleQTMEntropyPaid : Bool
    songBernevigHcLiteralMatrixImported : Bool
    fcHybridizationLiteralMatrixImported : Bool
    selfConsistentInteractingSolvePaid : Bool
    qtmSpectralReplayPaid : Bool
    entropySourceDataReplayPaid : Bool
    sourceParametersOwnedByDASHI : Bool
    dashiOwnsTypedComposition : Bool

open MATBGInteractingTHF2026Boundary public

canonicalTHF2026Boundary : MATBGInteractingTHF2026Boundary
canonicalTHF2026Boundary =
  matbg-interacting-thf-2026-boundary
    true true true true false false false false false false false true

record THFAttributionBoundary : Set where
  constructor thf-attribution-boundary
  field
    xiaoOwnsReportedParameterSetAndMethods : Bool
    zhangOwnsReportedEntropyExperimentAndModelComparison : Bool
    dashiDoesNotReattributeSourceResults : Bool
    typedCrossSampleCompositionDoesNotCreateEmpiricalSameObject : Bool

open THFAttributionBoundary public

canonicalTHFAttributionBoundary : THFAttributionBoundary
canonicalTHFAttributionBoundary =
  thf-attribution-boundary true true true true
