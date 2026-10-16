module DASHI.Physics.CondensedMatter.MATBGTHFSelfConsistencyQTMExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-EXACT SELF-CONSISTENCY / QTM OBSERVER CONTRACT
--
-- Xiao et al. Nature 653 (2026), DOI 10.1038/s41586-026-10378-x,
-- Methods section "THF model reproducing the Dirac revivals" defines:
--   mu_f = mu - W <delta n_c>
--   mu_c = mu - W <delta n_f> - V <delta n_c>
--   A_alpha(k,w) = -(1/pi) Im Tr G_alpha,eta(k,w)
--   <delta n_alpha> = 4 int_{-inf}^0 dw int d^2k/A_BZ A_alpha - n_alpha^0
-- and solves <delta n_f>, <delta n_c>, mu self-consistently for each total
-- density.  The same paper gives the QTM Fermi-golden-rule tunnelling-current
-- observer and the G_T=G_B=0 matrix I + sigma_x.
--
-- This module literalizes the obligations and source relations. It does NOT
-- choose an ultraviolet/BZ discretization, identify the Methods symbol V with
-- the parameter-list symbol Y, solve the coupled Green-function integral, or
-- claim experimental QTM replay.
------------------------------------------------------------------------

record THFSelfConsistencyEquationReceipt : Set where
  constructor thf-self-consistency-equation-receipt
  field
    sourceDOI : String
    fElectrochemicalPotential : String
    cElectrochemicalPotential : String
    spectralFunctionDefinition : String
    densityIntegralDefinition : String
    degeneracyFactor : String
    solvedVariables : String
    sourceNotationCaveat : String

open THFSelfConsistencyEquationReceipt public

canonicalTHFSelfConsistencyEquationReceipt : THFSelfConsistencyEquationReceipt
canonicalTHFSelfConsistencyEquationReceipt =
  thf-self-consistency-equation-receipt
    "10.1038/s41586-026-10378-x"
    "mu_f = mu - W <delta n_c>"
    "mu_c = mu - W <delta n_f> - V <delta n_c>"
    "A_alpha(k,omega) = -(1/pi) Im Tr G_alpha,eta(k,omega)"
    "<delta n_alpha> = 4 integral_{-infinity}^0 d omega integral d^2k/A_BZ A_alpha(k,omega) - n_alpha^0"
    "4 for spin and valley under flavour-symmetric assumption"
    "<delta n_f>, <delta n_c>, mu at each total density"
    "Methods parameter list names Y=45 meV while the displayed mu_c relation uses V; no identification is silently imposed here"

record QTMGoldenRuleObserverReceipt : Set where
  constructor qtm-golden-rule-observer-receipt
  field
    sourceDOI : String
    currentKernel : String
    momentumConservation : String
    spectralFunctionsPresent : String
    tunnellingMatrixRole : String
    zeroBraggMatrix : String
    matrixElementConsumer : String
    reportedBestRatio : String

open QTMGoldenRuleObserverReceipt public

canonicalQTMGoldenRuleObserverReceipt : QTMGoldenRuleObserverReceipt
canonicalQTMGoldenRuleObserverReceipt =
  qtm-golden-rule-observer-receipt
    "10.1038/s41586-026-10378-x"
    "I proportional to integral d omega (f_B(omega)-f_T(omega+e phi)) sum |<u_gr|T|u_tbg>|^2 delta_momentum A_B A_T"
    "k_T + G_T = k_B + G_B"
    "TBG and graphene-probe spectral functions both enter the current"
    "T^{G_T,G_B} acts in sublattice space and projects the TBG top-layer wavefunction"
    "T^{0,0} = I + sigma_x"
    "|<I + sigma_x>| on the TBG state carries layer and sublattice information"
    "w0/w1 = 0.6 reported as best agreement for the flat-band matrix-element comparison"

record THFSelfConsistencyQTMBoundary : Set where
  constructor thf-self-consistency-qtm-boundary
  field
    selfConsistencyEquationsSourcePaid : Bool
    spectralDensityDefinitionSourcePaid : Bool
    densityIntegralSourcePaid : Bool
    spinValleyFactorSourcePaid : Bool
    qtmGoldenRuleObserverSourcePaid : Bool
    zeroBraggMatrixElementSourcePaid : Bool
    fullCoupledGreenFunctionFormulaSourcePaid : Bool
    sourceNotationVAmbiguityPreserved : Bool
    songBernevigBZNormalizationImported : Bool
    fullSelfConsistentNumericalSolvePaid : Bool
    qtmElectrostaticsNumericallyReplayed : Bool
    qtmExperimentalDataReplayPaid : Bool
    sameSampleEntropyPaid : Bool

open THFSelfConsistencyQTMBoundary public

canonicalTHFSelfConsistencyQTMBoundary : THFSelfConsistencyQTMBoundary
canonicalTHFSelfConsistencyQTMBoundary =
  thf-self-consistency-qtm-boundary
    true true true true true true true true
    false false false false false

record THFSelfConsistencyQTMAttributionBoundary : Set where
  constructor thf-self-consistency-qtm-attribution-boundary
  field
    xiaoEtAlOwn2026SelfConsistencyAndQTMObserverEquations : Bool
    songBernevigOwnReferencedTHFSingleParticleDefinitions : Bool
    dashiOwnsTypedObligationSeparation : Bool
    sourceFormulaDoesNotCreateUniqueDiscretization : Bool
    sourceFormulaDoesNotCreateNumericalFit : Bool
    sourceFormulaDoesNotCreateSameSampleEntropy : Bool

open THFSelfConsistencyQTMAttributionBoundary public

canonicalTHFSelfConsistencyQTMAttributionBoundary : THFSelfConsistencyQTMAttributionBoundary
canonicalTHFSelfConsistencyQTMAttributionBoundary =
  thf-self-consistency-qtm-attribution-boundary true true true true true true
