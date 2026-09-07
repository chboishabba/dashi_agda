module DASHI.Analysis.RiemannG2LeastPrivilegeClayCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set₁)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact as Certified
import DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeCompilerExact as FreshGamma
import DASHI.Analysis.DeBruijnNewman2026SourceWeldExact as DBN

------------------------------------------------------------------------
-- LEAST-PRIVILEGE CLAY CUTSET
--
-- The prize-facing high consumer already asks only for a
-- HighOffLineAnalyticCoreProducer.  The uniform certified route is a useful
-- sufficient producer for that interface, but it is deliberately NOT promoted
-- to a mandatory Clay hypothesis.  A direct inhabitant of the two analytic
-- cores + attachments + completion is enough.
--
-- Consequence for proof search: do not require reconstruction of a certified
-- finite-near packet if an OffAnalyticCore is available by another theorem, and
-- do not require historical 8889 Gamma identity if a fresh theorem exists on
-- the literal final taper.
------------------------------------------------------------------------

PreferredHighProducer :
  (analytic : Analytic.AnalyticSubstrate) ->
  (High : Universal.AnalyticNontrivialZero analytic -> Set) ->
  Set₁
PreferredHighProducer analytic High =
  Universal.HighOffLineAnalyticCoreProducer analytic High

preferredOffLeaf : Set₁
preferredOffLeaf = Core.OffAnalyticCore

preferredGammaLeaf : Set₁
preferredGammaLeaf = Core.GammaAnalyticCore

certifiedOffWitnessIsSufficient :
  Certified.CertifiedOffCoreWitness ->
  preferredOffLeaf
certifiedOffWitnessIsSufficient = Certified.compiledOffCore

freshGammaWitnessIsSufficient :
  Certified.FreshGammaCoreWitness ->
  preferredGammaLeaf
freshGammaWitnessIsSufficient = Certified.compiledGammaCore

uniformCertifiedRouteIsSufficient :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  Certified.UniformCertifiedHighOffLineProducer analytic High ->
  PreferredHighProducer analytic High
uniformCertifiedRouteIsSufficient =
  Certified.compileUniformCertifiedHighOffLineProducer

------------------------------------------------------------------------
-- CURRENT GAMMA SEARCH PIN
------------------------------------------------------------------------

historical8889IdentityRequiredForCurrentFreshGamma : Bool
historical8889IdentityRequiredForCurrentFreshGamma =
  FreshGamma.historical8889IdentityRequiredForFreshEnvelope
    FreshGamma.canonicalFreshSameTaperGammaEnvelopeBoundary

historical8889IdentityRequiredForCurrentFreshGammaIsFalse :
  historical8889IdentityRequiredForCurrentFreshGamma ≡ false
historical8889IdentityRequiredForCurrentFreshGammaIsFalse = refl

historicalPrecisionRecoveryRequiredForCurrentFreshGamma : Bool
historicalPrecisionRecoveryRequiredForCurrentFreshGamma =
  FreshGamma.historicalPrecisionLossLocalizationRequiredForFreshEnvelope
    FreshGamma.canonicalFreshSameTaperGammaEnvelopeBoundary

historicalPrecisionRecoveryRequiredForCurrentFreshGammaIsFalse :
  historicalPrecisionRecoveryRequiredForCurrentFreshGamma ≡ false
historicalPrecisionRecoveryRequiredForCurrentFreshGammaIsFalse = refl

freshSameFinalTaperRequiredForCurrentGamma : Bool
freshSameFinalTaperRequiredForCurrentGamma =
  FreshGamma.sameLiteralFinalTaperStillRequired
    FreshGamma.canonicalFreshSameTaperGammaEnvelopeBoundary

freshSameFinalTaperRequiredForCurrentGammaIsTrue :
  freshSameFinalTaperRequiredForCurrentGamma ≡ true
freshSameFinalTaperRequiredForCurrentGammaIsTrue = refl

------------------------------------------------------------------------
-- CLAY QUANTIFIER PIN
------------------------------------------------------------------------

oneFixedCertifiedCaseIsClayHighProducer : Bool
oneFixedCertifiedCaseIsClayHighProducer =
  Certified.oneFixedFiniteCertificateIsClayLevelHighProducer
    Certified.canonicalUniformCertifiedHighOffLineBoundary

oneFixedCertifiedCaseIsClayHighProducerIsFalse :
  oneFixedCertifiedCaseIsClayHighProducer ≡ false
oneFixedCertifiedCaseIsClayHighProducerIsFalse = refl

perHighOffLineFamilyRequired : Bool
perHighOffLineFamilyRequired =
  Certified.perHighOffLineCertificateFamilyRequired
    Certified.canonicalUniformCertifiedHighOffLineBoundary

perHighOffLineFamilyRequiredIsTrue :
  perHighOffLineFamilyRequired ≡ true
perHighOffLineFamilyRequiredIsTrue = refl

------------------------------------------------------------------------
-- LOW SIDE REMAINS INDEPENDENT.
------------------------------------------------------------------------

plattTrudgianSourceRecovered : Bool
plattTrudgianSourceRecovered = DBN.plattTrudgianSourceRecovered

plattTrudgianSourceRecoveredIsTrue :
  plattTrudgianSourceRecovered ≡ true
plattTrudgianSourceRecoveredIsTrue = refl

plattTrudgianTheoremImportedIntoAgda : Bool
plattTrudgianTheoremImportedIntoAgda = false

plattTrudgianTheoremImportedIntoAgdaIsFalse :
  plattTrudgianTheoremImportedIntoAgda ≡ false
plattTrudgianTheoremImportedIntoAgdaIsFalse = refl

------------------------------------------------------------------------
-- AUTHORITATIVE SEARCH READING.
------------------------------------------------------------------------

record LeastPrivilegeClayCutsetBoundary : Set where
  constructor least-privilege-clay-cutset-boundary
  field
    primitiveHighConsumerIsDirectAnalyticCoreProducer : Bool
    primitiveHighConsumerIsDirectAnalyticCoreProducerIsTrue :
      primitiveHighConsumerIsDirectAnalyticCoreProducer ≡ true

    certifiedFiniteNearOffRouteIsSufficientNotMandatory : Bool
    certifiedFiniteNearOffRouteIsSufficientNotMandatoryIsTrue :
      certifiedFiniteNearOffRouteIsSufficientNotMandatory ≡ true

    freshSameTaperGammaRouteIsSufficientNotHistoricalIdentityBound : Bool
    freshSameTaperGammaRouteIsSufficientNotHistoricalIdentityBoundIsTrue :
      freshSameTaperGammaRouteIsSufficientNotHistoricalIdentityBound ≡ true

    oneFixedHighCaseIsInsufficientForClayQuantifier : Bool
    oneFixedHighCaseIsInsufficientForClayQuantifierIsTrue :
      oneFixedHighCaseIsInsufficientForClayQuantifier ≡ true

    lowOrdinateTheoremStillIndependent : Bool
    lowOrdinateTheoremStillIndependentIsTrue :
      lowOrdinateTheoremStillIndependent ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalLeastPrivilegeClayCutsetBoundary :
  LeastPrivilegeClayCutsetBoundary
canonicalLeastPrivilegeClayCutsetBoundary =
  least-privilege-clay-cutset-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    "The primitive prize-facing high requirement is HighOffLineAnalyticCoreProducer, not the stronger uniform certified decomposition. Certified finite-near Off and fresh same-taper Gamma witnesses remain sufficient producers and may be used wherever they are cheapest, but neither decomposition is mandatory if a direct analytic core is available. For fresh Gamma, historical 8889 identity and historical precision-loss recovery are off the critical path; the exact final-taper theorem is live. The high theorem must still be uniform over every high off-line nontrivial zero. The low verified-zero theorem remains an independent Agda attachment. RH is not derived here."
