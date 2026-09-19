module DASHI.Biology.Agriculture.QueenslandLegumeResidueFirstOrderKineticsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.ConstructiveNitrogenTransportKernelExact as Transport

------------------------------------------------------------------------
-- NORTHERN-AUSTRALIAN LEGUME-RESIDUE FIRST-ORDER N KINETICS
--
-- SOURCE PROPOSITION
--
-- Thomson, Cameron, Dalal & Hoult (2007) report a 17-week Vertisol
-- glasshouse experiment with optimum-moisture and alternate wet-dry regimes,
-- with/without 4 t/ha-equivalent legume residues following legume phases.
-- Residue N release followed first-order kinetics.  The paper reports k values
-- from 0.045 to 0.325 per week and corresponding half-times from 2.1 to
-- 15.4 weeks at 23 C.  Residue chemistry and moisture context remain indexed.
--
-- DASHI RECONSTRUCTION
--
-- This owner represents those reported kinetics as a source-bounded candidate
-- for the residueMineralisationRoute.  It does NOT identify one universal k,
-- manufacture a Bishop-real discrete ratio r, transport the fit to Acacia or
-- Senegalia, or turn residue mineralisation into living below-ground transfer.
------------------------------------------------------------------------

thomsonEtAl2007DOI : String
thomsonEtAl2007DOI = "10.1071/EA05290"

thomsonEtAl2007 : Attribution.AttributedSource
thomsonEtAl2007 = Attribution.mkDOISource
  "S. J. Thomson; J. A. L. Cameron; Ram C. Dalal; E. Hoult"
  "Alternate wet-dry regime during fallow failed to improve nitrogen release from added legume residues in legume-wheat rotations on a Vertisol"
  "Australian Journal of Experimental Agriculture 47(7):855-861"
  "2007" thomsonEtAl2007DOI "https://doi.org/10.1071/EA05290"
  Attribution.academicArticleSource
  "Northern-Australian semiarid-subtropical Vertisol experiment measuring potential legume contribution to following wheat over 17 weeks under optimum-moisture and alternate wet-dry regimes, with or without 4 t/ha-equivalent residue additions. The source reports first-order residue-N release, k = 0.045-0.325 per week, half-times 2.1-15.4 weeks at 23 C, and residue-chemistry dependence. Retained as a residue-mineralisation kinetic-shape receipt, not an Acacia/Senegalia or living-root-transfer result."
  Attribution.publicAttribution

data KineticRoute : Set where
  residueMineralisation : KineticRoute

record FirstOrderResidueKineticsReceipt : Set where
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    route : KineticRoute
    experimentDurationWeeks : Nat
    rateLowerMilliPerWeek : Nat
    rateUpperMilliPerWeek : Nat
    halfTimeLowerTenthsWeeks : Nat
    halfTimeUpperTenthsWeeks : Nat
    experimentTemperatureCelsius : Nat
    experimentReading : String
    modelReading : String
    boundedReading : String

open FirstOrderResidueKineticsReceipt public

thomson2007Kinetics : FirstOrderResidueKineticsReceipt
thomson2007Kinetics = record
  { source = thomsonEtAl2007
  ; sourceDOI = thomsonEtAl2007DOI
  ; route = residueMineralisation
  ; experimentDurationWeeks = 17
  ; rateLowerMilliPerWeek = 45
  ; rateUpperMilliPerWeek = 325
  ; halfTimeLowerTenthsWeeks = 21
  ; halfTimeUpperTenthsWeeks = 154
  ; experimentTemperatureCelsius = 23
  ; experimentReading =
      "Vertisol glasshouse experiment under optimum moisture or alternate wet-dry moisture regimes, with/without 4 t/ha-equivalent legume residues; field fallow observations are discussed separately in the source."
  ; modelReading =
      "Residue N release followed first-order kinetics; reported k range is 0.045-0.325 per week and reported half-time range is 2.1-15.4 weeks at 23 C."
  ; boundedReading =
      "The reported range spans residue/treatment contexts and is not one universal rate. It is a continuous-time first-order fit for residue mineralisation, not a directly constructed Bishop discrete ratio and not a living-root-transfer kernel."
  }

candidateTransportRoute : Transport.NitrogenTransportRoute
candidateTransportRoute = Transport.residueMineralisationRoute

record FirstOrderKineticsBoundary : Set where
  field
    firstOrderResidueReleaseShapeObserved : Bool
    reportedRateRangeImpliesOneUniversalRate : Bool
    residueChemistryMayBeErased : Bool
    moistureRegimeMayBeErased : Bool
    glasshouseKineticsEqualsFieldKinetics : Bool
    northernAustralianResidueKineticsCreatesAcaciaSameObjectKernel : Bool
    residueMineralisationKineticsEqualsLivingBelowGroundTransfer : Bool
    continuousFirstOrderFitDirectlySuppliesDiscreteBishopRatio : Bool
    sourceFitAutomaticallyPaysPolynomialGeometricMajorant : Bool
    sourceFitCreatesFertilizerReplacementValue : Bool
    sourceFitCreatesDeploymentAuthority : Bool

open FirstOrderKineticsBoundary public

canonicalFirstOrderKineticsBoundary : FirstOrderKineticsBoundary
canonicalFirstOrderKineticsBoundary = record
  { firstOrderResidueReleaseShapeObserved = true
  ; reportedRateRangeImpliesOneUniversalRate = false
  ; residueChemistryMayBeErased = false
  ; moistureRegimeMayBeErased = false
  ; glasshouseKineticsEqualsFieldKinetics = false
  ; northernAustralianResidueKineticsCreatesAcaciaSameObjectKernel = false
  ; residueMineralisationKineticsEqualsLivingBelowGroundTransfer = false
  ; continuousFirstOrderFitDirectlySuppliesDiscreteBishopRatio = false
  ; sourceFitAutomaticallyPaysPolynomialGeometricMajorant = false
  ; sourceFitCreatesFertilizerReplacementValue = false
  ; sourceFitCreatesDeploymentAuthority = false
  }

attributionRule : String
attributionRule =
  "Thomson, Cameron, Dalal & Hoult 2007 (DOI 10.1071/EA05290) owns the reported Vertisol experiment, first-order residue-N-release finding, reported k range, half-times, moisture treatments and residue-chemistry relationships. DASHI owns only the typed source receipt, its placement on the residue-mineralisation route, and the no-promotion boundary. DASHI does not attribute its constructive convolution, tail, Bishop-series or future continuous-to-discrete compiler theorems to Thomson et al.; nor does the source create an Acacia/Senegalia same-object kernel, living-root-transfer evidence, fertilizer-replacement value or deployment authority."
