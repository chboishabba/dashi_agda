module DASHI.Physics.QuantumVacuum.CasimirQuantumInequalityBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionExact as Pointwise

------------------------------------------------------------------------
-- CASIMIR POINTWISE NEGATIVE ENERGY -> QI / AVERAGED-CONDITION BOUNDARY
--
-- The local Brown-Maclay owner proves the ideal-plate pointwise fingerprint.
-- Ford/Roman source-back restrictions on negative energy and the relation
-- between averaged conditions and quantum inequalities.  Neither citation
-- chooses a worldline, sampling function, reference vacuum/background, or
-- difference inequality for our exact Casimir object.
------------------------------------------------------------------------

fordRoman1995DOI : String
fordRoman1995DOI = "10.1103/PhysRevD.51.4277"

fordRoman1997DOI : String
fordRoman1997DOI = "10.1103/PhysRevD.55.2082"

fordRoman1995 : Attribution.AttributedSource
fordRoman1995 =
  Attribution.mkDOISource
    "L. H. Ford and Thomas A. Roman"
    "Averaged energy conditions and quantum inequalities"
    "Physical Review D 51, 4277"
    "1995"
    fordRoman1995DOI
    "https://doi.org/10.1103/PhysRevD.51.4277"
    Attribution.academicArticleSource
    "source for the relation between averaged energy conditions and quantum inequalities, including the role of a Casimir-vacuum reference/background in difference inequalities; not an automatic ANEC or engineering theorem for this DASHI stress object"
    Attribution.publicAttribution

fordRoman1997 : Attribution.AttributedSource
fordRoman1997 =
  Attribution.mkDOISource
    "L. H. Ford and Thomas A. Roman"
    "Restrictions on negative energy density in flat spacetime"
    "Physical Review D 55, 2082"
    "1997"
    fordRoman1997DOI
    "https://doi.org/10.1103/PhysRevD.55.2082"
    Attribution.academicArticleSource
    "source for flat-spacetime quantum-inequality restrictions on negative energy density, including electromagnetic-field bounds; not a same-object Casimir sampling prescription by citation alone"
    Attribution.publicAttribution

------------------------------------------------------------------------
-- Proof-relevant sampling/background payment.
------------------------------------------------------------------------

record CasimirQuantumInequalityPrescription : Set₁ where
  field
    Worldline : Set
    SamplingFunction : Set
    ReferenceState : Set

    worldline : Worldline
    samplingFunction : SamplingFunction
    referenceState : ReferenceState

    sameCasimirStressObject : Set
    samplingFunctionAdmissible : Set
    referenceBackgroundSpecified : Set
    casimirVersusReferenceDifferenceSpecified : Set

    AveragedObservable : Set
    averagedObservable : AveragedObservable

    QuantumInequalityBound : Set
    quantumInequalityBound : QuantumInequalityBound

    durationMagnitudeInterpretation : Set
    reading : String

open CasimirQuantumInequalityPrescription public

record CasimirANECNullCurvePrescription : Set₁ where
  field
    NullCurve : Set
    AffineParameter : Set
    nullCurve : NullCurve

    curveCompleteOrBoundaryTreatmentSpecified : Set
    plateBoundaryTreatmentSpecified : Set
    sameRenormalizedStressObject : Set

    ANECIntegral : Set
    anecIntegral : ANECIntegral
    convergenceOrDistributionalMeaning : Set

    reading : String

open CasimirANECNullCurvePrescription public

------------------------------------------------------------------------
-- Pointwise result is available, but neither averaged lane is manufactured.
------------------------------------------------------------------------

pointwiseNECViolationOwned :
  Pointwise.casimirNEC ≡ Pointwise.conditionViolated
pointwiseNECViolationOwned = refl

data PointwiseNECViolationAutomaticallyPaysANECViolation : Set where
data QILiteratureAutomaticallySuppliesCasimirSamplingWitness : Set where
data CasimirBackgroundMayBeSilentlyReplacedByMinkowskiVacuum : Set where
data QIBoundAutomaticallyLicensesMacroscopicNegativeEnergyEngineering : Set where

pointwiseNECDoesNotPayANEC :
  PointwiseNECViolationAutomaticallyPaysANECViolation → ⊥
pointwiseNECDoesNotPayANEC ()

qiLiteratureDoesNotSupplySamplingWitness :
  QILiteratureAutomaticallySuppliesCasimirSamplingWitness → ⊥
qiLiteratureDoesNotSupplySamplingWitness ()

casimirBackgroundCannotBeSilentlyReplaced :
  CasimirBackgroundMayBeSilentlyReplacedByMinkowskiVacuum → ⊥
casimirBackgroundCannotBeSilentlyReplaced ()

qiDoesNotLicenseEngineering :
  QIBoundAutomaticallyLicensesMacroscopicNegativeEnergyEngineering → ⊥
qiDoesNotLicenseEngineering ()

------------------------------------------------------------------------
-- Machine-readable source/payment boundary.
------------------------------------------------------------------------

record CasimirQuantumInequalityBoundary : Set where
  constructor casimir-quantum-inequality-boundary
  field
    pointwiseCasimirNECViolationOwned : Bool
    fordRoman1995SourcePaid : Bool
    fordRoman1997SourcePaid : Bool
    backgroundVacuumQualificationTracked : Bool

    concreteWorldlineSamplingPrescriptionPaid : Bool
    exactCasimirQITheoremInstantiated : Bool
    exactCasimirANECIntegralPaid : Bool
    macroscopicNegativeEnergyEngineeringPaid : Bool

open CasimirQuantumInequalityBoundary public

canonicalCasimirQuantumInequalityBoundary : CasimirQuantumInequalityBoundary
canonicalCasimirQuantumInequalityBoundary =
  casimir-quantum-inequality-boundary
    true true true true
    false false false false

casimirQuantumInequalityReading : String
casimirQuantumInequalityReading =
  "The ideal-plate Casimir stress has a theorem-bearing pointwise NEC violation, while Ford-Roman source-back quantum-inequality and averaged-condition restrictions. A same-object QI/ANEC claim still requires an explicit worldline/null curve, sampling function or affine prescription, reference background, averaged observable and bound/integral. Pointwise violation and literature citations do not manufacture those payments or a macroscopic negative-energy engineering licence."
