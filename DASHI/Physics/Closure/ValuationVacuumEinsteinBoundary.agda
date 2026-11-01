module DASHI.Physics.Closure.ValuationVacuumEinsteinBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.AdmissibilityJetSpec as Spec
import DASHI.Geometry.InvariantSignatureDecidability as Decide
import DASHI.Physics.Closure.FirstWitnessVacuumBridge as Witness

------------------------------------------------------------------------
-- Valuation-field / vacuum / Einstein boundary.
--
-- This module gives typed names to the proposed bridge:
--   valuation field -> saturation / residue
--   admissible metric + diffeomorphism + two-jet invariant basis
--   saturated vacuum -> candidate Einstein-vacuum carrier
--   residue energy -> candidate curvature-source carrier
--
-- It deliberately does not assert the missing mathematical steps:
--   * construction of a smooth Lorentzian manifold from a kernel tower;
--   * derivation of a metric or Levi-Civita connection from the valuation;
--   * Lovelock / Einstein--Hilbert uniqueness under all required hypotheses;
--   * variation of an action and identification of physical stress-energy;
--   * equality of ionization-style defect energy and gravitational mass.


data SaturationStatus : Set where
  unsaturated : SaturationStatus
  saturated : SaturationStatus
  partiallySaturated : SaturationStatus
  saturationUndecided : SaturationStatus

saturationStatusName : SaturationStatus → String
saturationStatusName unsaturated = "unsaturated"
saturationStatusName saturated = "saturated"
saturationStatusName partiallySaturated = "partially-saturated"
saturationStatusName saturationUndecided = "saturation-undecided"


data ResidueKind : Set where
  noResidue : ResidueKind
  localResidue : ResidueKind
  distributedResidue : ResidueKind
  competingResidues : ResidueKind

residueKindName : ResidueKind → String
residueKindName noResidue = "no-residue"
residueKindName localResidue = "local-residue"
residueKindName distributedResidue = "distributed-residue"
residueKindName competingResidues = "competing-residues"

record ValuationFieldCarrier : Set where
  constructor mkValuationFieldCarrier
  field
    valuationLabel : String
    depth : Nat
    saturation : SaturationStatus
    residue : ResidueKind
    localVariationPresent : Bool
    quotientStable : Bool
    finiteJetObservable : Bool
    fieldStatement : String

open ValuationFieldCarrier public

saturatedVacuumValuation : ValuationFieldCarrier
saturatedVacuumValuation =
  mkValuationFieldCarrier
    "saturated-vacuum-valuation"
    (suc (suc zero))
    saturated
    noResidue
    false
    true
    true
    "candidate uniform saturated valuation carrier with no typed physical stress-energy claim"

localResidueValuation : ValuationFieldCarrier
localResidueValuation =
  mkValuationFieldCarrier
    "local-residue-valuation"
    (suc (suc zero))
    partiallySaturated
    localResidue
    true
    false
    true
    "candidate local defect carrier; local variation is present but gravitational sourcing is not yet derived"

competingResidueValuation : ValuationFieldCarrier
competingResidueValuation =
  mkValuationFieldCarrier
    "competing-residue-valuation"
    (suc (suc zero))
    saturationUndecided
    competingResidues
    true
    false
    false
    "competing residues require a richer invariant family or deeper lift before a unique effective source is assigned"

record ValuationInducedMetricBoundary : Set where
  constructor mkValuationInducedMetricBoundary
  field
    metricBoundaryLabel : String
    valuationCarrier : ValuationFieldCarrier
    admissibilitySpec : Spec.DepthAdmissibilitySpec
    invariantDecisionBoundary : Decide.DepthDecisionBoundary
    metricExists : Bool
    LorentzianSignatureDerived : Bool
    LeviCivitaConnectionDerived : Bool
    conformalMetricCandidateAvailable : Bool
    WeylCompatibilityCandidateAvailable : Bool
    metricDerivationClaimed : Bool
    metricBoundaryStatement : String

open ValuationInducedMetricBoundary public

canonicalValuationMetricBoundary : ValuationInducedMetricBoundary
canonicalValuationMetricBoundary =
  mkValuationInducedMetricBoundary
    "valuation-induced-metric-boundary"
    saturatedVacuumValuation
    Spec.metricDiffeomorphismTwoJetSpec
    Decide.canonicalDepthDecisionBoundary
    false
    false
    false
    true
    true
    false
    "conformal and Weyl-style maps are candidate interfaces; no metric, signature, or connection derivation is promoted"

record EinsteinVacuumCandidate : Set where
  constructor mkEinsteinVacuumCandidate
  field
    candidateLabel : String
    valuationCarrier : ValuationFieldCarrier
    metricBoundary : ValuationInducedMetricBoundary
    closedShellAnalogyUsed : Bool
    diffeomorphismAdmissibilityRequired : Bool
    localityRequired : Bool
    twoJetCapRequired : Bool
    constantVacuumTermPermitted : Bool
    EinsteinHilbertBasisSelected : Bool
    actionVariationCompleted : Bool
    EinsteinVacuumEquationDerived : Bool
    candidateStatement : String

open EinsteinVacuumCandidate public

canonicalEinsteinVacuumCandidate : EinsteinVacuumCandidate
canonicalEinsteinVacuumCandidate =
  mkEinsteinVacuumCandidate
    "saturated-valuation-einstein-vacuum-candidate"
    saturatedVacuumValuation
    canonicalValuationMetricBoundary
    true
    true
    true
    true
    true
    false
    false
    false
    "saturation supplies a vacuum analogy and the metric+diffeomorphism+two-jet row supplies an admissible target basis; Einstein equations remain unproved"

record ResidueCurvatureSourceCandidate : Set where
  constructor mkResidueCurvatureSourceCandidate
  field
    sourceCandidateLabel : String
    residueValuation : ValuationFieldCarrier
    firstWitnessBoundary : Witness.VacuumFirstWitnessBoundary
    metricBoundary : ValuationInducedMetricBoundary
    defectEnergyCarrierAvailable : Bool
    covariantStressEnergyConstructed : Bool
    BianchiCompatibilityProved : Bool
    conservationLawProved : Bool
    curvatureSourceEquationDerived : Bool
    ionizationAnalogyUsed : Bool
    ionizationEnergyEqualsMassClaimed : Bool
    sourceCandidateStatement : String

open ResidueCurvatureSourceCandidate public

canonicalResidueCurvatureSourceCandidate : ResidueCurvatureSourceCandidate
canonicalResidueCurvatureSourceCandidate =
  mkResidueCurvatureSourceCandidate
    "residue-curvature-source-candidate"
    localResidueValuation
    Witness.canonicalVacuumFirstWitnessBoundary
    canonicalValuationMetricBoundary
    true
    false
    false
    false
    false
    true
    false
    "defect energy may seed a source carrier, but stress-energy, conservation, curvature sourcing, and mass identification require separate proofs"

record VacuumGeometryPromotionBoundary : Set where
  constructor mkVacuumGeometryPromotionBoundary
  field
    boundaryLabel : String
    valuationRows : List ValuationFieldCarrier
    metricBoundary : ValuationInducedMetricBoundary
    vacuumCandidate : EinsteinVacuumCandidate
    residueCandidate : ResidueCurvatureSourceCandidate
    closedShellIsEinsteinVacuumTheoremProved : Bool
    residueEnergyIsCurvatureSourceTheoremProved : Bool
    quantumGRUnificationProved : Bool
    theoryOfEverythingClaimPermitted : Bool
    candidateBridgeRecorded : Bool
    boundaryHolds : Bool
    boundaryStatement : String

open VacuumGeometryPromotionBoundary public

canonicalVacuumGeometryPromotionBoundary : VacuumGeometryPromotionBoundary
canonicalVacuumGeometryPromotionBoundary =
  mkVacuumGeometryPromotionBoundary
    "vacuum-geometry-promotion-boundary"
    (saturatedVacuumValuation
     ∷ localResidueValuation
     ∷ competingResidueValuation
     ∷ [])
    canonicalValuationMetricBoundary
    canonicalEinsteinVacuumCandidate
    canonicalResidueCurvatureSourceCandidate
    false
    false
    false
    false
    true
    true
    "the repo records a typed candidate bridge from valuation saturation and residues to geometric admissibility while explicitly blocking GR, quantum-GR, and theory-of-everything promotion"

canonicalMetricNotDerived : metricDerivationClaimed canonicalValuationMetricBoundary ≡ false
canonicalMetricNotDerived = refl

canonicalEinsteinVacuumNotDerived :
  EinsteinVacuumEquationDerived canonicalEinsteinVacuumCandidate ≡ false
canonicalEinsteinVacuumNotDerived = refl

canonicalResidueCurvatureNotDerived :
  curvatureSourceEquationDerived canonicalResidueCurvatureSourceCandidate ≡ false
canonicalResidueCurvatureNotDerived = refl

canonicalTheoryOfEverythingPromotionBlocked :
  theoryOfEverythingClaimPermitted canonicalVacuumGeometryPromotionBoundary ≡ false
canonicalTheoryOfEverythingPromotionBlocked = refl
