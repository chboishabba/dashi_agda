module DASHI.Physics.Plasma.KSW668IsotopeCausalResidualExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra

------------------------------------------------------------------------
-- E1/E2: exact carbon-isotope accounting on the original C3 real field.
--
-- Observed final = initial + measured chemical uptake
--                        + nuclear production - clearance.
-- A production residual can be identified only when all the other channels
-- are measured on the SAME carrier / interval with closure. An isotope ratio
-- alone is not the source ledger.
------------------------------------------------------------------------

observedIsotopeAmount :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F
observedIsotopeAmount {F = F} initial uptake production clearance =
  C3.add F
    (C3.add F initial uptake)
    (C3.add F production (C3.negate F clearance))

reconstructNuclearResidual :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F
reconstructNuclearResidual {F = F} final initial uptake clearance =
  C3.add F
    (C3.add F
      (C3.add F final (C3.negate F initial))
      (C3.negate F uptake))
    clearance

originalBiologicalIsotopeReactionCausalResidual :
  ∀ {r : Level} {F : C3.RealField r}
    (initial uptake production clearance : C3.Carrier F) →
  reconstructNuclearResidual
    (observedIsotopeAmount initial uptake production clearance)
    initial uptake clearance
  ≡ production
originalBiologicalIsotopeReactionCausalResidual {F = F}
    initial uptake production clearance =
  R.solve 4
    (λ i u p c →
      (((((i R.⊕ u) R.⊕ (p R.⊕ (R.⊝ c)))
          R.⊕ (R.⊝ i))
          R.⊕ (R.⊝ u))
          R.⊕ c)
      R.⊜ p)
    refl initial uptake production clearance
  where module R = Algebra.Solver F

record SameSampleIsotopeEvidence : Set₁ where
  constructor same-sample-isotope-evidence
  field
    Specimen ObservationWindow : Set
    initialInventoryMeasured : Set
    uptakeAndFractionationMeasured : Set
    clearanceMeasured : Set
    finalInventoryMeasured : Set
    backgroundRadiocarbonCharacterised : Set
    radiochemicalContaminationExcluded : Set
    neutronExposureOrAlternativeNuclearSourceMeasured : Set
    uncertaintyAndDetectionLimit : Set
    causalInterventionProtocol : Set
    specimenReference : String
    sourceReference : String

------------------------------------------------------------------------
-- C1/C2: physical nuclear kinematics are separate from atom/period shell
-- and from the finite proton/neutron count identities.
------------------------------------------------------------------------

record NuclearFourMomentum
    {r : Level} (F : C3.RealField r) : Set r where
  constructor nuclear-four-momentum
  field
    energy px py pz : C3.Carrier F

record SameReactionKinematics {r : Level}
    (F : C3.RealField r) : Set r where
  constructor same-reaction-kinematics
  field
    incoming outgoing : NuclearFourMomentum F
    exactFourMomentumConservation : incoming ≡ outgoing
    reactionChannel : String
    measuredMassAndQValueSource : String
    crossSectionEnergyAndUncertaintySource : String
    targetDensityAndFluxSource : String
    rateLawAndBackgroundSource : String

------------------------------------------------------------------------
-- D1/D2: preserve operational transport and KK/geometry as independent
-- producers. A spatial entanglement metric cannot inhabit this record by
-- definition. Physical event and source/stress/observer data are required.
------------------------------------------------------------------------

record SelectedPhysicalTransportTest : Set₁ where
  constructor selected-physical-transport-test
  field
    Event Metric FieldState MatterState : Set
    emission reception : Event
    physicalMetric : Metric
    transportState : FieldState
    travelerState : MatterState
    originalLorentzConeProof : Set
    causalWorldlineOrMetricExtensionProof : Set
    energyMomentumConservationProof : Set
    operationalSignalReadoutProof : Set
    receiverClockCalibration : Set
    sameObjectKKEinsteinStressProof : Set
    eventReference : String
    experimentReference : String

------------------------------------------------------------------------
-- These requirement records have NO canonical physical inhabitant.
-- In particular: evidence field : Set is an obligation, not its proof.
------------------------------------------------------------------------
