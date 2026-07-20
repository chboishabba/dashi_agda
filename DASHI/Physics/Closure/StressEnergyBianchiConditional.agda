module DASHI.Physics.Closure.StressEnergyBianchiConditional where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.EinsteinHilbertVariationConditional as EH
import DASHI.Physics.Closure.FirstWitnessVacuumBridge as FirstWitness
import DASHI.Physics.Closure.ValuationVacuumEinsteinBoundary as Vacuum

------------------------------------------------------------------------
-- Conditional source/conservation ladder.
--
-- The Euler/PDA first-witness lane supplies exact-once defect attribution.
-- That attribution is useful bookkeeping, but it is not stress-energy.
-- To reach a GR source one must additionally supply a diffeomorphism-covariant
-- matter action, its metric variation, the contracted Bianchi identity, and
-- the relevant equations of motion / Noether identity.

record DefectSourceWitness : Set where
  constructor mkDefectSourceWitness
  field
    sourceLabel : String
    residueCarrier : Vacuum.ValuationFieldCarrier
    firstWitnessBoundary : FirstWitness.VacuumFirstWitnessBoundary
    defectAttributedExactlyOnce : Bool
    sourceLocalizable : Bool
    sourceAdditiveOnDisjointWitnessClasses : Bool
    sourceStatement : String

open DefectSourceWitness public

record CovariantStressEnergyWitness (source : DefectSourceWitness) : Set where
  constructor mkCovariantStressEnergyWitness
  field
    stressEnergyLabel : String
    matterActionSupplied : Bool
    matterActionDiffeomorphismInvariant : Bool
    metricVariationDefinesSymmetricTensor : Bool
    tensorLivesOnLorentzianBase : Bool
    sourceMappedToTensorByDeclaredCoupling : Bool
    couplingUniversalAcrossMatterCarriers : Bool
    stressEnergyStatement : String

open CovariantStressEnergyWitness public

record BianchiConservationWitness
  (source : DefectSourceWitness)
  (stress : CovariantStressEnergyWitness source) : Set where
  constructor mkBianchiConservationWitness
  field
    contractedBianchiIdentitySupplied : Bool
    matterEquationsOfMotionSupplied : Bool
    NoetherIdentitySupplied : Bool
    covariantDivergenceVanishes : Bool
    conservationStatement : String

open BianchiConservationWitness public

record ConservedEinsteinSourceReceipt
  (source : DefectSourceWitness)
  (stress : CovariantStressEnergyWitness source)
  (conservation : BianchiConservationWitness source stress) : Set where
  constructor mkConservedEinsteinSourceReceipt
  field
    EinsteinEquationReceiptAvailable : Bool
    exactOnceReceipt : defectAttributedExactlyOnce source ≡ true
    matterActionReceipt : matterActionSupplied stress ≡ true
    diffeomorphismReceipt : matterActionDiffeomorphismInvariant stress ≡ true
    stressTensorReceipt : metricVariationDefinesSymmetricTensor stress ≡ true
    universalCouplingReceipt : couplingUniversalAcrossMatterCarriers stress ≡ true
    BianchiReceipt : contractedBianchiIdentitySupplied conservation ≡ true
    NoetherReceipt : NoetherIdentitySupplied conservation ≡ true
    conservationReceipt : covariantDivergenceVanishes conservation ≡ true

open ConservedEinsteinSourceReceipt public

assembleConservedEinsteinSourceReceipt :
  (source : DefectSourceWitness) →
  (stress : CovariantStressEnergyWitness source) →
  (conservation : BianchiConservationWitness source stress) →
  defectAttributedExactlyOnce source ≡ true →
  matterActionSupplied stress ≡ true →
  matterActionDiffeomorphismInvariant stress ≡ true →
  metricVariationDefinesSymmetricTensor stress ≡ true →
  couplingUniversalAcrossMatterCarriers stress ≡ true →
  contractedBianchiIdentitySupplied conservation ≡ true →
  NoetherIdentitySupplied conservation ≡ true →
  covariantDivergenceVanishes conservation ≡ true →
  ConservedEinsteinSourceReceipt source stress conservation
assembleConservedEinsteinSourceReceipt source stress conservation exactOnce action diffeo tensor universal bianchi noether conserved =
  mkConservedEinsteinSourceReceipt true exactOnce action diffeo tensor universal bianchi noether conserved

canonicalConditionalDefectSource : DefectSourceWitness
canonicalConditionalDefectSource =
  mkDefectSourceWitness
    "conditional-exact-once-defect-source"
    Vacuum.localResidueValuation
    FirstWitness.canonicalVacuumFirstWitnessBoundary
    true
    true
    true
    "unique first-witness attribution prevents duplicate source counting but does not by itself define a tensor"

canonicalConditionalStressEnergy :
  CovariantStressEnergyWitness canonicalConditionalDefectSource
canonicalConditionalStressEnergy =
  mkCovariantStressEnergyWitness
    "conditional-covariant-stress-energy"
    true true true true true true
    "stress-energy is supplied by metric variation of a diffeomorphism-invariant matter action with a declared universal coupling"

canonicalConditionalBianchiConservation :
  BianchiConservationWitness
    canonicalConditionalDefectSource
    canonicalConditionalStressEnergy
canonicalConditionalBianchiConservation =
  mkBianchiConservationWitness
    true true true true
    "contracted Bianchi plus matter Noether identity and equations of motion close covariant conservation"

canonicalConditionalConservedSourceReceipt :
  ConservedEinsteinSourceReceipt
    canonicalConditionalDefectSource
    canonicalConditionalStressEnergy
    canonicalConditionalBianchiConservation
canonicalConditionalConservedSourceReceipt =
  assembleConservedEinsteinSourceReceipt
    canonicalConditionalDefectSource
    canonicalConditionalStressEnergy
    canonicalConditionalBianchiConservation
    refl refl refl refl refl refl refl refl

record MassIdentificationBoundary : Set where
  constructor mkMassIdentificationBoundary
  field
    defectEnergyCarrierAvailable : Bool
    exactOnceAttributionAvailable : Bool
    inertialMassDefinitionSupplied : Bool
    passiveGravitationalMassDefinitionSupplied : Bool
    activeGravitationalMassDefinitionSupplied : Bool
    equivalencePrincipleBridgeSupplied : Bool
    NewtonianLimitMatched : Bool
    ionizationStyleEnergyIdentifiedWithMass : Bool
    boundaryStatement : String

open MassIdentificationBoundary public

canonicalMassIdentificationBoundary : MassIdentificationBoundary
canonicalMassIdentificationBoundary =
  mkMassIdentificationBoundary
    true
    true
    false
    false
    false
    false
    false
    false
    "defect bookkeeping is available, but inertial/active/passive mass, equivalence, and Newtonian matching remain unsupplied"

canonicalResidueEnergyNotMass :
  ionizationStyleEnergyIdentifiedWithMass canonicalMassIdentificationBoundary ≡ false
canonicalResidueEnergyNotMass = refl
