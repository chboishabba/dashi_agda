module DASHI.Physics.Closure.TypedStressEnergyMassBridge where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Base369 using (TriTruth; tri-mid)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Closure.FirstWitnessVacuumBridge as FirstWitness
import DASHI.Physics.Closure.StressEnergyBianchiConditional as Conditional
import DASHI.Physics.Closure.SymbolicEinsteinHilbertModel as EH

------------------------------------------------------------------------
-- Tensor and action-variation carriers.
--
-- The public construction route is deliberately:
--
--   defect + declared matter-action coupling -> action variation -> tensor.
--
-- There is no exported direct coercion from DefectEnergy to StressTensor.

Tensor4 : Set
Tensor4 = Flat.Axis4 → Flat.Axis4 → TriTruth

zeroTensor : Tensor4
zeroTensor _ _ = tri-mid

PointwiseTensorEqual : Tensor4 → Tensor4 → Set
PointwiseTensorEqual left right =
  (a b : Flat.Axis4) → left a b ≡ right a b

SymmetricTensor : Tensor4 → Set
SymmetricTensor tensor =
  (a b : Flat.Axis4) → tensor a b ≡ tensor b a

ZeroTensor : Tensor4 → Set
ZeroTensor tensor =
  (a b : Flat.Axis4) → tensor a b ≡ tri-mid

zeroTensorSymmetric : SymmetricTensor zeroTensor
zeroTensorSymmetric _ _ = refl

zeroTensorIsZero : ZeroTensor zeroTensor
zeroTensorIsZero _ _ = refl

record MatterActionVariation : Set where
  constructor mkMatterActionVariation
  field
    actionLabel : String
    stressTensor : Tensor4
    stressSymmetric : SymmetricTensor stressTensor
    metricVariationReceipt : String
    NoetherReceipt : String
    actionScope : String

open MatterActionVariation public

vacuumMatterActionVariation : MatterActionVariation
vacuumMatterActionVariation =
  mkMatterActionVariation
    "zero-vacuum-matter-action"
    zeroTensor
    zeroTensorSymmetric
    "zero matter action has zero metric variation in the flat vacuum model"
    "zero source satisfies the flat Noether/conservation identity"
    "concrete vacuum case only; no nonzero residue source is inferred"

------------------------------------------------------------------------
-- Exact-once defect bookkeeping remains separate from tensor construction.

record DefectEnergy : Set where
  constructor mkDefectEnergy
  field
    defectAmount : Nat
    defectLabel : String

open DefectEnergy public

zeroDefectEnergy : DefectEnergy
zeroDefectEnergy = mkDefectEnergy zero "zero-vacuum-defect-energy"

record DefectMatterCoupling (energy : DefectEnergy) : Set where
  constructor mkDefectMatterCoupling
  field
    couplingLabel : String
    firstWitnessBoundary : FirstWitness.VacuumFirstWitnessBoundary
    actionVariation : MatterActionVariation
    coupledSourceTensor : Tensor4
    tensorComesFromActionVariation :
      PointwiseTensorEqual
        coupledSourceTensor
        (stressTensor actionVariation)
    couplingScope : String

open DefectMatterCoupling public

stressFromDefectRequiresCoupling :
  (energy : DefectEnergy) → DefectMatterCoupling energy → Tensor4
stressFromDefectRequiresCoupling energy coupling =
  coupledSourceTensor coupling

zeroVacuumDefectCoupling : DefectMatterCoupling zeroDefectEnergy
zeroVacuumDefectCoupling =
  mkDefectMatterCoupling
    "zero-vacuum-defect-to-action-coupling"
    FirstWitness.canonicalVacuumFirstWitnessBoundary
    vacuumMatterActionVariation
    zeroTensor
    (λ _ _ → refl)
    "the zero defect maps to zero stress only through an explicit action-variation witness"

zeroVacuumCoupledStressIsZero :
  ZeroTensor
    (stressFromDefectRequiresCoupling
      zeroDefectEnergy
      zeroVacuumDefectCoupling)
zeroVacuumCoupledStressIsZero _ _ = refl

------------------------------------------------------------------------
-- Flat Bianchi / conservation receipt for the zero-source model.

record FlatBianchiStressReceipt : Set where
  constructor mkFlatBianchiStressReceipt
  field
    EinsteinTensorZero :
      ZeroTensor EH.flatEinsteinTensor
    stressTensorZero : ZeroTensor zeroTensor
    contractedBianchiAtZero :
      (a b : Flat.Axis4) → EH.flatEinsteinTensor a b ≡ tri-mid
    covariantStressDivergenceAtZero :
      (a b : Flat.Axis4) → zeroTensor a b ≡ tri-mid
    receiptScope : String

open FlatBianchiStressReceipt public

flatBianchiStressReceipt : FlatBianchiStressReceipt
flatBianchiStressReceipt =
  mkFlatBianchiStressReceipt
    EH.flatEinsteinIsZero
    zeroTensorIsZero
    EH.flatEinsteinIsZero
    zeroTensorIsZero
    "exact zero-source conservation check in the flat model; not the general Bianchi theorem"

------------------------------------------------------------------------
-- Mass notions remain distinct types.

record InertialMass : Set where
  constructor mkInertialMass
  field inertialAmount : Nat
open InertialMass public

record ActiveGravitationalMass : Set where
  constructor mkActiveGravitationalMass
  field activeAmount : Nat
open ActiveGravitationalMass public

record PassiveGravitationalMass : Set where
  constructor mkPassiveGravitationalMass
  field passiveAmount : Nat
open PassiveGravitationalMass public

zeroInertialMass : InertialMass
zeroInertialMass = mkInertialMass zero

zeroActiveMass : ActiveGravitationalMass
zeroActiveMass = mkActiveGravitationalMass zero

zeroPassiveMass : PassiveGravitationalMass
zeroPassiveMass = mkPassiveGravitationalMass zero


data NaturalUnitsCEqualsOne : Set where
  cEqualsOne : NaturalUnitsCEqualsOne

record EquivalencePrincipleWitness
  (inertial : InertialMass)
  (active : ActiveGravitationalMass)
  (passive : PassiveGravitationalMass) : Set where
  constructor mkEquivalencePrincipleWitness
  field
    inertialEqualsActive : inertialAmount inertial ≡ activeAmount active
    inertialEqualsPassive : inertialAmount inertial ≡ passiveAmount passive

open EquivalencePrincipleWitness public


data NewtonianLimitMatch : ActiveGravitationalMass → Set where
  zeroNewtonianMatch : NewtonianLimitMatch zeroActiveMass

record MassIdentificationWitness (energy : DefectEnergy) : Set where
  constructor mkMassIdentificationWitness
  field
    unitConvention : NaturalUnitsCEqualsOne
    inertial : InertialMass
    active : ActiveGravitationalMass
    passive : PassiveGravitationalMass
    energyMatchesInertial :
      defectAmount energy ≡ inertialAmount inertial
    equivalenceWitness :
      EquivalencePrincipleWitness inertial active passive
    NewtonianMatch : NewtonianLimitMatch active
    identificationScope : String

open MassIdentificationWitness public

zeroMassIdentificationWitness :
  MassIdentificationWitness zeroDefectEnergy
zeroMassIdentificationWitness =
  mkMassIdentificationWitness
    cEqualsOne
    zeroInertialMass
    zeroActiveMass
    zeroPassiveMass
    refl
    (mkEquivalencePrincipleWitness refl refl)
    zeroNewtonianMatch
    "zero-energy/zero-mass vacuum normalization only"

activeMassFromDefectRequiresWitness :
  (energy : DefectEnergy) →
  MassIdentificationWitness energy →
  ActiveGravitationalMass
activeMassFromDefectRequiresWitness energy witness = active witness

passiveMassFromDefectRequiresWitness :
  (energy : DefectEnergy) →
  MassIdentificationWitness energy →
  PassiveGravitationalMass
passiveMassFromDefectRequiresWitness energy witness = passive witness

inertialMassFromDefectRequiresWitness :
  (energy : DefectEnergy) →
  MassIdentificationWitness energy →
  InertialMass
inertialMassFromDefectRequiresWitness energy witness = inertial witness

------------------------------------------------------------------------
-- Existing conditional boundary remains fail-closed for nonzero residues.

residueEnergyNotMass :
  Conditional.ionizationStyleEnergyIdentifiedWithMass
    Conditional.canonicalMassIdentificationBoundary
  ≡ false
residueEnergyNotMass = Conditional.canonicalResidueEnergyNotMass
