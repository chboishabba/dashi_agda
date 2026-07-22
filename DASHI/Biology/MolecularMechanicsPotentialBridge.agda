module DASHI.Biology.MolecularMechanicsPotentialBridge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.CandidateOnlyCore as CandidateOnly

------------------------------------------------------------------------
-- Molecular mechanics as an effective-potential bridge.
--
-- This module formalises the modelling distinction described in the
-- accompanying discussion:
--
--   * an atomistic configuration is retained as the state carrier;
--   * electronic structure is replaced by an effective potential;
--   * forces are read from a chosen negative-gradient operator;
--   * only potential differences are physically compared;
--   * free energy adds an entropy contribution;
--   * electrostatic potential and coarse-grained models are separate lanes.
--
-- The module does not claim that an arbitrary force field is derived from the
-- many-electron Schrödinger equation, predicts protein folding, or supplies a
-- validated biochemical model.  Those remain explicit external obligations.

------------------------------------------------------------------------
-- Abstract scalar, configuration, and vector carriers.

record ScalarAlgebra : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    _+_ : Scalar → Scalar → Scalar
    _-_ : Scalar → Scalar → Scalar
    _*_ : Scalar → Scalar → Scalar
    negate : Scalar → Scalar

open ScalarAlgebra public

record MolecularCarrier (S : ScalarAlgebra) : Set₁ where
  field
    Atom : Set
    Configuration : Set
    ForceField : Set
    atomCount : Configuration → Nat
    zeroForce : ForceField
    addForce : ForceField → ForceField → ForceField
    scaleForce : Scalar S → ForceField → ForceField

open MolecularCarrier public

------------------------------------------------------------------------
-- Effective force-field decomposition.

record MolecularPotential
  (S : ScalarAlgebra)
  (M : MolecularCarrier S) : Set₁ where
  field
    bondPotential : Configuration M → Scalar S
    anglePotential : Configuration M → Scalar S
    torsionPotential : Configuration M → Scalar S
    electrostaticPotentialEnergy : Configuration M → Scalar S
    vanDerWaalsPotential : Configuration M → Scalar S

  totalPotential : Configuration M → Scalar S
  totalPotential x =
    _+_ S (bondPotential x)
      (_+_ S (anglePotential x)
        (_+_ S (torsionPotential x)
          (_+_ S (electrostaticPotentialEnergy x)
            (vanDerWaalsPotential x))))

open MolecularPotential public

molecularPotentialDecomposition :
  {S : ScalarAlgebra} →
  {M : MolecularCarrier S} →
  (P : MolecularPotential S M) →
  (x : Configuration M) →
  totalPotential P x ≡
    _+_ S (bondPotential P x)
      (_+_ S (anglePotential P x)
        (_+_ S (torsionPotential P x)
          (_+_ S (electrostaticPotentialEnergy P x)
            (vanDerWaalsPotential P x))))
molecularPotentialDecomposition P x = refl

------------------------------------------------------------------------
-- Potential differences and invariance under a constant energy offset.

potentialDifference :
  {S : ScalarAlgebra} →
  {M : MolecularCarrier S} →
  MolecularPotential S M →
  Configuration M →
  Configuration M →
  Scalar S
potentialDifference {S} P initial final =
  _-_ S (totalPotential P final) (totalPotential P initial)

record ConstantShiftLaw (S : ScalarAlgebra) : Set₁ where
  field
    shiftedDifferenceCancels :
      (final initial offset : Scalar S) →
      _-_ S (_+_ S final offset) (_+_ S initial offset) ≡
      _-_ S final initial

open ConstantShiftLaw public

potentialDifferenceIgnoresConstantOffset :
  {S : ScalarAlgebra} →
  (law : ConstantShiftLaw S) →
  (final initial offset : Scalar S) →
  _-_ S (_+_ S final offset) (_+_ S initial offset) ≡
  _-_ S final initial
potentialDifferenceIgnoresConstantOffset law =
  shiftedDifferenceCancels law

------------------------------------------------------------------------
-- Force is the negative gradient of the chosen effective potential.
--
-- Differentiability and the implementation of the gradient are deliberately
-- explicit inputs.  The bridge therefore cannot silently promote an arbitrary
-- potential into a physically validated force field.

record PotentialGradient
  (S : ScalarAlgebra)
  (M : MolecularCarrier S) : Set₁ where
  field
    gradient :
      (Configuration M → Scalar S) →
      Configuration M →
      ForceField M

open PotentialGradient public

forceFromPotential :
  {S : ScalarAlgebra} →
  {M : MolecularCarrier S} →
  PotentialGradient S M →
  MolecularPotential S M →
  Configuration M →
  ForceField M
forceFromPotential {S} {M} G P x =
  scaleForce M (negate S (_+_ S (zero S) (zero S)))
    (gradient G (totalPotential P) x)

-- The abstract scalar interface above intentionally does not assume a literal
-- numeric -1.  A concrete model supplies its own negative-gradient action.
record NegativeGradientAction
  (S : ScalarAlgebra)
  (M : MolecularCarrier S) : Set₁ where
  field
    negativeGradient :
      (Configuration M → Scalar S) →
      Configuration M →
      ForceField M

open NegativeGradientAction public

molecularForce :
  {S : ScalarAlgebra} →
  {M : MolecularCarrier S} →
  NegativeGradientAction S M →
  MolecularPotential S M →
  Configuration M →
  ForceField M
molecularForce G P = negativeGradient G (totalPotential P)

molecularForceIsNegativeGradient :
  {S : ScalarAlgebra} →
  {M : MolecularCarrier S} →
  (G : NegativeGradientAction S M) →
  (P : MolecularPotential S M) →
  (x : Configuration M) →
  molecularForce G P x ≡ negativeGradient G (totalPotential P) x
molecularForceIsNegativeGradient G P x = refl

------------------------------------------------------------------------
-- Electrostatic potential is distinct from total molecular potential energy.

record ElectrostaticField
  (S : ScalarAlgebra)
  (M : MolecularCarrier S) : Set₁ where
  field
    Point : Set
    charge : Atom M → Scalar S
    electricPotential : Point → Scalar S
    atomPosition : Configuration M → Atom M → Point

  electrostaticEnergyAt :
    Configuration M →
    Atom M →
    Scalar S
  electrostaticEnergyAt x atom =
    _*_ S (charge atom) (electricPotential (atomPosition x atom))

open ElectrostaticField public

electrostaticEnergyIsChargeTimesPotential :
  {S : ScalarAlgebra} →
  {M : MolecularCarrier S} →
  (E : ElectrostaticField S M) →
  (x : Configuration M) →
  (atom : Atom M) →
  electrostaticEnergyAt E x atom ≡
  _*_ S (charge E atom)
    (electricPotential E (atomPosition E x atom))
electrostaticEnergyIsChargeTimesPotential E x atom = refl

------------------------------------------------------------------------
-- Free energy adds the entropy contribution to the energetic carrier.

record ThermodynamicFreeEnergy
  (S : ScalarAlgebra)
  (M : MolecularCarrier S) : Set₁ where
  field
    enthalpy : Configuration M → Scalar S
    entropy : Configuration M → Scalar S
    temperature : Scalar S

  freeEnergy : Configuration M → Scalar S
  freeEnergy x =
    _-_ S (enthalpy x) (_*_ S temperature (entropy x))

open ThermodynamicFreeEnergy public

freeEnergyDefinition :
  {S : ScalarAlgebra} →
  {M : MolecularCarrier S} →
  (T : ThermodynamicFreeEnergy S M) →
  (x : Configuration M) →
  freeEnergy T x ≡
  _-_ S (enthalpy T x)
    (_*_ S (temperature T) (entropy T x))
freeEnergyDefinition T x = refl

------------------------------------------------------------------------
-- All-atom versus coarse-grained modelling.

record CoarseGraining
  {S : ScalarAlgebra}
  (allAtom : MolecularCarrier S)
  (coarse : MolecularCarrier S) : Set₁ where
  field
    coarseConfiguration :
      Configuration allAtom →
      Configuration coarse

    effectiveCoarsePotential :
      Configuration coarse →
      Scalar S

    informationDiscarded : Bool
    informationDiscardedIsFalse : informationDiscarded ≡ false

open CoarseGraining public

------------------------------------------------------------------------
-- Explicit approximation obligations.

record MolecularMechanicsValidationBoundary
  (S : ScalarAlgebra)
  (M : MolecularCarrier S)
  (P : MolecularPotential S M) : Set₁ where
  field
    parameterisationEvidence : Set
    quantumCalibrationEvidence : Set
    solventModelEvidence : Set
    samplingAdequacyEvidence : Set
    experimentalValidationEvidence : Set

    noFirstPrinciplesDerivationClaim : Bool
    noFirstPrinciplesDerivationClaimIsFalse :
      noFirstPrinciplesDerivationClaim ≡ false

    noUniversalFoldingPredictionClaim : Bool
    noUniversalFoldingPredictionClaimIsFalse :
      noUniversalFoldingPredictionClaim ≡ false

    noBiochemicalAuthorityClaim : Bool
    noBiochemicalAuthorityClaimIsFalse :
      noBiochemicalAuthorityClaim ≡ false

open MolecularMechanicsValidationBoundary public

------------------------------------------------------------------------
-- Candidate-only receipt surface.

molecularMechanicsBridgeOwner : String
molecularMechanicsBridgeOwner =
  "DASHI.Biology.MolecularMechanicsPotentialBridge"

canonicalPotentialLandscapeRow : CandidateOnly.CandidateOnlyRow
canonicalPotentialLandscapeRow =
  CandidateOnly.mkCandidateOnlyRow
    "molecular potential landscape"
    molecularMechanicsBridgeOwner
    "totalPotential"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "A molecular configuration is assigned an effective potential assembled from bonded and non-bonded terms."
    "The effective potential is not thereby derived from exact electronic structure or experimentally validated."

canonicalNegativeGradientForceRow : CandidateOnly.CandidateOnlyRow
canonicalNegativeGradientForceRow =
  CandidateOnly.mkCandidateOnlyRow
    "negative-gradient molecular force"
    molecularMechanicsBridgeOwner
    "molecularForce"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "A supplied negative-gradient action converts the effective potential into a force field."
    "Differentiability, numerical accuracy, force-field calibration, and physical validity remain external obligations."

canonicalPotentialDifferenceRow : CandidateOnly.CandidateOnlyRow
canonicalPotentialDifferenceRow =
  CandidateOnly.mkCandidateOnlyRow
    "potential-energy difference"
    molecularMechanicsBridgeOwner
    "potentialDifference"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "Initial and final configurations are compared through a potential-energy difference rather than an absolute energy origin."
    "Energetic preference alone does not establish kinetics, entropy, folding probability, or biological function."

canonicalFreeEnergyRow : CandidateOnly.CandidateOnlyRow
canonicalFreeEnergyRow =
  CandidateOnly.mkCandidateOnlyRow
    "thermodynamic free energy"
    molecularMechanicsBridgeOwner
    "freeEnergy"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "The thermodynamic bridge distinguishes potential energy from enthalpy-minus-temperature-times-entropy free energy."
    "A formal free-energy expression does not supply entropy estimation, equilibrium sampling, or experimental validation."

canonicalElectrostaticPotentialRow : CandidateOnly.CandidateOnlyRow
canonicalElectrostaticPotentialRow =
  CandidateOnly.mkCandidateOnlyRow
    "electrostatic potential field"
    molecularMechanicsBridgeOwner
    "electrostaticEnergyAt"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "Electrostatic energy is represented as charge times an environmental electric potential at an atomic position."
    "The field model does not automatically resolve solvent, screening, polarization, ions, or electron correlation."

canonicalMolecularMechanicsRows :
  List CandidateOnly.CandidateOnlyRow
canonicalMolecularMechanicsRows =
  canonicalPotentialLandscapeRow
  ∷ canonicalNegativeGradientForceRow
  ∷ canonicalPotentialDifferenceRow
  ∷ canonicalFreeEnergyRow
  ∷ canonicalElectrostaticPotentialRow
  ∷ []

canonicalPotentialLandscapeReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalPotentialLandscapeRow
canonicalPotentialLandscapeReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalPotentialLandscapeRow
    refl refl refl refl refl refl refl refl

canonicalNegativeGradientForceReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalNegativeGradientForceRow
canonicalNegativeGradientForceReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalNegativeGradientForceRow
    refl refl refl refl refl refl refl refl

canonicalPotentialDifferenceReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalPotentialDifferenceRow
canonicalPotentialDifferenceReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalPotentialDifferenceRow
    refl refl refl refl refl refl refl refl

canonicalFreeEnergyReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalFreeEnergyRow
canonicalFreeEnergyReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalFreeEnergyRow
    refl refl refl refl refl refl refl refl

canonicalElectrostaticPotentialReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalElectrostaticPotentialRow
canonicalElectrostaticPotentialReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalElectrostaticPotentialRow
    refl refl refl refl refl refl refl refl
