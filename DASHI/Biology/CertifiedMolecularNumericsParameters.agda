module DASHI.Biology.CertifiedMolecularNumericsParameters where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using
  ( Float
  ; primFloatPlus
  ; primFloatMinus
  ; primFloatTimes
  ; primFloatDiv
  ; primFloatLess
  )
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Biology.ConcreteProteinMolecularMechanics

------------------------------------------------------------------------
-- Certified interval architecture.
--
-- Float endpoints remain executable.  Rigour comes only after a backend proves
-- that every primitive enclosure is outward rounded.  This module therefore
-- separates interval syntax and propagation from the backend certificate.

record Interval : Set where
  constructor interval
  field
    lower : Float
    upper : Float

open Interval public

intervalOrdered : Interval → Bool
intervalOrdered i with primFloatLess (upper i) (lower i)
... | true = false
... | false = true

pointInterval : Float → Interval
pointInterval x = interval x x

intervalPlus : Interval → Interval → Interval
intervalPlus a b =
  interval
    (lower a +f lower b)
    (upper a +f upper b)

intervalNegate : Interval → Interval
intervalNegate a =
  interval
    (negf (upper a))
    (negf (lower a))

intervalMinus : Interval → Interval → Interval
intervalMinus a b = intervalPlus a (intervalNegate b)

minimum4 : Float → Float → Float → Float → Float
minimum4 a b c d with primFloatLess a b
... | true with primFloatLess a c
...   | true with primFloatLess a d
...     | true = a
...     | false = d
...   | false with primFloatLess c d
...     | true = c
...     | false = d
... | false with primFloatLess b c
...   | true with primFloatLess b d
...     | true = b
...     | false = d
...   | false with primFloatLess c d
...     | true = c
...     | false = d

maximum4 : Float → Float → Float → Float → Float
maximum4 a b c d with primFloatLess a b
... | true with primFloatLess b c
...   | true with primFloatLess c d
...     | true = d
...     | false = c
...   | false with primFloatLess b d
...     | true = d
...     | false = b
... | false with primFloatLess a c
...   | true with primFloatLess c d
...     | true = d
...     | false = c
...   | false with primFloatLess a d
...     | true = d
...     | false = a

intervalTimes : Interval → Interval → Interval
intervalTimes a b =
  interval
    (minimum4 ll lu ul uu)
    (maximum4 ll lu ul uu)
  where
    ll : Float
    ll = lower a *f lower b

    lu : Float
    lu = lower a *f upper b

    ul : Float
    ul = upper a *f lower b

    uu : Float
    uu = upper a *f upper b

record OutwardRoundedIntervalBackend : Set where
  field
    additionEnclosesExactResult : Bool
    subtractionEnclosesExactResult : Bool
    multiplicationEnclosesExactResult : Bool
    divisionEnclosesExactResultAwayFromZero : Bool
    squareRootEnclosesExactResultOnNonnegativeDomain : Bool
    sineEnclosesExactResult : Bool
    cosineEnclosesExactResult : Bool
    exponentialEnclosesExactResult : Bool
    logarithmEnclosesExactResultOnPositiveDomain : Bool
    noNaNEndpoints : Bool
    noInfiniteEndpoints : Bool
    backendName : String

open OutwardRoundedIntervalBackend public

record CertifiedEnergyComparison : Set where
  constructor certifiedEnergyComparison
  field
    firstEnergy : Interval
    secondEnergy : Interval
    strictSeparation : Bool
    separationMargin : Float
    backendCertified : Bool

open CertifiedEnergyComparison public

intervalStrictlyBelow : Interval → Interval → Bool
intervalStrictlyBelow a b = primFloatLess (upper a) (lower b)

mkCertifiedEnergyComparison :
  OutwardRoundedIntervalBackend →
  Interval →
  Interval →
  CertifiedEnergyComparison
mkCertifiedEnergyComparison backend a b =
  certifiedEnergyComparison
    a b
    (intervalStrictlyBelow a b)
    (lower b -f upper a)
    (additionEnclosesExactResult backend)

record CertifiedConvergenceClaim : Set where
  field
    approximationSequence : Nat → Interval
    candidateLimit : Interval
    tailIndex : Nat
    tailErrorBound : Float
    tailContainedInLimitEnclosure : Bool
    monotoneErrorBound : Bool
    backendCertified : Bool

open CertifiedConvergenceClaim public

------------------------------------------------------------------------
-- Force-field parameter schemas and provenance.

record AtomTypeParameter : Set where
  constructor atomTypeParameter
  field
    atomTypeName : String
    atomTypeElement : Element
    atomTypeMass : Float
    atomTypeCharge : Float
    atomTypeSigma : Float
    atomTypeEpsilon : Float

open AtomTypeParameter public

record BondTypeParameter : Set where
  constructor bondTypeParameter
  field
    bondTypeLeft : String
    bondTypeRight : String
    bondTypeStiffness : Float
    bondTypeLength : Float

open BondTypeParameter public

record AngleTypeParameter : Set where
  constructor angleTypeParameter
  field
    angleTypeLeft : String
    angleTypeCentre : String
    angleTypeRight : String
    angleTypeStiffness : Float
    angleTypeEquilibrium : Float

open AngleTypeParameter public

record TorsionTypeParameter : Set where
  constructor torsionTypeParameter
  field
    torsionTypeA : String
    torsionTypeB : String
    torsionTypeC : String
    torsionTypeD : String
    torsionTypeAmplitude : Float
    torsionTypeMultiplicity : Float
    torsionTypePhase : Float

open TorsionTypeParameter public

record ForceFieldParameterSet : Set where
  constructor forceFieldParameterSet
  field
    parameterSetName : String
    parameterSetVersion : String
    parameterSetCitation : String
    parameterSetLicense : String
    atomTypeParameters : List AtomTypeParameter
    bondTypeParameters : List BondTypeParameter
    angleTypeParameters : List AngleTypeParameter
    torsionTypeParameters : List TorsionTypeParameter
    mixingRule : String
    electrostaticConvention : String
    sourceFilesVerified : Bool
    unitConversionVerified : Bool
    parameterCoverageVerified : Bool
    experimentallyValidated : Bool

open ForceFieldParameterSet public

-- A complete import surface for externally supplied AMBER/CHARMM/OPLS data.
-- The repo does not copy or relabel third-party tables without their source,
-- version, unit convention, and licence being provided.

record ExternalParameterImport : Set where
  field
    importedParameters : ForceFieldParameterSet
    sourceChecksum : String
    parserVersion : String
    sourceProvenanceVerified : Bool
    licenceCompatible : Bool
    allRequiredAtomTypesPresent : Bool
    allRequiredBondTypesPresent : Bool
    allRequiredAngleTypesPresent : Bool
    allRequiredTorsionTypesPresent : Bool

open ExternalParameterImport public

-- Small executable DASHI-owned demonstration set.  These values are deliberately
-- illustrative and are not labelled AMBER, CHARMM, or OPLS parameters.

minimalHydrogen : AtomTypeParameter
minimalHydrogen =
  atomTypeParameter "H-demo" hydrogen 1.008 0.1 1.2 0.015

minimalCarbon : AtomTypeParameter
minimalCarbon =
  atomTypeParameter "C-demo" carbon 12.011 0.0 3.4 0.10

minimalNitrogen : AtomTypeParameter
minimalNitrogen =
  atomTypeParameter "N-demo" nitrogen 14.007 (negf 0.3) 3.2 0.17

minimalOxygen : AtomTypeParameter
minimalOxygen =
  atomTypeParameter "O-demo" oxygen 15.999 (negf 0.5) 3.0 0.20

minimalCNBond : BondTypeParameter
minimalCNBond =
  bondTypeParameter "C-demo" "N-demo" 300.0 1.33

minimalNCCAngle : AngleTypeParameter
minimalNCCAngle =
  angleTypeParameter "N-demo" "C-demo" "C-demo" 50.0 2.09439510239

minimalPeptideTorsion : TorsionTypeParameter
minimalPeptideTorsion =
  torsionTypeParameter
    "C-demo" "N-demo" "C-demo" "C-demo"
    1.0 2.0 3.14159265359

minimalDemonstrationParameterSet : ForceFieldParameterSet
minimalDemonstrationParameterSet =
  forceFieldParameterSet
    "DASHI-Minimal-Protein-Demonstration"
    "1"
    "Internal executable demonstration; not a validated biomolecular force field."
    "Repository licence"
    (minimalHydrogen ∷ minimalCarbon ∷ minimalNitrogen ∷ minimalOxygen ∷ [])
    (minimalCNBond ∷ [])
    (minimalNCCAngle ∷ [])
    (minimalPeptideTorsion ∷ [])
    "Lorentz-Berthelot demonstration mixing"
    "Reduced-unit pair Coulomb demonstration"
    true true false false

minimalSetNotExperimentallyValidated :
  experimentallyValidated minimalDemonstrationParameterSet ≡ false
minimalSetNotExperimentallyValidated = refl

record ParameterAssignmentBoundary : Set where
  field
    atomTypingUnique : Bool
    residueTemplatesComplete : Bool
    terminalPatchesApplied : Bool
    protonationStateSpecified : Bool
    missingParametersAbsent : Bool
    unitsConsistent : Bool
    oneFourScalingSpecified : Bool
    exclusionsSpecified : Bool

open ParameterAssignmentBoundary public
