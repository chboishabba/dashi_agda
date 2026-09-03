module DASHI.Physics.QuantumVacuum.PerfectConductorMaxwellSpectrumBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as U1
import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Cutset
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- PERFECT-CONDUCTOR MAXWELL SPECTRUM, BIDI
--
-- This owner connects the repo's U(1)/Maxwell application surface to the
-- Casimir plate-spectrum interface without pretending the existing symbolic
-- Maxwell adapter already proves the conducting-boundary eigenmode theorem.
--
-- Forward direction:
--   Maxwell/U(1) field + perfect-conductor boundary eigenmode receipt
--     -> physical TE/TM longitudinal spectrum
--     -> ParallelPlateSpectralModel.
--
-- Reverse direction:
--   a consumer of the physical spectrum can project the exact Maxwell/PDE
--   obligations that still have to be discharged.
------------------------------------------------------------------------

data PerfectConductorPlate : Set where
  lowerPlate upperPlate : PerfectConductorPlate

data BoundaryConditionClass : Set where
  tangentialElectricZero
  normalMagneticZero
  sourceFreeInterior : BoundaryConditionClass

data ModeFamily : Set where
  transverseElectric
  transverseMagnetic : ModeFamily

record PerfectConductorBoundaryProblem : Set₁ where
  field
    FieldState : Set
    fieldSocket : U1.U1ElectromagneticFieldSocket

    separation : Q.Length
    plate : PerfectConductorPlate → Set

    TangentialElectricCondition : Set
    NormalMagneticCondition : Set
    SourceFreeInteriorCondition : Set

    tangentialElectricClosed : TangentialElectricCondition
    normalMagneticClosed : NormalMagneticCondition
    sourceFreeInteriorClosed : SourceFreeInteriorCondition

    boundaryReading : String

open PerfectConductorBoundaryProblem public

record ConductingModeEigenproblem
    (B : PerfectConductorBoundaryProblem) : Set₁ where
  field
    Transverse : Set
    Mode : Set

    transverse : Mode → Transverse
    longitudinal : Mode → Nat
    family : Mode → ModeFamily

    isEigenmode : Mode → Set
    admissible : Mode → Set

    longitudinalWaveNumber : Mode → Set
    longitudinalQuantisation :
      (m : Mode) →
      admissible m →
      longitudinalWaveNumber m

    teBoundaryEigenmode :
      (m : Mode) →
      family m ≡ transverseElectric →
      admissible m →
      isEigenmode m

    tmBoundaryEigenmode :
      (m : Mode) →
      family m ≡ transverseMagnetic →
      admissible m →
      isEigenmode m

    zeroSectorSemantics : Set
    polarisationMultiplicitySemantics : Set
    eigenproblemReading : String

open ConductingModeEigenproblem public

------------------------------------------------------------------------
-- Same-object weld to the Casimir scalar spectrum.
------------------------------------------------------------------------

record PerfectConductorSpectrumProducer
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    boundaryProblem : PerfectConductorBoundaryProblem
    eigenproblem : ConductingModeEigenproblem boundaryProblem

    transverseSquared :
      Transverse eigenproblem → Casimir.Scalar kernel
    square root : Casimir.Scalar kernel → Casimir.Scalar kernel
    divide : Casimir.Scalar kernel → Casimir.Scalar kernel → Casimir.Scalar kernel

    frequency :
      Q.Length → Mode eigenproblem → Casimir.Scalar kernel

    frequencyLaw :
      (d : Q.Length) →
      (m : Mode eigenproblem) →
      admissible eigenproblem m →
      frequency d m ≡
        Casimir._*_ kernel
          (Casimir.lightSpeed kernel)
          (root
            (Casimir._+_ kernel
              (transverseSquared (transverse eigenproblem m))
              (square
                (divide
                  (Casimir._*_ kernel
                    (Casimir.fromNat kernel (longitudinal eigenproblem m))
                    (Casimir.pi kernel))
                  (Casimir.lengthValue kernel d)))))

    sameU1FieldAsCasimirField : Set
    sameBoundarySeparation : Set
    producerReading : String

open PerfectConductorSpectrumProducer public

modeIndexOf :
  {kernel : Casimir.CasimirScalarModel} →
  (P : PerfectConductorSpectrumProducer kernel) →
  Mode (eigenproblem P) →
  Cutset.ParallelPlateModeIndex (Transverse (eigenproblem P))
modeIndexOf P m =
  Cutset.parallelPlateMode
    (transverse (eigenproblem P) m)
    (longitudinal (eigenproblem P) m)
    (caseFamily (family (eigenproblem P) m))
  where
  caseFamily : ModeFamily → Cutset.Polarisation
  caseFamily transverseElectric = Cutset.TE
  caseFamily transverseMagnetic = Cutset.TM

asParallelPlateSpectralModel :
  (kernel : Casimir.CasimirScalarModel) →
  PerfectConductorSpectrumProducer kernel →
  Cutset.ParallelPlateSpectralModel kernel
asParallelPlateSpectralModel kernel P = record
  { Transverse = Transverse (eigenproblem P)
  ; Mode = Mode (eigenproblem P)
  ; modeIndex = modeIndexOf P
  ; transverseSquared = transverseSquared P
  ; square = square P
  ; root = root P
  ; divide = divide P
  ; frequency = frequency P
  ; admissible = λ d m → admissible (eigenproblem P) m
  ; frequencyLaw = λ d m adm → frequencyLaw P d m adm
  ; spectralReading = "Perfect-conductor Maxwell/U(1) spectrum welded to the Casimir mode carrier."
  }

------------------------------------------------------------------------
-- Reverse obligations: these are the literal H_Maxwell payments.
------------------------------------------------------------------------

record MaxwellSpectrumObligations
    (B : PerfectConductorBoundaryProblem) : Set₁ where
  field
    metricHodgeAuthority : Set
    inhomogeneousMaxwellLawAuthority : Set
    perfectConductorTraceTheorem : Set
    sourceFreeInteriorWaveEquation : Set
    teTmCompleteness : Set
    longitudinalQuantisationAtNpiOverD : Set
    zeroSectorCounting : Set
    transverseMomentumCompleteness : Set

open MaxwellSpectrumObligations public

------------------------------------------------------------------------
-- Existing Maxwell infrastructure contributes carrier/provenance structure,
-- not the missing conducting-boundary PDE theorem.
------------------------------------------------------------------------

record MaxwellCrossPollinationBoundary : Set where
  field
    exteriorCalculusAdapterExists : Bool
    u1ApplicationSocketExists : Bool
    existingAdapterProvesPlateEigenmodes : Bool
    existingAdapterProvesModeCompleteness : Bool

    exteriorCalculusAdapterExistsIsTrue :
      exteriorCalculusAdapterExists ≡ true
    u1ApplicationSocketExistsIsTrue :
      u1ApplicationSocketExists ≡ true
    existingAdapterProvesPlateEigenmodesIsFalse :
      existingAdapterProvesPlateEigenmodes ≡ false
    existingAdapterProvesModeCompletenessIsFalse :
      existingAdapterProvesModeCompleteness ≡ false

open MaxwellCrossPollinationBoundary public

canonicalMaxwellCrossPollinationBoundary : MaxwellCrossPollinationBoundary
canonicalMaxwellCrossPollinationBoundary = record
  { exteriorCalculusAdapterExists = true
  ; u1ApplicationSocketExists = true
  ; existingAdapterProvesPlateEigenmodes = false
  ; existingAdapterProvesModeCompleteness = false
  ; exteriorCalculusAdapterExistsIsTrue = refl
  ; u1ApplicationSocketExistsIsTrue = refl
  ; existingAdapterProvesPlateEigenmodesIsFalse = refl
  ; existingAdapterProvesModeCompletenessIsFalse = refl
  }

------------------------------------------------------------------------
-- Sideways proof firewall.
------------------------------------------------------------------------

data SymbolicMaxwellAdapterClosesCasimirSpectrumPermission : Set where

symbolicMaxwellAdapterCannotAutoCloseCasimirSpectrum :
  SymbolicMaxwellAdapterClosesCasimirSpectrumPermission → ⊥
symbolicMaxwellAdapterCannotAutoCloseCasimirSpectrum ()
