module DASHI.Physics.Closure.NSTriadKNLuoPhysicalEnumerationReuseExact where

------------------------------------------------------------------------
-- PURPOSE
-- Reuse the repository's existing exact physical Fourier infrastructure in
-- the Luo cutoff-flux route.  The literal cutoff-cube enumeration, output
-- fibres, exact hard high-output selection, three-leg energy orbit,
-- conjugation/swap closure, validated fibre image and code/physical kernel
-- equality are already constructive.
--
-- What remains is narrower: compare the repository hard projector with Luo's
-- smooth low-pass convention, and instantiate the local signed coefficient
-- majorant and uniform weighted-Schur constants on the selected subset.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as OutputFiber
import DASHI.Physics.Closure.NSTriadKNPhysicalHardHighTriadSelectionExact as HighSelection
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalSymmetryEnumerationClosure as Symmetry
import DASHI.Physics.Closure.NSTriadKNValidatedPhysicalFiberImage as FiberImage
import DASHI.Physics.Closure.NSTriadKNExactPhysicalKernelIdentification as ExactKernel
import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel as FourierKernel
import DASHI.Physics.Closure.NSCompactGammaOffPacketTriadMajorization as Majorization

literalPhysicalTriads : Nat → List Physical.PhysicalTriadIncidence
literalPhysicalTriads = Physical.physicalTriadEnumeration

literalPhysicalTriadSound :
  ∀ {cutoff triad} →
  Cube._∈_ triad (literalPhysicalTriads cutoff) →
  Physical.PhysicalTriadInCutoff cutoff triad
literalPhysicalTriadSound = Physical.physicalTriadEnumerationCutoffSound

literalPhysicalTriadComplete :
  ∀ {cutoff triad} →
  Physical.PhysicalTriadInCutoff cutoff triad →
  Physical.PhysicalTriadEnumerationHit cutoff triad
literalPhysicalTriadComplete = Physical.physicalTriadEnumerationComplete

literalPhysicalTriadNoDuplicates :
  (cutoff : Nat) →
  Cube.NoDuplicates (literalPhysicalTriads cutoff)
literalPhysicalTriadNoDuplicates =
  Physical.physicalTriadEnumerationNoDuplicates

literalOutputFiber :
  Nat → Z3.FourierMode → List Physical.PhysicalTriadIncidence
literalOutputFiber = OutputFiber.physicalOutputFiber

literalOutputFiberSound :
  ∀ {cutoff output triad} →
  Cube._∈_ triad (literalOutputFiber cutoff output) →
  Physical.k triad ≡ output
literalOutputFiberSound = OutputFiber.physicalOutputFiberSound

literalOutputFiberComplete :
  ∀ {cutoff output triad} →
  Cube._∈_ triad (literalPhysicalTriads cutoff) →
  Physical.k triad ≡ output →
  Cube._∈_ triad (literalOutputFiber cutoff output)
literalOutputFiberComplete = OutputFiber.physicalOutputFiberComplete

record LuoPhysicalEnumerationReuseReceipt : Set where
  constructor receipt
  field
    literalCutoffTriadEnumerationConstructed :
      Physical.physicalTriadEnumerationImplemented ≡ true

    literalCutoffTriadEnumerationDuplicateFree :
      Physical.physicalTriadEnumerationDuplicateFree ≡ true

    literalCutoffRealityPolicyConstructed :
      Physical.physicalTriadRealityPolicyImplemented ≡ true

    literalOutputFiberConstructed :
      OutputFiber.physicalOutputFiberImplemented ≡ true

    hardHighOutputSelectionConstructed :
      HighSelection.hardHighOutputSelectionConstructed ≡ true

    hardHighSelectionSoundComplete :
      HighSelection.hardHighSelectionSoundComplete ≡ true

    hardHighSelectionDuplicateFree :
      HighSelection.hardHighSelectionDuplicateFree ≡ true

    hardLowHighPartitionConstructed :
      HighSelection.hardLowHighPartitionConstructed ≡ true

    threeLegEnergyOrbitConstructed :
      Orbit.physicalTriadEnergyOrbitConstructed ≡ true

    swapConjugationEnumerationClosureConstructed :
      Symmetry.physicalSymmetryEnumerationClosureImplemented ≡ true

    validatedPhysicalFiberImageConstructed :
      FiberImage.validatedPhysicalFiberImageConstructed ≡ true

    exactPhysicalKernelIdentificationReductionConstructed :
      ExactKernel.exactPhysicalKernelIdentificationReductionImplemented ≡ true

open LuoPhysicalEnumerationReuseReceipt public

luoPhysicalEnumerationReuseReceipt : LuoPhysicalEnumerationReuseReceipt
luoPhysicalEnumerationReuseReceipt = receipt
  Physical.physicalTriadEnumerationImplementedIsTrue
  Physical.physicalTriadEnumerationDuplicateFreeIsTrue
  Physical.physicalTriadRealityPolicyImplementedIsTrue
  OutputFiber.physicalOutputFiberImplementedIsTrue
  HighSelection.hardHighOutputSelectionConstructedIsTrue
  HighSelection.hardHighSelectionSoundCompleteIsTrue
  HighSelection.hardHighSelectionDuplicateFreeIsTrue
  HighSelection.hardLowHighPartitionConstructedIsTrue
  Orbit.physicalTriadEnergyOrbitConstructedIsTrue
  Symmetry.physicalSymmetryEnumerationClosureImplementedIsTrue
  FiberImage.validatedPhysicalFiberImageConstructedIsTrue
  ExactKernel.exactPhysicalKernelIdentificationReductionImplementedIsTrue

literalPhysicalCutoffEnumerationAvailableToLuoRoute : Bool
literalPhysicalCutoffEnumerationAvailableToLuoRoute = true

literalPhysicalOutputFibresAvailableToLuoRoute : Bool
literalPhysicalOutputFibresAvailableToLuoRoute = true

hardProjectedHighFrequencySelectionConstructed : Bool
hardProjectedHighFrequencySelectionConstructed = true

validatedPhysicalKernelImageAvailableToLuoRoute : Bool
validatedPhysicalKernelImageAvailableToLuoRoute = true

fourierBiotSavartKernelDefinedByPairIncidenceFold : Bool
fourierBiotSavartKernelDefinedByPairIncidenceFold = true

finiteTriadMajorizationCompositionAvailable : Bool
finiteTriadMajorizationCompositionAvailable = true

hardProjectorComparedWithLuoSmoothProjector : Bool
hardProjectorComparedWithLuoSmoothProjector = false

physicalFluxCoefficientMajorantInstantiated : Bool
physicalFluxCoefficientMajorantInstantiated = false

physicalFullCutoffWeightedSchurInstantiated : Bool
physicalFullCutoffWeightedSchurInstantiated = false

literalPhysicalCutoffEnumerationAvailableToLuoRouteIsTrue :
  literalPhysicalCutoffEnumerationAvailableToLuoRoute ≡ true
literalPhysicalCutoffEnumerationAvailableToLuoRouteIsTrue = refl

literalPhysicalOutputFibresAvailableToLuoRouteIsTrue :
  literalPhysicalOutputFibresAvailableToLuoRoute ≡ true
literalPhysicalOutputFibresAvailableToLuoRouteIsTrue = refl

hardProjectedHighFrequencySelectionConstructedIsTrue :
  hardProjectedHighFrequencySelectionConstructed ≡ true
hardProjectedHighFrequencySelectionConstructedIsTrue = refl

validatedPhysicalKernelImageAvailableToLuoRouteIsTrue :
  validatedPhysicalKernelImageAvailableToLuoRoute ≡ true
validatedPhysicalKernelImageAvailableToLuoRouteIsTrue = refl

fourierBiotSavartKernelDefinedByPairIncidenceFoldIsTrue :
  fourierBiotSavartKernelDefinedByPairIncidenceFold ≡ true
fourierBiotSavartKernelDefinedByPairIncidenceFoldIsTrue = refl

finiteTriadMajorizationCompositionAvailableIsTrue :
  finiteTriadMajorizationCompositionAvailable ≡ true
finiteTriadMajorizationCompositionAvailableIsTrue = refl

hardProjectorComparedWithLuoSmoothProjectorIsFalse :
  hardProjectorComparedWithLuoSmoothProjector ≡ false
hardProjectorComparedWithLuoSmoothProjectorIsFalse = refl

physicalFluxCoefficientMajorantInstantiatedIsFalse :
  physicalFluxCoefficientMajorantInstantiated ≡ false
physicalFluxCoefficientMajorantInstantiatedIsFalse = refl

physicalFullCutoffWeightedSchurInstantiatedIsFalse :
  physicalFullCutoffWeightedSchurInstantiated ≡ false
physicalFullCutoffWeightedSchurInstantiatedIsFalse = refl
