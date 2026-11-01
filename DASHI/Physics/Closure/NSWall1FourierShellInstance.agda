module DASHI.Physics.Closure.NSWall1FourierShellInstance where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Lattice
open Lattice using
  ( FourierMode
  ; ShellPredicate
  ; ShellSeparated
  ; InShell
  )
open import DASHI.Physics.Closure.NSPairIncidenceKernel using (PairIncidenceData)
open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel

------------------------------------------------------------------------
-- Active Wall-1 Fourier shell instance.
--
-- The lattice carrier is fixed to Z^3.  Scalar/vector arithmetic remains a
-- socket so exact rationals, intervals, or another certified carrier can be
-- used without changing the shell or triad definitions.
------------------------------------------------------------------------

record Wall1FourierShellData
    {v s : Level}
    (Vector : Set v)
    (Scalar : Set s) : Set (lsuc (v ⊔ s)) where
  field
    laws : FourierVectorLaws FourierMode Vector Scalar

    integerWaveVector : FourierMode → Vector
    waveVectorIsIntegerEmbedding :
      ∀ mode → waveVector laws mode ≡ integerWaveVector mode

    lowShell highShell : ShellPredicate
    shellSeparation : ShellSeparated lowShell highShell

    activeLowModes : List FourierMode
    activeHighModes : List FourierMode

    ActiveLow : FourierMode → Set
    ActiveHigh : FourierMode → Set

    activeLowInLowShell :
      ∀ mode → ActiveLow mode → InShell lowShell mode

    activeHighInHighShell :
      ∀ mode → ActiveHigh mode → InShell highShell mode

    backgroundAmplitude : FourierMode → Scalar
    backgroundPolarization : FourierMode → Vector
    perturbationPolarization : FourierMode → Vector

    backgroundVorticity : FourierMode → Vector
    backgroundVorticityDefinition :
      ∀ mode →
      backgroundVorticity mode ≡
      vectorScale laws
        (backgroundAmplitude mode)
        (backgroundPolarization mode)

    backgroundDivergenceFree :
      ∀ mode →
      vectorDot laws
        (waveVector laws mode)
        (backgroundVorticity mode)
      ≡ scalarZero laws

    perturbationDivergenceFree :
      ∀ mode →
      vectorDot laws
        (waveVector laws mode)
        (perturbationPolarization mode)
      ≡ scalarZero laws

    triads :
      List
        (ResonantFourierTriad
          FourierMode
          Lattice.addMode
          Lattice.NonZeroMode)

    targetModes sourceModes : List FourierMode

    targetWeight sourceWeight : FourierMode → Scalar

open Wall1FourierShellData public

wall1TransferData :
  ∀ {v s}
    {Vector : Set v}
    {Scalar : Set s} →
  Wall1FourierShellData Vector Scalar →
  FourierBiotSavartTransferData FourierMode Vector Scalar
wall1TransferData W = record
  { laws = laws W
  ; addMode = Lattice.addMode
  ; NonZeroMode = Lattice.NonZeroMode
  ; triads = triads W
  ; targetModes = targetModes W
  ; sourceModes = sourceModes W
  ; backgroundVorticity = backgroundVorticity W
  ; perturbationPolarization = perturbationPolarization W
  ; backgroundDivergenceFree = backgroundDivergenceFree W
  ; perturbationDivergenceFree = perturbationDivergenceFree W
  ; targetWeight = targetWeight W
  ; sourceWeight = sourceWeight W
  }

wall1PairIncidenceData :
  ∀ {v s}
    {Vector : Set v}
    {Scalar : Set s} →
  Wall1FourierShellData Vector Scalar →
  PairIncidenceData
    (ResonantFourierTriad
      FourierMode
      Lattice.addMode
      Lattice.NonZeroMode)
    FourierMode FourierMode Scalar
wall1PairIncidenceData W =
  fourierPairIncidenceData (wall1TransferData W)

wall1BiotSavartKernel :
  ∀ {v s}
    {Vector : Set v}
    {Scalar : Set s} →
  Wall1FourierShellData Vector Scalar →
  FourierMode → FourierMode → Scalar
wall1BiotSavartKernel W =
  fourierBiotSavartKernel (wall1TransferData W)
