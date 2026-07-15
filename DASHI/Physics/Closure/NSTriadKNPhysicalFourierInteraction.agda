module DASHI.Physics.Closure.NSTriadKNPhysicalFourierInteraction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Sector

------------------------------------------------------------------------
-- Exact Fourier-space convection interaction.
--
-- For left + right + out = 0, the convolution output is -out.  We use one
-- canonical *unordered* input pair: its coefficient is the sum of the two
-- ordered convolution terms.  The leading minus is the energy-transfer
-- convention from the periodic Navier--Stokes equation.
--
--   - Re < conjugate(u_out), P_{-out} i [
--          (right . u_left) u_right + (left . u_right) u_left ] >.
--
-- paired with conjugate(u_out), then take its real part.  This fixes a
-- convention; a later equivalence theorem may relate it to a symmetrised
-- convention, but must not silently replace it by sampled ``coherence``.
------------------------------------------------------------------------

record ExactNSFourierInteractionStructure
    (S : Scalar.ExactOrderedScalar)
    (C : Fourier.ComplexFourierInterface S) : Set₁ where
  field
    complexMultiply : Fourier.Complex C → Fourier.Complex C → Fourier.Complex C
    imaginaryUnit : Fourier.Complex C
    scaleFourierVector : Fourier.Complex C → Fourier.FourierVector C → Fourier.FourierVector C
    addFourierVector : Fourier.FourierVector C → Fourier.FourierVector C → Fourier.FourierVector C
    lerayProject : Lattice.LatticeMode3 → Fourier.FourierVector C → Fourier.FourierVector C
    complexInner : Fourier.FourierVector C → Fourier.FourierVector C → Fourier.Complex C
    realPart : Fourier.Complex C → Scalar.Scalar S

open ExactNSFourierInteractionStructure public

physicalNSFourierTrilinearTerm :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  ExactNSFourierInteractionStructure S C →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) →
  Lattice.LatticeTriad → Fourier.Complex C
physicalNSFourierTrilinearTerm {C = C} I u τ =
  complexInner I
    (Fourier.conjugateVector C (u (Lattice.out τ)))
    (lerayProject I (Lattice.modeNeg (Lattice.out τ))
      (addFourierVector I
        (scaleFourierVector I
          (complexMultiply I (imaginaryUnit I)
            (Fourier.dotModeCoefficient C (Lattice.right τ) (u (Lattice.left τ))))
          (u (Lattice.right τ)))
        (scaleFourierVector I
          (complexMultiply I (imaginaryUnit I)
            (Fourier.dotModeCoefficient C (Lattice.left τ) (u (Lattice.right τ))))
          (u (Lattice.left τ)))))

-- This is the two-input helper only.  It represents the sum of the two
-- ordered convolution terms and is therefore correct on a non-diagonal
-- input-swap orbit, but would double the singleton orbit `(p , p)`.
-- The canonical physical coefficient for a cutoff carrier is defined in
-- `NSTriadKNFiniteConvolutionReconstruction` on `UnorderedInputOrbit`.
offDiagonalSymmetrizedInteraction :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  ExactNSFourierInteractionStructure S C →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) →
  Lattice.LatticeTriad → Scalar.Scalar S
offDiagonalSymmetrizedInteraction {S = S} I u τ =
  Scalar.neg S (realPart I (physicalNSFourierTrilinearTerm I u τ))

offDiagonalSymmetrizedInteractionFormula :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : ExactNSFourierInteractionStructure S C) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  (τ : Lattice.LatticeTriad) →
  offDiagonalSymmetrizedInteraction I u τ ≡
  Scalar.neg S (realPart I (physicalNSFourierTrilinearTerm I u τ))
offDiagonalSymmetrizedInteractionFormula I u τ = refl

offDiagonalSymmetrizedInteractionLawFromFourierConvection :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  ExactNSFourierInteractionStructure S C →
  {N : Nat} → Fourier.PhysicalTriadInteractionLaw S C N
offDiagonalSymmetrizedInteractionLawFromFourierConvection I =
  record { coherenceFormula = offDiagonalSymmetrizedInteraction I }

-- This is the PDE-identification theorem still required for the physical
-- route.  The existing local Python harness receives triads/coherences as
-- inputs, so it cannot inhabit this theorem.  In particular, this remains
-- false until a finite-shell energy-transfer convention and its convolution
-- expansion are proved in the chosen exact scalar model.
record TriadInteractionReconstructsConvection
    {S : Scalar.ExactOrderedScalar} {C : Fourier.ComplexFourierInterface S}
    (I : ExactNSFourierInteractionStructure S C)
    (N : Nat) : Set₁ where
  field
    shellConvectionEnergyTransfer :
      (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
    finiteTriadInteractionSum :
      (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
    reconstructs :
      (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
      finiteTriadInteractionSum u ≡ shellConvectionEnergyTransfer u

physicalInteractionReconstructionClosed : Bool
physicalInteractionReconstructionClosed = false

------------------------------------------------------------------------
-- The precise Fourier/PDE bridge for a finite output shell and an exact
-- input cutoff.  This deliberately identifies the signed scalar transfer
-- only; the auxiliary absolute/negative pair-Laplacian is related later by a
-- separate bad-transfer domination theorem.
------------------------------------------------------------------------

record FiniteTriadExpansionReconstructsConvection
    {S : Scalar.ExactOrderedScalar} {C : Fourier.ComplexFourierInterface S}
    (I : ExactNSFourierInteractionStructure S C)
    (N R : Nat)
    (sector : Sector.ExactOutputRetainedSectorLaw N R)
    (enumeration : Sector.ExactCutoffRetainedTriadEnumeration N R sector) : Set₁ where
  field
    cutoffConvectionEnergyTransfer :
      (Lattice.LatticeMode3 → Fourier.FourierVector C) →
      Lattice.LatticeMode3 → Scalar.Scalar S
    shellTriadInteractionSum :
      (Lattice.LatticeMode3 → Fourier.FourierVector C) →
      Lattice.LatticeMode3 → Scalar.Scalar S
    finiteTriadExpansionReconstructsConvection :
      (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
      (k : Lattice.LatticeMode3) →
      Lattice.inExactShell? N k ≡ true →
      shellTriadInteractionSum u k ≡ cutoffConvectionEnergyTransfer u k

finiteTriadExpansionReconstructsConvectionClosed : Bool
finiteTriadExpansionReconstructsConvectionClosed = false
