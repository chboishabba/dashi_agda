module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitInteraction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (map)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNFiniteConvolutionReconstruction as Reconstruction
import DASHI.Physics.Closure.NSTriadKNPhysicalFourierInteraction as Interaction

------------------------------------------------------------------------
-- Authoritative physical interaction on the cutoff quotient carrier.
--
-- A labelled triad has two input orders, whereas the direct Fourier
-- convolution is quotiented here by input swap.  This interface therefore
-- deliberately does not reuse `PhysicalTriadInteractionLaw`: its carrier is
-- an `UnorderedInputOrbit`, so a diagonal input pair is a singleton and an
-- off-diagonal pair has its two ordered summands exactly once each.
------------------------------------------------------------------------

record PhysicalCutoffOrbitInteractionLaw
    {S : Scalar.ExactOrderedScalar} {C : Fourier.ComplexFourierInterface S}
    (I : Interaction.ExactNSFourierInteractionStructure S C)
    (N R : Nat) : Set₁ where
  field
    orbitInteraction :
      (Lattice.LatticeMode3 → Fourier.FourierVector C) →
      Reconstruction.UnorderedInputOrbit → Scalar.Scalar S
    orbitInteractionIsCanonical :
      (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
      (o : Reconstruction.UnorderedInputOrbit) →
      orbitInteraction u o ≡ Reconstruction.canonicalOrbitInteraction I u o

open PhysicalCutoffOrbitInteractionLaw public

canonicalPhysicalCutoffOrbitInteractionLaw :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (N R : Nat) → PhysicalCutoffOrbitInteractionLaw I N R
canonicalPhysicalCutoffOrbitInteractionLaw I N R =
  record
    { orbitInteraction = Reconstruction.canonicalOrbitInteraction I
    ; orbitInteractionIsCanonical = λ u o → refl
    }

physicalCutoffOrbitInteractionSum :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (N R : Nat) →
  PhysicalCutoffOrbitInteractionLaw I N R →
  (Lattice.LatticeMode3 → Fourier.FourierVector C) → Scalar.Scalar S
physicalCutoffOrbitInteractionSum {S = S} I N R law u =
  Reconstruction.sumScalarList S
    (map (orbitInteraction law u)
      (Reconstruction.canonicalUnorderedInputOrbits N R))

canonicalOrbitSumEqualsPhysicalCutoffOrbitInteractionSum :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : Reconstruction.ExactFiniteSumAuthority S) →
  (N R : Nat) →
  (law : PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  Reconstruction.canonicalUnorderedTriadInteractionSum I N R u ≡
  physicalCutoffOrbitInteractionSum I N R law u
canonicalOrbitSumEqualsPhysicalCutoffOrbitInteractionSum {S = S} I A N R law u =
  Reconstruction.sumScalarList-resp-pointwise S A
    (Reconstruction.canonicalOrbitInteraction I u)
    (orbitInteraction law u)
    (λ o → sym (orbitInteractionIsCanonical law u o))
    (Reconstruction.canonicalUnorderedInputOrbits N R)

-- This is the advertised finite Fourier reconstruction with the
-- authoritative orbit-indexed physical coefficient on the right.  It is a
-- theorem about the direct ordered convolution, not a definition of it.
finiteTriadExpansionReconstructsPhysicalCutoffOrbitInteraction :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (A : Reconstruction.ExactFiniteSumAuthority S) →
  (N R : Nat) →
  (law : PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Lattice.LatticeMode3 → Fourier.FourierVector C) →
  Reconstruction.cutoffShellConvection I N R u ≡
  physicalCutoffOrbitInteractionSum I N R law u
finiteTriadExpansionReconstructsPhysicalCutoffOrbitInteraction
  I A N R law u =
  trans
    (Reconstruction.finiteTriadExpansionReconstructsCutoffConvection I A N R u)
    (canonicalOrbitSumEqualsPhysicalCutoffOrbitInteractionSum I A N R law u)

------------------------------------------------------------------------
-- Orbit-derived auxiliary Gram weights.
--
-- The existing `AdmissibleFourierShellData` still carries a labelled-triad
-- coherence field.  It remains useful here for its Fourier coefficients and
-- nonnegative amplitudes only; the weights below intentionally obtain their
-- interaction from the authoritative cutoff-orbit law instead.
------------------------------------------------------------------------

cutoffOrbitAmplitudeFactor :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  Fourier.AdmissibleFourierShellData S C N interaction →
  Reconstruction.UnorderedInputOrbit → Scalar.Scalar S
cutoffOrbitAmplitudeFactor u o =
  Fourier.triadAmplitudeFactor u (Reconstruction.representative o)

cutoffOrbitAbsoluteCoefficient :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (R : Nat) →
  (law : PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  Reconstruction.UnorderedInputOrbit → Scalar.Scalar S
cutoffOrbitAbsoluteCoefficient {S = S} I R law u o =
  Scalar._*_ S (cutoffOrbitAmplitudeFactor u o)
    (Scalar.abs S (orbitInteraction law (Fourier.coefficient u) o))

cutoffOrbitNegativeCoefficient :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (R : Nat) →
  (law : PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  Reconstruction.UnorderedInputOrbit → Scalar.Scalar S
cutoffOrbitNegativeCoefficient {S = S} I R law u o =
  Scalar._*_ S (cutoffOrbitAmplitudeFactor u o)
    (Scalar.maxNegative S (orbitInteraction law (Fourier.coefficient u) o))

cutoffOrbitNegativeCoefficientNonnegative :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (R : Nat) →
  (law : PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (o : Reconstruction.UnorderedInputOrbit) →
  Scalar.Nonnegative S (cutoffOrbitNegativeCoefficient I R law u o)
cutoffOrbitNegativeCoefficientNonnegative {S = S} I R law u o =
  Scalar.multiplicationPreservesNonnegative S
    (Fourier.amplitudeFactorNonnegative u (Reconstruction.representative o))
    (Scalar.maxNegativeNonnegative S
      (orbitInteraction law (Fourier.coefficient u) o))

cutoffOrbitNegativeCoefficientLeAbsolute :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) →
  (R : Nat) →
  (law : PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (o : Reconstruction.UnorderedInputOrbit) →
  Scalar._≤_ S
    (cutoffOrbitNegativeCoefficient I R law u o)
    (cutoffOrbitAbsoluteCoefficient I R law u o)
cutoffOrbitNegativeCoefficientLeAbsolute {S = S} I R law u o =
  Scalar.multiplicationMonotoneNonnegativeRight S
    (Fourier.amplitudeFactorNonnegative u (Reconstruction.representative o))
    (Scalar.maxNegativeLeAbs S
      (orbitInteraction law (Fourier.coefficient u) o))
