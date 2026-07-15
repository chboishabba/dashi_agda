module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitPairIncidences where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNExactPairIncidenceGramAssembly as LegacyGram
import DASHI.Physics.Closure.NSTriadKNExactRetainedPairIncidences as Incidence
import DASHI.Physics.Closure.NSTriadKNFiniteConvolutionReconstruction as Reconstruction
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitInteraction as OrbitInteraction
import DASHI.Physics.Closure.NSTriadKNPhysicalFourierInteraction as Interaction

------------------------------------------------------------------------
-- The three-slot incidence carrier on canonical convolution orbits.
--
-- An orbit is the quotient of the two ordered input positions in the
-- Fourier convolution.  An incidence remains an occurrence: even when a
-- diagonal orbit has equal endpoints, its three PairSlot values are kept.
-- This is therefore a multigraph carrier, rather than a list of distinct
-- endpoint pairs.
------------------------------------------------------------------------

record OrbitPairIncidence : Set where
  constructor mkOrbitPairIncidence
  field
    orbit : Reconstruction.UnorderedInputOrbit
    slot  : Incidence.PairSlot

open OrbitPairIncidence public

orbitPairIncidencesFor : Reconstruction.UnorderedInputOrbit → List OrbitPairIncidence
orbitPairIncidencesFor o =
  mkOrbitPairIncidence o Incidence.firstPair ∷
  mkOrbitPairIncidence o Incidence.secondPair ∷
  mkOrbitPairIncidence o Incidence.thirdPair ∷ []

orbitPairIncidencesForHasThreeSlots :
  (o : Reconstruction.UnorderedInputOrbit) →
  orbitPairIncidencesFor o ≡
    mkOrbitPairIncidence o Incidence.firstPair ∷
    mkOrbitPairIncidence o Incidence.secondPair ∷
    mkOrbitPairIncidence o Incidence.thirdPair ∷ []
orbitPairIncidencesForHasThreeSlots o = refl

expandOrbitPairIncidences :
  List Reconstruction.UnorderedInputOrbit → List OrbitPairIncidence
expandOrbitPairIncidences [] = []
expandOrbitPairIncidences (o ∷ os) =
  orbitPairIncidencesFor o ++ expandOrbitPairIncidences os

physicalCutoffOrbitPairIncidences : Nat → Nat → List OrbitPairIncidence
physicalCutoffOrbitPairIncidences N R =
  expandOrbitPairIncidences (Reconstruction.canonicalUnorderedInputOrbits N R)

-- Erasure deliberately lands in the old labelled-triad occurrence carrier.
-- This is the compatibility map; the orbit carrier above is authoritative
-- for the physical Fourier route because it has already quotiented swaps.
eraseOrbitPairIncidence : OrbitPairIncidence → Incidence.PairIncidence
eraseOrbitPairIncidence (mkOrbitPairIncidence o s) =
  Incidence.mkPairIncidence (Reconstruction.representative o) s

orbitIncidenceSource : OrbitPairIncidence → Lattice.LatticeMode3
orbitIncidenceSource r = Incidence.sourceMode (eraseOrbitPairIncidence r)

orbitIncidenceTarget : OrbitPairIncidence → Lattice.LatticeMode3
orbitIncidenceTarget r = Incidence.targetMode (eraseOrbitPairIncidence r)

orbitIncidenceRemaining : OrbitPairIncidence → Lattice.LatticeMode3
orbitIncidenceRemaining r = Incidence.remainingMode (eraseOrbitPairIncidence r)

orbitRepresentativeIncidenceAgreement :
  (o : Reconstruction.UnorderedInputOrbit) → (s : Incidence.PairSlot) →
  eraseOrbitPairIncidence (mkOrbitPairIncidence o s) ≡
    Incidence.mkPairIncidence (Reconstruction.representative o) s
orbitRepresentativeIncidenceAgreement o s = refl

orbitRepresentativeFoldAgreement :
  (o : Reconstruction.UnorderedInputOrbit) →
  map eraseOrbitPairIncidence (orbitPairIncidencesFor o) ≡
    Incidence.pairIncidencesFor (Reconstruction.representative o)
orbitRepresentativeFoldAgreement o = refl

------------------------------------------------------------------------
-- Diagonal multigraph degeneracy.
--
-- The first occurrence is the zero edge; the second and third occurrences
-- have the same endpoints.  They remain separate occurrences so that the
-- Python-derived three-slot convention is preserved exactly.
------------------------------------------------------------------------

diagonalFirstSlotEndpointsAgree :
  (o : Reconstruction.UnorderedInputOrbit) →
  Reconstruction.orbitKind o ≡ Reconstruction.diagonal →
  orbitIncidenceSource (mkOrbitPairIncidence o Incidence.firstPair) ≡
  orbitIncidenceTarget (mkOrbitPairIncidence o Incidence.firstPair)
diagonalFirstSlotEndpointsAgree o diagonal =
  Reconstruction.swapOrbitKindDiagonalImpliesInputsEqual
    (Reconstruction.representative o) diagonal

diagonalRemainingSlotEndpointsAgree :
  (o : Reconstruction.UnorderedInputOrbit) →
  Reconstruction.orbitKind o ≡ Reconstruction.diagonal →
  (orbitIncidenceSource (mkOrbitPairIncidence o Incidence.secondPair) ≡
   orbitIncidenceSource (mkOrbitPairIncidence o Incidence.thirdPair)) ×
  (orbitIncidenceTarget (mkOrbitPairIncidence o Incidence.secondPair) ≡
   orbitIncidenceTarget (mkOrbitPairIncidence o Incidence.thirdPair))
diagonalRemainingSlotEndpointsAgree o diagonal =
  Reconstruction.swapOrbitKindDiagonalImpliesInputsEqual
    (Reconstruction.representative o) diagonal , refl

------------------------------------------------------------------------
-- Canonical orbit-derived weights.  `cutoffOrbitAmplitudeFactor` already
-- carries the 1/3 allocation, so each of the three occurrences below gets
-- exactly the established per-slot coefficient.
------------------------------------------------------------------------

orbitIncidenceMAbs :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) → (R : Nat) →
  (law : OrbitInteraction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  OrbitPairIncidence → Scalar.Scalar S
orbitIncidenceMAbs I R law u r =
  OrbitInteraction.cutoffOrbitAbsoluteCoefficient I R law u (orbit r)

orbitIncidenceMNeg :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) → (R : Nat) →
  (law : OrbitInteraction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  OrbitPairIncidence → Scalar.Scalar S
orbitIncidenceMNeg I R law u r =
  OrbitInteraction.cutoffOrbitNegativeCoefficient I R law u (orbit r)

orbitIncidenceMNegNonnegative :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) → (R : Nat) →
  (law : OrbitInteraction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (r : OrbitPairIncidence) → Scalar.Nonnegative S (orbitIncidenceMNeg I R law u r)
orbitIncidenceMNegNonnegative I R law u r =
  OrbitInteraction.cutoffOrbitNegativeCoefficientNonnegative I R law u (orbit r)

orbitIncidenceMAbsNonnegative :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) → (R : Nat) →
  (law : OrbitInteraction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (r : OrbitPairIncidence) → Scalar.Nonnegative S (orbitIncidenceMAbs I R law u r)
orbitIncidenceMAbsNonnegative I R law u r =
  OrbitInteraction.cutoffOrbitAbsoluteCoefficientNonnegative I R law u (orbit r)

orbitIncidenceMNegLeMAbs :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) → (R : Nat) →
  (law : OrbitInteraction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (r : OrbitPairIncidence) →
  Scalar._≤_ S (orbitIncidenceMNeg I R law u r) (orbitIncidenceMAbs I R law u r)
orbitIncidenceMNegLeMAbs I R law u r =
  OrbitInteraction.cutoffOrbitNegativeCoefficientLeAbsolute I R law u (orbit r)

-- The old labelled-triad weights agree exactly when its legacy coherence is
-- identified with the canonical orbit interaction at the representative.
-- This hypothesis is explicit: the old data record has not been silently
-- promoted into the authoritative Fourier lane.
orbitRepresentativeAbsoluteWeightAgreement :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) → (R : Nat) →
  (law : OrbitInteraction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (o : Reconstruction.UnorderedInputOrbit) → (s : Incidence.PairSlot) →
  Fourier.coherence u (Reconstruction.representative o) ≡
    OrbitInteraction.orbitInteraction law (Fourier.coefficient u) o →
  orbitIncidenceMAbs I R law u (mkOrbitPairIncidence o s) ≡
    LegacyGram.pairIncidenceAbsoluteCoefficient u
      (Incidence.mkPairIncidence (Reconstruction.representative o) s)
orbitRepresentativeAbsoluteWeightAgreement I R law u o s coherence≡
  rewrite coherence≡ = refl

orbitRepresentativeNegativeWeightAgreement :
  {S : Scalar.ExactOrderedScalar} → {C : Fourier.ComplexFourierInterface S} →
  {N : Nat} → {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (I : Interaction.ExactNSFourierInteractionStructure S C) → (R : Nat) →
  (law : OrbitInteraction.PhysicalCutoffOrbitInteractionLaw I N R) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (o : Reconstruction.UnorderedInputOrbit) → (s : Incidence.PairSlot) →
  Fourier.coherence u (Reconstruction.representative o) ≡
    OrbitInteraction.orbitInteraction law (Fourier.coefficient u) o →
  orbitIncidenceMNeg I R law u (mkOrbitPairIncidence o s) ≡
    LegacyGram.pairIncidenceNegativeCoefficient u
      (Incidence.mkPairIncidence (Reconstruction.representative o) s)
orbitRepresentativeNegativeWeightAgreement I R law u o s coherence≡
  rewrite coherence≡ = refl
