module DASHI.Physics.Closure.NSTriadKNHardHighPhysicalZ3PairEncodingExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean Leray; Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin;
-- DASHI repository contributors.
-- Titles: "Sur le mouvement d'un liquide visqueux emplissant l'espace";
-- "Fourier Analysis and Nonlinear Partial Differential Equations";
-- exact Z3 hard-high/full-shell reindexing in the DASHI formal development.
-- DOI: 10.1007/BF02547354; 10.1007/978-3-642-16830-7.
-- The finite reindexing theorem itself is repository-original and has no DOI.
--
-- PURPOSE
-- Identify the primitive physical triad incidence
--
--   p + q = k
--
-- with the concrete Z3 resonant-pair carrier used by the mature SC1--SC9
-- full-shell programme.  The pair stores p and q; its target resonance is
-- exactly the physical triad's resonance proof.  No phase, polarization or
-- coefficient data are discarded by this combinatorial reindexing because
-- those belong to the separate atom/majorant layer.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalHardHighTriadSelectionExact as High
import DASHI.Physics.Closure.NSZ3CutoffUniformIntegerShellSchur as Z3Shell
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel

encodePhysicalPair :
  Physical.PhysicalTriadIncidence → Z3Shell.Z3ResonantPair
encodePhysicalPair triad =
  Z3Shell.pair (Physical.p triad) (Physical.q triad)

encodedPhysicalPairResonates :
  (triad : Physical.PhysicalTriadIncidence) →
  Z3Shell.Z3Resonant
    (Physical.k triad)
    (encodePhysicalPair triad)
encodedPhysicalPairResonates triad = Physical.resonance triad

decodeResonantPair :
  (target : Z3.FourierMode) →
  (pair : Z3Shell.Z3ResonantPair) →
  Z3Shell.Z3Resonant target pair →
  Physical.PhysicalTriadIncidence
decodeResonantPair target pair resonance =
  Physical.physicalTriad
    (Z3Shell.left pair)
    (Z3Shell.right pair)
    target resonance

decodeEncodedPhysicalPair :
  (triad : Physical.PhysicalTriadIncidence) →
  decodeResonantPair
    (Physical.k triad)
    (encodePhysicalPair triad)
    (encodedPhysicalPairResonates triad)
  ≡ triad
decodeEncodedPhysicalPair
  (Physical.physicalTriad p q k resonance) = refl

encodeDecodedResonantPair :
  (target : Z3.FourierMode) →
  (pair : Z3Shell.Z3ResonantPair) →
  (resonance : Z3Shell.Z3Resonant target pair) →
  encodePhysicalPair (decodeResonantPair target pair resonance) ≡ pair
encodeDecodedResonantPair target (Z3Shell.pair left right) resonance = refl

mapPhysicalPairs :
  List Physical.PhysicalTriadIncidence →
  List Z3Shell.Z3ResonantPair
mapPhysicalPairs [] = []
mapPhysicalPairs (triad ∷ triads) =
  encodePhysicalPair triad ∷ mapPhysicalPairs triads

hardHighPhysicalZ3Pairs :
  Nat → Nat → List Z3Shell.Z3ResonantPair
hardHighPhysicalZ3Pairs shell cubeCutoff =
  mapPhysicalPairs (High.hardHighPhysicalTriads shell cubeCutoff)

encodedHardHighMemberResonates :
  ∀ {shell cubeCutoff triad} →
  Cube._∈_ triad (High.hardHighPhysicalTriads shell cubeCutoff) →
  Z3Shell.Z3Resonant
    (Physical.k triad)
    (encodePhysicalPair triad)
encodedHardHighMemberResonates {triad = triad} member =
  encodedPhysicalPairResonates triad

record HardHighPhysicalZ3FullShellPairIdentification
    {s i : Level}
    {Scalar : Set s}
    (family :
      FullShell.FullShellFourierFamily
        {i = i} Z3Shell.Z3ResonantPair Z3.FourierMode Scalar)
    (K N shell cubeCutoff : Nat) : Set (lsuc (s ⊔ i)) where
  field
    fullShellPairListIsEncodedHardHighList :
      PairKernel.pairs (FullShell.pairDataAt family K N)
        ≡ hardHighPhysicalZ3Pairs shell cubeCutoff

open HardHighPhysicalZ3FullShellPairIdentification public

encodedHardHighListIsFullShellPairList :
  ∀ {s i}
    {Scalar : Set s}
    {family :
      FullShell.FullShellFourierFamily
        {i = i} Z3Shell.Z3ResonantPair Z3.FourierMode Scalar}
    {K N shell cubeCutoff} →
  HardHighPhysicalZ3FullShellPairIdentification
    family K N shell cubeCutoff →
  hardHighPhysicalZ3Pairs shell cubeCutoff
    ≡ PairKernel.pairs (FullShell.pairDataAt family K N)
encodedHardHighListIsFullShellPairList identification =
  sym (fullShellPairListIsEncodedHardHighList identification)

hardHighPhysicalToZ3PairEncodingClosed : Bool
hardHighPhysicalToZ3PairEncodingClosed = true

hardHighPhysicalResonanceTransportClosed : Bool
hardHighPhysicalResonanceTransportClosed = true

hardHighFullShellPairListIdentificationSurfaceConstructed : Bool
hardHighFullShellPairListIdentificationSurfaceConstructed = true

hardHighPhysicalToZ3PairEncodingClosedIsTrue :
  hardHighPhysicalToZ3PairEncodingClosed ≡ true
hardHighPhysicalToZ3PairEncodingClosedIsTrue = refl

hardHighPhysicalResonanceTransportClosedIsTrue :
  hardHighPhysicalResonanceTransportClosed ≡ true
hardHighPhysicalResonanceTransportClosedIsTrue = refl

hardHighFullShellPairListIdentificationSurfaceConstructedIsTrue :
  hardHighFullShellPairListIdentificationSurfaceConstructed ≡ true
hardHighFullShellPairListIdentificationSurfaceConstructedIsTrue = refl
