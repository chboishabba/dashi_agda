module DASHI.Physics.Closure.NSTriadKNHardHighPhysicalZ3PairCompletenessRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 63 D/F CONTRIBUTION
--
-- `NSTriadKNHardHighPhysicalZ3PairEncodingExact` already maps each literal
-- physical triad p+q=k to the mature Z3 resonant-pair carrier storing exactly
-- (p,q).  Round63 upgrades the map to a complete finite enumeration theorem on
-- the actual hard-high list:
--
--   * every selected physical triad occurs in the encoded Z3 pair list;
--   * every encoded Z3 pair has a selected physical-triad preimage;
--   * the encoder is injective (resonance determines k from p,q);
--   * therefore the encoded list is duplicate-free whenever the physical list
--     is duplicate-free.
--
-- This closes the CONCRETE side of the requested
-- `officialPairEnumerationIsFourierComplete` bridge.  The only remaining D/F
-- enumeration equality is now the already-isolated official full-shell list
-- -> this concrete encoded list identification; no pair semantics are missing.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalHardHighTriadSelectionExact as High
import DASHI.Physics.Closure.NSZ3CutoffUniformIntegerShellSchur as Z3Shell
import DASHI.Physics.Closure.NSTriadKNHardHighPhysicalZ3PairEncodingExact as Encode

encodePhysicalPairInjective : Cube.Injective Encode.encodePhysicalPair
encodePhysicalPairInjective
  {Physical.physicalTriad p q k resonance}
  {Physical.physicalTriad p′ q′ k′ resonance′}
  equality
  with equality
... | refl
  with resonance | resonance′
... | refl | refl = refl

encodedMemberFromPhysicalMember :
  ∀ {triads triad} →
  triad Cube.∈ triads →
  Encode.encodePhysicalPair triad Cube.∈ Encode.mapPhysicalPairs triads
encodedMemberFromPhysicalMember (Cube.here equality) =
  Cube.here (cong Encode.encodePhysicalPair equality)
encodedMemberFromPhysicalMember (Cube.there member) =
  Cube.there (encodedMemberFromPhysicalMember member)

record EncodedPhysicalPreimage
    (pair : Z3Shell.Z3ResonantPair)
    (triads : List Physical.PhysicalTriadIncidence) : Set where
  constructor encoded-preimage
  field
    triad : Physical.PhysicalTriadIncidence
    triadMember : triad Cube.∈ triads
    encodedPairExact : Encode.encodePhysicalPair triad ≡ pair

open EncodedPhysicalPreimage public

encodedMemberHasPhysicalPreimage :
  ∀ {triads pair} →
  pair Cube.∈ Encode.mapPhysicalPairs triads →
  EncodedPhysicalPreimage pair triads
encodedMemberHasPhysicalPreimage {triads = []} ()
encodedMemberHasPhysicalPreimage {triads = head ∷ tail}
  (Cube.here equality) =
  encoded-preimage head (Cube.here refl) equality
encodedMemberHasPhysicalPreimage {triads = head ∷ tail}
  (Cube.there member)
  with encodedMemberHasPhysicalPreimage {triads = tail} member
... | encoded-preimage triad triadMember exact =
  encoded-preimage triad (Cube.there triadMember) exact

hardHighPhysicalMemberEncodes :
  ∀ {shell cubeCutoff triad} →
  triad Cube.∈ High.hardHighPhysicalTriads shell cubeCutoff →
  Encode.encodePhysicalPair triad
    Cube.∈ Encode.hardHighPhysicalZ3Pairs shell cubeCutoff
hardHighPhysicalMemberEncodes = encodedMemberFromPhysicalMember

hardHighEncodedMemberHasSelectedPhysicalPreimage :
  ∀ {shell cubeCutoff pair} →
  pair Cube.∈ Encode.hardHighPhysicalZ3Pairs shell cubeCutoff →
  EncodedPhysicalPreimage
    pair (High.hardHighPhysicalTriads shell cubeCutoff)
hardHighEncodedMemberHasSelectedPhysicalPreimage = encodedMemberHasPhysicalPreimage

encodedHardHighPairsNoDuplicates :
  (shell cubeCutoff : Nat) →
  Cube.NoDuplicates (Encode.hardHighPhysicalZ3Pairs shell cubeCutoff)
encodedHardHighPairsNoDuplicates shell cubeCutoff =
  Cube.mapNoDuplicates
    Encode.encodePhysicalPair
    encodePhysicalPairInjective
    (High.hardHighPhysicalTriadNoDuplicates shell cubeCutoff)

encodedPreimagePreservesLeftMode :
  ∀ {pair triads} →
  (preimage : EncodedPhysicalPreimage pair triads) →
  Physical.p (triad preimage) ≡ Z3Shell.left pair
encodedPreimagePreservesLeftMode
  (encoded-preimage triad member refl) = refl

encodedPreimagePreservesRightMode :
  ∀ {pair triads} →
  (preimage : EncodedPhysicalPreimage pair triads) →
  Physical.q (triad preimage) ≡ Z3Shell.right pair
encodedPreimagePreservesRightMode
  (encoded-preimage triad member refl) = refl

encodedPreimagePreservesResonance :
  ∀ {pair triads} →
  (preimage : EncodedPhysicalPreimage pair triads) →
  Z3Shell.Z3Resonant (Physical.k (triad preimage)) pair
encodedPreimagePreservesResonance
  (encoded-preimage triad member refl) =
  Encode.encodedPhysicalPairResonates triad

hardHighPhysicalZ3EnumerationComplete : Bool
hardHighPhysicalZ3EnumerationComplete = true

hardHighPhysicalZ3EnumerationDuplicateFree : Bool
hardHighPhysicalZ3EnumerationDuplicateFree = true

hardHighPhysicalZ3EnumerationCompleteIsTrue :
  hardHighPhysicalZ3EnumerationComplete ≡ true
hardHighPhysicalZ3EnumerationCompleteIsTrue = refl

hardHighPhysicalZ3EnumerationDuplicateFreeIsTrue :
  hardHighPhysicalZ3EnumerationDuplicateFree ≡ true
hardHighPhysicalZ3EnumerationDuplicateFreeIsTrue = refl
