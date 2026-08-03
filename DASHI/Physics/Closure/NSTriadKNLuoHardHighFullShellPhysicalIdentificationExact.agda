module DASHI.Physics.Closure.NSTriadKNLuoHardHighFullShellPhysicalIdentificationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal/year: Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- PURPOSE
-- Isolate the one repository-specific representation theorem between the
-- literal hard-high physical triad list and the mature compact-Gamma/full-shell
-- Schur owner.  Once one proof-relevant encoding identifies those lists, the
-- existing analytic leaf supplies signed-coefficient domination and the
-- existing triad/full-shell coherence supplies equality with the exact pair
-- fold.  No second Schur theorem is introduced.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalHardHighTriadSelectionExact as High
import DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram as Closure
import DASHI.Physics.Closure.NSCompactGammaDifferentiatedTriadInstantiation as Triads
import DASHI.Physics.Closure.NSCompactGammaTriadFullShellCoherence as Coherence
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

record HardHighPhysicalFullShellIdentification
    (program : Closure.CompactGammaAnalyticClosure)
    (K N shell cubeCutoff : Nat) : Setω where
  field
    encodePhysical :
      Physical.PhysicalTriadIncidence → Closure.Pair program

    decodePair :
      Closure.Pair program → Physical.PhysicalTriadIncidence

    encodeDecode :
      (pair : Closure.Pair program) →
      encodePhysical (decodePair pair) ≡ pair

    decodeEncode :
      (triad : Physical.PhysicalTriadIncidence) →
      decodePair (encodePhysical triad) ≡ triad

    selectedPhysicalListIsPairAtoms :
      mapList encodePhysical
        (High.hardHighPhysicalTriads shell cubeCutoff)
      ≡
      Triads.pairAtoms (Closure.differentiatedTriadsAt program K N)

    physicalSignedMagnitude :
      Physical.PhysicalTriadIncidence →
      Scalar (Closure.arithmetic program)

    physicalIncidenceMajorant :
      Physical.PhysicalTriadIncidence →
      Scalar (Closure.arithmetic program)

    physicalSignedMagnitudeAgreement :
      (triad : Physical.PhysicalTriadIncidence) →
      physicalSignedMagnitude triad ≡
      Triads.signedTriadMagnitude
        (Closure.differentiatedTriadsAt program K N)
        (encodePhysical triad)

    physicalIncidenceMajorantAgreement :
      (triad : Physical.PhysicalTriadIncidence) →
      physicalIncidenceMajorant triad ≡
      Triads.triadMajorant
        (Closure.differentiatedTriadsAt program K N)
        (encodePhysical triad)

open HardHighPhysicalFullShellIdentification public

selectedPhysicalListIsFullShellPairList :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N shell cubeCutoff : Nat) →
  (I : HardHighPhysicalFullShellIdentification
    program K N shell cubeCutoff) →
  mapList (encodePhysical I)
    (High.hardHighPhysicalTriads shell cubeCutoff)
  ≡
  PairKernel.pairs
    (FullShell.pairDataAt (Closure.fullShellFamily program) K N)
selectedPhysicalListIsFullShellPairList program K N shell cubeCutoff I =
  trans
    (selectedPhysicalListIsPairAtoms I)
    (Coherence.pairListsMatch
      (Closure.triadFullShellCoherence program) K N)

physicalSignedCoefficientDominated :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N shell cubeCutoff : Nat) →
  (I : HardHighPhysicalFullShellIdentification
    program K N shell cubeCutoff) →
  (triad : Physical.PhysicalTriadIncidence) →
  _≤_ (Closure.arithmetic program)
    (physicalSignedMagnitude I triad)
    (physicalIncidenceMajorant I triad)
physicalSignedCoefficientDominated program K N shell cubeCutoff I triad =
  subst
    (λ left →
      _≤_ (Closure.arithmetic program)
        left (physicalIncidenceMajorant I triad))
    (sym (physicalSignedMagnitudeAgreement I triad))
    (subst
      (λ right →
        _≤_ (Closure.arithmetic program)
          (Triads.signedTriadMagnitude
            (Closure.differentiatedTriadsAt program K N)
            (encodePhysical I triad))
          right)
      (sym (physicalIncidenceMajorantAgreement I triad))
      (Coherence.coherentLocalMajorization
        (Closure.triadFullShellCoherence program)
        K N (encodePhysical I triad)))

hardHighPhysicalFullShellRepresentationTheoremConstructed : Bool
hardHighPhysicalFullShellRepresentationTheoremConstructed = true

physicalSignedCoefficientDominationTheoremConstructed : Bool
physicalSignedCoefficientDominationTheoremConstructed = true

canonicalHardHighPhysicalFullShellIdentificationInhabited : Bool
canonicalHardHighPhysicalFullShellIdentificationInhabited = false

hardHighPhysicalFullShellRepresentationTheoremConstructedIsTrue :
  hardHighPhysicalFullShellRepresentationTheoremConstructed ≡ true
hardHighPhysicalFullShellRepresentationTheoremConstructedIsTrue = refl

physicalSignedCoefficientDominationTheoremConstructedIsTrue :
  physicalSignedCoefficientDominationTheoremConstructed ≡ true
physicalSignedCoefficientDominationTheoremConstructedIsTrue = refl

canonicalHardHighPhysicalFullShellIdentificationInhabitedIsFalse :
  canonicalHardHighPhysicalFullShellIdentificationInhabited ≡ false
canonicalHardHighPhysicalFullShellIdentificationInhabitedIsFalse = refl
