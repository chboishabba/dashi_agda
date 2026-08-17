module DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsStructuredTriadicAtomsRound72Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND72 / STATIC PAIRING -> FINE STRUCTURED TRIADIC ATOMS
--
-- `StaticPhysicalShellPairing` still carries the literal per-incidence
--
--     triadValue : PhysicalTriadIncidence -> Q.
--
-- Round25 classifies the exact physical output fibre without changing those
-- values.  Round62's `LocalizedPDEAtom` is therefore emitted here BEFORE the
-- classwise sums collapse to seven aggregate rationals.
--
-- LH, HL and CC have canonical owners.  HH is deliberately different: the
-- signed constituent language permits exactly HH-good or HH-bad, but the repo
-- does not currently construct a per-incidence good/bad decision.  We expose
-- that one genuine authority as `HHOwnerSelection`; no HH atom is duplicated or
-- arbitrarily assigned.
--
-- The main exact theorem is
--
--   triadicSignedSum(structuredTriadicAtoms pairing hhSelection)
--     = physicalOutputInteractionSum cutoff output triadValue.
--
-- Thus the STATIC fine-source half of the localized trajectory theorem is now
-- constructed modulo only the explicit HH ownership decision.  Time dependence,
-- chain rule, diffusion and boundary/kernel production remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSumRound25Exact as Five
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNSignedConstituentTreeRound28Exact as Signed
import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as Concentration

record HHOwnerSelection : Set where
  field
    selectedHHOwner : Support.ClassifiedPhysicalTriad → Tax.TaxOwner
    selectedHHCompatible :
      ∀ classified →
      Support.sourceClass classified ≡ Support.HH →
      Signed.CompatibleOwner
        (Signed.physicalSource (Support.triadicSource classified))
        (selectedHHOwner classified)

open HHOwnerSelection public

canonicalOwnerForClassified :
  HHOwnerSelection →
  (classified : Support.ClassifiedPhysicalTriad) → Tax.TaxOwner
canonicalOwnerForClassified hh classified
  with Support.sourceClass classified
... | Support.LH = Tax.LH
... | Support.HL = Tax.HL
... | Support.HH = selectedHHOwner hh classified
... | Support.CC = Tax.CC

canonicalOwnerCompatible :
  (hh : HHOwnerSelection) →
  (classified : Support.ClassifiedPhysicalTriad) →
  Signed.CompatibleOwner
    (Signed.physicalSource (Support.triadicSource classified))
    (canonicalOwnerForClassified hh classified)
canonicalOwnerCompatible hh classified
  with Support.sourceClass classified in classProof
... | Support.LH =
  Signed.lhCompatibilityCanonical
    (Support.triadicSource classified)
    (cong Support.triadicToFiveClass classProof)
... | Support.HL =
  Signed.hlCompatibilityCanonical
    (Support.triadicSource classified)
    (cong Support.triadicToFiveClass classProof)
... | Support.HH =
  selectedHHCompatible hh classified classProof
... | Support.CC =
  Signed.ccCompatibilityCanonical
    (Support.triadicSource classified)
    (cong Support.triadicToFiveClass classProof)

structuredTriadicAtomsFromClassified :
  (pairing : Shell.StaticPhysicalShellPairing) →
  HHOwnerSelection →
  List Support.ClassifiedPhysicalTriad →
  List Structured.LocalizedPDEAtom
structuredTriadicAtomsFromClassified pairing hh [] = []
structuredTriadicAtomsFromClassified pairing hh (classified ∷ rest) =
  Structured.physicalAtom
    (Support.triadicSource classified)
    (canonicalOwnerForClassified hh classified)
    (canonicalOwnerCompatible hh classified)
    (Shell.triadValue pairing (Support.incidence classified))
  ∷ structuredTriadicAtomsFromClassified pairing hh rest

structuredTriadicAtoms :
  (pairing : Shell.StaticPhysicalShellPairing) →
  HHOwnerSelection →
  List Structured.LocalizedPDEAtom
structuredTriadicAtoms pairing hh =
  structuredTriadicAtomsFromClassified pairing hh
    (Support.classifiedPhysicalOutputFiber
      (Shell.cutoff pairing) (Shell.output pairing))

classifiedTriadValueSum :
  (pairing : Shell.StaticPhysicalShellPairing) →
  List Support.ClassifiedPhysicalTriad → ℚ
classifiedTriadValueSum pairing [] = 0ℚ
classifiedTriadValueSum pairing (classified ∷ rest) =
  Shell.triadValue pairing (Support.incidence classified)
  + classifiedTriadValueSum pairing rest

structuredTriadicSignedSumClassifiedExact :
  (pairing : Shell.StaticPhysicalShellPairing) →
  (hh : HHOwnerSelection) →
  (classified : List Support.ClassifiedPhysicalTriad) →
  Concentration.triadicSignedSum
    (structuredTriadicAtomsFromClassified pairing hh classified)
  ≡ classifiedTriadValueSum pairing classified
structuredTriadicSignedSumClassifiedExact pairing hh [] = refl
structuredTriadicSignedSumClassifiedExact pairing hh (classified ∷ rest)
  rewrite structuredTriadicSignedSumClassifiedExact pairing hh rest = refl

classifiedTriadValueSumErasesExact :
  (pairing : Shell.StaticPhysicalShellPairing) →
  (classified : List Support.ClassifiedPhysicalTriad) →
  classifiedTriadValueSum pairing classified
  ≡ Five.triadValueSum (Shell.triadValue pairing)
      (Support.eraseClassifiedPhysicalTriads classified)
classifiedTriadValueSumErasesExact pairing [] = refl
classifiedTriadValueSumErasesExact pairing (classified ∷ rest)
  rewrite classifiedTriadValueSumErasesExact pairing rest = refl

structuredTriadicSignedSumExact :
  (pairing : Shell.StaticPhysicalShellPairing) →
  (hh : HHOwnerSelection) →
  Concentration.triadicSignedSum (structuredTriadicAtoms pairing hh)
  ≡ Five.physicalOutputInteractionSum
      (Shell.cutoff pairing) (Shell.output pairing) (Shell.triadValue pairing)
structuredTriadicSignedSumExact pairing hh =
  trans
    (structuredTriadicSignedSumClassifiedExact pairing hh
      (Support.classifiedPhysicalOutputFiber
        (Shell.cutoff pairing) (Shell.output pairing)))
    (trans
      (classifiedTriadValueSumErasesExact pairing
        (Support.classifiedPhysicalOutputFiber
          (Shell.cutoff pairing) (Shell.output pairing)))
      (cong
        (Five.triadValueSum (Shell.triadValue pairing))
        (Support.classifiedPhysicalOutputFiberErasesExactly
          (Shell.cutoff pairing) (Shell.output pairing))))

comStructuredAtom :
  (pairing : Shell.StaticPhysicalShellPairing) →
  Structured.LocalizedPDEAtom
comStructuredAtom pairing =
  Structured.physicalAtom
    (Support.differentiatedCommutator (Shell.output pairing))
    Tax.Com
    (Signed.comCompatibilityCanonical
      (Support.differentiatedCommutator (Shell.output pairing)) refl)
    (Shell.commutatorValue pairing (Shell.output pairing))

round72StaticFineTriadicAtomsConstructedModuloHHSelection : Bool
round72StaticFineTriadicAtomsConstructedModuloHHSelection = true

round72StaticFineTriadicSignedSumExact : Bool
round72StaticFineTriadicSignedSumExact = true

round72StaticComAtomConstructed : Bool
round72StaticComAtomConstructed = true

round72PerIncidenceHHGoodBadSelectionConstructed : Bool
round72PerIncidenceHHGoodBadSelectionConstructed = false

round72TimeDependentStructuredAtomIdentityConstructed : Bool
round72TimeDependentStructuredAtomIdentityConstructed = false

round72StaticFineTriadicSignedSumExactIsTrue :
  round72StaticFineTriadicSignedSumExact ≡ true
round72StaticFineTriadicSignedSumExactIsTrue = refl

round72PerIncidenceHHGoodBadSelectionConstructedIsFalse :
  round72PerIncidenceHHGoodBadSelectionConstructed ≡ false
round72PerIncidenceHHGoodBadSelectionConstructedIsFalse = refl
