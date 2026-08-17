module DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsFineFiveSourceAtomsRound72Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND72 / COMPLETE STATIC FIVE-SOURCE REFINEMENT
--
-- Round72 already refines every classified triadic incidence into one exact
-- Round62 `physicalAtom`, modulo the genuine per-incidence HH-good/HH-bad
-- selection.  Append the differentiated Com cell as the final physical atom.
--
-- The resulting list is still the exact Round62 LocalizedPDEAtom language.
-- Flattening it to SignedConstituent and taking the repository's official signed
-- total reconstructs the exact Round25 five-source total:
--
--   signedConstituentTotal (flattenAtoms fineFiveSourceAtoms)
--     = fiveSourceTotal cutoff output triadValue commutatorValue.
--
-- This closes the STATIC five-source refinement seam.  A selected trajectory
-- still has to instantiate the DynamicPhysicalShellBalance and add the literal
-- boundary/kernel/tail atoms produced by localization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (_+_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSumRound25Exact as Five
import DASHI.Physics.Closure.NSTriadKNSignedConstituentTreeRound28Exact as Signed
import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEConstituentPartitionRound62Exact as Partition
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsStructuredTriadicAtomsRound72Exact as Fine

fineFiveSourceAtomsFromClassified :
  (pairing : Shell.StaticPhysicalShellPairing) →
  (hh : Fine.HHOwnerSelection) →
  List Support.ClassifiedPhysicalTriad →
  List Structured.LocalizedPDEAtom
fineFiveSourceAtomsFromClassified pairing hh [] =
  Fine.comStructuredAtom pairing ∷ []
fineFiveSourceAtomsFromClassified pairing hh (classified ∷ rest) =
  Structured.physicalAtom
    (Support.triadicSource classified)
    (Fine.canonicalOwnerForClassified hh classified)
    (Fine.canonicalOwnerCompatible hh classified)
    (Shell.triadValue pairing (Support.incidence classified))
  ∷ fineFiveSourceAtomsFromClassified pairing hh rest

fineFiveSourceAtoms :
  (pairing : Shell.StaticPhysicalShellPairing) →
  Fine.HHOwnerSelection →
  List Structured.LocalizedPDEAtom
fineFiveSourceAtoms pairing hh =
  fineFiveSourceAtomsFromClassified pairing hh
    (Support.classifiedPhysicalOutputFiber
      (Shell.cutoff pairing) (Shell.output pairing))

flattenedFineFiveSourceTotalFromClassified :
  (pairing : Shell.StaticPhysicalShellPairing) →
  (hh : Fine.HHOwnerSelection) →
  (classified : List Support.ClassifiedPhysicalTriad) →
  Signed.signedConstituentTotal
    (Structured.flattenAtoms
      (fineFiveSourceAtomsFromClassified pairing hh classified))
  ≡ Fine.classifiedTriadValueSum pairing classified
      + Shell.commutatorValue pairing (Shell.output pairing)
flattenedFineFiveSourceTotalFromClassified pairing hh [] =
  ℚP.+-identityʳ (Shell.commutatorValue pairing (Shell.output pairing))
flattenedFineFiveSourceTotalFromClassified pairing hh (classified ∷ rest) =
  trans
    (cong
      (Shell.triadValue pairing (Support.incidence classified) +_)
      (flattenedFineFiveSourceTotalFromClassified pairing hh rest))
    (sym
      (ℚP.+-assoc
        (Shell.triadValue pairing (Support.incidence classified))
        (Fine.classifiedTriadValueSum pairing rest)
        (Shell.commutatorValue pairing (Shell.output pairing))))

flattenedFineFiveSourceTotalExact :
  (pairing : Shell.StaticPhysicalShellPairing) →
  (hh : Fine.HHOwnerSelection) →
  Signed.signedConstituentTotal
    (Structured.flattenAtoms (fineFiveSourceAtoms pairing hh))
  ≡ Five.fiveSourceTotal
      (Shell.cutoff pairing)
      (Shell.output pairing)
      (Shell.triadValue pairing)
      (Shell.commutatorValue pairing)
flattenedFineFiveSourceTotalExact pairing hh =
  let
    classified = Support.classifiedPhysicalOutputFiber
      (Shell.cutoff pairing) (Shell.output pairing)
  in
  trans
    (flattenedFineFiveSourceTotalFromClassified pairing hh classified)
    (trans
      (cong
        (λ triadTotal →
          triadTotal + Shell.commutatorValue pairing (Shell.output pairing))
        (trans
          (Fine.classifiedTriadValueSumErasesExact pairing classified)
          (cong
            (Five.triadValueSum (Shell.triadValue pairing))
            (Support.classifiedPhysicalOutputFiberErasesExactly
              (Shell.cutoff pairing) (Shell.output pairing)))))
      (sym
        (Five.fiveSourceTotalExpands
          (Shell.cutoff pairing)
          (Shell.output pairing)
          (Shell.triadValue pairing)
          (Shell.commutatorValue pairing))))

staticPairingAsOneLocalizedPDEConstituentSource :
  (pairing : Shell.StaticPhysicalShellPairing) →
  (hh : Fine.HHOwnerSelection) →
  Partition.OneLocalizedPDEConstituentSource
staticPairingAsOneLocalizedPDEConstituentSource pairing hh = record
  { Partition.OneLocalizedPDEConstituentSource.constituents =
      Structured.flattenAtoms (fineFiveSourceAtoms pairing hh)
  ; Partition.OneLocalizedPDEConstituentSource.localizedNonlinearValue =
      Five.fiveSourceTotal
        (Shell.cutoff pairing) (Shell.output pairing)
        (Shell.triadValue pairing) (Shell.commutatorValue pairing)
  ; Partition.OneLocalizedPDEConstituentSource.literalConstituentExpansion =
      sym (flattenedFineFiveSourceTotalExact pairing hh)
  }

round72StaticFiveSourceRefinesToOneStructuredConstituentList : Bool
round72StaticFiveSourceRefinesToOneStructuredConstituentList = true

round72StaticFiveSourceRefinesToOneStructuredConstituentListIsTrue :
  round72StaticFiveSourceRefinesToOneStructuredConstituentList ≡ true
round72StaticFiveSourceRefinesToOneStructuredConstituentListIsTrue = refl
