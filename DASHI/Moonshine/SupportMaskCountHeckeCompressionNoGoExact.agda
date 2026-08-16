module DASHI.Moonshine.SupportMaskCountHeckeCompressionNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- David Blackwell,
-- "Equivalent Comparisons of Experiments",
-- Annals of Mathematical Statistics 24(2):265-272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- Saunders Mac Lane,
-- "Categories for the Working Mathematician", second edition,
-- Graduate Texts in Mathematics 5, Springer, 1998.
-- DOI: 10.1007/978-1-4757-4721-8.
--
-- DASHI CONTRIBUTION
--
-- Give an exact operator-relevant compression falsifier on the repository's
-- concrete support-mask Hecke correspondence.
--
-- Compress a support mask to the number of marked SSP coordinates.  The masks
--
--   {p2} and {p3}
--
-- both have support count one, but under the p2 correspondence their projected
-- count-valued 15-way fibres differ.  Hence support count is not sufficient to
-- define the quotient correspondence: equal coarse observations can still be
-- separated by the admitted Hecke operation.
--
-- This is a finite DASHI theorem.  Blackwell supplies sufficiency/comparison
-- vocabulary only; no statistical interpretation is imported.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import MonsterOntos using (p2; p3)

import Ontology.Hecke.CorrespondenceRepresentation as Hecke
import Ontology.Hecke.FactorVecCorrespondence as MaskHecke
import Ontology.Hecke.FactorVecInstances as Factor

bitNat : Bool → Nat
bitNat false = 0
bitNat true = 1

supportCount : Factor.SupportMask → Nat
supportCount
  (mkVec15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71) =
  bitNat b2 + bitNat b3 + bitNat b5 + bitNat b7 + bitNat b11
  + bitNat b13 + bitNat b17 + bitNat b19 + bitNat b23 + bitNat b29
  + bitNat b31 + bitNat b41 + bitNat b47 + bitNat b59 + bitNat b71

p2Only p3Only : Factor.SupportMask
p2Only =
  mkVec15 true false false false false false false false false false
    false false false false false
p3Only =
  mkVec15 false true false false false false false false false false
    false false false false false

p2OnlyCountIsOne : supportCount p2Only ≡ 1
p2OnlyCountIsOne = refl

p3OnlyCountIsOne : supportCount p3Only ≡ 1
p3OnlyCountIsOne = refl

sameSupportCount : supportCount p2Only ≡ supportCount p3Only
sameSupportCount = refl

projectedCountCorrespondence :
  Factor.SupportMask → Vec15 Nat
projectedCountCorrespondence mask =
  Hecke.map15 supportCount
    (MaskHecke.supportMaskCorrespondence p2 mask)

first15 : ∀ {A : Set} → Vec15 A → A
first15
  (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  a2

p2OnlyFirstProjectedCountIsOne :
  first15 (projectedCountCorrespondence p2Only) ≡ 1
p2OnlyFirstProjectedCountIsOne = refl

p3OnlyFirstProjectedCountIsTwo :
  first15 (projectedCountCorrespondence p3Only) ≡ 2
p3OnlyFirstProjectedCountIsTwo = refl

oneNotTwo : 1 ≡ 2 → ⊥
oneNotTwo ()

projectedCountCorrespondencesDiffer :
  projectedCountCorrespondence p2Only
  ≡ projectedCountCorrespondence p3Only →
  ⊥
projectedCountCorrespondencesDiffer equality =
  oneNotTwo (cong first15 equality)

------------------------------------------------------------------------
-- Therefore the support-count projection fails exactly the congruence premise
-- required by HeckeCorrespondenceQuotientDescentExact.
------------------------------------------------------------------------

supportCountNotHeckeCongruent :
  Σ Factor.SupportMask (λ left →
  Σ Factor.SupportMask (λ right →
    (supportCount left ≡ supportCount right)
    ×
    (Hecke.map15 supportCount
      (MaskHecke.supportMaskCorrespondence p2 left)
      ≡
     Hecke.map15 supportCount
      (MaskHecke.supportMaskCorrespondence p2 right) → ⊥)))
supportCountNotHeckeCongruent =
  p2Only , (p3Only , (sameSupportCount , projectedCountCorrespondencesDiffer))

record SupportCountCompressionBoundary : Set where
  field
    equalSupportCountCanHideHeckeRelevantDifference : Bool
    equalSupportCountCanHideHeckeRelevantDifferenceIsTrue :
      equalSupportCountCanHideHeckeRelevantDifference ≡ true

    supportCountAloneDefinesHeckeQuotient : Bool
    supportCountAloneDefinesHeckeQuotientIsFalse :
      supportCountAloneDefinesHeckeQuotient ≡ false

    fullSupportMaskQuotientRefuted : Bool
    fullSupportMaskQuotientRefutedIsFalse :
      fullSupportMaskQuotientRefuted ≡ false

canonicalSupportCountCompressionBoundary : SupportCountCompressionBoundary
canonicalSupportCountCompressionBoundary =
  record
    { equalSupportCountCanHideHeckeRelevantDifference = true
    ; equalSupportCountCanHideHeckeRelevantDifferenceIsTrue = refl
    ; supportCountAloneDefinesHeckeQuotient = false
    ; supportCountAloneDefinesHeckeQuotientIsFalse = refl
    ; fullSupportMaskQuotientRefuted = false
    ; fullSupportMaskQuotientRefutedIsFalse = refl
    }
