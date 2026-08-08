module DASHI.Physics.YangMills.BalabanP33PhysicalPlaquetteFirstVariationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Compute the first derivative of the repository's literal ordered plaquette
-- product using exactly the same positive-link and inverse-link jets consumed
-- by the sixteen-atom Hessian.  The result is the four ordered Leibniz terms
--
--   U0' U1 U2^-1 U3^-1
-- + U0 U1' U2^-1 U3^-1
-- + U0 U1 (U2^-1)' U3^-1
-- + U0 U1 U2^-1 (U3^-1)'.
--
-- No independently chosen orientation convention enters: the theorem unfolds
-- `plaquetteFactorJets`, whose third and fourth first jets are already
-- `-X U^-1` under the repository's right-exponential convention.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates

plaquetteJet0 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.QuaternionFactorJet
plaquetteJet0 background field plaquette =
  Jets.link0 (Physical.plaquetteJetData background field plaquette)

plaquetteJet1 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.QuaternionFactorJet
plaquetteJet1 background field plaquette =
  Jets.link1 (Physical.plaquetteJetData background field plaquette)

plaquetteJet2 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.QuaternionFactorJet
plaquetteJet2 background field plaquette =
  Jets.link2 (Physical.plaquetteJetData background field plaquette)

plaquetteJet3 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.QuaternionFactorJet
plaquetteJet3 background field plaquette =
  Jets.link3 (Physical.plaquetteJetData background field plaquette)

firstVariationTerm0 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.RationalQuaternion
firstVariationTerm0 background field plaquette =
  let
    j0 = plaquetteJet0 background field plaquette
    j1 = plaquetteJet1 background field plaquette
    j2 = plaquetteJet2 background field plaquette
    j3 = plaquetteJet3 background field plaquette
  in
  Q.factorFirst j0 Q.*q
    (Q.factorValue j1 Q.*q
      (Q.factorValue j2 Q.*q
        (Q.factorValue j3 Q.*q Q.oneQ)))

firstVariationTerm1 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.RationalQuaternion
firstVariationTerm1 background field plaquette =
  let
    j0 = plaquetteJet0 background field plaquette
    j1 = plaquetteJet1 background field plaquette
    j2 = plaquetteJet2 background field plaquette
    j3 = plaquetteJet3 background field plaquette
  in
  Q.factorValue j0 Q.*q
    (Q.factorFirst j1 Q.*q
      (Q.factorValue j2 Q.*q
        (Q.factorValue j3 Q.*q Q.oneQ)))

firstVariationTerm2 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.RationalQuaternion
firstVariationTerm2 background field plaquette =
  let
    j0 = plaquetteJet0 background field plaquette
    j1 = plaquetteJet1 background field plaquette
    j2 = plaquetteJet2 background field plaquette
    j3 = plaquetteJet3 background field plaquette
  in
  Q.factorValue j0 Q.*q
    (Q.factorValue j1 Q.*q
      (Q.factorFirst j2 Q.*q
        (Q.factorValue j3 Q.*q Q.oneQ)))

firstVariationTerm3 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.RationalQuaternion
firstVariationTerm3 background field plaquette =
  let
    j0 = plaquetteJet0 background field plaquette
    j1 = plaquetteJet1 background field plaquette
    j2 = plaquetteJet2 background field plaquette
    j3 = plaquetteJet3 background field plaquette
  in
  Q.factorValue j0 Q.*q
    (Q.factorValue j1 Q.*q
      (Q.factorValue j2 Q.*q
        (Q.factorFirst j3 Q.*q Q.oneQ)))

plaquetteFirstVariationTerms4 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → List Q.RationalQuaternion
plaquetteFirstVariationTerms4 background field plaquette =
  firstVariationTerm0 background field plaquette ∷
  firstVariationTerm1 background field plaquette ∷
  firstVariationTerm2 background field plaquette ∷
  firstVariationTerm3 background field plaquette ∷ []

generatedFirstVariationTermsAreFourOrdered :
  ∀ background field plaquette →
  Q.firstVariationTerms
    (Physical.plaquetteFactorJets background field plaquette)
  ≡ plaquetteFirstVariationTerms4 background field plaquette
generatedFirstVariationTermsAreFourOrdered background field plaquette = refl

plaquetteFirstVariationTermCountExact :
  ∀ background field plaquette →
  length (plaquetteFirstVariationTerms4 background field plaquette) ≡ 4
plaquetteFirstVariationTermCountExact background field plaquette = refl

plaquetteFirstVariation :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Q.RationalQuaternion
plaquetteFirstVariation background field plaquette =
  Q.orderedFirstProduct
    (Physical.plaquetteFactorJets background field plaquette)

plaquetteFirstVariationIsFourOrderedSum :
  ∀ background field plaquette →
  plaquetteFirstVariation background field plaquette
  ≡ Q.sumQuaternion
      (plaquetteFirstVariationTerms4 background field plaquette)
plaquetteFirstVariationIsFourOrderedSum background field plaquette =
  trans
    (sym
      (Q.sumFirstVariationTermsExact
        (Physical.plaquetteFactorJets background field plaquette)))
    (cong Q.sumQuaternion
      (generatedFirstVariationTermsAreFourOrdered
        background field plaquette))

physicalPlaquetteFirstVariationLevel : ProofLevel
physicalPlaquetteFirstVariationLevel = machineChecked

physicalPlaquetteFirstVariationOrientationLevel : ProofLevel
physicalPlaquetteFirstVariationOrientationLevel = machineChecked
