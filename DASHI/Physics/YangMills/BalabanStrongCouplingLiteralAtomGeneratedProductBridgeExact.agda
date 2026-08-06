module DASHI.Physics.YangMills.BalabanStrongCouplingLiteralAtomGeneratedProductBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Eliminate a possible correspondence seam between the named sixteen atoms
-- whose norms are computed in Round Thirty One and the recursive second
-- derivative of the actual ordered four-factor quaternion product.  Mapping
-- the named placement interpretation over the literal constructor enumeration
-- is definitionally the generated `secondVariationTerms` list.
--
-- The specialization to two positive and two inverse right-exponential jets is
-- therefore not an independently supplied atom family: it is exactly the
-- product-rule output used by the Wilson Hessian.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (map)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionAtomNormExact as Atom

placementAtoms :
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  List Q.RationalQuaternion
placementAtoms jet0 jet1 jet2 jet3 =
  map (Atom.placementAtom jet0 jet1 jet2 jet3)
    Placement.plaquetteSecondVariationPlacements4

placementAtomsMatchGeneratedProductRule :
  ∀ jet0 jet1 jet2 jet3 →
  placementAtoms jet0 jet1 jet2 jet3
  ≡ Q.secondVariationTerms
      (Q.fourFactorJets jet0 jet1 jet2 jet3)
placementAtomsMatchGeneratedProductRule jet0 jet1 jet2 jet3 = refl

orientedPlaquetteJets :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  List Q.QuaternionFactorJet
orientedPlaquetteJets unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 =
  Q.fourFactorJets
    (Atom.positiveUnitJet unit0 insertion0)
    (Atom.positiveUnitJet unit1 insertion1)
    (Atom.inverseUnitJet unit2 insertion2)
    (Atom.inverseUnitJet unit3 insertion3)

orientedPlacementAtomsAreGeneratedTerms :
  ∀ unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 →
  map
    (Atom.orientedPlaquetteAtom
      unit0 insertion0 unit1 insertion1
      unit2 insertion2 unit3 insertion3)
    Placement.plaquetteSecondVariationPlacements4
  ≡ Q.secondVariationTerms
      (orientedPlaquetteJets
        unit0 insertion0 unit1 insertion1
        unit2 insertion2 unit3 insertion3)
orientedPlacementAtomsAreGeneratedTerms
    unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 = refl

orientedPlacementAtomSumIsWilsonSecondVariation :
  ∀ unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 →
  Q.sumQuaternion
    (map
      (Atom.orientedPlaquetteAtom
        unit0 insertion0 unit1 insertion1
        unit2 insertion2 unit3 insertion3)
      Placement.plaquetteSecondVariationPlacements4)
  ≡ Q.orderedSecondProduct
      (orientedPlaquetteJets
        unit0 insertion0 unit1 insertion1
        unit2 insertion2 unit3 insertion3)
orientedPlacementAtomSumIsWilsonSecondVariation
    unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 =
  Q.sumSecondVariationTermsExact
    (orientedPlaquetteJets
      unit0 insertion0 unit1 insertion1
      unit2 insertion2 unit3 insertion3)
