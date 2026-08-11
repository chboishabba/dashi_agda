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
-- Eliminate a correspondence seam between the named sixteen atoms whose norms
-- are computed in Round Thirty One and the recursive second derivative of the
-- actual ordered four-factor quaternion product.
--
-- The recursive product rule has a specific generated order: the second atom
-- at slot zero, the two copies of the three first/first descendants involving
-- slot zero, then the inherited three-factor second derivative, recursively.
-- This module names that exact order and proves definitionally that mapping the
-- placement interpretation over it is `secondVariationTerms`.
--
-- The canonical human-facing enumeration and this recursive enumeration contain
-- the same four diagonal and twelve ordered-cross constructors, but are not
-- falsely identified as order-equal lists.  Their scalar budgets are checked
-- independently against the same closed formula.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length; map)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionAtomNormExact as Atom

recursivePlacementOrder4 :
  List Placement.PlaquetteSecondVariationPlacement4
recursivePlacementOrder4 =
  Placement.secondAt0 ∷
  Placement.firstFirst Placement.ordered01 ∷
  Placement.firstFirst Placement.ordered02 ∷
  Placement.firstFirst Placement.ordered03 ∷
  Placement.firstFirst Placement.ordered10 ∷
  Placement.firstFirst Placement.ordered20 ∷
  Placement.firstFirst Placement.ordered30 ∷
  Placement.secondAt1 ∷
  Placement.firstFirst Placement.ordered12 ∷
  Placement.firstFirst Placement.ordered13 ∷
  Placement.firstFirst Placement.ordered21 ∷
  Placement.firstFirst Placement.ordered31 ∷
  Placement.secondAt2 ∷
  Placement.firstFirst Placement.ordered23 ∷
  Placement.firstFirst Placement.ordered32 ∷
  Placement.secondAt3 ∷ []

recursivePlacementOrderCountExact :
  length recursivePlacementOrder4 ≡ 16
recursivePlacementOrderCountExact = refl

recursivePlacementAtoms :
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  List Q.RationalQuaternion
recursivePlacementAtoms jet0 jet1 jet2 jet3 =
  map (Atom.placementAtom jet0 jet1 jet2 jet3)
    recursivePlacementOrder4

recursivePlacementAtomsMatchGeneratedProductRule :
  ∀ jet0 jet1 jet2 jet3 →
  recursivePlacementAtoms jet0 jet1 jet2 jet3
  ≡ Q.secondVariationTerms
      (Q.fourFactorJets jet0 jet1 jet2 jet3)
recursivePlacementAtomsMatchGeneratedProductRule jet0 jet1 jet2 jet3 = refl

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

orientedRecursiveAtomsAreGeneratedTerms :
  ∀ unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 →
  map
    (Atom.orientedPlaquetteAtom
      unit0 insertion0 unit1 insertion1
      unit2 insertion2 unit3 insertion3)
    recursivePlacementOrder4
  ≡ Q.secondVariationTerms
      (orientedPlaquetteJets
        unit0 insertion0 unit1 insertion1
        unit2 insertion2 unit3 insertion3)
orientedRecursiveAtomsAreGeneratedTerms
    unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 = refl

orientedRecursiveAtomSumIsWilsonSecondVariation :
  ∀ unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 →
  Q.sumQuaternion
    (map
      (Atom.orientedPlaquetteAtom
        unit0 insertion0 unit1 insertion1
        unit2 insertion2 unit3 insertion3)
      recursivePlacementOrder4)
  ≡ Q.orderedSecondProduct
      (orientedPlaquetteJets
        unit0 insertion0 unit1 insertion1
        unit2 insertion2 unit3 insertion3)
orientedRecursiveAtomSumIsWilsonSecondVariation
    unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 =
  Q.sumSecondVariationTermsExact
    (orientedPlaquetteJets
      unit0 insertion0 unit1 insertion1
      unit2 insertion2 unit3 insertion3)
