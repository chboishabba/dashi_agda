module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlAtomTransportExact where

open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlPolynomialExact public
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact public

flatPlaquetteSixteenAtomsAreCurlSquare :
  ∀ forward0 forward1 inverse2 inverse3 →
  wilsonSecondVariationAtomSum
    (flatOrientedPlaquetteJets forward0 forward1 inverse2 inverse3)
  ≡ vectorNormSq (plaquetteCurlVector forward0 forward1 inverse2 inverse3)
flatPlaquetteSixteenAtomsAreCurlSquare forward0 forward1 inverse2 inverse3 =
  trans
    (sym (wilsonSecondVariationIsAtomSum
      (flatOrientedPlaquetteJets forward0 forward1 inverse2 inverse3)))
    (flatPlaquetteWilsonIsCurlSquare
      forward0 forward1 inverse2 inverse3)
