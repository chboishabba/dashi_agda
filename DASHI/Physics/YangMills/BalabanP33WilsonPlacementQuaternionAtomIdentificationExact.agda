module DASHI.Physics.YangMills.BalabanP33WilsonPlacementQuaternionAtomIdentificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Identify every constructor in the sixteen-placement Wilson Hessian carrier
-- with the corresponding concrete quaternion product-rule atom.  The placement
-- order was chosen to match the recursive derivative normal form, so mapping
-- this explicit interpretation over the placement enumeration is definitionally
-- equal to the generated quaternion atom list.
--
-- This proves a bijective, name-bearing connection between
--
--   4 diagonal second-link atoms + 12 cross multiplicity atoms
--
-- and the actual ordered quaternion second derivative.  The Wilson scalar sum
-- and the transported inner-product factorisations can therefore be applied to
-- individual named placements, not merely to an anonymous sixteen-element list.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (Quaternion; _*q_)
import DASHI.Physics.YangMills.BalabanP33QuaternionProductSecondVariationExact as Product
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement

oneFactor : Product.QuaternionFactorJet → List Product.QuaternionFactorJet
oneFactor third = third ∷ []

twoFactors :
  Product.QuaternionFactorJet → Product.QuaternionFactorJet →
  List Product.QuaternionFactorJet
twoFactors second third = second ∷ third ∷ []

threeFactors :
  Product.QuaternionFactorJet → Product.QuaternionFactorJet →
  Product.QuaternionFactorJet → List Product.QuaternionFactorJet
threeFactors first second third = first ∷ second ∷ third ∷ []

placementQuaternionAtom :
  Product.QuaternionFactorJet → Product.QuaternionFactorJet →
  Product.QuaternionFactorJet → Product.QuaternionFactorJet →
  Placement.PlaquetteSecondVariationPlacement4 → Quaternion
placementQuaternionAtom first second third fourth Placement.secondAt0 =
  Product.factorSecond first *q
    Product.orderedValueProduct (threeFactors second third fourth)
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered01) =
  Product.factorFirst first *q
    (Product.factorFirst second *q
      Product.orderedValueProduct (twoFactors third fourth))
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered02) =
  Product.factorFirst first *q
    (Product.factorValue second *q
      (Product.factorFirst third *q
        Product.orderedValueProduct (oneFactor fourth)))
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered03) =
  Product.factorFirst first *q
    (Product.factorValue second *q
      (Product.factorValue third *q
        (Product.factorFirst fourth *q
          Product.orderedValueProduct [])))
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered10) =
  placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered01)
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered20) =
  placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered02)
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered30) =
  placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered03)
placementQuaternionAtom first second third fourth Placement.secondAt1 =
  Product.factorValue first *q
    (Product.factorSecond second *q
      Product.orderedValueProduct (twoFactors third fourth))
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered12) =
  Product.factorValue first *q
    (Product.factorFirst second *q
      (Product.factorFirst third *q
        Product.orderedValueProduct (oneFactor fourth)))
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered13) =
  Product.factorValue first *q
    (Product.factorFirst second *q
      (Product.factorValue third *q
        (Product.factorFirst fourth *q
          Product.orderedValueProduct [])))
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered21) =
  placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered12)
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered31) =
  placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered13)
placementQuaternionAtom first second third fourth Placement.secondAt2 =
  Product.factorValue first *q
    (Product.factorValue second *q
      (Product.factorSecond third *q
        Product.orderedValueProduct (oneFactor fourth)))
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered23) =
  Product.factorValue first *q
    (Product.factorValue second *q
      (Product.factorFirst third *q
        (Product.factorFirst fourth *q
          Product.orderedValueProduct [])))
placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered32) =
  placementQuaternionAtom first second third fourth
    (Placement.firstFirst Placement.ordered23)
placementQuaternionAtom first second third fourth Placement.secondAt3 =
  Product.factorValue first *q
    (Product.factorValue second *q
      (Product.factorValue third *q
        (Product.factorSecond fourth *q
          Product.orderedValueProduct [])))

placementAtomsMatchGeneratedProductRule :
  ∀ first second third fourth →
  map (placementQuaternionAtom first second third fourth)
    Placement.plaquetteSecondVariationPlacements4
  ≡ Product.secondVariationTerms
      (Product.fourFactorJets first second third fourth)
placementAtomsMatchGeneratedProductRule first second third fourth = refl

placementAtomSumIsOrderedSecondVariation :
  ∀ first second third fourth →
  Product.sumQuaternion
    (map (placementQuaternionAtom first second third fourth)
      Placement.plaquetteSecondVariationPlacements4)
  ≡ Product.orderedSecondProduct
      (Product.fourFactorJets first second third fourth)
placementAtomSumIsOrderedSecondVariation first second third fourth =
  Product.sumSecondVariationTermsExact
    (Product.fourFactorJets first second third fourth)

wilsonPlacementQuaternionIdentificationLevel : ProofLevel
wilsonPlacementQuaternionIdentificationLevel = machineChecked

wilsonNamedAtomSumLevel : ProofLevel
wilsonNamedAtomSumLevel = machineChecked
