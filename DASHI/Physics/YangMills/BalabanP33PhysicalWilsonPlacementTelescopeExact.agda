module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonPlacementTelescopeExact where

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
-- Connect the sixteen named Wilson placements to the literal physical
-- plaquette jets, then telescope every background-minus-flat atom into four
-- terms with one selected-factor defect each.
--
-- This is the exact algebraic producer required before any norm estimate:
-- no anonymous atom list and no independently supplied correspondence remain.
-- For every physical plaquette and every one of the four diagonal plus twelve
-- ordered cross placements, the module proves
--
--   Atom_A - Atom_1
--     = T0 + T1 + T2 + T3,
--
-- where Tr contains one and only one selected factor difference.  The later
-- analytic Wilson estimate must bound these concrete terms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33WilsonPlacementQuaternionAtomIdentificationExact as Named
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope

data FactorSelection : Set where
  valueSelection firstSelection secondSelection : FactorSelection

applySelection :
  FactorSelection → Q.QuaternionFactorJet → Q.RationalQuaternion
applySelection valueSelection jet = Q.factorValue jet
applySelection firstSelection jet = Q.factorFirst jet
applySelection secondSelection jet = Q.factorSecond jet

selection0 selection1 selection2 selection3 :
  Placement.PlaquetteSecondVariationPlacement4 → FactorSelection

selection0 Placement.secondAt0 = secondSelection
selection0 Placement.secondAt1 = valueSelection
selection0 Placement.secondAt2 = valueSelection
selection0 Placement.secondAt3 = valueSelection
selection0 (Placement.firstFirst Placement.ordered01) = firstSelection
selection0 (Placement.firstFirst Placement.ordered10) = firstSelection
selection0 (Placement.firstFirst Placement.ordered02) = firstSelection
selection0 (Placement.firstFirst Placement.ordered20) = firstSelection
selection0 (Placement.firstFirst Placement.ordered03) = firstSelection
selection0 (Placement.firstFirst Placement.ordered30) = firstSelection
selection0 (Placement.firstFirst Placement.ordered12) = valueSelection
selection0 (Placement.firstFirst Placement.ordered21) = valueSelection
selection0 (Placement.firstFirst Placement.ordered13) = valueSelection
selection0 (Placement.firstFirst Placement.ordered31) = valueSelection
selection0 (Placement.firstFirst Placement.ordered23) = valueSelection
selection0 (Placement.firstFirst Placement.ordered32) = valueSelection

selection1 Placement.secondAt0 = valueSelection
selection1 Placement.secondAt1 = secondSelection
selection1 Placement.secondAt2 = valueSelection
selection1 Placement.secondAt3 = valueSelection
selection1 (Placement.firstFirst Placement.ordered01) = firstSelection
selection1 (Placement.firstFirst Placement.ordered10) = firstSelection
selection1 (Placement.firstFirst Placement.ordered02) = valueSelection
selection1 (Placement.firstFirst Placement.ordered20) = valueSelection
selection1 (Placement.firstFirst Placement.ordered03) = valueSelection
selection1 (Placement.firstFirst Placement.ordered30) = valueSelection
selection1 (Placement.firstFirst Placement.ordered12) = firstSelection
selection1 (Placement.firstFirst Placement.ordered21) = firstSelection
selection1 (Placement.firstFirst Placement.ordered13) = firstSelection
selection1 (Placement.firstFirst Placement.ordered31) = firstSelection
selection1 (Placement.firstFirst Placement.ordered23) = valueSelection
selection1 (Placement.firstFirst Placement.ordered32) = valueSelection

selection2 Placement.secondAt0 = valueSelection
selection2 Placement.secondAt1 = valueSelection
selection2 Placement.secondAt2 = secondSelection
selection2 Placement.secondAt3 = valueSelection
selection2 (Placement.firstFirst Placement.ordered01) = valueSelection
selection2 (Placement.firstFirst Placement.ordered10) = valueSelection
selection2 (Placement.firstFirst Placement.ordered02) = firstSelection
selection2 (Placement.firstFirst Placement.ordered20) = firstSelection
selection2 (Placement.firstFirst Placement.ordered03) = valueSelection
selection2 (Placement.firstFirst Placement.ordered30) = valueSelection
selection2 (Placement.firstFirst Placement.ordered12) = firstSelection
selection2 (Placement.firstFirst Placement.ordered21) = firstSelection
selection2 (Placement.firstFirst Placement.ordered13) = valueSelection
selection2 (Placement.firstFirst Placement.ordered31) = valueSelection
selection2 (Placement.firstFirst Placement.ordered23) = firstSelection
selection2 (Placement.firstFirst Placement.ordered32) = firstSelection

selection3 Placement.secondAt0 = valueSelection
selection3 Placement.secondAt1 = valueSelection
selection3 Placement.secondAt2 = valueSelection
selection3 Placement.secondAt3 = secondSelection
selection3 (Placement.firstFirst Placement.ordered01) = valueSelection
selection3 (Placement.firstFirst Placement.ordered10) = valueSelection
selection3 (Placement.firstFirst Placement.ordered02) = valueSelection
selection3 (Placement.firstFirst Placement.ordered20) = valueSelection
selection3 (Placement.firstFirst Placement.ordered03) = firstSelection
selection3 (Placement.firstFirst Placement.ordered30) = firstSelection
selection3 (Placement.firstFirst Placement.ordered12) = valueSelection
selection3 (Placement.firstFirst Placement.ordered21) = valueSelection
selection3 (Placement.firstFirst Placement.ordered13) = firstSelection
selection3 (Placement.firstFirst Placement.ordered31) = firstSelection
selection3 (Placement.firstFirst Placement.ordered23) = firstSelection
selection3 (Placement.firstFirst Placement.ordered32) = firstSelection

selectedFactor0 selectedFactor1 selectedFactor2 selectedFactor3 :
  Q.QuaternionFactorJet → Placement.PlaquetteSecondVariationPlacement4 →
  Q.RationalQuaternion
selectedFactor0 jet placement = applySelection (selection0 placement) jet
selectedFactor1 jet placement = applySelection (selection1 placement) jet
selectedFactor2 jet placement = applySelection (selection2 placement) jet
selectedFactor3 jet placement = applySelection (selection3 placement) jet

namedPlacementAtomIsSelectedProduct :
  ∀ first second third fourth placement →
  Named.placementQuaternionAtom first second third fourth placement
  ≡ Telescope.orderedProduct4
      (selectedFactor0 first placement)
      (selectedFactor1 second placement)
      (selectedFactor2 third placement)
      (selectedFactor3 fourth placement)
namedPlacementAtomIsSelectedProduct first second third fourth Placement.secondAt0 = refl
namedPlacementAtomIsSelectedProduct first second third fourth Placement.secondAt1 = refl
namedPlacementAtomIsSelectedProduct first second third fourth Placement.secondAt2 = refl
namedPlacementAtomIsSelectedProduct first second third fourth Placement.secondAt3 = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered01) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered10) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered02) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered20) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered03) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered30) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered12) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered21) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered13) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered31) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered23) = refl
namedPlacementAtomIsSelectedProduct first second third fourth
  (Placement.firstFirst Placement.ordered32) = refl

physicalNamedPlacementAtom :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 →
  Q.RationalQuaternion
physicalNamedPlacementAtom background fieldValue plaquette placement =
  let
    dataSet = Physical.plaquetteJetData background fieldValue plaquette
  in
  Named.placementQuaternionAtom
    (Jets.link0 dataSet) (Jets.link1 dataSet)
    (Jets.link2 dataSet) (Jets.link3 dataSet)
    placement

physicalPlacementAtoms :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → List Q.RationalQuaternion
physicalPlacementAtoms background fieldValue plaquette =
  map (physicalNamedPlacementAtom background fieldValue plaquette)
    Placement.plaquetteSecondVariationPlacements4

physicalPlacementAtomsMatchGeneratedProductRule :
  ∀ background fieldValue plaquette →
  physicalPlacementAtoms background fieldValue plaquette
  ≡ Q.secondVariationTerms
      (Physical.plaquetteFactorJets background fieldValue plaquette)
physicalPlacementAtomsMatchGeneratedProductRule background fieldValue plaquette =
  let
    dataSet = Physical.plaquetteJetData background fieldValue plaquette
  in
  Named.placementAtomsMatchGeneratedProductRule
    (Jets.link0 dataSet) (Jets.link1 dataSet)
    (Jets.link2 dataSet) (Jets.link3 dataSet)

physicalNamedPlacementDefect :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 →
  Q.RationalQuaternion
physicalNamedPlacementDefect background fieldValue plaquette placement =
  Telescope._-q_
    (physicalNamedPlacementAtom background fieldValue plaquette placement)
    (physicalNamedPlacementAtom
      Physical.identityBackground fieldValue plaquette placement)

physicalNamedPlacementDefectTelescopeExact :
  ∀ background fieldValue plaquette placement →
  physicalNamedPlacementDefect background fieldValue plaquette placement
  ≡
  let
    backgroundData = Physical.plaquetteJetData background fieldValue plaquette
    identityData =
      Physical.plaquetteJetData Physical.identityBackground fieldValue plaquette

    a0 = selectedFactor0 (Jets.link0 backgroundData) placement
    a1 = selectedFactor1 (Jets.link1 backgroundData) placement
    a2 = selectedFactor2 (Jets.link2 backgroundData) placement
    a3 = selectedFactor3 (Jets.link3 backgroundData) placement

    b0 = selectedFactor0 (Jets.link0 identityData) placement
    b1 = selectedFactor1 (Jets.link1 identityData) placement
    b2 = selectedFactor2 (Jets.link2 identityData) placement
    b3 = selectedFactor3 (Jets.link3 identityData) placement
  in
  Telescope.fourFactorTelescope a0 a1 a2 a3 b0 b1 b2 b3
physicalNamedPlacementDefectTelescopeExact
    background fieldValue plaquette placement
  rewrite namedPlacementAtomIsSelectedProduct
      (Jets.link0 (Physical.plaquetteJetData background fieldValue plaquette))
      (Jets.link1 (Physical.plaquetteJetData background fieldValue plaquette))
      (Jets.link2 (Physical.plaquetteJetData background fieldValue plaquette))
      (Jets.link3 (Physical.plaquetteJetData background fieldValue plaquette))
      placement
        | namedPlacementAtomIsSelectedProduct
      (Jets.link0
        (Physical.plaquetteJetData
          Physical.identityBackground fieldValue plaquette))
      (Jets.link1
        (Physical.plaquetteJetData
          Physical.identityBackground fieldValue plaquette))
      (Jets.link2
        (Physical.plaquetteJetData
          Physical.identityBackground fieldValue plaquette))
      (Jets.link3
        (Physical.plaquetteJetData
          Physical.identityBackground fieldValue plaquette))
      placement =
  Telescope.fourFactorDifferenceTelescopeExact _ _ _ _ _ _ _ _

physicalPlacementWilsonScalarDefect :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 →
  ℚ
physicalPlacementWilsonScalarDefect background fieldValue plaquette placement =
  Telescope.wilsonScalarDifference
    (physicalNamedPlacementAtom background fieldValue plaquette placement)
    (physicalNamedPlacementAtom
      Physical.identityBackground fieldValue plaquette placement)

physicalPlacementWilsonScalarDefectTelescopeExact :
  ∀ background fieldValue plaquette placement →
  physicalPlacementWilsonScalarDefect
    background fieldValue plaquette placement
  ≡
  let
    backgroundData = Physical.plaquetteJetData background fieldValue plaquette
    identityData =
      Physical.plaquetteJetData Physical.identityBackground fieldValue plaquette

    a0 = selectedFactor0 (Jets.link0 backgroundData) placement
    a1 = selectedFactor1 (Jets.link1 backgroundData) placement
    a2 = selectedFactor2 (Jets.link2 backgroundData) placement
    a3 = selectedFactor3 (Jets.link3 backgroundData) placement

    b0 = selectedFactor0 (Jets.link0 identityData) placement
    b1 = selectedFactor1 (Jets.link1 identityData) placement
    b2 = selectedFactor2 (Jets.link2 identityData) placement
    b3 = selectedFactor3 (Jets.link3 identityData) placement
  in
  Telescope.wilsonScalar
    (Telescope.fourFactorTelescope a0 a1 a2 a3 b0 b1 b2 b3)
physicalPlacementWilsonScalarDefectTelescopeExact
    background fieldValue plaquette placement
  rewrite namedPlacementAtomIsSelectedProduct
      (Jets.link0 (Physical.plaquetteJetData background fieldValue plaquette))
      (Jets.link1 (Physical.plaquetteJetData background fieldValue plaquette))
      (Jets.link2 (Physical.plaquetteJetData background fieldValue plaquette))
      (Jets.link3 (Physical.plaquetteJetData background fieldValue plaquette))
      placement
        | namedPlacementAtomIsSelectedProduct
      (Jets.link0
        (Physical.plaquetteJetData
          Physical.identityBackground fieldValue plaquette))
      (Jets.link1
        (Physical.plaquetteJetData
          Physical.identityBackground fieldValue plaquette))
      (Jets.link2
        (Physical.plaquetteJetData
          Physical.identityBackground fieldValue plaquette))
      (Jets.link3
        (Physical.plaquetteJetData
          Physical.identityBackground fieldValue plaquette))
      placement =
  Telescope.wilsonScalarDifferenceTelescopeExact _ _ _ _ _ _ _ _

physicalWilsonNamedPlacementIdentificationLevel : ProofLevel
physicalWilsonNamedPlacementIdentificationLevel = machineChecked

physicalWilsonPlacementTelescopeLevel : ProofLevel
physicalWilsonPlacementTelescopeLevel = machineChecked

physicalWilsonPlacementNormEstimateLevel : ProofLevel
physicalWilsonPlacementNormEstimateLevel = conditional
