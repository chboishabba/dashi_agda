module DASHI.Physics.YangMills.BalabanCanonicalGreenHigherMobiusDegreeVanishExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Consume the literal four-slot subset-layer theorem on the exact source and
-- defect states already used by the canonical KKT Green construction.  Since
--
--   L2=3L1, L3=3L1, L4=L1,
--
-- the repository's Möbius formulas give D2=D3=D4=0 pointwise for both state
-- families.  Linearity of the actual KKT constraint map then gives the same
-- exact vanishing for the canonical multiplier degree vectors.  Consequently
-- every Green degree block except (1,1) is exactly zero; this is stronger than
-- a norm bound and removes the previous polarization charge for those blocks.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as GreenDegree
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeStatePreimageExact as Preimage
import DASHI.Physics.YangMills.BalabanPlaquetteSubsetMobiusDegreeOneCollapseExact as Collapse

------------------------------------------------------------------------
-- Source and defect layer identities on the exact canonical states.
------------------------------------------------------------------------

sourceLayer2Three :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.sourceLayerState inputs Degree.degree2 coordinate
  ≡ (+ 3 / 1) * Preimage.sourceLayerState inputs Degree.degree1 coordinate
sourceLayer2Three {firstVariationCovector = source} {plaquette = plaquette}
    inputs coordinate =
  Collapse.layer2IsThreeLayer1 source plaquette coordinate

sourceLayer3Three :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.sourceLayerState inputs Degree.degree3 coordinate
  ≡ (+ 3 / 1) * Preimage.sourceLayerState inputs Degree.degree1 coordinate
sourceLayer3Three {firstVariationCovector = source} {plaquette = plaquette}
    inputs coordinate =
  Collapse.layer3IsThreeLayer1 source plaquette coordinate

sourceLayer4One :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.sourceLayerState inputs Degree.degree4 coordinate
  ≡ Preimage.sourceLayerState inputs Degree.degree1 coordinate
sourceLayer4One {firstVariationCovector = source} {plaquette = plaquette}
    inputs coordinate =
  Collapse.layer4IsLayer1 source plaquette coordinate

defectLayer2Three :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.defectLayerState inputs Degree.degree2 coordinate
  ≡ (+ 3 / 1) * Preimage.defectLayerState inputs Degree.degree1 coordinate
defectLayer2Three {bondField = field} {plaquette = plaquette}
    inputs coordinate =
  Collapse.layer2IsThreeLayer1
    (Physical.encodePhysicalSU2 field) plaquette coordinate

defectLayer3Three :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.defectLayerState inputs Degree.degree3 coordinate
  ≡ (+ 3 / 1) * Preimage.defectLayerState inputs Degree.degree1 coordinate
defectLayer3Three {bondField = field} {plaquette = plaquette}
    inputs coordinate =
  Collapse.layer3IsThreeLayer1
    (Physical.encodePhysicalSU2 field) plaquette coordinate

defectLayer4One :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.defectLayerState inputs Degree.degree4 coordinate
  ≡ Preimage.defectLayerState inputs Degree.degree1 coordinate
defectLayer4One {bondField = field} {plaquette = plaquette}
    inputs coordinate =
  Collapse.layer4IsLayer1
    (Physical.encodePhysicalSU2 field) plaquette coordinate

------------------------------------------------------------------------
-- Higher Möbius state degrees vanish pointwise.
------------------------------------------------------------------------

sourceDegree2Zero :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.sourceDegreeState inputs Degree.degree2 coordinate ≡ 0ℚ
sourceDegree2Zero inputs coordinate
  rewrite sourceLayer2Three inputs coordinate =
  ℚRing.solve-∀ (Preimage.sourceLayerState inputs Degree.degree1 coordinate)

sourceDegree3Zero :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.sourceDegreeState inputs Degree.degree3 coordinate ≡ 0ℚ
sourceDegree3Zero inputs coordinate
  rewrite sourceLayer3Three inputs coordinate
        | sourceLayer2Three inputs coordinate =
  ℚRing.solve-∀ (Preimage.sourceLayerState inputs Degree.degree1 coordinate)

sourceDegree4Zero :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.sourceDegreeState inputs Degree.degree4 coordinate ≡ 0ℚ
sourceDegree4Zero inputs coordinate
  rewrite sourceLayer4One inputs coordinate
        | sourceLayer3Three inputs coordinate
        | sourceLayer2Three inputs coordinate =
  ℚRing.solve-∀ (Preimage.sourceLayerState inputs Degree.degree1 coordinate)

defectDegree2Zero :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.defectDegreeState inputs Degree.degree2 coordinate ≡ 0ℚ
defectDegree2Zero inputs coordinate
  rewrite defectLayer2Three inputs coordinate =
  ℚRing.solve-∀ (Preimage.defectLayerState inputs Degree.degree1 coordinate)

defectDegree3Zero :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.defectDegreeState inputs Degree.degree3 coordinate ≡ 0ℚ
defectDegree3Zero inputs coordinate
  rewrite defectLayer3Three inputs coordinate
        | defectLayer2Three inputs coordinate =
  ℚRing.solve-∀ (Preimage.defectLayerState inputs Degree.degree1 coordinate)

defectDegree4Zero :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.defectDegreeState inputs Degree.degree4 coordinate ≡ 0ℚ
defectDegree4Zero inputs coordinate
  rewrite defectLayer4One inputs coordinate
        | defectLayer3Three inputs coordinate
        | defectLayer2Three inputs coordinate =
  ℚRing.solve-∀ (Preimage.defectLayerState inputs Degree.degree1 coordinate)

------------------------------------------------------------------------
-- Constraint-map transport of pointwise zero.
------------------------------------------------------------------------

constraintApplyPointwiseZero :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    state →
  (∀ coordinate → state coordinate ≡ 0ℚ) →
  ∀ row → Pseudo.constraintApply pseudoData state row ≡ 0ℚ
constraintApplyPointwiseZero pseudoData state pointwise row =
  trans
    (Rect.applyRectangularVectorCong
      KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      pointwise row)
    (Rect.applyRectangularZero
      KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData) row)

sourceDegreeVector2Zero :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    row →
  GreenDegree.sourceDegreeVector
    (Canonical.canonicalConstraintAtoms inputs) Degree.degree2 row ≡ 0ℚ
sourceDegreeVector2Zero {pseudoData = pseudoData} inputs row =
  trans
    (sym (Preimage.sourceDegreeStateConstraintExact inputs Degree.degree2 row))
    (constraintApplyPointwiseZero pseudoData
      (Preimage.sourceDegreeState inputs Degree.degree2)
      (sourceDegree2Zero inputs) row)

sourceDegreeVector3Zero :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    row →
  GreenDegree.sourceDegreeVector
    (Canonical.canonicalConstraintAtoms inputs) Degree.degree3 row ≡ 0ℚ
sourceDegreeVector3Zero {pseudoData = pseudoData} inputs row =
  trans
    (sym (Preimage.sourceDegreeStateConstraintExact inputs Degree.degree3 row))
    (constraintApplyPointwiseZero pseudoData
      (Preimage.sourceDegreeState inputs Degree.degree3)
      (sourceDegree3Zero inputs) row)

sourceDegreeVector4Zero :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    row →
  GreenDegree.sourceDegreeVector
    (Canonical.canonicalConstraintAtoms inputs) Degree.degree4 row ≡ 0ℚ
sourceDegreeVector4Zero {pseudoData = pseudoData} inputs row =
  trans
    (sym (Preimage.sourceDegreeStateConstraintExact inputs Degree.degree4 row))
    (constraintApplyPointwiseZero pseudoData
      (Preimage.sourceDegreeState inputs Degree.degree4)
      (sourceDegree4Zero inputs) row)

defectDegreeVector2Zero :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    row →
  GreenDegree.defectDegreeVector
    (Canonical.canonicalConstraintAtoms inputs) Degree.degree2 row ≡ 0ℚ
defectDegreeVector2Zero {pseudoData = pseudoData} inputs row =
  trans
    (sym (Preimage.defectDegreeStateConstraintExact inputs Degree.degree2 row))
    (constraintApplyPointwiseZero pseudoData
      (Preimage.defectDegreeState inputs Degree.degree2)
      (defectDegree2Zero inputs) row)

defectDegreeVector3Zero :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    row →
  GreenDegree.defectDegreeVector
    (Canonical.canonicalConstraintAtoms inputs) Degree.degree3 row ≡ 0ℚ
defectDegreeVector3Zero {pseudoData = pseudoData} inputs row =
  trans
    (sym (Preimage.defectDegreeStateConstraintExact inputs Degree.degree3 row))
    (constraintApplyPointwiseZero pseudoData
      (Preimage.defectDegreeState inputs Degree.degree3)
      (defectDegree3Zero inputs) row)

defectDegreeVector4Zero :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    row →
  GreenDegree.defectDegreeVector
    (Canonical.canonicalConstraintAtoms inputs) Degree.degree4 row ≡ 0ℚ
defectDegreeVector4Zero {pseudoData = pseudoData} inputs row =
  trans
    (sym (Preimage.defectDegreeStateConstraintExact inputs Degree.degree4 row))
    (constraintApplyPointwiseZero pseudoData
      (Preimage.defectDegreeState inputs Degree.degree4)
      (defectDegree4Zero inputs) row)

canonicalGreenHigherMobiusDegreeVanishLevel : ProofLevel
canonicalGreenHigherMobiusDegreeVanishLevel = machineChecked
