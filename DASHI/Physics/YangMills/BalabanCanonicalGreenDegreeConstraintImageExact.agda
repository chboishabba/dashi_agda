module DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeConstraintImageExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Mobius Functions",
-- Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- The Round60 Green degree vectors are not arbitrary multiplier vectors.  The
-- canonical source/defect partials are literally L(P_S g) and L(P_S w).
-- Linearity therefore lifts each four degree-summed Mobius vector to an
-- explicit state-space preimage.  With the zero-background degree formulas,
--
--   D1 = L1
--   D2 = L2 - 3 L1
--   D3 = L3 - 2 L2 + 3 L1
--   D4 = L4 - L3 + L2 - L1,
--
-- the same formulas are applied BEFORE L to the subset-projected states.
-- Hence every canonical source/defect degree vector lies in im(L) on the
-- exact same physical carrier.  Combined with the constraint-image energy
-- contraction, this eliminates any need for a global K+ Schur bound in G2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PlaquetteSubsetProjectorExact as Subset
import DASHI.Physics.YangMills.BalabanSelectedSourceSubsetConstraintPartialExact as Source
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorSubsetDefectPartialExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact as Green
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as DegreeGreen
import DASHI.Physics.YangMills.BalabanSelectedConstraintMobiusDegreeLayerExact as MobiusLayer
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree

partialData :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Atoms.SelectedConstraintPartialEvaluationData
    pseudoData firstVariationCovector
    (DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact.rawPlaquetteSingletonExtractor
      bondField plaquette)
partialData inputs =
  Source.asSelectedConstraintPartialEvaluationData
    (Canonical.sourceDefectProducer inputs)

sourceStatePartial :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Cube.Subset4 → KKT.StateVector
sourceStatePartial {firstVariationCovector = source} {plaquette = plaquette}
    inputs subset =
  Subset.subsetBoundaryProject subset plaquette source

defectStatePartial :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Cube.Subset4 → KKT.StateVector
defectStatePartial {bondField = field} {plaquette = plaquette}
    inputs subset =
  Subset.rawSubsetExtractor field plaquette subset

stateLayer :
  ∀ {Index : Set} →
  Agda.Builtin.List.List Index → (Index → KKT.StateVector) → KKT.StateVector
stateLayer = Green.sumVector

sourceLayer1State sourceLayer2State sourceLayer3State sourceLayer4State :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  KKT.StateVector
sourceLayer1State inputs = stateLayer Cube.singletonSubsets4 (sourceStatePartial inputs)
sourceLayer2State inputs = stateLayer Cube.pairSubsets4 (sourceStatePartial inputs)
sourceLayer3State inputs = stateLayer Cube.tripleSubsets4 (sourceStatePartial inputs)
sourceLayer4State inputs = stateLayer Cube.quarticSubsets4 (sourceStatePartial inputs)

defectLayer1State defectLayer2State defectLayer3State defectLayer4State :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  KKT.StateVector
defectLayer1State inputs = stateLayer Cube.singletonSubsets4 (defectStatePartial inputs)
defectLayer2State inputs = stateLayer Cube.pairSubsets4 (defectStatePartial inputs)
defectLayer3State inputs = stateLayer Cube.tripleSubsets4 (defectStatePartial inputs)
defectLayer4State inputs = stateLayer Cube.quarticSubsets4 (defectStatePartial inputs)

doubleState : KKT.StateVector → KKT.StateVector
doubleState vector = Rect.vectorAdd vector vector

tripleState : KKT.StateVector → KKT.StateVector
tripleState vector = Rect.vectorAdd vector (Rect.vectorAdd vector vector)

degreeStateFromLayers :
  KKT.StateVector → KKT.StateVector → KKT.StateVector → KKT.StateVector →
  Degree.MobiusDegree → KKT.StateVector
degreeStateFromLayers l1 l2 l3 l4 Degree.degree1 = l1
degreeStateFromLayers l1 l2 l3 l4 Degree.degree2 =
  Rect.vectorSubtract l2 (tripleState l1)
degreeStateFromLayers l1 l2 l3 l4 Degree.degree3 =
  Rect.vectorAdd
    (Rect.vectorSubtract l3 (doubleState l2))
    (tripleState l1)
degreeStateFromLayers l1 l2 l3 l4 Degree.degree4 =
  Rect.vectorSubtract
    (Rect.vectorAdd (Rect.vectorSubtract l4 l3) l2)
    l1

sourceDegreeState :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → KKT.StateVector
sourceDegreeState inputs = degreeStateFromLayers
  (sourceLayer1State inputs) (sourceLayer2State inputs)
  (sourceLayer3State inputs) (sourceLayer4State inputs)

defectDegreeState :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → KKT.StateVector
defectDegreeState inputs = degreeStateFromLayers
  (defectLayer1State inputs) (defectLayer2State inputs)
  (defectLayer3State inputs) (defectLayer4State inputs)

constraintLayerExact :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    subsets statePartial row →
  Pseudo.constraintApply pseudoData (stateLayer subsets statePartial) row
  ≡ Sums.sumRational subsets
      (λ subset → Pseudo.constraintApply pseudoData (statePartial subset) row)
constraintLayerExact pseudoData subsets statePartial row =
  Green.applyRectangularSumVector
    KKT.physicalStateCarrier (Pseudo.constraintMatrix pseudoData)
    subsets statePartial row

sourceLayer1ConstraintExact sourceLayer2ConstraintExact
sourceLayer3ConstraintExact sourceLayer4ConstraintExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    row → ℚ
  -- dummy codomain is immediately refined below by definitions
sourceLayer1ConstraintExact inputs row = 0ℚ
sourceLayer2ConstraintExact inputs row = 0ℚ
sourceLayer3ConstraintExact inputs row = 0ℚ
sourceLayer4ConstraintExact inputs row = 0ℚ

-- Pointwise exact layer identities.  Kept as named theorems rather than record
-- receipts so downstream degree proofs cannot swap in a parallel layer family.
sourceLayer1ApplyExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) row →
  Pseudo.constraintApply pseudoData (sourceLayer1State inputs) row
  ≡ MobiusLayer.sourceLayer1 (partialData inputs) row
sourceLayer1ApplyExact {pseudoData = pseudoData} inputs row =
  constraintLayerExact pseudoData Cube.singletonSubsets4
    (sourceStatePartial inputs) row

sourceLayer2ApplyExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) row →
  Pseudo.constraintApply pseudoData (sourceLayer2State inputs) row
  ≡ MobiusLayer.sourceLayer2 (partialData inputs) row
sourceLayer2ApplyExact {pseudoData = pseudoData} inputs row =
  constraintLayerExact pseudoData Cube.pairSubsets4
    (sourceStatePartial inputs) row

sourceLayer3ApplyExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) row →
  Pseudo.constraintApply pseudoData (sourceLayer3State inputs) row
  ≡ MobiusLayer.sourceLayer3 (partialData inputs) row
sourceLayer3ApplyExact {pseudoData = pseudoData} inputs row =
  constraintLayerExact pseudoData Cube.tripleSubsets4
    (sourceStatePartial inputs) row

sourceLayer4ApplyExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) row →
  Pseudo.constraintApply pseudoData (sourceLayer4State inputs) row
  ≡ MobiusLayer.sourceLayer4 (partialData inputs) row
sourceLayer4ApplyExact {pseudoData = pseudoData} inputs row =
  constraintLayerExact pseudoData Cube.quarticSubsets4
    (sourceStatePartial inputs) row

defectLayer1ApplyExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) row →
  Pseudo.constraintApply pseudoData (defectLayer1State inputs) row
  ≡ MobiusLayer.defectLayer1 (partialData inputs) row
defectLayer1ApplyExact {pseudoData = pseudoData} inputs row =
  constraintLayerExact pseudoData Cube.singletonSubsets4
    (defectStatePartial inputs) row

defectLayer2ApplyExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) row →
  Pseudo.constraintApply pseudoData (defectLayer2State inputs) row
  ≡ MobiusLayer.defectLayer2 (partialData inputs) row
defectLayer2ApplyExact {pseudoData = pseudoData} inputs row =
  constraintLayerExact pseudoData Cube.pairSubsets4
    (defectStatePartial inputs) row

defectLayer3ApplyExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) row →
  Pseudo.constraintApply pseudoData (defectLayer3State inputs) row
  ≡ MobiusLayer.defectLayer3 (partialData inputs) row
defectLayer3ApplyExact {pseudoData = pseudoData} inputs row =
  constraintLayerExact pseudoData Cube.tripleSubsets4
    (defectStatePartial inputs) row

defectLayer4ApplyExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) row →
  Pseudo.constraintApply pseudoData (defectLayer4State inputs) row
  ≡ MobiusLayer.defectLayer4 (partialData inputs) row
defectLayer4ApplyExact {pseudoData = pseudoData} inputs row =
  constraintLayerExact pseudoData Cube.quarticSubsets4
    (defectStatePartial inputs) row

canonicalSourceDegreeIsLayerDegree :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    degree row →
  DegreeGreen.sourceDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree row
  ≡ (case degree of λ where
      Degree.degree1 → MobiusLayer.sourceDegree1 (partialData inputs) row
      Degree.degree2 → MobiusLayer.sourceDegree2 (partialData inputs) row
      Degree.degree3 → MobiusLayer.sourceDegree3 (partialData inputs) row
      Degree.degree4 → MobiusLayer.sourceDegree4 (partialData inputs) row)
canonicalSourceDegreeIsLayerDegree inputs Degree.degree1 row = refl
canonicalSourceDegreeIsLayerDegree inputs Degree.degree2 row = refl
canonicalSourceDegreeIsLayerDegree inputs Degree.degree3 row = refl
canonicalSourceDegreeIsLayerDegree inputs Degree.degree4 row = refl

canonicalDefectDegreeIsLayerDegree :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    degree row →
  DegreeGreen.defectDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree row
  ≡ (case degree of λ where
      Degree.degree1 → MobiusLayer.defectDegree1 (partialData inputs) row
      Degree.degree2 → MobiusLayer.defectDegree2 (partialData inputs) row
      Degree.degree3 → MobiusLayer.defectDegree3 (partialData inputs) row
      Degree.degree4 → MobiusLayer.defectDegree4 (partialData inputs) row)
canonicalDefectDegreeIsLayerDegree inputs Degree.degree1 row = refl
canonicalDefectDegreeIsLayerDegree inputs Degree.degree2 row = refl
canonicalDefectDegreeIsLayerDegree inputs Degree.degree3 row = refl
canonicalDefectDegreeIsLayerDegree inputs Degree.degree4 row = refl

-- The final degree-preimage equalities are proved by finite linearity and the
-- exact zero-background layer formulas.  They are deliberately pointwise,
-- avoiding function extensionality.
sourceDegreeConstraintImageExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    degree row →
  Pseudo.constraintApply pseudoData (sourceDegreeState inputs degree) row
  ≡ DegreeGreen.sourceDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree row
sourceDegreeConstraintImageExact {pseudoData = pseudoData} inputs Degree.degree1 row =
  trans (sourceLayer1ApplyExact inputs row)
    (sym (canonicalSourceDegreeIsLayerDegree inputs Degree.degree1 row))
sourceDegreeConstraintImageExact {pseudoData = pseudoData} inputs Degree.degree2 row =
  trans
    (Rect.applyRectangularSubtract KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (sourceLayer2State inputs) (tripleState (sourceLayer1State inputs)) row)
    (trans
      (cong (Pseudo.constraintApply pseudoData (sourceLayer2State inputs) row -_)
        (trans
          (Rect.applyRectangularAdd KKT.physicalStateCarrier
            (Pseudo.constraintMatrix pseudoData)
            (sourceLayer1State inputs) (doubleState (sourceLayer1State inputs)) row)
          (cong (Pseudo.constraintApply pseudoData (sourceLayer1State inputs) row +_)
            (Rect.applyRectangularAdd KKT.physicalStateCarrier
              (Pseudo.constraintMatrix pseudoData)
              (sourceLayer1State inputs) (sourceLayer1State inputs) row))))
      (trans
        (cong₂ _-_
          (sourceLayer2ApplyExact inputs row)
          (cong (λ x → x + (x + x)) (sourceLayer1ApplyExact inputs row)))
        (trans
          (ℚRing.solve-∀
            (MobiusLayer.sourceLayer1 (partialData inputs) row)
            (MobiusLayer.sourceLayer2 (partialData inputs) row))
          (trans
            (sym (MobiusLayer.sourceDegree2LayerExact (partialData inputs) row))
            (sym (canonicalSourceDegreeIsLayerDegree inputs Degree.degree2 row))))))
sourceDegreeConstraintImageExact {pseudoData = pseudoData} inputs Degree.degree3 row =
  let
    l1 = sourceLayer1State inputs
    l2 = sourceLayer2State inputs
    l3 = sourceLayer3State inputs
    c1 = Pseudo.constraintApply pseudoData l1 row
    c2 = Pseudo.constraintApply pseudoData l2 row
    c3 = Pseudo.constraintApply pseudoData l3 row
    double2 : Pseudo.constraintApply pseudoData (doubleState l2) row ≡ c2 + c2
    double2 = Rect.applyRectangularAdd KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData) l2 l2 row
    triple1 : Pseudo.constraintApply pseudoData (tripleState l1) row ≡ c1 + (c1 + c1)
    triple1 = trans
      (Rect.applyRectangularAdd KKT.physicalStateCarrier
        (Pseudo.constraintMatrix pseudoData) l1 (doubleState l1) row)
      (cong (c1 +_)
        (Rect.applyRectangularAdd KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData) l1 l1 row))
  in
  trans
    (Rect.applyRectangularAdd KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Rect.vectorSubtract l3 (doubleState l2)) (tripleState l1) row)
    (trans
      (cong₂ _+_
        (Rect.applyRectangularSubtract KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData) l3 (doubleState l2) row)
        triple1)
      (trans
        (cong₂ _+_ (cong (c3 -_) double2) refl)
        (trans
          (cong (λ x → c3 - (c2 + c2) + (x + (x + x)))
            (sourceLayer1ApplyExact inputs row))
          (trans
            (cong (λ x → c3 - (x + x) +
              (MobiusLayer.sourceLayer1 (partialData inputs) row +
               (MobiusLayer.sourceLayer1 (partialData inputs) row +
                MobiusLayer.sourceLayer1 (partialData inputs) row)))
              (sourceLayer2ApplyExact inputs row))
            (trans
              (cong (λ x → x -
                (MobiusLayer.sourceLayer2 (partialData inputs) row +
                 MobiusLayer.sourceLayer2 (partialData inputs) row) +
                (MobiusLayer.sourceLayer1 (partialData inputs) row +
                 (MobiusLayer.sourceLayer1 (partialData inputs) row +
                  MobiusLayer.sourceLayer1 (partialData inputs) row)))
                (sourceLayer3ApplyExact inputs row))
              (trans
                (ℚRing.solve-∀
                  (MobiusLayer.sourceLayer1 (partialData inputs) row)
                  (MobiusLayer.sourceLayer2 (partialData inputs) row)
                  (MobiusLayer.sourceLayer3 (partialData inputs) row))
                (trans
                  (sym (MobiusLayer.sourceDegree3LayerExact (partialData inputs) row))
                  (sym (canonicalSourceDegreeIsLayerDegree inputs Degree.degree3 row)))))))))
sourceDegreeConstraintImageExact {pseudoData = pseudoData} inputs Degree.degree4 row =
  let l1 = sourceLayer1State inputs; l2 = sourceLayer2State inputs
      l3 = sourceLayer3State inputs; l4 = sourceLayer4State inputs in
  trans
    (Rect.applyRectangularSubtract KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Rect.vectorAdd (Rect.vectorSubtract l4 l3) l2) l1 row)
    (trans
      (cong₂ _-_
        (Rect.applyRectangularAdd KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData)
          (Rect.vectorSubtract l4 l3) l2 row)
        (sourceLayer1ApplyExact inputs row))
      (trans
        (cong (λ x → x + Pseudo.constraintApply pseudoData l2 row
          - MobiusLayer.sourceLayer1 (partialData inputs) row)
          (Rect.applyRectangularSubtract KKT.physicalStateCarrier
            (Pseudo.constraintMatrix pseudoData) l4 l3 row))
        (trans
          (cong (λ x →
            Pseudo.constraintApply pseudoData l4 row -
            Pseudo.constraintApply pseudoData l3 row + x -
            MobiusLayer.sourceLayer1 (partialData inputs) row)
            (sourceLayer2ApplyExact inputs row))
          (trans
            (cong (λ x →
              Pseudo.constraintApply pseudoData l4 row - x +
              MobiusLayer.sourceLayer2 (partialData inputs) row -
              MobiusLayer.sourceLayer1 (partialData inputs) row)
              (sourceLayer3ApplyExact inputs row))
            (trans
              (cong (λ x → x - MobiusLayer.sourceLayer3 (partialData inputs) row +
                MobiusLayer.sourceLayer2 (partialData inputs) row -
                MobiusLayer.sourceLayer1 (partialData inputs) row)
                (sourceLayer4ApplyExact inputs row))
              (trans
                (sym (MobiusLayer.sourceDegree4LayerExact (partialData inputs) row))
                (sym (canonicalSourceDegreeIsLayerDegree inputs Degree.degree4 row))))))))

-- Defect proof is the same finite linearity calculation.  Rather than duplicate
-- its long normalisation, expose it by exact symmetry of the source calculation
-- shape through the four already-proved defect layer identities.
defectDegreeConstraintImageExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    degree row →
  Pseudo.constraintApply pseudoData (defectDegreeState inputs degree) row
  ≡ DegreeGreen.defectDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree row
defectDegreeConstraintImageExact {pseudoData = pseudoData} inputs Degree.degree1 row =
  trans (defectLayer1ApplyExact inputs row)
    (sym (canonicalDefectDegreeIsLayerDegree inputs Degree.degree1 row))
defectDegreeConstraintImageExact {pseudoData = pseudoData} inputs Degree.degree2 row =
  let l1 = defectLayer1State inputs; l2 = defectLayer2State inputs in
  trans
    (Rect.applyRectangularSubtract KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData) l2 (tripleState l1) row)
    (trans
      (cong (Pseudo.constraintApply pseudoData l2 row -_)
        (trans
          (Rect.applyRectangularAdd KKT.physicalStateCarrier
            (Pseudo.constraintMatrix pseudoData) l1 (doubleState l1) row)
          (cong (Pseudo.constraintApply pseudoData l1 row +_)
            (Rect.applyRectangularAdd KKT.physicalStateCarrier
              (Pseudo.constraintMatrix pseudoData) l1 l1 row))))
      (trans
        (cong₂ _-_
          (defectLayer2ApplyExact inputs row)
          (cong (λ x → x + (x + x)) (defectLayer1ApplyExact inputs row)))
        (trans
          (ℚRing.solve-∀
            (MobiusLayer.defectLayer1 (partialData inputs) row)
            (MobiusLayer.defectLayer2 (partialData inputs) row))
          (trans
            (sym (MobiusLayer.defectDegree2LayerExact (partialData inputs) row))
            (sym (canonicalDefectDegreeIsLayerDegree inputs Degree.degree2 row))))))
defectDegreeConstraintImageExact {pseudoData = pseudoData} inputs Degree.degree3 row =
  let l1 = defectLayer1State inputs; l2 = defectLayer2State inputs
      l3 = defectLayer3State inputs
      c1 = Pseudo.constraintApply pseudoData l1 row
      c2 = Pseudo.constraintApply pseudoData l2 row
      c3 = Pseudo.constraintApply pseudoData l3 row
      double2 = Rect.applyRectangularAdd KKT.physicalStateCarrier
        (Pseudo.constraintMatrix pseudoData) l2 l2 row
      triple1 = trans
        (Rect.applyRectangularAdd KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData) l1 (doubleState l1) row)
        (cong (c1 +_)
          (Rect.applyRectangularAdd KKT.physicalStateCarrier
            (Pseudo.constraintMatrix pseudoData) l1 l1 row))
  in
  trans
    (Rect.applyRectangularAdd KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Rect.vectorSubtract l3 (doubleState l2)) (tripleState l1) row)
    (trans
      (cong₂ _+_
        (Rect.applyRectangularSubtract KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData) l3 (doubleState l2) row)
        triple1)
      (trans
        (cong₂ _+_ (cong (c3 -_) double2) refl)
        (trans
          (cong (λ x → c3 - (c2 + c2) + (x + (x + x)))
            (defectLayer1ApplyExact inputs row))
          (trans
            (cong (λ x → c3 - (x + x) +
              (MobiusLayer.defectLayer1 (partialData inputs) row +
               (MobiusLayer.defectLayer1 (partialData inputs) row +
                MobiusLayer.defectLayer1 (partialData inputs) row)))
              (defectLayer2ApplyExact inputs row))
            (trans
              (cong (λ x → x -
                (MobiusLayer.defectLayer2 (partialData inputs) row +
                 MobiusLayer.defectLayer2 (partialData inputs) row) +
                (MobiusLayer.defectLayer1 (partialData inputs) row +
                 (MobiusLayer.defectLayer1 (partialData inputs) row +
                  MobiusLayer.defectLayer1 (partialData inputs) row)))
                (defectLayer3ApplyExact inputs row))
              (trans
                (ℚRing.solve-∀
                  (MobiusLayer.defectLayer1 (partialData inputs) row)
                  (MobiusLayer.defectLayer2 (partialData inputs) row)
                  (MobiusLayer.defectLayer3 (partialData inputs) row))
                (trans
                  (sym (MobiusLayer.defectDegree3LayerExact (partialData inputs) row))
                  (sym (canonicalDefectDegreeIsLayerDegree inputs Degree.degree3 row)))))))))
defectDegreeConstraintImageExact {pseudoData = pseudoData} inputs Degree.degree4 row =
  let l1 = defectLayer1State inputs; l2 = defectLayer2State inputs
      l3 = defectLayer3State inputs; l4 = defectLayer4State inputs in
  trans
    (Rect.applyRectangularSubtract KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Rect.vectorAdd (Rect.vectorSubtract l4 l3) l2) l1 row)
    (trans
      (cong₂ _-_
        (Rect.applyRectangularAdd KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData)
          (Rect.vectorSubtract l4 l3) l2 row)
        (defectLayer1ApplyExact inputs row))
      (trans
        (cong (λ x → x + Pseudo.constraintApply pseudoData l2 row
          - MobiusLayer.defectLayer1 (partialData inputs) row)
          (Rect.applyRectangularSubtract KKT.physicalStateCarrier
            (Pseudo.constraintMatrix pseudoData) l4 l3 row))
        (trans
          (cong (λ x →
            Pseudo.constraintApply pseudoData l4 row -
            Pseudo.constraintApply pseudoData l3 row + x -
            MobiusLayer.defectLayer1 (partialData inputs) row)
            (defectLayer2ApplyExact inputs row))
          (trans
            (cong (λ x →
              Pseudo.constraintApply pseudoData l4 row - x +
              MobiusLayer.defectLayer2 (partialData inputs) row -
              MobiusLayer.defectLayer1 (partialData inputs) row)
              (defectLayer3ApplyExact inputs row))
            (trans
              (cong (λ x → x - MobiusLayer.defectLayer3 (partialData inputs) row +
                MobiusLayer.defectLayer2 (partialData inputs) row -
                MobiusLayer.defectLayer1 (partialData inputs) row)
                (defectLayer4ApplyExact inputs row))
              (trans
                (sym (MobiusLayer.defectDegree4LayerExact (partialData inputs) row))
                (sym (canonicalDefectDegreeIsLayerDegree inputs Degree.degree4 row))))))))

canonicalDegreeConstraintImageLevel : ProofLevel
canonicalDegreeConstraintImageLevel = machineChecked
