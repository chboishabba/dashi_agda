module DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockCombesThomasConstantsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Name every scalar entering the complete saddle-block tilt.  The perturbation
-- is the sum of the Hessian, adjoint-constraint and constraint blocks.  Its
-- Neumann parameter is therefore
--
--   C_K (S_H + S_L* + S_L),
--
-- not an unnamed operator norm.  A half-contraction certificate gives the
-- explicit tilted inverse majorant 2 C_K.  The final theorem untwists a bounded
-- tilted Green entry to a geometric off-diagonal bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT

oneHalf : ℚ
oneHalf = + 1 / 2

record SelectedKKTCombesThomasConstants : Set where
  field
    selectedKKTInverseNormUpper : ℚ
    selectedKKTWeightedHessianRowMass : ℚ
    selectedKKTWeightedAdjointRowMass : ℚ
    selectedKKTWeightedConstraintRowMass : ℚ
    selectedKKTInteractionRange : ℚ
    selectedKKTAdmissibleTilt : ℚ

    inverseNormNonnegative : 0ℚ ≤ selectedKKTInverseNormUpper
    hessianMassNonnegative : 0ℚ ≤ selectedKKTWeightedHessianRowMass
    adjointMassNonnegative : 0ℚ ≤ selectedKKTWeightedAdjointRowMass
    constraintMassNonnegative : 0ℚ ≤ selectedKKTWeightedConstraintRowMass
    interactionRangeNonnegative : 0ℚ ≤ selectedKKTInteractionRange
    admissibleTiltNonnegative : 0ℚ ≤ selectedKKTAdmissibleTilt

    selectedKKTCombesThomasSmallness :
      selectedKKTInverseNormUpper
      * (selectedKKTWeightedHessianRowMass
        + selectedKKTWeightedAdjointRowMass
        + selectedKKTWeightedConstraintRowMass)
      ≤ oneHalf

open SelectedKKTCombesThomasConstants public

selectedKKTWeightedRowMass :
  SelectedKKTCombesThomasConstants → ℚ
selectedKKTWeightedRowMass constants =
  selectedKKTWeightedHessianRowMass constants
  + selectedKKTWeightedAdjointRowMass constants
  + selectedKKTWeightedConstraintRowMass constants

selectedKKTWeightedRowMassNonnegative : ∀ constants →
  0ℚ ≤ selectedKKTWeightedRowMass constants
selectedKKTWeightedRowMassNonnegative constants =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (hessianMassNonnegative constants)
      (adjointMassNonnegative constants))
    (constraintMassNonnegative constants)

selectedKKTNeumannParameter :
  SelectedKKTCombesThomasConstants → ℚ
selectedKKTNeumannParameter constants =
  selectedKKTInverseNormUpper constants
  * selectedKKTWeightedRowMass constants

selectedKKTNeumannParameterBelowHalf : ∀ constants →
  selectedKKTNeumannParameter constants ≤ oneHalf
selectedKKTNeumannParameterBelowHalf =
  selectedKKTCombesThomasSmallness

selectedKKTTiltedInverseMajorant :
  SelectedKKTCombesThomasConstants → ℚ
selectedKKTTiltedInverseMajorant constants =
  (+ 2 / 1) * selectedKKTInverseNormUpper constants

selectedKKTTiltedInverseMajorantNonnegative : ∀ constants →
  0ℚ ≤ selectedKKTTiltedInverseMajorant constants
selectedKKTTiltedInverseMajorantNonnegative constants =
  let
    twoNonnegative : 0ℚ ≤ (+ 2 / 1)
    twoNonnegative = ℚP.nonNegative⁻¹ (+ 2 / 1)
  in
  ℚP.*-mono-≤ twoNonnegative (inverseNormNonnegative constants)

record ThreeBlockTiltEstimate
    (constants : SelectedKKTCombesThomasConstants)
    (hessian adjoint constraint : ℚ) : Set where
  field
    hessianUpper :
      hessian ≤ selectedKKTWeightedHessianRowMass constants
    adjointUpper :
      adjoint ≤ selectedKKTWeightedAdjointRowMass constants
    constraintUpper :
      constraint ≤ selectedKKTWeightedConstraintRowMass constants
open ThreeBlockTiltEstimate public

threeBlockTiltMassUpper :
  ∀ {constants hessian adjoint constraint} →
  ThreeBlockTiltEstimate constants hessian adjoint constraint →
  hessian + adjoint + constraint
  ≤ selectedKKTWeightedRowMass constants
threeBlockTiltMassUpper estimate =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (hessianUpper estimate)
      (adjointUpper estimate))
    (constraintUpper estimate)

threeBlockNeumannParameterBelowHalf :
  ∀ {constants hessian adjoint constraint} →
  ThreeBlockTiltEstimate constants hessian adjoint constraint →
  0ℚ ≤ selectedKKTInverseNormUpper constants →
  selectedKKTInverseNormUpper constants
    * (hessian + adjoint + constraint)
  ≤ oneHalf
threeBlockNeumannParameterBelowHalf
    {constants} estimate inverseNonnegative =
  let
    instance
      inverseNN : ℚ.NonNegative
        (selectedKKTInverseNormUpper constants)
      inverseNN = ℚ.nonNegative inverseNonnegative
  in
  ℚP.≤-trans
    (ℚP.*-monoˡ-≤-nonNeg
      (selectedKKTInverseNormUpper constants)
      (threeBlockTiltMassUpper estimate))
    (selectedKKTCombesThomasSmallness constants)

record SelectedKKTKernelDecayData
    {Site : Set}
    (constants : SelectedKKTCombesThomasConstants)
    (green : CT.Matrix Site)
    (root target : Site) : Set₁ where
  field
    weight inverseWeight : Site → ℚ
    weightInverseLaw : ∀ site →
      inverseWeight site * weight site ≡ 1ℚ
    rootInverseWeightOne : inverseWeight root ≡ 1ℚ
    targetWeightNonnegative : 0ℚ ≤ weight target
    targetWeightAbsolute : ∣ weight target ∣ ≡ weight target

    tiltedKKTGreenEntryUpper :
      ∣ CT.diagonalConjugate weight inverseWeight green root target ∣
      ≤ selectedKKTTiltedInverseMajorant constants
open SelectedKKTKernelDecayData public

selectedKKTCombesThomasDecay :
  ∀ {Site}
    (constants : SelectedKKTCombesThomasConstants)
    (green : CT.Matrix Site)
    root target →
  SelectedKKTKernelDecayData constants green root target →
  ∣ green root target ∣
  ≤ selectedKKTTiltedInverseMajorant constants
      * weight _ target
selectedKKTCombesThomasDecay constants green root target data =
  CT.combesThomasKernelDecayFromTiltedEntry
    (weight data)
    (inverseWeight data)
    (weightInverseLaw data)
    green root target
    (selectedKKTTiltedInverseMajorant constants)
    (rootInverseWeightOne data)
    (targetWeightNonnegative data)
    (targetWeightAbsolute data)
    (tiltedKKTGreenEntryUpper data)

record FullBlockFiniteRange
    {Site : Set}
    (kernel : CT.Matrix Site)
    (constants : SelectedKKTCombesThomasConstants) : Set₁ where
  field
    distance : Site → Site → ℚ
    outsideInteractionRangeZero : ∀ left right →
      selectedKKTInteractionRange constants < distance left right →
      kernel left right ≡ 0ℚ
open FullBlockFiniteRange public

selectedKKTInteractionRangeExact :
  ∀ {Site kernel constants}
    (finiteRange : FullBlockFiniteRange {Site} kernel constants)
    left right →
  selectedKKTInteractionRange constants < distance finiteRange left right →
  kernel left right ≡ 0ℚ
selectedKKTInteractionRangeExact = outsideInteractionRangeZero

fullBlockKKTCombesThomasConstantsLevel : ProofLevel
fullBlockKKTCombesThomasConstantsLevel = machineChecked

fullBlockKKTThreePieceSmallnessLevel : ProofLevel
fullBlockKKTThreePieceSmallnessLevel = machineChecked

fullBlockKKTDecayExtractionLevel : ProofLevel
fullBlockKKTDecayExtractionLevel = machineChecked

selectedPhysicalKKTConstantsProducerLevel : ProofLevel
selectedPhysicalKKTConstantsProducerLevel = conditional
