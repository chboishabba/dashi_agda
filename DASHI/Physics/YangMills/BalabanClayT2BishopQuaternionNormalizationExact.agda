module DASHI.Physics.YangMills.BalabanClayT2BishopQuaternionNormalizationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_)
open import Data.Rational using (ℚ; _/_)

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Series
import DASHI.Physics.YangMills.BalabanClayT2GeneratedQuaternionJetExact as Jet
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact exponential/logarithm normalization for the generated quaternion jet.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- BSc Honours thesis, Dalhousie University, April 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Hall fixes the SU(2)/quaternion formulas.  Bishop supplies the constructive
-- real completion used for the sine/cosine and local logarithm series.  DASHI's
-- generated polynomial jet and coefficient audit remain independent finite data.
------------------------------------------------------------------------

record Vec3B : Set where
  constructor vec3B
  field
    x y z : Bishop.Bishopℝ

open Vec3B public

record QuaternionB : Set where
  constructor quaternionB
  field
    scalar : Bishop.Bishopℝ
    vector : Vec3B

open QuaternionB public

addB : Bishop.Bishopℝ → Bishop.Bishopℝ → Bishop.Bishopℝ
addB = Bishop.bishopAdd

subB : Bishop.Bishopℝ → Bishop.Bishopℝ → Bishop.Bishopℝ
subB = Bishop.bishopSub

mulB : Bishop.Bishopℝ → Bishop.Bishopℝ → Bishop.Bishopℝ
mulB = Bishop.bishopMul

negB : Bishop.Bishopℝ → Bishop.Bishopℝ
negB = Bishop.bishopNeg

addVecB : Vec3B → Vec3B → Vec3B
addVecB (vec3B ax ay az) (vec3B bx by bz) =
  vec3B (addB ax bx) (addB ay by) (addB az bz)

negVecB : Vec3B → Vec3B
negVecB (vec3B ax ay az) = vec3B (negB ax) (negB ay) (negB az)

scaleVecB : Bishop.Bishopℝ → Vec3B → Vec3B
scaleVecB coefficient (vec3B ax ay az) =
  vec3B (mulB coefficient ax) (mulB coefficient ay) (mulB coefficient az)

dotB : Vec3B → Vec3B → Bishop.Bishopℝ
dotB (vec3B ax ay az) (vec3B bx by bz) =
  addB (mulB ax bx) (addB (mulB ay by) (mulB az bz))

crossB : Vec3B → Vec3B → Vec3B
crossB (vec3B ax ay az) (vec3B bx by bz) = vec3B
  (subB (mulB ay bz) (mulB az by))
  (subB (mulB az bx) (mulB ax bz))
  (subB (mulB ax by) (mulB ay bx))

multiplyQuaternionB : QuaternionB → QuaternionB → QuaternionB
multiplyQuaternionB left right = quaternionB
  (subB
    (mulB (scalar left) (scalar right))
    (dotB (vector left) (vector right)))
  (addVecB
    (scaleVecB (scalar left) (vector right))
    (addVecB
      (scaleVecB (scalar right) (vector left))
      (crossB (vector left) (vector right))))

inverseQuaternionB : QuaternionB → QuaternionB
inverseQuaternionB value = quaternionB (scalar value) (negVecB (vector value))

fourProductB : QuaternionB → QuaternionB → QuaternionB → QuaternionB → QuaternionB
fourProductB q0 q1 q2 q3 =
  multiplyQuaternionB
    (multiplyQuaternionB (multiplyQuaternionB q0 q1) (inverseQuaternionB q2))
    (inverseQuaternionB q3)

fourProductDefinitionExact : ∀ q0 q1 q2 q3 →
  fourProductB q0 q1 q2 q3
  ≡ multiplyQuaternionB
      (multiplyQuaternionB (multiplyQuaternionB q0 q1) (inverseQuaternionB q2))
      (inverseQuaternionB q3)
fourProductDefinitionExact q0 q1 q2 q3 = refl

scalarQuarticBound vectorCubicBound : ℚ
scalarQuarticBound = + 1 / 384
vectorCubicBound = + 1 / 48

record BishopSU2ExponentialJetData
    (series : Series.BishopElementaryPowerSeriesData) : Set₁ where
  field
    norm : Vec3B → Bishop.Bishopℝ
    half : Bishop.Bishopℝ
    oneEighth : Bishop.Bishopℝ

    sincHalf : Vec3B → Bishop.Bishopℝ
    sincHalfDefinition : ∀ value → Set

    exactLinkExponential : Vec3B → QuaternionB
    secondOrderLinkJet : Vec3B → QuaternionB

    exactLinkExponentialCoordinates : ∀ value →
      exactLinkExponential value
      ≡ quaternionB
          (Series.bishopCos series (mulB half (norm value)))
          (scaleVecB (mulB half (sincHalf value)) value)

    secondOrderJetCoordinates : ∀ value → Set

    scalarJetRemainder : Vec3B → Bishop.Bishopℝ
    vectorJetRemainder : Vec3B → Vec3B

    scalarRemainderDefinition : ∀ value → Set
    vectorRemainderDefinition : ∀ value → Set

    scalarRemainderQuarticBound : ∀ value → Set
    vectorRemainderCubicBound : ∀ value → Set

    exactLinkUnitNorm : ∀ value → Set
    secondOrderJetNormBound : ∀ value → Set

open BishopSU2ExponentialJetData public

record BishopQuaternionLogData
    (series : Series.BishopElementaryPowerSeriesData) : Set₁ where
  field
    InLogChart : QuaternionB → Set
    vectorNorm : Vec3B → Bishop.Bishopℝ
    arcsinOverX : Bishop.Bishopℝ → Bishop.Bishopℝ

    quaternionLog : QuaternionB → Vec3B
    quaternionLogVectorFormulaExact : ∀ quaternion →
      InLogChart quaternion → Set

    arcsinOverXSeriesTerms : Bishop.Bishopℝ → Nat → Bishop.Bishopℝ
    arcsinOverXAbsoluteConvergence : ∀ point → Set
    arcsinOverXDefinedByBishopLimit : ∀ point → Set
    arcsinOverXQuadraticRemainder : ∀ point → Set

open BishopQuaternionLogData public

record GeneratedQuaternionNormalizationData
    (series : Series.BishopElementaryPowerSeriesData)
    (exponentialData : BishopSU2ExponentialJetData series)
    (logData : BishopQuaternionLogData series)
    (Plaquette Block : Set) : Set₁ where
  field
    linkCoordinate : Plaquette → Jet.Link4 → Vec3B

    exactPlaquetteQuaternion : Plaquette → QuaternionB
    jetPlaquetteQuaternion : Plaquette → QuaternionB

    exactPlaquetteDefinition : ∀ plaquette →
      exactPlaquetteQuaternion plaquette
      ≡ fourProductB
          (exactLinkExponential exponentialData (linkCoordinate plaquette Jet.link0))
          (exactLinkExponential exponentialData (linkCoordinate plaquette Jet.link1))
          (exactLinkExponential exponentialData (linkCoordinate plaquette Jet.link2))
          (exactLinkExponential exponentialData (linkCoordinate plaquette Jet.link3))

    jetPlaquetteDefinition : ∀ plaquette →
      jetPlaquetteQuaternion plaquette
      ≡ fourProductB
          (secondOrderLinkJet exponentialData (linkCoordinate plaquette Jet.link0))
          (secondOrderLinkJet exponentialData (linkCoordinate plaquette Jet.link1))
          (secondOrderLinkJet exponentialData (linkCoordinate plaquette Jet.link2))
          (secondOrderLinkJet exponentialData (linkCoordinate plaquette Jet.link3))

    quaternionProductPerturbationTelescoping : ∀ plaquette → Set
    fourLinkExactMinusJetProductCubic : ∀ plaquette → Set

    exactPlaquetteLog : Plaquette → Vec3B
    exactPlaquetteLogDefinition : ∀ plaquette → Set
    exactQuaternionLogMinusJetCubic : ∀ plaquette → Set

    plaquetteCurl : Plaquette → Vec3B
    plaquetteQuadraticCommutator : Plaquette → Vec3B
    generatedDegreeOneEqualsPlaquetteCurl : ∀ plaquette → Set
    generatedDegreeTwoEqualsHalfBracketSum : ∀ plaquette → Set
    linearCurlAndQuadraticCommutatorAreRemovedExactly : ∀ plaquette → Set

    chargedPlaquettes : Block → List Plaquette
    chargedPlaquettesCountAtMost96 : ∀ block → length (chargedPlaquettes block) ≤ 96
    configuredPlaquetteChargeIncludesCollars : Set

    scalarEnumerationExact :
      Jet.coefficientL1 Jet.scalarCubicTerms
      ≡ Jet.generatedScalarCoefficientL1
    vector0EnumerationExact :
      Jet.coefficientL1 Jet.vector0CubicTerms
      ≡ Jet.generatedVectorCoefficientL1
    vector1EnumerationExact :
      Jet.coefficientL1 Jet.vector1CubicTerms
      ≡ Jet.generatedVectorCoefficientL1
    vector2EnumerationExact :
      Jet.coefficientL1 Jet.vector2CubicTerms
      ≡ Jet.generatedVectorCoefficientL1

open GeneratedQuaternionNormalizationData public

asGeneratedQuaternionJetAudit :
  ∀ {series exponentialData logData Plaquette Block} →
  GeneratedQuaternionNormalizationData
    series exponentialData logData Plaquette Block →
  Jet.GeneratedQuaternionJetAudit
asGeneratedQuaternionJetAudit dataSet = record
  { scalarEnumerationExact = scalarEnumerationExact dataSet
  ; vector0EnumerationExact = vector0EnumerationExact dataSet
  ; vector1EnumerationExact = vector1EnumerationExact dataSet
  ; vector2EnumerationExact = vector2EnumerationExact dataSet
  ; exactExponentialMinusSecondOrderJetCubic =
      ∀ plaquette → fourLinkExactMinusJetProductCubic dataSet plaquette
  ; exactQuaternionLogMinusJetCubic =
      ∀ plaquette → exactQuaternionLogMinusJetCubic dataSet plaquette
  ; linearCurlAndQuadraticCommutatorAreRemovedExactly =
      ∀ plaquette →
        linearCurlAndQuadraticCommutatorAreRemovedExactly dataSet plaquette
  ; configuredPlaquetteChargeIncludesCollars =
      configuredPlaquetteChargeIncludesCollars dataSet
  }

bishopQuaternionAlgebraLevel : ProofLevel
bishopQuaternionAlgebraLevel = machineChecked

bishopQuaternionJetFormulaLevel : ProofLevel
bishopQuaternionJetFormulaLevel = machineChecked

bishopQuaternionTranscendentalTailInputsLevel : ProofLevel
bishopQuaternionTranscendentalTailInputsLevel = conditional

quaternionCollarCountingInputsLevel : ProofLevel
quaternionCollarCountingInputsLevel = conditional
