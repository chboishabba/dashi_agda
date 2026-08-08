module DASHI.Physics.YangMills.YangMillsCompactSimpleGroupPromotionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Anthony W. Knapp,
-- "Lie Groups Beyond an Introduction".
-- DOI: 10.1007/978-1-4757-2453-0.
--
-- N. Bourbaki,
-- "Lie Groups and Lie Algebras, Chapters 4--6".
-- ISBN: 978-3-540-69171-6.  No DOI is assigned on the cited edition page.
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay problem description.
-- No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Make Gate VII fail closed.  An SU(N)-parameterised proof does not cover the
-- B, C, D or exceptional families merely by renaming N.  Every compact-simple
-- instance must carry group-specific geometric and analytic constants.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)

data DynkinFamily : Set where
  familyA familyB familyC familyD : Nat → DynkinFamily
  exceptionalG2 exceptionalF4 exceptionalE6 exceptionalE7 exceptionalE8 :
    DynkinFamily

data CoverageStrength : Set where
  oneSU2Instance : CoverageStrength
  oneSU3Instance : CoverageStrength
  allSUNInstances : CoverageStrength
  allClassicalFamilies : CoverageStrength
  allCompactSimpleGroups : CoverageStrength

data RequiredGroupDatum : Set where
  rootDatum : RequiredGroupDatum
  compactRealForm : RequiredGroupDatum
  normalizedInvariantInnerProduct : RequiredGroupDatum
  faithfulUnitaryRepresentation : RequiredGroupDatum
  haarProbabilityMeasure : RequiredGroupDatum
  adjointCasimir : RequiredGroupDatum
  dualCoxeterNumber : RequiredGroupDatum
  injectivityRadius : RequiredGroupDatum
  structureConstantNormBound : RequiredGroupDatum
  ricciLowerBound : RequiredGroupDatum
  characterHeatKernelBounds : RequiredGroupDatum
  bchPrincipalLogRadius : RequiredGroupDatum

requiredGroupData : List RequiredGroupDatum
requiredGroupData =
  rootDatum
  ∷ compactRealForm
  ∷ normalizedInvariantInnerProduct
  ∷ faithfulUnitaryRepresentation
  ∷ haarProbabilityMeasure
  ∷ adjointCasimir
  ∷ dualCoxeterNumber
  ∷ injectivityRadius
  ∷ structureConstantNormBound
  ∷ ricciLowerBound
  ∷ characterHeatKernelBounds
  ∷ bchPrincipalLogRadius
  ∷ []

requiredGroupDatumCountExact : length requiredGroupData ≡ 12
requiredGroupDatumCountExact = refl

exceptionalFamilies : List DynkinFamily
exceptionalFamilies =
  exceptionalG2
  ∷ exceptionalF4
  ∷ exceptionalE6
  ∷ exceptionalE7
  ∷ exceptionalE8
  ∷ []

exceptionalFamilyCountExact : length exceptionalFamilies ≡ 5
exceptionalFamilyCountExact = refl

-- Standard dual Coxeter numbers in the long-root-squared-equals-two
-- normalization.  The table is data, not yet a proof of any analytic bound.
dualCoxeterExceptional : DynkinFamily → Nat
dualCoxeterExceptional exceptionalG2 = 4
dualCoxeterExceptional exceptionalF4 = 9
dualCoxeterExceptional exceptionalE6 = 12
dualCoxeterExceptional exceptionalE7 = 18
dualCoxeterExceptional exceptionalE8 = 30
dualCoxeterExceptional (familyA n) = n
dualCoxeterExceptional (familyB n) = n
dualCoxeterExceptional (familyC n) = n
dualCoxeterExceptional (familyD n) = n

g2DualCoxeterExact : dualCoxeterExceptional exceptionalG2 ≡ 4
g2DualCoxeterExact = refl

f4DualCoxeterExact : dualCoxeterExceptional exceptionalF4 ≡ 9
f4DualCoxeterExact = refl

e6DualCoxeterExact : dualCoxeterExceptional exceptionalE6 ≡ 12
e6DualCoxeterExact = refl

e7DualCoxeterExact : dualCoxeterExceptional exceptionalE7 ≡ 18
e7DualCoxeterExact = refl

e8DualCoxeterExact : dualCoxeterExceptional exceptionalE8 ≡ 30
e8DualCoxeterExact = refl

record CompactSimpleYMData (Group : Set) : Set₁ where
  field
    family : DynkinFamily

    RootDatum : Set
    CompactRealForm : Set
    InvariantInnerProduct : Set
    FaithfulUnitaryRepresentation : Set
    HaarProbabilityMeasure : Set
    AdjointCasimirConstant : Set
    DualCoxeterConstant : Set
    InjectivityRadiusConstant : Set
    StructureConstantBound : Set
    RicciLowerBoundConstant : Set
    CharacterHeatKernelBound : Set
    BCHPrincipalLogRadius : Set

    rootDatumWitness : RootDatum
    compactRealFormWitness : CompactRealForm
    invariantInnerProductWitness : InvariantInnerProduct
    faithfulRepresentationWitness : FaithfulUnitaryRepresentation
    haarProbabilityWitness : HaarProbabilityMeasure
    adjointCasimirWitness : AdjointCasimirConstant
    dualCoxeterWitness : DualCoxeterConstant
    injectivityRadiusWitness : InjectivityRadiusConstant
    structureConstantWitness : StructureConstantBound
    ricciLowerWitness : RicciLowerBoundConstant
    characterHeatKernelWitness : CharacterHeatKernelBound
    bchPrincipalLogWitness : BCHPrincipalLogRadius

open CompactSimpleYMData public

su2IsNotAllSUN : oneSU2Instance ≡ allSUNInstances → ⊥
su2IsNotAllSUN ()

su3IsNotAllSUN : oneSU3Instance ≡ allSUNInstances → ⊥
su3IsNotAllSUN ()

sunIsNotAllClassical : allSUNInstances ≡ allClassicalFamilies → ⊥
sunIsNotAllClassical ()

sunIsNotAllCompactSimple :
  allSUNInstances ≡ allCompactSimpleGroups → ⊥
sunIsNotAllCompactSimple ()

classicalIsNotAllCompactSimple :
  allClassicalFamilies ≡ allCompactSimpleGroups → ⊥
classicalIsNotAllCompactSimple ()

exceptionalG2IsNotAType :
  exceptionalG2 ≡ familyA 2 → ⊥
exceptionalG2IsNotAType ()

exceptionalE8IsNotAType :
  exceptionalE8 ≡ familyA 8 → ⊥
exceptionalE8IsNotAType ()

record GroupUniformProofFamily : Set₁ where
  field
    Group : Set
    compactSimpleData : Group → CompactSimpleYMData Group
    PhysicalConstruction : Group → Set
    construction : (group : Group) → PhysicalConstruction group

-- No inhabitant is manufactured from an SU(N)-only theorem.
