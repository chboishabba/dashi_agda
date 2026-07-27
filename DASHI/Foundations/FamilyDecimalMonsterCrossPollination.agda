module DASHI.Foundations.FamilyDecimalMonsterCrossPollination where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Moonshine.MonsterCharacterTableExact as MCT
import DASHI.TrackedPrimes as TP
import JFixedPoint as J
import Ontology.GodelLattice as Lattice

------------------------------------------------------------------------
-- A three-role family chart: two support roles and one dependent role.
--
-- This is a dependency/fibre grammar. It does not assign real mortality rates,
-- presume family structure, or claim statistical independence.
------------------------------------------------------------------------

data FamilyRole : Set where
  parentRoleA : FamilyRole
  parentRoleB : FamilyRole
  childRole : FamilyRole

familyRoleCount : Nat
familyRoleCount = 3

parentSupportCount : Nat
parentSupportCount = 2

dependentChildCount : Nat
dependentChildCount = 1

twoSupportsPlusOneDependent :
  parentSupportCount + dependentChildCount ≡ familyRoleCount
twoSupportsPlusOneDependent = refl

record OneThirdRiskChartAssumptions : Set where
  field
    exactlyOneRoleSelected : Bool
    rolesEquiprobable : Bool
    eventsIndependent : Bool
    empiricalCalibrationSupplied : Bool

canonicalOneThirdRiskChartAssumptions :
  OneThirdRiskChartAssumptions
canonicalOneThirdRiskChartAssumptions = record
  { exactlyOneRoleSelected = true
  ; rolesEquiprobable = true
  ; eventsIndependent = false
  ; empiricalCalibrationSupplied = false
  }

record ThreeRoleSupportFibre : Set₁ where
  field
    SupportRole : Set
    DependentRole : Set
    firstSupport : SupportRole
    secondSupport : SupportRole
    dependent : DependentRole
    supportCount : Nat
    dependentCount : Nat
    totalRoleCount : Nat
    countLaw :
      supportCount + dependentCount ≡ totalRoleCount
    modelTracksBothSupportsThroughAdolescence : Bool
    actualOutcomeProbabilityClaimed : Bool
    universalFamilyFormClaimed : Bool

canonicalTwoParentOneChildSupportFibre : ThreeRoleSupportFibre
canonicalTwoParentOneChildSupportFibre = record
  { SupportRole = FamilyRole
  ; DependentRole = FamilyRole
  ; firstSupport = parentRoleA
  ; secondSupport = parentRoleB
  ; dependent = childRole
  ; supportCount = parentSupportCount
  ; dependentCount = dependentChildCount
  ; totalRoleCount = familyRoleCount
  ; countLaw = twoSupportsPlusOneDependent
  ; modelTracksBothSupportsThroughAdolescence = true
  ; actualOutcomeProbabilityClaimed = false
  ; universalFamilyFormClaimed = false
  }

record OneThirdRoleWeight : Set where
  field
    numerator : Nat
    denominator : Nat
    numeratorIsOne : numerator ≡ 1
    denominatorIsThree : denominator ≡ 3
    conditionalOnAssumptions : OneThirdRiskChartAssumptions
    empiricalRiskClaimed : Bool

canonicalOneThirdRoleWeight : OneThirdRoleWeight
canonicalOneThirdRoleWeight = record
  { numerator = 1
  ; denominator = 3
  ; numeratorIsOne = refl
  ; denominatorIsThree = refl
  ; conditionalOnAssumptions = canonicalOneThirdRiskChartAssumptions
  ; empiricalRiskClaimed = false
  }

------------------------------------------------------------------------
-- Decimal 3.57 as display address, statistical feature and symbolic cylinder.
------------------------------------------------------------------------

data DecimalAddressUse : Set where
  labelDecompositionUse : DecimalAddressUse
  statisticalFeatureUse : DecimalAddressUse
  symbolicCylinderUse : DecimalAddressUse
  stageLensUse : DecimalAddressUse

record Decimal357Address : Set where
  field
    integerDigit : Nat
    firstFractionalDigit : Nat
    secondFractionalDigit : Nat
    numerator : Nat
    denominator : Nat
    exactRationalEvaluation :
      numerator ≡ 357
    exactScale :
      denominator ≡ 100
    exactPlaceValue :
      numerator
      ≡ integerDigit * 100
        + firstFractionalDigit * 10
        + secondFractionalDigit
    stageInteger : Atlas.StageAtlasZeroToEleven
    stageFirstFractional : Atlas.StageAtlasZeroToEleven
    stageSecondFractional : Atlas.StageAtlasZeroToEleven
    uses : List DecimalAddressUse
    decimalDigitsArePAdicDigits : Bool
    stageLensIsInterpretive : Bool
    statisticalPredictivenessProved : Bool
    symbolicCylinderAvailable : Bool

canonicalDecimal357Address : Decimal357Address
canonicalDecimal357Address = record
  { integerDigit = 3
  ; firstFractionalDigit = 5
  ; secondFractionalDigit = 7
  ; numerator = 357
  ; denominator = 100
  ; exactRationalEvaluation = refl
  ; exactScale = refl
  ; exactPlaceValue = refl
  ; stageInteger = Atlas.atlas-3
  ; stageFirstFractional = Atlas.atlas-5
  ; stageSecondFractional = Atlas.atlas-7
  ; uses =
      labelDecompositionUse
      ∷ statisticalFeatureUse
      ∷ symbolicCylinderUse
      ∷ stageLensUse
      ∷ []
  ; decimalDigitsArePAdicDigits = false
  ; stageLensIsInterpretive = true
  ; statisticalPredictivenessProved = false
  ; symbolicCylinderAvailable = true
  }

record SymbolicCylinderAddress : Set where
  field
    radix : Nat
    prefix : List Nat
    prefixLength : Nat
    commonPrefixDefinesCoarseCell : Bool
    suffixRefinesCell : Bool
    realDynamicalConjugacyProved : Bool

canonical357SymbolicCylinder : SymbolicCylinderAddress
canonical357SymbolicCylinder = record
  { radix = 10
  ; prefix = 3 ∷ 5 ∷ 7 ∷ []
  ; prefixLength = 3
  ; commonPrefixDefinesCoarseCell = true
  ; suffixRefinesCell = true
  ; realDynamicalConjugacyProved = false
  }

------------------------------------------------------------------------
-- Prime-lane coordinates and irreducible representations are separate forms
-- of decomposition. Existing Vec15 updates commute when their operators do.
------------------------------------------------------------------------

incrementLaneUpdatesCommute :
  (p q : TP.SSP) →
  (vector : Lattice.Vec15 Nat) →
  Lattice.updateVec15 p suc
    (Lattice.updateVec15 q suc vector)
  ≡
  Lattice.updateVec15 q suc
    (Lattice.updateVec15 p suc vector)
incrementLaneUpdatesCommute p q vector =
  Lattice.updateVec15-commutes
    p q suc suc
    (λ value → refl)
    vector

exactMonsterTableClassCount :
  (table : MCT.ExactMonsterCharacterTable) →
  MCT.ExactMonsterCharacterTable.classCount table ≡ 194
exactMonsterTableClassCount table =
  MCT.ExactMonsterCharacterTable.classCountIs194 table

exactMonsterTableIrreducibleCount :
  (table : MCT.ExactMonsterCharacterTable) →
  MCT.ExactMonsterCharacterTable.irreducibleCount table ≡ 194
exactMonsterTableIrreducibleCount table =
  MCT.ExactMonsterCharacterTable.irreducibleCountIs194 table

monsterSmallestNontrivialPlusOne :
  196883 + 1 ≡ 196884
monsterSmallestNontrivialPlusOne = refl

monsterUnitObservationContracts :
  J.contract J.unit-obs ≡ 196884
monsterUnitObservationContracts = J.unit-converges

record MonsterRepresentationSeparationReceipt : Set where
  field
    characterTableClassCountRole : Nat
    characterTableIrreducibleCountRole : Nat
    smallestNontrivialDegreeRole : Nat
    firstJCoefficientRole : Nat
    classCountIs194 :
      characterTableClassCountRole ≡ 194
    irreducibleCountIs194 :
      characterTableIrreducibleCountRole ≡ 194
    jIsDegreePlusOne :
      smallestNontrivialDegreeRole + 1 ≡ firstJCoefficientRole
    repositoryExactTableContractCarries194 : Bool
    factorValuationDecompositionIsIrrepDecomposition : Bool
    primeSupportImpliesMonsterOrigin : Bool
    concreteCharacterTableInstanceImportedHere : Bool
    symmetryAnalogyRequiresAdapter : Bool

canonicalMonsterRepresentationSeparationReceipt :
  MonsterRepresentationSeparationReceipt
canonicalMonsterRepresentationSeparationReceipt = record
  { characterTableClassCountRole = 194
  ; characterTableIrreducibleCountRole = 194
  ; smallestNontrivialDegreeRole = 196883
  ; firstJCoefficientRole = 196884
  ; classCountIs194 = refl
  ; irreducibleCountIs194 = refl
  ; jIsDegreePlusOne = monsterSmallestNontrivialPlusOne
  ; repositoryExactTableContractCarries194 = true
  ; factorValuationDecompositionIsIrrepDecomposition = false
  ; primeSupportImpliesMonsterOrigin = false
  ; concreteCharacterTableInstanceImportedHere = false
  ; symmetryAnalogyRequiresAdapter = true
  }

record FamilyDecimalMonsterAuthorityBoundary : Set where
  field
    oneThirdIsEmpiricalMortalityRateClaimed : Bool
    twoParentStructureUniversalised : Bool
    decimalAddressPredictsDynamicsClaimed : Bool
    symbolicCylinderEqualsRealOrbitClaimed : Bool
    valuationProfileEqualsIrrepDecompositionClaimed : Bool
    trackedPrimeSupportProvesMonsterOriginClaimed : Bool
    conditionalStructuralAnalogiesAvailable : Bool

canonicalFamilyDecimalMonsterAuthorityBoundary :
  FamilyDecimalMonsterAuthorityBoundary
canonicalFamilyDecimalMonsterAuthorityBoundary = record
  { oneThirdIsEmpiricalMortalityRateClaimed = false
  ; twoParentStructureUniversalised = false
  ; decimalAddressPredictsDynamicsClaimed = false
  ; symbolicCylinderEqualsRealOrbitClaimed = false
  ; valuationProfileEqualsIrrepDecompositionClaimed = false
  ; trackedPrimeSupportProvesMonsterOriginClaimed = false
  ; conditionalStructuralAnalogiesAvailable = true
  }
