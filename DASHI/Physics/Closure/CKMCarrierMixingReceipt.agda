module DASHI.Physics.Closure.CKMCarrierMixingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import Ontology.GodelLattice as GL
import DASHI.Physics.Closure.HiggsSymmetryBreakingReceipt as Higgs
import DASHI.Physics.Closure.CKMEntryField as Field
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.YM.FroggattNielsenExpansion as FN
import DASHI.Physics.YM.WolfensteinCKM as Wolf

module DHR where
  postulate
    LocalisedEndomorphism :
      Set

    Intertwiner :
      LocalisedEndomorphism →
      LocalisedEndomorphism →
      Set

    DHRGaugeReceiptSurface :
      Setω

    DHRFormalismPrimitiveReceipt :
      Setω

    DHRSelectionCriterionTarget :
      Set

    DHRCategoryPrimitiveSurface :
      Set

    canonicalDHRGaugeReceiptSurface :
      DHRGaugeReceiptSurface

    canonicalDHRFormalismPrimitiveReceipt :
      DHRFormalismPrimitiveReceipt

    canonicalDHRSelectionCriterionTarget :
      DHRSelectionCriterionTarget

    canonicalDHRCategoryPrimitiveSurface :
      DHRCategoryPrimitiveSurface

    criterionProved :
      DHRSelectionCriterionTarget →
      Bool

    primitiveCategoryLawsProved :
      DHRCategoryPrimitiveSurface →
      Bool

------------------------------------------------------------------------
-- CKM carrier-mixing receipt surface.
--
-- This module records only a bounded target surface for quark weak-to-mass
-- carrier mixing.  It does not derive CKM, Yukawa closure, Higgs closure,
-- Standard Model closure, angle values, CP phase values, or any terminal
-- promotion.

data CKMCarrierMixingStatus : Set where
  ckmCarrierMixingTargetsOnlyNoPromotion :
    CKMCarrierMixingStatus

data CKMCarrierMixingFirstMissing : Set where
  missingCarrierMixingTheorem :
    CKMCarrierMixingFirstMissing

data CKMAnglePhaseTarget : Set where
  theta12Target :
    CKMAnglePhaseTarget

  theta23Target :
    CKMAnglePhaseTarget

  theta13Target :
    CKMAnglePhaseTarget

  cpViolatingPhaseTarget :
    CKMAnglePhaseTarget

canonicalCKMAnglePhaseTargets :
  List CKMAnglePhaseTarget
canonicalCKMAnglePhaseTargets =
  theta12Target
  ∷ theta23Target
  ∷ theta13Target
  ∷ cpViolatingPhaseTarget
  ∷ []

data CKMCarrierMixingOpenObligation : Set where
  missingWeakEigenstateCarrier :
    CKMCarrierMixingOpenObligation

  missingMassEigenstateCarrier :
    CKMCarrierMixingOpenObligation

  missingCarrierMixingMap :
    CKMCarrierMixingOpenObligation

  missingUnitaryCKMMatrixTarget :
    CKMCarrierMixingOpenObligation

  missingAnglePhaseTargets :
    CKMCarrierMixingOpenObligation

  missingYukawaDiagonalizationInterface :
    CKMCarrierMixingOpenObligation

  missingDHRYukawaCompatibility :
    CKMCarrierMixingOpenObligation

  missingCarrierMixingTheoremObligation :
    CKMCarrierMixingOpenObligation

canonicalCKMCarrierMixingOpenObligations :
  List CKMCarrierMixingOpenObligation
canonicalCKMCarrierMixingOpenObligations =
  missingWeakEigenstateCarrier
  ∷ missingMassEigenstateCarrier
  ∷ missingCarrierMixingMap
  ∷ missingUnitaryCKMMatrixTarget
  ∷ missingAnglePhaseTargets
  ∷ missingYukawaDiagonalizationInterface
  ∷ missingDHRYukawaCompatibility
  ∷ missingCarrierMixingTheoremObligation
  ∷ []

data CKMCarrierMixingPromotionAuthorityToken : Set where

data CKMCarrierMixingDependency : Set where
  dhrGaugeTransportDependency :
    CKMCarrierMixingDependency

  higgsSymmetryBreakingDependency :
    CKMCarrierMixingDependency

  yukawaDiagonalizationDependency :
    CKMCarrierMixingDependency

  carrierMixingTheoremDependency :
    CKMCarrierMixingDependency

  ckmUnitarityProofDependency :
    CKMCarrierMixingDependency

canonicalCKMCarrierMixingDependencies :
  List CKMCarrierMixingDependency
canonicalCKMCarrierMixingDependencies =
  dhrGaugeTransportDependency
  ∷ higgsSymmetryBreakingDependency
  ∷ yukawaDiagonalizationDependency
  ∷ carrierMixingTheoremDependency
  ∷ ckmUnitarityProofDependency
  ∷ []

data CKMYukawaDHRCompatibilityBlocker : Set where
  missingLeftRightQuarkCarrierFamilies :
    CKMYukawaDHRCompatibilityBlocker

  missingYukawaMatrixCarrier :
    CKMYukawaDHRCompatibilityBlocker

  missingYukawaDHRIntertwinerCompatibility :
    CKMYukawaDHRCompatibilityBlocker

  missingBiunitaryDiagonalizationProof :
    CKMYukawaDHRCompatibilityBlocker

  missingWeakToMassBasisMixingIdentification :
    CKMYukawaDHRCompatibilityBlocker

  missingCKMUnitarityTransport :
    CKMYukawaDHRCompatibilityBlocker

canonicalCKMYukawaDHRCompatibilityBlockers :
  List CKMYukawaDHRCompatibilityBlocker
canonicalCKMYukawaDHRCompatibilityBlockers =
  missingLeftRightQuarkCarrierFamilies
  ∷ missingYukawaMatrixCarrier
  ∷ missingYukawaDHRIntertwinerCompatibility
  ∷ missingBiunitaryDiagonalizationProof
  ∷ missingWeakToMassBasisMixingIdentification
  ∷ missingCKMUnitarityTransport
  ∷ []

data CKMLeftRightQuarkCarrierFamilyBlocker : Set where
  missingLeftQuarkDoubletCarrierFamily :
    CKMLeftRightQuarkCarrierFamilyBlocker

  missingRightUpQuarkCarrierFamily :
    CKMLeftRightQuarkCarrierFamilyBlocker

  missingRightDownQuarkCarrierFamily :
    CKMLeftRightQuarkCarrierFamilyBlocker

  missingThreeGenerationCarrierFamily :
    CKMLeftRightQuarkCarrierFamilyBlocker

  missingQuarkFamilyYukawaMatrixCarrier :
    CKMLeftRightQuarkCarrierFamilyBlocker

  missingQuarkFamilyDHRCompatibility :
    CKMLeftRightQuarkCarrierFamilyBlocker

canonicalCKMLeftRightQuarkCarrierFamilyBlockers :
  List CKMLeftRightQuarkCarrierFamilyBlocker
canonicalCKMLeftRightQuarkCarrierFamilyBlockers =
  missingLeftQuarkDoubletCarrierFamily
  ∷ missingRightUpQuarkCarrierFamily
  ∷ missingRightDownQuarkCarrierFamily
  ∷ missingThreeGenerationCarrierFamily
  ∷ missingQuarkFamilyYukawaMatrixCarrier
  ∷ missingQuarkFamilyDHRCompatibility
  ∷ []

canonicalCKMLeftRightQuarkCarrierFamilyBlockersAfterLeftQuarkSupply :
  List CKMLeftRightQuarkCarrierFamilyBlocker
canonicalCKMLeftRightQuarkCarrierFamilyBlockersAfterLeftQuarkSupply =
  missingRightUpQuarkCarrierFamily
  ∷ missingRightDownQuarkCarrierFamily
  ∷ missingQuarkFamilyYukawaMatrixCarrier
  ∷ missingQuarkFamilyDHRCompatibility
  ∷ []

canonicalCKMLeftRightQuarkCarrierFamilyBlockersAfterRightHandedQuarkSupply :
  List CKMLeftRightQuarkCarrierFamilyBlocker
canonicalCKMLeftRightQuarkCarrierFamilyBlockersAfterRightHandedQuarkSupply =
  missingQuarkFamilyYukawaMatrixCarrier
  ∷ missingQuarkFamilyDHRCompatibility
  ∷ []

canonicalCKMLeftRightQuarkCarrierFamilyBlockersAfterYukawaSVDInterfaceSupply :
  List CKMLeftRightQuarkCarrierFamilyBlocker
canonicalCKMLeftRightQuarkCarrierFamilyBlockersAfterYukawaSVDInterfaceSupply =
  missingQuarkFamilyDHRCompatibility
  ∷ []

canonicalCKMYukawaDHRCompatibilityBlockersAfterRightHandedFamilySupply :
  List CKMYukawaDHRCompatibilityBlocker
canonicalCKMYukawaDHRCompatibilityBlockersAfterRightHandedFamilySupply =
  missingYukawaMatrixCarrier
  ∷ missingYukawaDHRIntertwinerCompatibility
  ∷ missingBiunitaryDiagonalizationProof
  ∷ missingWeakToMassBasisMixingIdentification
  ∷ missingCKMUnitarityTransport
  ∷ []

canonicalCKMYukawaDHRCompatibilityBlockersAfterYukawaSVDInterfaceSupply :
  List CKMYukawaDHRCompatibilityBlocker
canonicalCKMYukawaDHRCompatibilityBlockersAfterYukawaSVDInterfaceSupply =
  missingYukawaDHRIntertwinerCompatibility
  ∷ missingWeakToMassBasisMixingIdentification
  ∷ missingCKMUnitarityTransport
  ∷ []

data LeftQuarkDoubletCarrierPrimitiveRequest : Set where
  missingSU3ColourTripletRepresentationPrimitive :
    LeftQuarkDoubletCarrierPrimitiveRequest

  missingSU2LWeakDoubletRepresentationPrimitive :
    LeftQuarkDoubletCarrierPrimitiveRequest

  missingU1YHyperchargeOneSixthPrimitive :
    LeftQuarkDoubletCarrierPrimitiveRequest

  missingLeftChiralityPrimitive :
    LeftQuarkDoubletCarrierPrimitiveRequest

  missingThreeGenerationFamilyPrimitive :
    LeftQuarkDoubletCarrierPrimitiveRequest

canonicalLeftQuarkDoubletCarrierPrimitiveRequests :
  List LeftQuarkDoubletCarrierPrimitiveRequest
canonicalLeftQuarkDoubletCarrierPrimitiveRequests =
  missingSU3ColourTripletRepresentationPrimitive
  ∷ missingSU2LWeakDoubletRepresentationPrimitive
  ∷ missingU1YHyperchargeOneSixthPrimitive
  ∷ missingLeftChiralityPrimitive
  ∷ missingThreeGenerationFamilyPrimitive
  ∷ []

data LeftQuarkMatterRepresentationMissingFieldConstructor : Set where
  missingLeftQuarkMatterRepresentationConstructor :
    LeftQuarkMatterRepresentationMissingFieldConstructor

  missingLeftQuarkHyperchargeAssignmentConstructor :
    LeftQuarkMatterRepresentationMissingFieldConstructor

  missingLeftQuarkGenerationStructureConstructor :
    LeftQuarkMatterRepresentationMissingFieldConstructor

  missingLeftQuarkSU3ColourTripletRepresentationConstructor :
    LeftQuarkMatterRepresentationMissingFieldConstructor

  missingLeftQuarkSU2LWeakDoubletRepresentationConstructor :
    LeftQuarkMatterRepresentationMissingFieldConstructor

  missingLeftQuarkU1YHyperchargeOneSixthConstructor :
    LeftQuarkMatterRepresentationMissingFieldConstructor

  missingLeftQuarkLeftChiralityConstructor :
    LeftQuarkMatterRepresentationMissingFieldConstructor

  missingLeftQuarkThreeGenerationFamilyConstructor :
    LeftQuarkMatterRepresentationMissingFieldConstructor

canonicalLeftQuarkMatterRepresentationMissingFieldConstructors :
  List LeftQuarkMatterRepresentationMissingFieldConstructor
canonicalLeftQuarkMatterRepresentationMissingFieldConstructors =
  []

data LeftQuarkCarrierFamilySuppliedEvidenceConstructor : Set where
  suppliedLeftQuarkMatterRepresentationConstructor :
    LeftQuarkCarrierFamilySuppliedEvidenceConstructor

  suppliedLeftQuarkFamilyPrimitiveConstructor :
    LeftQuarkCarrierFamilySuppliedEvidenceConstructor

  suppliedLeftQuarkThreeGenerationStructureConstructor :
    LeftQuarkCarrierFamilySuppliedEvidenceConstructor

canonicalLeftQuarkCarrierFamilySuppliedEvidenceConstructors :
  List LeftQuarkCarrierFamilySuppliedEvidenceConstructor
canonicalLeftQuarkCarrierFamilySuppliedEvidenceConstructors =
  suppliedLeftQuarkMatterRepresentationConstructor
  ∷ suppliedLeftQuarkFamilyPrimitiveConstructor
  ∷ suppliedLeftQuarkThreeGenerationStructureConstructor
  ∷ []

data RightHandedQuarkCarrierPrimitiveRequest : Set where
  missingRightQuarkSU3ColourTripletRepresentationPrimitive :
    RightHandedQuarkCarrierPrimitiveRequest

  missingRightQuarkSU2LWeakSingletRepresentationPrimitive :
    RightHandedQuarkCarrierPrimitiveRequest

  missingRightUpU1YHyperchargeTwoThirdsPrimitive :
    RightHandedQuarkCarrierPrimitiveRequest

  missingRightDownU1YHyperchargeMinusOneThirdPrimitive :
    RightHandedQuarkCarrierPrimitiveRequest

  missingRightChiralityPrimitive :
    RightHandedQuarkCarrierPrimitiveRequest

  missingRightQuarkThreeGenerationFamilyPrimitive :
    RightHandedQuarkCarrierPrimitiveRequest

canonicalRightHandedQuarkCarrierPrimitiveRequests :
  List RightHandedQuarkCarrierPrimitiveRequest
canonicalRightHandedQuarkCarrierPrimitiveRequests =
  missingRightQuarkSU3ColourTripletRepresentationPrimitive
  ∷ missingRightQuarkSU2LWeakSingletRepresentationPrimitive
  ∷ missingRightUpU1YHyperchargeTwoThirdsPrimitive
  ∷ missingRightDownU1YHyperchargeMinusOneThirdPrimitive
  ∷ missingRightChiralityPrimitive
  ∷ missingRightQuarkThreeGenerationFamilyPrimitive
  ∷ []

data RightHandedQuarkCarrierFamilySuppliedEvidenceConstructor :
  Set where
  suppliedRightUpQuarkGenericMatterRepresentationConstructor :
    RightHandedQuarkCarrierFamilySuppliedEvidenceConstructor

  suppliedRightDownQuarkGenericMatterRepresentationConstructor :
    RightHandedQuarkCarrierFamilySuppliedEvidenceConstructor

  suppliedRightUpQuarkHyperchargePrimitiveConstructor :
    RightHandedQuarkCarrierFamilySuppliedEvidenceConstructor

  suppliedRightDownQuarkHyperchargePrimitiveConstructor :
    RightHandedQuarkCarrierFamilySuppliedEvidenceConstructor

  suppliedRightQuarkThreeGenerationStructureConstructor :
    RightHandedQuarkCarrierFamilySuppliedEvidenceConstructor

canonicalRightHandedQuarkCarrierFamilySuppliedEvidenceConstructors :
  List RightHandedQuarkCarrierFamilySuppliedEvidenceConstructor
canonicalRightHandedQuarkCarrierFamilySuppliedEvidenceConstructors =
  suppliedRightUpQuarkGenericMatterRepresentationConstructor
  ∷ suppliedRightDownQuarkGenericMatterRepresentationConstructor
  ∷ suppliedRightUpQuarkHyperchargePrimitiveConstructor
  ∷ suppliedRightDownQuarkHyperchargePrimitiveConstructor
  ∷ suppliedRightQuarkThreeGenerationStructureConstructor
  ∷ []

canonicalLeftRightQuarkMatterTargets :
  List Matter.StandardModelMatterSectorTarget
canonicalLeftRightQuarkMatterTargets =
  Matter.leftQuarkDoubletTarget
  ∷ Matter.rightUpQuarkTarget
  ∷ Matter.rightDownQuarkTarget
  ∷ []

LeftQuarkSU3ColourTripletRepresentation :
  Set
LeftQuarkSU3ColourTripletRepresentation =
  Matter.GaugeRepresentationPrimitive

LeftQuarkSU2LWeakDoubletRepresentation :
  Set
LeftQuarkSU2LWeakDoubletRepresentation =
  Matter.GaugeRepresentationPrimitive

LeftQuarkU1YHyperchargeOneSixth :
  Set
LeftQuarkU1YHyperchargeOneSixth =
  Matter.HyperchargePrimitive

LeftQuarkLeftChirality :
  Set
LeftQuarkLeftChirality =
  Matter.ChiralityPrimitive

LeftQuarkThreeGenerationFamily :
  Set
LeftQuarkThreeGenerationFamily =
  Matter.GenerationPrimitive

RightQuarkSU3ColourTripletRepresentation :
  Set
RightQuarkSU3ColourTripletRepresentation =
  Matter.GaugeRepresentationPrimitive

RightQuarkSU2LWeakSingletRepresentation :
  Set
RightQuarkSU2LWeakSingletRepresentation =
  Matter.GaugeRepresentationPrimitive

RightUpU1YHyperchargeTwoThirds :
  Set
RightUpU1YHyperchargeTwoThirds =
  Matter.HyperchargePrimitive

RightDownU1YHyperchargeMinusOneThird :
  Set
RightDownU1YHyperchargeMinusOneThird =
  Matter.HyperchargePrimitive

RightQuarkRightChirality :
  Set
RightQuarkRightChirality =
  Matter.ChiralityPrimitive

RightQuarkThreeGenerationFamily :
  Set
RightQuarkThreeGenerationFamily =
  Matter.GenerationPrimitive

canonicalSU2LWeakSingletPrimitive :
  Matter.GaugeRepresentationPrimitive
canonicalSU2LWeakSingletPrimitive =
  Matter.gaugeRepresentationPrimitive
    Matter.su2LWeakFactor
    Matter.representationDimensionOne
    "SU2_L singlet"

canonicalHyperchargeTwoThirdsPrimitive :
  Matter.HyperchargePrimitive
canonicalHyperchargeTwoThirdsPrimitive =
  Matter.hyperchargePrimitive
    2
    3
    true
    "Y=+2/3"

canonicalHyperchargeMinusOneThirdPrimitive :
  Matter.HyperchargePrimitive
canonicalHyperchargeMinusOneThirdPrimitive =
  Matter.hyperchargePrimitive
    1
    3
    false
    "Y=-1/3"

canonicalRightQuarkThreeColourComponentPrimitive :
  Matter.ComponentPrimitive
canonicalRightQuarkThreeColourComponentPrimitive =
  Matter.componentPrimitive
    3
    "three colour components per generation"

postulate
  ckmRightHandedQuarkCompactGaugeGroup :
    Matter.CompactGaugeGroup

canonicalRightUpQuarkFamilyMatterRepresentation :
  Matter.MatterRepresentation
canonicalRightUpQuarkFamilyMatterRepresentation =
  Matter.matterRepresentationAdapterTarget
    ckmRightHandedQuarkCompactGaugeGroup
    Matter.rightUpQuarkTarget

canonicalRightDownQuarkFamilyMatterRepresentation :
  Matter.MatterRepresentation
canonicalRightDownQuarkFamilyMatterRepresentation =
  Matter.matterRepresentationAdapterTarget
    ckmRightHandedQuarkCompactGaugeGroup
    Matter.rightDownQuarkTarget

record LeftQuarkDoubletCarrierFamilyDefinitionRequest : Setω where
  field
    matterSectorTarget :
      Matter.StandardModelMatterSectorTarget

    matterSectorTargetIsLeftQuarkDoublet :
      matterSectorTarget
      ≡
      Matter.leftQuarkDoubletTarget

    matterRepresentationCarrierTarget :
      Set

    matterRepresentationCarrierTargetIsMatterRepresentation :
      matterRepresentationCarrierTarget
      ≡
      Matter.MatterRepresentation

    hyperchargeAssignmentCarrierTarget :
      Set

    hyperchargeAssignmentCarrierTargetIsMatterHypercharge :
      hyperchargeAssignmentCarrierTarget
      ≡
      Matter.HyperchargeAssignment

    generationStructureCarrierTarget :
      Set

    generationStructureCarrierTargetIsMatterGenerationStructure :
      generationStructureCarrierTarget
      ≡
      Matter.GenerationStructure

    colourTripletRepresentationTarget :
      Set

    colourTripletRepresentationTargetIsPrimitive :
      colourTripletRepresentationTarget
      ≡
      LeftQuarkSU3ColourTripletRepresentation

    weakDoubletRepresentationTarget :
      Set

    weakDoubletRepresentationTargetIsPrimitive :
      weakDoubletRepresentationTarget
      ≡
      LeftQuarkSU2LWeakDoubletRepresentation

    hyperchargeOneSixthTarget :
      Set

    hyperchargeOneSixthTargetIsPrimitive :
      hyperchargeOneSixthTarget
      ≡
      LeftQuarkU1YHyperchargeOneSixth

    leftChiralityTarget :
      Set

    leftChiralityTargetIsPrimitive :
      leftChiralityTarget
      ≡
      LeftQuarkLeftChirality

    threeGenerationFamilyTarget :
      Set

    threeGenerationFamilyTargetIsPrimitive :
      threeGenerationFamilyTarget
      ≡
      LeftQuarkThreeGenerationFamily

    requestedPrimitives :
      List LeftQuarkDoubletCarrierPrimitiveRequest

    requestedPrimitivesAreCanonical :
      requestedPrimitives
      ≡
      canonicalLeftQuarkDoubletCarrierPrimitiveRequests

    leftQuarkDoubletFamilyConstructed :
      Bool

    leftQuarkDoubletFamilyConstructedIsFalse :
      leftQuarkDoubletFamilyConstructed ≡ false

    boundary :
      List String

open LeftQuarkDoubletCarrierFamilyDefinitionRequest public

canonicalLeftQuarkDoubletCarrierFamilyDefinitionRequest :
  LeftQuarkDoubletCarrierFamilyDefinitionRequest
canonicalLeftQuarkDoubletCarrierFamilyDefinitionRequest =
  record
    { matterSectorTarget =
        Matter.leftQuarkDoubletTarget
    ; matterSectorTargetIsLeftQuarkDoublet =
        refl
    ; matterRepresentationCarrierTarget =
        Matter.MatterRepresentation
    ; matterRepresentationCarrierTargetIsMatterRepresentation =
        refl
    ; hyperchargeAssignmentCarrierTarget =
        Matter.HyperchargeAssignment
    ; hyperchargeAssignmentCarrierTargetIsMatterHypercharge =
        refl
    ; generationStructureCarrierTarget =
        Matter.GenerationStructure
    ; generationStructureCarrierTargetIsMatterGenerationStructure =
        refl
    ; colourTripletRepresentationTarget =
        LeftQuarkSU3ColourTripletRepresentation
    ; colourTripletRepresentationTargetIsPrimitive =
        refl
    ; weakDoubletRepresentationTarget =
        LeftQuarkSU2LWeakDoubletRepresentation
    ; weakDoubletRepresentationTargetIsPrimitive =
        refl
    ; hyperchargeOneSixthTarget =
        LeftQuarkU1YHyperchargeOneSixth
    ; hyperchargeOneSixthTargetIsPrimitive =
        refl
    ; leftChiralityTarget =
        LeftQuarkLeftChirality
    ; leftChiralityTargetIsPrimitive =
        refl
    ; threeGenerationFamilyTarget =
        LeftQuarkThreeGenerationFamily
    ; threeGenerationFamilyTargetIsPrimitive =
        refl
    ; requestedPrimitives =
        canonicalLeftQuarkDoubletCarrierPrimitiveRequests
    ; requestedPrimitivesAreCanonical =
        refl
    ; leftQuarkDoubletFamilyConstructed =
        false
    ; leftQuarkDoubletFamilyConstructedIsFalse =
        refl
    ; boundary =
        "Left quark family is narrowed to Matter.leftQuarkDoubletTarget"
        ∷ "Required primitive: SU3_c colour triplet representation"
        ∷ "Required primitive: SU2_L weak doublet representation"
        ∷ "Required primitive: U1_Y hypercharge one sixth"
        ∷ "Required primitive: left chirality"
        ∷ "Required primitive: three-generation family carrier"
        ∷ "This records the target (3,2,1/6) with left chirality but does not construct a CKM, Yukawa, Higgs, W4, or terminal promotion"
        ∷ []
    }

record LeftQuarkDoubletCarrierFamilyDefinitionSurface : Setω where
  field
    leftQuarkCarrierFamilyDefinitionRequest :
      LeftQuarkDoubletCarrierFamilyDefinitionRequest

    leftQuarkMatterTarget :
      Matter.StandardModelMatterSectorTarget

    leftQuarkMatterTargetIsLeftQuarkDoublet :
      leftQuarkMatterTarget
      ≡
      Matter.leftQuarkDoubletTarget

    leftQuarkMatterRepresentationCarrier :
      Set

    leftQuarkMatterRepresentationCarrierIsMatterRepresentation :
      leftQuarkMatterRepresentationCarrier
      ≡
      Matter.MatterRepresentation

    leftQuarkHyperchargeCarrier :
      Set

    leftQuarkHyperchargeCarrierIsMatterHypercharge :
      leftQuarkHyperchargeCarrier
      ≡
      Matter.HyperchargeAssignment

    leftQuarkGenerationCarrier :
      Set

    leftQuarkGenerationCarrierIsMatterGenerationStructure :
      leftQuarkGenerationCarrier
      ≡
      Matter.GenerationStructure

    leftQuarkColourTripletPrimitive :
      Set

    leftQuarkColourTripletPrimitiveIsRequestedPrimitive :
      leftQuarkColourTripletPrimitive
      ≡
      LeftQuarkSU3ColourTripletRepresentation

    leftQuarkWeakDoubletPrimitive :
      Set

    leftQuarkWeakDoubletPrimitiveIsRequestedPrimitive :
      leftQuarkWeakDoubletPrimitive
      ≡
      LeftQuarkSU2LWeakDoubletRepresentation

    leftQuarkHyperchargeOneSixthPrimitive :
      Set

    leftQuarkHyperchargeOneSixthPrimitiveIsRequestedPrimitive :
      leftQuarkHyperchargeOneSixthPrimitive
      ≡
      LeftQuarkU1YHyperchargeOneSixth

    leftQuarkChiralityPrimitive :
      Set

    leftQuarkChiralityPrimitiveIsRequestedPrimitive :
      leftQuarkChiralityPrimitive
      ≡
      LeftQuarkLeftChirality

    leftQuarkThreeGenerationPrimitive :
      Set

    leftQuarkThreeGenerationPrimitiveIsRequestedPrimitive :
      leftQuarkThreeGenerationPrimitive
      ≡
      LeftQuarkThreeGenerationFamily

    leftQuarkFamilySurfaceRecorded :
      Bool

    leftQuarkFamilySurfaceRecordedIsTrue :
      leftQuarkFamilySurfaceRecorded ≡ true

    leftQuarkDoubletFamilySurfaceConstructed :
      Bool

    leftQuarkDoubletFamilySurfaceConstructedIsFalse :
      leftQuarkDoubletFamilySurfaceConstructed ≡ false

    leftQuarkYukawaMatrixSurfaceConstructed :
      Bool

    leftQuarkYukawaMatrixSurfaceConstructedIsFalse :
      leftQuarkYukawaMatrixSurfaceConstructed ≡ false

    leftQuarkCKMMixingSurfaceConstructed :
      Bool

    leftQuarkCKMMixingSurfaceConstructedIsFalse :
      leftQuarkCKMMixingSurfaceConstructed ≡ false

    leftQuarkHiggsDependencyDischarged :
      Bool

    leftQuarkHiggsDependencyDischargedIsFalse :
      leftQuarkHiggsDependencyDischarged ≡ false

    leftQuarkW4CalibrationSurfaceConstructed :
      Bool

    leftQuarkW4CalibrationSurfaceConstructedIsFalse :
      leftQuarkW4CalibrationSurfaceConstructed ≡ false

    leftQuarkPromotionSurfaceConstructed :
      Bool

    leftQuarkPromotionSurfaceConstructedIsFalse :
      leftQuarkPromotionSurfaceConstructed ≡ false

    leftQuarkFamilySurfaceBoundary :
      List String

open LeftQuarkDoubletCarrierFamilyDefinitionSurface public

canonicalLeftQuarkDoubletCarrierFamilyDefinitionSurface :
  LeftQuarkDoubletCarrierFamilyDefinitionSurface
canonicalLeftQuarkDoubletCarrierFamilyDefinitionSurface =
  record
    { leftQuarkCarrierFamilyDefinitionRequest =
        canonicalLeftQuarkDoubletCarrierFamilyDefinitionRequest
    ; leftQuarkMatterTarget =
        Matter.leftQuarkDoubletTarget
    ; leftQuarkMatterTargetIsLeftQuarkDoublet =
        refl
    ; leftQuarkMatterRepresentationCarrier =
        Matter.MatterRepresentation
    ; leftQuarkMatterRepresentationCarrierIsMatterRepresentation =
        refl
    ; leftQuarkHyperchargeCarrier =
        Matter.HyperchargeAssignment
    ; leftQuarkHyperchargeCarrierIsMatterHypercharge =
        refl
    ; leftQuarkGenerationCarrier =
        Matter.GenerationStructure
    ; leftQuarkGenerationCarrierIsMatterGenerationStructure =
        refl
    ; leftQuarkColourTripletPrimitive =
        LeftQuarkSU3ColourTripletRepresentation
    ; leftQuarkColourTripletPrimitiveIsRequestedPrimitive =
        refl
    ; leftQuarkWeakDoubletPrimitive =
        LeftQuarkSU2LWeakDoubletRepresentation
    ; leftQuarkWeakDoubletPrimitiveIsRequestedPrimitive =
        refl
    ; leftQuarkHyperchargeOneSixthPrimitive =
        LeftQuarkU1YHyperchargeOneSixth
    ; leftQuarkHyperchargeOneSixthPrimitiveIsRequestedPrimitive =
        refl
    ; leftQuarkChiralityPrimitive =
        LeftQuarkLeftChirality
    ; leftQuarkChiralityPrimitiveIsRequestedPrimitive =
        refl
    ; leftQuarkThreeGenerationPrimitive =
        LeftQuarkThreeGenerationFamily
    ; leftQuarkThreeGenerationPrimitiveIsRequestedPrimitive =
        refl
    ; leftQuarkFamilySurfaceRecorded =
        true
    ; leftQuarkFamilySurfaceRecordedIsTrue =
        refl
    ; leftQuarkDoubletFamilySurfaceConstructed =
        false
    ; leftQuarkDoubletFamilySurfaceConstructedIsFalse =
        refl
    ; leftQuarkYukawaMatrixSurfaceConstructed =
        false
    ; leftQuarkYukawaMatrixSurfaceConstructedIsFalse =
        refl
    ; leftQuarkCKMMixingSurfaceConstructed =
        false
    ; leftQuarkCKMMixingSurfaceConstructedIsFalse =
        refl
    ; leftQuarkHiggsDependencyDischarged =
        false
    ; leftQuarkHiggsDependencyDischargedIsFalse =
        refl
    ; leftQuarkW4CalibrationSurfaceConstructed =
        false
    ; leftQuarkW4CalibrationSurfaceConstructedIsFalse =
        refl
    ; leftQuarkPromotionSurfaceConstructed =
        false
    ; leftQuarkPromotionSurfaceConstructedIsFalse =
        refl
    ; leftQuarkFamilySurfaceBoundary =
        "Carrier-family surface records Matter.leftQuarkDoubletTarget with MatterRepresentation, HyperchargeAssignment, and GenerationStructure sockets"
        ∷ "The (3,2,1/6) left-chiral three-generation family still depends on requested primitive representation carriers"
        ∷ "No Yukawa matrix, CKM mixing, Higgs dependency discharge, W4 calibration, or terminal promotion is constructed by this surface"
        ∷ []
    }

record LeftQuarkDoubletFamilyPrimitiveWitness : Setω where
  field
    carrierFamilyDefinitionRequest :
      LeftQuarkDoubletCarrierFamilyDefinitionRequest

    carrierFamilyDefinitionSurface :
      LeftQuarkDoubletCarrierFamilyDefinitionSurface

    matterSectorTarget :
      Matter.StandardModelMatterSectorTarget

    matterSectorTargetIsLeftQuarkDoublet :
      matterSectorTarget
      ≡
      Matter.leftQuarkDoubletTarget

    matterRepresentationSocket :
      Set

    matterRepresentationSocketIsMatterRepresentation :
      matterRepresentationSocket
      ≡
      Matter.MatterRepresentation

    hyperchargeSocket :
      Set

    hyperchargeSocketIsMatterHypercharge :
      hyperchargeSocket
      ≡
      Matter.HyperchargeAssignment

    generationStructureSocket :
      Set

    generationStructureSocketIsMatterGenerationStructure :
      generationStructureSocket
      ≡
      Matter.GenerationStructure

    colourTripletPrimitiveTarget :
      Set

    colourTripletPrimitiveTargetIsRequestedPrimitive :
      colourTripletPrimitiveTarget
      ≡
      LeftQuarkSU3ColourTripletRepresentation

    weakDoubletPrimitiveTarget :
      Set

    weakDoubletPrimitiveTargetIsRequestedPrimitive :
      weakDoubletPrimitiveTarget
      ≡
      LeftQuarkSU2LWeakDoubletRepresentation

    hyperchargeOneSixthPrimitiveTarget :
      Set

    hyperchargeOneSixthPrimitiveTargetIsRequestedPrimitive :
      hyperchargeOneSixthPrimitiveTarget
      ≡
      LeftQuarkU1YHyperchargeOneSixth

    leftChiralityPrimitiveTarget :
      Set

    leftChiralityPrimitiveTargetIsRequestedPrimitive :
      leftChiralityPrimitiveTarget
      ≡
      LeftQuarkLeftChirality

    threeGenerationFamilyPrimitiveTarget :
      Set

    threeGenerationFamilyPrimitiveTargetIsRequestedPrimitive :
      threeGenerationFamilyPrimitiveTarget
      ≡
      LeftQuarkThreeGenerationFamily

    requestedPrimitives :
      List LeftQuarkDoubletCarrierPrimitiveRequest

    requestedPrimitivesAreCanonical :
      requestedPrimitives
      ≡
      canonicalLeftQuarkDoubletCarrierPrimitiveRequests

    primitiveWitnessRecordsMatterSockets :
      Bool

    primitiveWitnessRecordsMatterSocketsIsTrue :
      primitiveWitnessRecordsMatterSockets ≡ true

    primitiveWitnessConstructsConcreteFamily :
      Bool

    primitiveWitnessConstructsConcreteFamilyIsFalse :
      primitiveWitnessConstructsConcreteFamily ≡ false

    primitiveWitnessConstructsYukawaOrCKM :
      Bool

    primitiveWitnessConstructsYukawaOrCKMIsFalse :
      primitiveWitnessConstructsYukawaOrCKM ≡ false

    primitiveWitnessDischargesHiggsOrW4 :
      Bool

    primitiveWitnessDischargesHiggsOrW4IsFalse :
      primitiveWitnessDischargesHiggsOrW4 ≡ false

    primitiveWitnessPromotesCKM :
      Bool

    primitiveWitnessPromotesCKMIsFalse :
      primitiveWitnessPromotesCKM ≡ false

    primitiveWitnessBoundary :
      List String

open LeftQuarkDoubletFamilyPrimitiveWitness public

record MatterRepresentationPrimitiveSupply : Setω where
  field
    leftQuarkPrimitiveWitness :
      LeftQuarkDoubletFamilyPrimitiveWitness

    matterSectorTarget :
      Matter.StandardModelMatterSectorTarget

    matterSectorTargetIsLeftQuarkDoublet :
      matterSectorTarget
      ≡
      Matter.leftQuarkDoubletTarget

    missingFieldConstructors :
      List LeftQuarkMatterRepresentationMissingFieldConstructor

    missingFieldConstructorsAreCanonical :
      missingFieldConstructors
      ≡
      canonicalLeftQuarkMatterRepresentationMissingFieldConstructors

    matterRepresentationConstructorSupplied :
      Bool

    matterRepresentationConstructorSuppliedIsTrue :
      matterRepresentationConstructorSupplied ≡ true

    hyperchargeAssignmentConstructorSupplied :
      Bool

    hyperchargeAssignmentConstructorSuppliedIsFalse :
      hyperchargeAssignmentConstructorSupplied ≡ false

    generationStructureConstructorSupplied :
      Bool

    generationStructureConstructorSuppliedIsTrue :
      generationStructureConstructorSupplied ≡ true

    representationChiralityFamilyConstructorsSupplied :
      Bool

    representationChiralityFamilyConstructorsSuppliedIsTrue :
      representationChiralityFamilyConstructorsSupplied ≡ true

    constructsLeftQuarkFamily :
      Bool

    constructsLeftQuarkFamilyIsFalse :
      constructsLeftQuarkFamily ≡ false

    dischargesYukawaHiggsW4CKMOrPromotion :
      Bool

    dischargesYukawaHiggsW4CKMOrPromotionIsFalse :
      dischargesYukawaHiggsW4CKMOrPromotion ≡ false

    supplyRequestBoundary :
      List String

open MatterRepresentationPrimitiveSupply public

canonicalLeftQuarkDoubletFamilyPrimitiveWitness :
  LeftQuarkDoubletFamilyPrimitiveWitness
canonicalLeftQuarkDoubletFamilyPrimitiveWitness =
  record
    { carrierFamilyDefinitionRequest =
        canonicalLeftQuarkDoubletCarrierFamilyDefinitionRequest
    ; carrierFamilyDefinitionSurface =
        canonicalLeftQuarkDoubletCarrierFamilyDefinitionSurface
    ; matterSectorTarget =
        Matter.leftQuarkDoubletTarget
    ; matterSectorTargetIsLeftQuarkDoublet =
        refl
    ; matterRepresentationSocket =
        Matter.MatterRepresentation
    ; matterRepresentationSocketIsMatterRepresentation =
        refl
    ; hyperchargeSocket =
        Matter.HyperchargeAssignment
    ; hyperchargeSocketIsMatterHypercharge =
        refl
    ; generationStructureSocket =
        Matter.GenerationStructure
    ; generationStructureSocketIsMatterGenerationStructure =
        refl
    ; colourTripletPrimitiveTarget =
        LeftQuarkSU3ColourTripletRepresentation
    ; colourTripletPrimitiveTargetIsRequestedPrimitive =
        refl
    ; weakDoubletPrimitiveTarget =
        LeftQuarkSU2LWeakDoubletRepresentation
    ; weakDoubletPrimitiveTargetIsRequestedPrimitive =
        refl
    ; hyperchargeOneSixthPrimitiveTarget =
        LeftQuarkU1YHyperchargeOneSixth
    ; hyperchargeOneSixthPrimitiveTargetIsRequestedPrimitive =
        refl
    ; leftChiralityPrimitiveTarget =
        LeftQuarkLeftChirality
    ; leftChiralityPrimitiveTargetIsRequestedPrimitive =
        refl
    ; threeGenerationFamilyPrimitiveTarget =
        LeftQuarkThreeGenerationFamily
    ; threeGenerationFamilyPrimitiveTargetIsRequestedPrimitive =
        refl
    ; requestedPrimitives =
        canonicalLeftQuarkDoubletCarrierPrimitiveRequests
    ; requestedPrimitivesAreCanonical =
        refl
    ; primitiveWitnessRecordsMatterSockets =
        true
    ; primitiveWitnessRecordsMatterSocketsIsTrue =
        refl
    ; primitiveWitnessConstructsConcreteFamily =
        false
    ; primitiveWitnessConstructsConcreteFamilyIsFalse =
        refl
    ; primitiveWitnessConstructsYukawaOrCKM =
        false
    ; primitiveWitnessConstructsYukawaOrCKMIsFalse =
        refl
    ; primitiveWitnessDischargesHiggsOrW4 =
        false
    ; primitiveWitnessDischargesHiggsOrW4IsFalse =
        refl
    ; primitiveWitnessPromotesCKM =
        false
    ; primitiveWitnessPromotesCKMIsFalse =
        refl
    ; primitiveWitnessBoundary =
        "Left-quark primitive witness uses Matter.leftQuarkDoubletTarget with MatterRepresentation, HyperchargeAssignment, and GenerationStructure sockets"
        ∷ "Concrete SU3_c triplet, SU2_L doublet, U1_Y +1/6, left chirality, six colour-weak components, and three-generation primitives are supplied by MatterRepresentationReceiptSurface"
        ∷ "No carrier family value, Yukawa matrix, CKM mixing, Higgs discharge, W4 calibration, or promotion is constructed"
        ∷ []
    }

canonicalLeftQuarkMatterRepresentationPrimitiveSupplyRequest :
  MatterRepresentationPrimitiveSupply
canonicalLeftQuarkMatterRepresentationPrimitiveSupplyRequest =
  record
    { leftQuarkPrimitiveWitness =
        canonicalLeftQuarkDoubletFamilyPrimitiveWitness
    ; matterSectorTarget =
        Matter.leftQuarkDoubletTarget
    ; matterSectorTargetIsLeftQuarkDoublet =
        refl
    ; missingFieldConstructors =
        canonicalLeftQuarkMatterRepresentationMissingFieldConstructors
    ; missingFieldConstructorsAreCanonical =
        refl
    ; matterRepresentationConstructorSupplied =
        true
    ; matterRepresentationConstructorSuppliedIsTrue =
        refl
    ; hyperchargeAssignmentConstructorSupplied =
        false
    ; hyperchargeAssignmentConstructorSuppliedIsFalse =
        refl
    ; generationStructureConstructorSupplied =
        true
    ; generationStructureConstructorSuppliedIsTrue =
        refl
    ; representationChiralityFamilyConstructorsSupplied =
        true
    ; representationChiralityFamilyConstructorsSuppliedIsTrue =
        refl
    ; constructsLeftQuarkFamily =
        false
    ; constructsLeftQuarkFamilyIsFalse =
        refl
    ; dischargesYukawaHiggsW4CKMOrPromotion =
        false
    ; dischargesYukawaHiggsW4CKMOrPromotionIsFalse =
        refl
    ; supplyRequestBoundary =
        "MatterRepresentationPrimitiveSupply request for the left quark family is narrowed to Matter.leftQuarkDoubletTarget"
        ∷ "MatterRepresentationReceiptSurface supplies Matter.canonicalLeftQuarkDoubletFamilyMatterRepresentation and Matter.canonicalThreeGenerationStructure as local constructor witnesses"
        ∷ "MatterRepresentationReceiptSurface supplies the SU3_c triplet, SU2_L doublet, numeric U1_Y +1/6, left chirality, six colour-weak components, and three-generation primitive data"
        ∷ "This request does not construct a quark family value, Yukawa matrix, Higgs dependency discharge, W4 calibration, CKM mixing, or promotion"
        ∷ []
    }

record LeftQuarkDoubletMatterSurfacePrimitiveRequest : Set where
  field
    matterSectorTarget :
      Matter.StandardModelMatterSectorTarget

    matterSectorTargetIsLeftQuarkDoublet :
      matterSectorTarget
      ≡
      Matter.leftQuarkDoubletTarget

    availableHyperchargeAssignment :
      Matter.HyperchargeAssignment

    availableHyperchargeAssignmentIsMatterSurfaceTarget :
      availableHyperchargeAssignment
      ≡
      Matter.hyperchargeAssignmentTarget Matter.leftQuarkDoubletTarget

    matterSurfaceLeftQuarkDoubletFamilyPrimitive :
      Matter.LeftQuarkDoubletFamilyPrimitive

    matterSurfaceLeftQuarkDoubletFamilyPrimitiveIsCanonical :
      matterSurfaceLeftQuarkDoubletFamilyPrimitive
      ≡
      Matter.canonicalLeftQuarkDoubletFamilyPrimitive

    matterSurfaceSU3ColourTripletPrimitive :
      Matter.GaugeRepresentationPrimitive

    matterSurfaceSU3ColourTripletPrimitiveIsCanonical :
      matterSurfaceSU3ColourTripletPrimitive
      ≡
      Matter.canonicalSU3ColourTripletPrimitive

    matterSurfaceSU2LWeakDoubletPrimitive :
      Matter.GaugeRepresentationPrimitive

    matterSurfaceSU2LWeakDoubletPrimitiveIsCanonical :
      matterSurfaceSU2LWeakDoubletPrimitive
      ≡
      Matter.canonicalSU2LWeakDoubletPrimitive

    matterSurfaceHyperchargeOneSixthPrimitive :
      Matter.HyperchargePrimitive

    matterSurfaceHyperchargeOneSixthPrimitiveIsCanonical :
      matterSurfaceHyperchargeOneSixthPrimitive
      ≡
      Matter.canonicalHyperchargeOneSixthPrimitive

    matterSurfaceLeftChiralityPrimitive :
      Matter.ChiralityPrimitive

    matterSurfaceLeftChiralityPrimitiveIsCanonical :
      matterSurfaceLeftChiralityPrimitive
      ≡
      Matter.leftChirality

    matterSurfaceSixColourWeakComponentPrimitive :
      Matter.ComponentPrimitive

    matterSurfaceSixColourWeakComponentPrimitiveIsCanonical :
      matterSurfaceSixColourWeakComponentPrimitive
      ≡
      Matter.canonicalLeftQuarkSixColourWeakComponentPrimitive

    matterSurfaceThreeGenerationPrimitive :
      Matter.GenerationPrimitive

    matterSurfaceThreeGenerationPrimitiveIsCanonical :
      matterSurfaceThreeGenerationPrimitive
      ≡
      Matter.canonicalThreeGenerationPrimitive

    matterSurfaceLeftQuarkDoubletFamilyMatterRepresentation :
      Matter.MatterRepresentation

    matterSurfaceLeftQuarkDoubletFamilyMatterRepresentationIsCanonical :
      matterSurfaceLeftQuarkDoubletFamilyMatterRepresentation
      ≡
      Matter.canonicalLeftQuarkDoubletFamilyMatterRepresentation

    matterSurfaceThreeGenerationStructure :
      Matter.GenerationStructure

    matterSurfaceThreeGenerationStructureIsCanonical :
      matterSurfaceThreeGenerationStructure
      ≡
      Matter.canonicalThreeGenerationStructure

    constructsConcreteLeftQuarkDoubletFamilyPrimitive :
      Bool

    constructsConcreteLeftQuarkDoubletFamilyPrimitiveIsTrue :
      constructsConcreteLeftQuarkDoubletFamilyPrimitive ≡ true

    keepsYukawaHiggsW4CKMAndPromotionOpen :
      Bool

    keepsYukawaHiggsW4CKMAndPromotionOpenIsTrue :
      keepsYukawaHiggsW4CKMAndPromotionOpen ≡ true

    localLeftQuarkMatterRepresentationConstructorSupplied :
      Bool

    localLeftQuarkMatterRepresentationConstructorSuppliedIsTrue :
      localLeftQuarkMatterRepresentationConstructorSupplied ≡ true

    localLeftQuarkGenerationStructureConstructorSupplied :
      Bool

    localLeftQuarkGenerationStructureConstructorSuppliedIsTrue :
      localLeftQuarkGenerationStructureConstructorSupplied ≡ true

    leftQuarkDoubletMatterSurfaceRequestBoundary :
      List String

open LeftQuarkDoubletMatterSurfacePrimitiveRequest public

canonicalLeftQuarkDoubletMatterSurfacePrimitiveRequest :
  LeftQuarkDoubletMatterSurfacePrimitiveRequest
canonicalLeftQuarkDoubletMatterSurfacePrimitiveRequest =
  record
    { matterSectorTarget =
        Matter.leftQuarkDoubletTarget
    ; matterSectorTargetIsLeftQuarkDoublet =
        refl
    ; availableHyperchargeAssignment =
        Matter.hyperchargeAssignmentTarget Matter.leftQuarkDoubletTarget
    ; availableHyperchargeAssignmentIsMatterSurfaceTarget =
        refl
    ; matterSurfaceLeftQuarkDoubletFamilyPrimitive =
        Matter.canonicalLeftQuarkDoubletFamilyPrimitive
    ; matterSurfaceLeftQuarkDoubletFamilyPrimitiveIsCanonical =
        refl
    ; matterSurfaceSU3ColourTripletPrimitive =
        Matter.canonicalSU3ColourTripletPrimitive
    ; matterSurfaceSU3ColourTripletPrimitiveIsCanonical =
        refl
    ; matterSurfaceSU2LWeakDoubletPrimitive =
        Matter.canonicalSU2LWeakDoubletPrimitive
    ; matterSurfaceSU2LWeakDoubletPrimitiveIsCanonical =
        refl
    ; matterSurfaceHyperchargeOneSixthPrimitive =
        Matter.canonicalHyperchargeOneSixthPrimitive
    ; matterSurfaceHyperchargeOneSixthPrimitiveIsCanonical =
        refl
    ; matterSurfaceLeftChiralityPrimitive =
        Matter.leftChirality
    ; matterSurfaceLeftChiralityPrimitiveIsCanonical =
        refl
    ; matterSurfaceSixColourWeakComponentPrimitive =
        Matter.canonicalLeftQuarkSixColourWeakComponentPrimitive
    ; matterSurfaceSixColourWeakComponentPrimitiveIsCanonical =
        refl
    ; matterSurfaceThreeGenerationPrimitive =
        Matter.canonicalThreeGenerationPrimitive
    ; matterSurfaceThreeGenerationPrimitiveIsCanonical =
        refl
    ; matterSurfaceLeftQuarkDoubletFamilyMatterRepresentation =
        Matter.canonicalLeftQuarkDoubletFamilyMatterRepresentation
    ; matterSurfaceLeftQuarkDoubletFamilyMatterRepresentationIsCanonical =
        refl
    ; matterSurfaceThreeGenerationStructure =
        Matter.canonicalThreeGenerationStructure
    ; matterSurfaceThreeGenerationStructureIsCanonical =
        refl
    ; constructsConcreteLeftQuarkDoubletFamilyPrimitive =
        true
    ; constructsConcreteLeftQuarkDoubletFamilyPrimitiveIsTrue =
        refl
    ; keepsYukawaHiggsW4CKMAndPromotionOpen =
        true
    ; keepsYukawaHiggsW4CKMAndPromotionOpenIsTrue =
        refl
    ; localLeftQuarkMatterRepresentationConstructorSupplied =
        true
    ; localLeftQuarkMatterRepresentationConstructorSuppliedIsTrue =
        refl
    ; localLeftQuarkGenerationStructureConstructorSupplied =
        true
    ; localLeftQuarkGenerationStructureConstructorSuppliedIsTrue =
        refl
    ; leftQuarkDoubletMatterSurfaceRequestBoundary =
        "MatterRepresentationReceiptSurface supplies the generic hypercharge adapter at Matter.leftQuarkDoubletTarget, a concrete LeftQuarkDoubletFamilyPrimitive, a canonical three-generation structure, and a canonical left-quark MatterRepresentation witness"
        ∷ "Matter-surface primitive constructors give SU3_c triplet, SU2_L doublet, numeric U1_Y +1/6, left chirality, six colour-weak components per generation, and three-generation data"
        ∷ "The constructor witnesses are a local representation layer and do not supply a quark-family carrier value, Yukawa matrix, Higgs discharge, W4 calibration, CKM mixing, or promotion evidence"
        ∷ []
    }

record LeftQuarkCarrierFamilySuppliedEvidence : Setω where
  field
    matterSurfacePrimitiveRequest :
      LeftQuarkDoubletMatterSurfacePrimitiveRequest

    suppliedConstructors :
      List LeftQuarkCarrierFamilySuppliedEvidenceConstructor

    suppliedConstructorsAreCanonical :
      suppliedConstructors
      ≡
      canonicalLeftQuarkCarrierFamilySuppliedEvidenceConstructors

    leftQuarkMatterRepresentation :
      Matter.MatterRepresentation

    leftQuarkMatterRepresentationIsCanonical :
      leftQuarkMatterRepresentation
      ≡
      Matter.canonicalLeftQuarkDoubletFamilyMatterRepresentation

    leftQuarkFamilyPrimitive :
      Matter.LeftQuarkDoubletFamilyPrimitive

    leftQuarkFamilyPrimitiveIsCanonical :
      leftQuarkFamilyPrimitive
      ≡
      Matter.canonicalLeftQuarkDoubletFamilyPrimitive

    leftQuarkThreeGenerationStructure :
      Matter.GenerationStructure

    leftQuarkThreeGenerationStructureIsCanonical :
      leftQuarkThreeGenerationStructure
      ≡
      Matter.canonicalThreeGenerationStructure

    leftQuarkCarrierFamilyTyped :
      Bool

    leftQuarkCarrierFamilyTypedIsTrue :
      leftQuarkCarrierFamilyTyped ≡ true

    rightUpQuarkCarrierFamilyTyped :
      Bool

    rightUpQuarkCarrierFamilyTypedIsFalse :
      rightUpQuarkCarrierFamilyTyped ≡ false

    rightDownQuarkCarrierFamilyTyped :
      Bool

    rightDownQuarkCarrierFamilyTypedIsFalse :
      rightDownQuarkCarrierFamilyTyped ≡ false

    yukawaMatrixCarrierConstructedFromSuppliedEvidence :
      Bool

    yukawaMatrixCarrierConstructedFromSuppliedEvidenceIsFalse :
      yukawaMatrixCarrierConstructedFromSuppliedEvidence ≡ false

    dhrCompatibilityConstructedFromSuppliedEvidence :
      Bool

    dhrCompatibilityConstructedFromSuppliedEvidenceIsFalse :
      dhrCompatibilityConstructedFromSuppliedEvidence ≡ false

    w4CalibrationConstructedFromSuppliedEvidence :
      Bool

    w4CalibrationConstructedFromSuppliedEvidenceIsFalse :
      w4CalibrationConstructedFromSuppliedEvidence ≡ false

    ckmPromotionConstructedFromSuppliedEvidence :
      Bool

    ckmPromotionConstructedFromSuppliedEvidenceIsFalse :
      ckmPromotionConstructedFromSuppliedEvidence ≡ false

    suppliedEvidenceBoundary :
      List String

open LeftQuarkCarrierFamilySuppliedEvidence public

canonicalLeftQuarkCarrierFamilySuppliedEvidence :
  LeftQuarkCarrierFamilySuppliedEvidence
canonicalLeftQuarkCarrierFamilySuppliedEvidence =
  record
    { matterSurfacePrimitiveRequest =
        canonicalLeftQuarkDoubletMatterSurfacePrimitiveRequest
    ; suppliedConstructors =
        canonicalLeftQuarkCarrierFamilySuppliedEvidenceConstructors
    ; suppliedConstructorsAreCanonical =
        refl
    ; leftQuarkMatterRepresentation =
        Matter.canonicalLeftQuarkDoubletFamilyMatterRepresentation
    ; leftQuarkMatterRepresentationIsCanonical =
        refl
    ; leftQuarkFamilyPrimitive =
        Matter.canonicalLeftQuarkDoubletFamilyPrimitive
    ; leftQuarkFamilyPrimitiveIsCanonical =
        refl
    ; leftQuarkThreeGenerationStructure =
        Matter.canonicalThreeGenerationStructure
    ; leftQuarkThreeGenerationStructureIsCanonical =
        refl
    ; leftQuarkCarrierFamilyTyped =
        true
    ; leftQuarkCarrierFamilyTypedIsTrue =
        refl
    ; rightUpQuarkCarrierFamilyTyped =
        false
    ; rightUpQuarkCarrierFamilyTypedIsFalse =
        refl
    ; rightDownQuarkCarrierFamilyTyped =
        false
    ; rightDownQuarkCarrierFamilyTypedIsFalse =
        refl
    ; yukawaMatrixCarrierConstructedFromSuppliedEvidence =
        false
    ; yukawaMatrixCarrierConstructedFromSuppliedEvidenceIsFalse =
        refl
    ; dhrCompatibilityConstructedFromSuppliedEvidence =
        false
    ; dhrCompatibilityConstructedFromSuppliedEvidenceIsFalse =
        refl
    ; w4CalibrationConstructedFromSuppliedEvidence =
        false
    ; w4CalibrationConstructedFromSuppliedEvidenceIsFalse =
        refl
    ; ckmPromotionConstructedFromSuppliedEvidence =
        false
    ; ckmPromotionConstructedFromSuppliedEvidenceIsFalse =
        refl
    ; suppliedEvidenceBoundary =
        "MatterRepresentationReceiptSurface supplies typed left-quark matter representation, primitive, and three-generation constructors"
        ∷ "This discharges the left-quark doublet entry in the refined CKM quark-family blocker ledger"
        ∷ "Right-handed up/down quark families are not supplied, so the coarse left/right-family compatibility blocker remains open"
        ∷ "No Yukawa matrix carrier, DHR compatibility proof, W4 calibration, CKM matrix, or promotion is constructed from this evidence"
        ∷ []
    }

record RightHandedQuarkMatterSurfacePrimitiveRequest : Setω where
  field
    requestedPrimitives :
      List RightHandedQuarkCarrierPrimitiveRequest

    requestedPrimitivesAreCanonical :
      requestedPrimitives
      ≡
      canonicalRightHandedQuarkCarrierPrimitiveRequests

    rightUpMatterTarget :
      Matter.StandardModelMatterSectorTarget

    rightUpMatterTargetIsRightUpQuark :
      rightUpMatterTarget
      ≡
      Matter.rightUpQuarkTarget

    rightDownMatterTarget :
      Matter.StandardModelMatterSectorTarget

    rightDownMatterTargetIsRightDownQuark :
      rightDownMatterTarget
      ≡
      Matter.rightDownQuarkTarget

    rightUpMatterRepresentation :
      Matter.MatterRepresentation

    rightUpMatterRepresentationIsGenericAdapter :
      rightUpMatterRepresentation
      ≡
      canonicalRightUpQuarkFamilyMatterRepresentation

    rightDownMatterRepresentation :
      Matter.MatterRepresentation

    rightDownMatterRepresentationIsGenericAdapter :
      rightDownMatterRepresentation
      ≡
      canonicalRightDownQuarkFamilyMatterRepresentation

    rightQuarkColourTripletPrimitive :
      Matter.GaugeRepresentationPrimitive

    rightQuarkColourTripletPrimitiveIsCanonical :
      rightQuarkColourTripletPrimitive
      ≡
      Matter.canonicalSU3ColourTripletPrimitive

    rightQuarkWeakSingletPrimitive :
      Matter.GaugeRepresentationPrimitive

    rightQuarkWeakSingletPrimitiveIsCanonical :
      rightQuarkWeakSingletPrimitive
      ≡
      canonicalSU2LWeakSingletPrimitive

    rightUpHyperchargeTwoThirdsPrimitive :
      Matter.HyperchargePrimitive

    rightUpHyperchargeTwoThirdsPrimitiveIsCanonical :
      rightUpHyperchargeTwoThirdsPrimitive
      ≡
      canonicalHyperchargeTwoThirdsPrimitive

    rightDownHyperchargeMinusOneThirdPrimitive :
      Matter.HyperchargePrimitive

    rightDownHyperchargeMinusOneThirdPrimitiveIsCanonical :
      rightDownHyperchargeMinusOneThirdPrimitive
      ≡
      canonicalHyperchargeMinusOneThirdPrimitive

    rightQuarkChiralityPrimitive :
      Matter.ChiralityPrimitive

    rightQuarkChiralityPrimitiveIsRight :
      rightQuarkChiralityPrimitive
      ≡
      Matter.rightChirality

    rightQuarkThreeGenerationStructure :
      Matter.GenerationStructure

    rightQuarkThreeGenerationStructureIsCanonical :
      rightQuarkThreeGenerationStructure
      ≡
      Matter.canonicalThreeGenerationStructure

    rightUpCarrierFamilyTyped :
      Bool

    rightUpCarrierFamilyTypedIsTrue :
      rightUpCarrierFamilyTyped ≡ true

    rightDownCarrierFamilyTyped :
      Bool

    rightDownCarrierFamilyTypedIsTrue :
      rightDownCarrierFamilyTyped ≡ true

    constructsRightQuarkYukawaMatrix :
      Bool

    constructsRightQuarkYukawaMatrixIsFalse :
      constructsRightQuarkYukawaMatrix ≡ false

    constructsRightQuarkCKMOrW4Promotion :
      Bool

    constructsRightQuarkCKMOrW4PromotionIsFalse :
      constructsRightQuarkCKMOrW4Promotion ≡ false

    rightHandedQuarkMatterSurfaceBoundary :
      List String

open RightHandedQuarkMatterSurfacePrimitiveRequest public

canonicalRightHandedQuarkMatterSurfacePrimitiveRequest :
  RightHandedQuarkMatterSurfacePrimitiveRequest
canonicalRightHandedQuarkMatterSurfacePrimitiveRequest =
  record
    { requestedPrimitives =
        canonicalRightHandedQuarkCarrierPrimitiveRequests
    ; requestedPrimitivesAreCanonical =
        refl
    ; rightUpMatterTarget =
        Matter.rightUpQuarkTarget
    ; rightUpMatterTargetIsRightUpQuark =
        refl
    ; rightDownMatterTarget =
        Matter.rightDownQuarkTarget
    ; rightDownMatterTargetIsRightDownQuark =
        refl
    ; rightUpMatterRepresentation =
        canonicalRightUpQuarkFamilyMatterRepresentation
    ; rightUpMatterRepresentationIsGenericAdapter =
        refl
    ; rightDownMatterRepresentation =
        canonicalRightDownQuarkFamilyMatterRepresentation
    ; rightDownMatterRepresentationIsGenericAdapter =
        refl
    ; rightQuarkColourTripletPrimitive =
        Matter.canonicalSU3ColourTripletPrimitive
    ; rightQuarkColourTripletPrimitiveIsCanonical =
        refl
    ; rightQuarkWeakSingletPrimitive =
        canonicalSU2LWeakSingletPrimitive
    ; rightQuarkWeakSingletPrimitiveIsCanonical =
        refl
    ; rightUpHyperchargeTwoThirdsPrimitive =
        canonicalHyperchargeTwoThirdsPrimitive
    ; rightUpHyperchargeTwoThirdsPrimitiveIsCanonical =
        refl
    ; rightDownHyperchargeMinusOneThirdPrimitive =
        canonicalHyperchargeMinusOneThirdPrimitive
    ; rightDownHyperchargeMinusOneThirdPrimitiveIsCanonical =
        refl
    ; rightQuarkChiralityPrimitive =
        Matter.rightChirality
    ; rightQuarkChiralityPrimitiveIsRight =
        refl
    ; rightQuarkThreeGenerationStructure =
        Matter.canonicalThreeGenerationStructure
    ; rightQuarkThreeGenerationStructureIsCanonical =
        refl
    ; rightUpCarrierFamilyTyped =
        true
    ; rightUpCarrierFamilyTypedIsTrue =
        refl
    ; rightDownCarrierFamilyTyped =
        true
    ; rightDownCarrierFamilyTypedIsTrue =
        refl
    ; constructsRightQuarkYukawaMatrix =
        false
    ; constructsRightQuarkYukawaMatrixIsFalse =
        refl
    ; constructsRightQuarkCKMOrW4Promotion =
        false
    ; constructsRightQuarkCKMOrW4PromotionIsFalse =
        refl
    ; rightHandedQuarkMatterSurfaceBoundary =
        "Right-up and right-down quark families are typed through Matter.matterRepresentationAdapterTarget at Matter.rightUpQuarkTarget and Matter.rightDownQuarkTarget"
        ∷ "The supplied primitive ledger records SU3_c triplet, SU2_L singlet, U1_Y +2/3 for right-up, U1_Y -1/3 for right-down, right chirality, and the canonical three-generation structure"
        ∷ "This generic adapter evidence types right-handed families only; it does not construct a Yukawa matrix carrier, CKM matrix, W4 calibration, or promotion"
        ∷ []
    }

record RightHandedQuarkCarrierFamilySuppliedEvidence : Setω where
  field
    matterSurfacePrimitiveRequest :
      RightHandedQuarkMatterSurfacePrimitiveRequest

    suppliedConstructors :
      List RightHandedQuarkCarrierFamilySuppliedEvidenceConstructor

    suppliedConstructorsAreCanonical :
      suppliedConstructors
      ≡
      canonicalRightHandedQuarkCarrierFamilySuppliedEvidenceConstructors

    rightUpMatterRepresentation :
      Matter.MatterRepresentation

    rightUpMatterRepresentationIsCanonical :
      rightUpMatterRepresentation
      ≡
      canonicalRightUpQuarkFamilyMatterRepresentation

    rightDownMatterRepresentation :
      Matter.MatterRepresentation

    rightDownMatterRepresentationIsCanonical :
      rightDownMatterRepresentation
      ≡
      canonicalRightDownQuarkFamilyMatterRepresentation

    rightQuarkThreeGenerationStructure :
      Matter.GenerationStructure

    rightQuarkThreeGenerationStructureIsCanonical :
      rightQuarkThreeGenerationStructure
      ≡
      Matter.canonicalThreeGenerationStructure

    rightUpQuarkCarrierFamilyTyped :
      Bool

    rightUpQuarkCarrierFamilyTypedIsTrue :
      rightUpQuarkCarrierFamilyTyped ≡ true

    rightDownQuarkCarrierFamilyTyped :
      Bool

    rightDownQuarkCarrierFamilyTypedIsTrue :
      rightDownQuarkCarrierFamilyTyped ≡ true

    yukawaMatrixCarrierConstructedFromRightHandedEvidence :
      Bool

    yukawaMatrixCarrierConstructedFromRightHandedEvidenceIsFalse :
      yukawaMatrixCarrierConstructedFromRightHandedEvidence ≡ false

    dhrCompatibilityConstructedFromRightHandedEvidence :
      Bool

    dhrCompatibilityConstructedFromRightHandedEvidenceIsFalse :
      dhrCompatibilityConstructedFromRightHandedEvidence ≡ false

    w4CalibrationConstructedFromRightHandedEvidence :
      Bool

    w4CalibrationConstructedFromRightHandedEvidenceIsFalse :
      w4CalibrationConstructedFromRightHandedEvidence ≡ false

    ckmPromotionConstructedFromRightHandedEvidence :
      Bool

    ckmPromotionConstructedFromRightHandedEvidenceIsFalse :
      ckmPromotionConstructedFromRightHandedEvidence ≡ false

    suppliedRightHandedEvidenceBoundary :
      List String

open RightHandedQuarkCarrierFamilySuppliedEvidence public

canonicalRightHandedQuarkCarrierFamilySuppliedEvidence :
  RightHandedQuarkCarrierFamilySuppliedEvidence
canonicalRightHandedQuarkCarrierFamilySuppliedEvidence =
  record
    { matterSurfacePrimitiveRequest =
        canonicalRightHandedQuarkMatterSurfacePrimitiveRequest
    ; suppliedConstructors =
        canonicalRightHandedQuarkCarrierFamilySuppliedEvidenceConstructors
    ; suppliedConstructorsAreCanonical =
        refl
    ; rightUpMatterRepresentation =
        canonicalRightUpQuarkFamilyMatterRepresentation
    ; rightUpMatterRepresentationIsCanonical =
        refl
    ; rightDownMatterRepresentation =
        canonicalRightDownQuarkFamilyMatterRepresentation
    ; rightDownMatterRepresentationIsCanonical =
        refl
    ; rightQuarkThreeGenerationStructure =
        Matter.canonicalThreeGenerationStructure
    ; rightQuarkThreeGenerationStructureIsCanonical =
        refl
    ; rightUpQuarkCarrierFamilyTyped =
        true
    ; rightUpQuarkCarrierFamilyTypedIsTrue =
        refl
    ; rightDownQuarkCarrierFamilyTyped =
        true
    ; rightDownQuarkCarrierFamilyTypedIsTrue =
        refl
    ; yukawaMatrixCarrierConstructedFromRightHandedEvidence =
        false
    ; yukawaMatrixCarrierConstructedFromRightHandedEvidenceIsFalse =
        refl
    ; dhrCompatibilityConstructedFromRightHandedEvidence =
        false
    ; dhrCompatibilityConstructedFromRightHandedEvidenceIsFalse =
        refl
    ; w4CalibrationConstructedFromRightHandedEvidence =
        false
    ; w4CalibrationConstructedFromRightHandedEvidenceIsFalse =
        refl
    ; ckmPromotionConstructedFromRightHandedEvidence =
        false
    ; ckmPromotionConstructedFromRightHandedEvidenceIsFalse =
        refl
    ; suppliedRightHandedEvidenceBoundary =
        "Supplied evidence now types both right-handed quark carrier families through generic MatterRepresentation constructors"
        ∷ "The refined CKM quark-family blocker ledger advances past missingRightUpQuarkCarrierFamily and missingRightDownQuarkCarrierFamily"
        ∷ "The next exact blocker is the Yukawa matrix carrier; DHR compatibility, W4 calibration, CKM matrix construction, and promotion remain false"
        ∷ []
    }

data CKMYukawaSVDInterfaceComponent : Set where
  suppliedUpYukawaCarrierComponent :
    CKMYukawaSVDInterfaceComponent

  suppliedDownYukawaCarrierComponent :
    CKMYukawaSVDInterfaceComponent

  suppliedLeftBiunitaryComponent :
    CKMYukawaSVDInterfaceComponent

  suppliedRightBiunitaryComponent :
    CKMYukawaSVDInterfaceComponent

  suppliedSingularValueCarrierComponent :
    CKMYukawaSVDInterfaceComponent

canonicalCKMYukawaSVDInterfaceComponents :
  List CKMYukawaSVDInterfaceComponent
canonicalCKMYukawaSVDInterfaceComponents =
  suppliedUpYukawaCarrierComponent
  ∷ suppliedDownYukawaCarrierComponent
  ∷ suppliedLeftBiunitaryComponent
  ∷ suppliedRightBiunitaryComponent
  ∷ suppliedSingularValueCarrierComponent
  ∷ []

record CKMYukawaSVDInterfaceSupply : Setω where
  field
    leftQuarkCarrierFamilySuppliedEvidence :
      LeftQuarkCarrierFamilySuppliedEvidence

    rightHandedQuarkCarrierFamilySuppliedEvidence :
      RightHandedQuarkCarrierFamilySuppliedEvidence

    suppliedComponents :
      List CKMYukawaSVDInterfaceComponent

    suppliedComponentsAreCanonical :
      suppliedComponents
      ≡
      canonicalCKMYukawaSVDInterfaceComponents

    upYukawaCarrierTarget :
      Set

    upYukawaCarrierTargetIsTextureTarget :
      upYukawaCarrierTarget
      ≡
      Matter.YukawaTextureTarget

    downYukawaCarrierTarget :
      Set

    downYukawaCarrierTargetIsTextureTarget :
      downYukawaCarrierTarget
      ≡
      Matter.YukawaTextureTarget

    leftBiunitaryCarrierTarget :
      Set

    leftBiunitaryCarrierTargetIsMixingMatrix :
      leftBiunitaryCarrierTarget
      ≡
      Matter.MixingMatrix

    rightBiunitaryCarrierTarget :
      Set

    rightBiunitaryCarrierTargetIsMixingMatrix :
      rightBiunitaryCarrierTarget
      ≡
      Matter.MixingMatrix

    singularValueCarrierTarget :
      Set

    singularValueCarrierTargetIsYukawaSector :
      singularValueCarrierTarget
      ≡
      Matter.YukawaSector

    yukawaCarrierInterfaceSupplied :
      Bool

    yukawaCarrierInterfaceSuppliedIsTrue :
      yukawaCarrierInterfaceSupplied ≡ true

    svdInterfaceSupplied :
      Bool

    svdInterfaceSuppliedIsTrue :
      svdInterfaceSupplied ≡ true

    biunitaryDiagonalizationProofSupplied :
      Bool

    biunitaryDiagonalizationProofSuppliedIsFalse :
      biunitaryDiagonalizationProofSupplied ≡ false

    dhrIntertwinerCompatibilitySupplied :
      Bool

    dhrIntertwinerCompatibilitySuppliedIsFalse :
      dhrIntertwinerCompatibilitySupplied ≡ false

    weakToMassBasisIdentificationSupplied :
      Bool

    weakToMassBasisIdentificationSuppliedIsFalse :
      weakToMassBasisIdentificationSupplied ≡ false

    ckmMatrixConstructedFromSVD :
      Bool

    ckmMatrixConstructedFromSVDIsFalse :
      ckmMatrixConstructedFromSVD ≡ false

    ckmPromotionConstructedFromSVD :
      Bool

    ckmPromotionConstructedFromSVDIsFalse :
      ckmPromotionConstructedFromSVD ≡ false

    yukawaSVDInterfaceBoundary :
      List String

open CKMYukawaSVDInterfaceSupply public

canonicalCKMYukawaSVDInterfaceSupply :
  CKMYukawaSVDInterfaceSupply
canonicalCKMYukawaSVDInterfaceSupply =
  record
    { leftQuarkCarrierFamilySuppliedEvidence =
        canonicalLeftQuarkCarrierFamilySuppliedEvidence
    ; rightHandedQuarkCarrierFamilySuppliedEvidence =
        canonicalRightHandedQuarkCarrierFamilySuppliedEvidence
    ; suppliedComponents =
        canonicalCKMYukawaSVDInterfaceComponents
    ; suppliedComponentsAreCanonical =
        refl
    ; upYukawaCarrierTarget =
        Matter.YukawaTextureTarget
    ; upYukawaCarrierTargetIsTextureTarget =
        refl
    ; downYukawaCarrierTarget =
        Matter.YukawaTextureTarget
    ; downYukawaCarrierTargetIsTextureTarget =
        refl
    ; leftBiunitaryCarrierTarget =
        Matter.MixingMatrix
    ; leftBiunitaryCarrierTargetIsMixingMatrix =
        refl
    ; rightBiunitaryCarrierTarget =
        Matter.MixingMatrix
    ; rightBiunitaryCarrierTargetIsMixingMatrix =
        refl
    ; singularValueCarrierTarget =
        Matter.YukawaSector
    ; singularValueCarrierTargetIsYukawaSector =
        refl
    ; yukawaCarrierInterfaceSupplied =
        true
    ; yukawaCarrierInterfaceSuppliedIsTrue =
        refl
    ; svdInterfaceSupplied =
        true
    ; svdInterfaceSuppliedIsTrue =
        refl
    ; biunitaryDiagonalizationProofSupplied =
        false
    ; biunitaryDiagonalizationProofSuppliedIsFalse =
        refl
    ; dhrIntertwinerCompatibilitySupplied =
        false
    ; dhrIntertwinerCompatibilitySuppliedIsFalse =
        refl
    ; weakToMassBasisIdentificationSupplied =
        false
    ; weakToMassBasisIdentificationSuppliedIsFalse =
        refl
    ; ckmMatrixConstructedFromSVD =
        false
    ; ckmMatrixConstructedFromSVDIsFalse =
        refl
    ; ckmPromotionConstructedFromSVD =
        false
    ; ckmPromotionConstructedFromSVDIsFalse =
        refl
    ; yukawaSVDInterfaceBoundary =
        "Symbolic up/down Yukawa carrier targets and left/right SVD carrier targets are supplied as an interface"
        ∷ "This is not a numeric Yukawa matrix, a biunitary diagonalization proof, a DHR compatibility proof, or a CKM matrix construction"
        ∷ "The next exact blocker is DHR intertwiner compatibility for the supplied Yukawa/SVD interface"
        ∷ []
    }

record CKMLeftRightQuarkCarrierFamilyAdapterRequest : Setω where
  field
    matterPrimeLaneYukawaReceipt :
      Matter.MatterPrimeLaneYukawaFNReceipt

    leftRightQuarkMatterTargets :
      List Matter.StandardModelMatterSectorTarget

    leftRightQuarkMatterTargetsAreCanonical :
      leftRightQuarkMatterTargets
      ≡
      canonicalLeftRightQuarkMatterTargets

    leftQuarkDoubletCarrierTarget :
      Set

    leftQuarkDoubletCarrierFamilyDefinitionRequest :
      LeftQuarkDoubletCarrierFamilyDefinitionRequest

    leftQuarkDoubletCarrierFamilyDefinitionSurface :
      LeftQuarkDoubletCarrierFamilyDefinitionSurface

    leftQuarkCarrierFamilySuppliedEvidence :
      LeftQuarkCarrierFamilySuppliedEvidence

    rightHandedQuarkCarrierFamilySuppliedEvidence :
      RightHandedQuarkCarrierFamilySuppliedEvidence

    rightUpQuarkCarrierTarget :
      Set

    rightDownQuarkCarrierTarget :
      Set

    threeGenerationFamilyCarrierTarget :
      Set

    yukawaMatrixCarrierTarget :
      Set

    dhrCompatibilityTarget :
      Set

    yukawaSVDInterfaceSupply :
      CKMYukawaSVDInterfaceSupply

    quarkFamilyBlockers :
      List CKMLeftRightQuarkCarrierFamilyBlocker

    firstQuarkFamilyBlocker :
      CKMLeftRightQuarkCarrierFamilyBlocker

    matterTargetsRecorded :
      Bool

    matterTargetsRecordedIsTrue :
      matterTargetsRecorded ≡ true

    leftQuarkCarrierFamilyTyped :
      Bool

    leftQuarkCarrierFamilyTypedIsTrue :
      leftQuarkCarrierFamilyTyped ≡ true

    rightUpQuarkCarrierFamilyTyped :
      Bool

    rightUpQuarkCarrierFamilyTypedIsTrue :
      rightUpQuarkCarrierFamilyTyped ≡ true

    rightDownQuarkCarrierFamilyTyped :
      Bool

    rightDownQuarkCarrierFamilyTypedIsTrue :
      rightDownQuarkCarrierFamilyTyped ≡ true

    yukawaSVDInterfaceSupplied :
      Bool

    yukawaSVDInterfaceSuppliedIsTrue :
      yukawaSVDInterfaceSupplied ≡ true

    leftRightCarrierFamiliesConstructed :
      Bool

    leftRightCarrierFamiliesConstructedIsFalse :
      leftRightCarrierFamiliesConstructed ≡ false

    yukawaMatrixCarrierConstructed :
      Bool

    yukawaMatrixCarrierConstructedIsFalse :
      yukawaMatrixCarrierConstructed ≡ false

    dhrCompatibilityConstructedFromFamilies :
      Bool

    dhrCompatibilityConstructedFromFamiliesIsFalse :
      dhrCompatibilityConstructedFromFamilies ≡ false

    quarkFamilyRequestBoundary :
      List String

open CKMLeftRightQuarkCarrierFamilyAdapterRequest public

record CKMYukawaDHRCompatibilityRequest : Setω where
  field
    weakCarrierTarget :
      Set

    massCarrierTarget :
      Set

    yukawaMatrixTarget :
      Set

    dhrIntertwinerCompatibilityTarget :
      Set

    diagonalizationTarget :
      Set

    ckmMatrixTarget :
      Set

    unitarityTarget :
      Set

    leftRightQuarkCarrierFamilyRequest :
      CKMLeftRightQuarkCarrierFamilyAdapterRequest

    yukawaSVDInterfaceSupply :
      CKMYukawaSVDInterfaceSupply

    blockers :
      List CKMYukawaDHRCompatibilityBlocker

    firstCompatibilityBlocker :
      CKMYukawaDHRCompatibilityBlocker

    nextCompatibilityBlockerAfterRightHandedFamilySupply :
      CKMYukawaDHRCompatibilityBlocker

    nextCompatibilityBlockerAfterYukawaSVDInterfaceSupply :
      CKMYukawaDHRCompatibilityBlocker

    yukawaSVDInterfaceSupplied :
      Bool

    yukawaSVDInterfaceSuppliedIsTrue :
      yukawaSVDInterfaceSupplied ≡ true

    yukawaMatrixConstructed :
      Bool

    yukawaMatrixConstructedIsFalse :
      yukawaMatrixConstructed ≡ false

    dhrCompatibilityConstructed :
      Bool

    dhrCompatibilityConstructedIsFalse :
      dhrCompatibilityConstructed ≡ false

    diagonalizationConstructed :
      Bool

    diagonalizationConstructedIsFalse :
      diagonalizationConstructed ≡ false

    ckmUnitaryConstructed :
      Bool

    ckmUnitaryConstructedIsFalse :
      ckmUnitaryConstructed ≡ false

    requestBoundary :
      List String

open CKMYukawaDHRCompatibilityRequest public

record CKMCarrierMixingDependencyReceipt : Setω where
  field
    dependencies :
      List CKMCarrierMixingDependency

    dependenciesAreCanonical :
      dependencies
      ≡
      canonicalCKMCarrierMixingDependencies

    higgsDependency :
      Higgs.HiggsSymmetryBreakingDependencyReceipt

    higgsStillNotPromoted :
      Higgs.noHiggsPromotionFromDependencyReceipt higgsDependency
      ≡
      false

    higgsAdapter4BoundaryStillRequired :
      Higgs.vHiggsAdapter4Boundary higgsDependency
      ≡
      true

    firstMathematicalBlocker :
      CKMCarrierMixingDependency

    firstGovernanceBlocker :
      CKMCarrierMixingDependency

    dhrTransportRequired :
      Bool

    dhrTransportRequiredIsTrue :
      dhrTransportRequired ≡ true

    yukawaDiagonalizationConstructed :
      Bool

    yukawaDiagonalizationConstructedIsFalse :
      yukawaDiagonalizationConstructed ≡ false

    dhrYukawaDiagonalizationRequired :
      Bool

    dhrYukawaDiagonalizationRequiredIsTrue :
      dhrYukawaDiagonalizationRequired ≡ true

    carrierMixingTheoremConstructed :
      Bool

    carrierMixingTheoremConstructedIsFalse :
      carrierMixingTheoremConstructed ≡ false

    ckmCarrierMixingProvableFromCurrentSurface :
      Bool

    ckmCarrierMixingProvableFromCurrentSurfaceIsFalse :
      ckmCarrierMixingProvableFromCurrentSurface ≡ false

    noCKMPromotionFromDependencyReceipt :
      Bool

    noCKMPromotionFromDependencyReceiptIsFalse :
      noCKMPromotionFromDependencyReceipt ≡ false

open CKMCarrierMixingDependencyReceipt public

canonicalCKMCarrierMixingDependencyReceipt :
  CKMCarrierMixingDependencyReceipt
canonicalCKMCarrierMixingDependencyReceipt =
  record
    { dependencies =
        canonicalCKMCarrierMixingDependencies
    ; dependenciesAreCanonical =
        refl
    ; higgsDependency =
        Higgs.canonicalHiggsSymmetryBreakingDependencyReceipt
    ; higgsStillNotPromoted =
        refl
    ; higgsAdapter4BoundaryStillRequired =
        refl
    ; firstMathematicalBlocker =
        yukawaDiagonalizationDependency
    ; firstGovernanceBlocker =
        higgsSymmetryBreakingDependency
    ; dhrTransportRequired =
        true
    ; dhrTransportRequiredIsTrue =
        refl
    ; yukawaDiagonalizationConstructed =
        false
    ; yukawaDiagonalizationConstructedIsFalse =
        refl
    ; dhrYukawaDiagonalizationRequired =
        true
    ; dhrYukawaDiagonalizationRequiredIsTrue =
        refl
    ; carrierMixingTheoremConstructed =
        false
    ; carrierMixingTheoremConstructedIsFalse =
        refl
    ; ckmCarrierMixingProvableFromCurrentSurface =
        false
    ; ckmCarrierMixingProvableFromCurrentSurfaceIsFalse =
        refl
    ; noCKMPromotionFromDependencyReceipt =
        false
    ; noCKMPromotionFromDependencyReceiptIsFalse =
        refl
    }

postulate
  WeakEigenstateCarrier :
    Set

  MassEigenstateCarrier :
    Set

  abstractWeakEigenstate :
    WeakEigenstateCarrier

  abstractMassEigenstate :
    MassEigenstateCarrier

  abstractCarrierMixingMap :
    WeakEigenstateCarrier →
    MassEigenstateCarrier

  abstractUnitaryCKMTarget :
    Set

canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest :
  CKMLeftRightQuarkCarrierFamilyAdapterRequest
canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest =
  record
    { matterPrimeLaneYukawaReceipt =
        Matter.canonicalMatterPrimeLaneYukawaFNReceipt
    ; leftRightQuarkMatterTargets =
        canonicalLeftRightQuarkMatterTargets
    ; leftRightQuarkMatterTargetsAreCanonical =
        refl
    ; leftQuarkDoubletCarrierTarget =
        Matter.MatterRepresentation
    ; leftQuarkDoubletCarrierFamilyDefinitionRequest =
        canonicalLeftQuarkDoubletCarrierFamilyDefinitionRequest
    ; leftQuarkDoubletCarrierFamilyDefinitionSurface =
        canonicalLeftQuarkDoubletCarrierFamilyDefinitionSurface
    ; leftQuarkCarrierFamilySuppliedEvidence =
        canonicalLeftQuarkCarrierFamilySuppliedEvidence
    ; rightHandedQuarkCarrierFamilySuppliedEvidence =
        canonicalRightHandedQuarkCarrierFamilySuppliedEvidence
    ; rightUpQuarkCarrierTarget =
        Matter.MatterRepresentation
    ; rightDownQuarkCarrierTarget =
        Matter.MatterRepresentation
    ; threeGenerationFamilyCarrierTarget =
        Matter.GenerationStructure
    ; yukawaMatrixCarrierTarget =
        Matter.YukawaTextureTarget
    ; dhrCompatibilityTarget =
        Matter.YukawaTextureTarget
    ; yukawaSVDInterfaceSupply =
        canonicalCKMYukawaSVDInterfaceSupply
    ; quarkFamilyBlockers =
        canonicalCKMLeftRightQuarkCarrierFamilyBlockersAfterYukawaSVDInterfaceSupply
    ; firstQuarkFamilyBlocker =
        missingQuarkFamilyDHRCompatibility
    ; matterTargetsRecorded =
        true
    ; matterTargetsRecordedIsTrue =
        refl
    ; leftQuarkCarrierFamilyTyped =
        true
    ; leftQuarkCarrierFamilyTypedIsTrue =
        refl
    ; rightUpQuarkCarrierFamilyTyped =
        true
    ; rightUpQuarkCarrierFamilyTypedIsTrue =
        refl
    ; rightDownQuarkCarrierFamilyTyped =
        true
    ; rightDownQuarkCarrierFamilyTypedIsTrue =
        refl
    ; yukawaSVDInterfaceSupplied =
        true
    ; yukawaSVDInterfaceSuppliedIsTrue =
        refl
    ; leftRightCarrierFamiliesConstructed =
        false
    ; leftRightCarrierFamiliesConstructedIsFalse =
        refl
    ; yukawaMatrixCarrierConstructed =
        false
    ; yukawaMatrixCarrierConstructedIsFalse =
        refl
    ; dhrCompatibilityConstructedFromFamilies =
        false
    ; dhrCompatibilityConstructedFromFamiliesIsFalse =
        refl
    ; quarkFamilyRequestBoundary =
        "MatterRepresentationReceiptSurface records left/right quark sector labels and a conditional Yukawa texture target"
        ∷ "The left quark doublet target is typed by supplied MatterRepresentationReceiptSurface constructors for (3,2,1/6), left chirality, and three generations"
        ∷ "Right up and right down quark carrier families are typed by supplied generic MatterRepresentation constructors at their matter targets with SU2_L singlet, right chirality, and hypercharges +2/3 and -1/3"
        ∷ "A symbolic Yukawa/SVD interface is supplied; the first refined blocker is now missingQuarkFamilyDHRCompatibility"
        ∷ []
    }

canonicalCKMYukawaDHRCompatibilityRequest :
  CKMYukawaDHRCompatibilityRequest
canonicalCKMYukawaDHRCompatibilityRequest =
  record
    { weakCarrierTarget =
        WeakEigenstateCarrier
    ; massCarrierTarget =
        MassEigenstateCarrier
    ; yukawaMatrixTarget =
        Matter.YukawaTextureTarget
    ; dhrIntertwinerCompatibilityTarget =
        Matter.YukawaTextureTarget
    ; diagonalizationTarget =
        Matter.MixingMatrix
    ; ckmMatrixTarget =
        Matter.MixingMatrix
    ; unitarityTarget =
        abstractUnitaryCKMTarget
    ; leftRightQuarkCarrierFamilyRequest =
        canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
    ; yukawaSVDInterfaceSupply =
        canonicalCKMYukawaSVDInterfaceSupply
    ; blockers =
        canonicalCKMYukawaDHRCompatibilityBlockersAfterYukawaSVDInterfaceSupply
    ; firstCompatibilityBlocker =
        missingYukawaDHRIntertwinerCompatibility
    ; nextCompatibilityBlockerAfterRightHandedFamilySupply =
        missingYukawaMatrixCarrier
    ; nextCompatibilityBlockerAfterYukawaSVDInterfaceSupply =
        missingYukawaDHRIntertwinerCompatibility
    ; yukawaSVDInterfaceSupplied =
        true
    ; yukawaSVDInterfaceSuppliedIsTrue =
        refl
    ; yukawaMatrixConstructed =
        false
    ; yukawaMatrixConstructedIsFalse =
        refl
    ; dhrCompatibilityConstructed =
        false
    ; dhrCompatibilityConstructedIsFalse =
        refl
    ; diagonalizationConstructed =
        false
    ; diagonalizationConstructedIsFalse =
        refl
    ; ckmUnitaryConstructed =
        false
    ; ckmUnitaryConstructedIsFalse =
        refl
    ; requestBoundary =
        "This request separates Yukawa diagonalization from DHR transport compatibility"
        ∷ "Left, right-up, and right-down quark families are typed by supplied-evidence surfaces, and a symbolic Yukawa/SVD interface is supplied"
        ∷ "The first CKM/Yukawa compatibility blocker advances to DHR intertwiner compatibility for that supplied interface"
        ∷ "The DHR compatibility proof must use the Paper 2 intertwiner carrier action, not the lane table alone"
        ∷ "CKM unitarity is downstream of biunitary diagonalization and weak-to-mass basis identification"
        ∷ []
    }

data CKMUnitarityTransportRequestComponent : Set where
  suppliedYukawaSVDInterfaceForUnitarityComponent :
    CKMUnitarityTransportRequestComponent

  requestedBiunitaryDiagonalizationLawComponent :
    CKMUnitarityTransportRequestComponent

  requestedWeakToMassBasisIdentificationLawComponent :
    CKMUnitarityTransportRequestComponent

  requestedCKMMatrixAsLeftUnitaryMismatchComponent :
    CKMUnitarityTransportRequestComponent

  requestedCKMUnitarityTransportLawComponent :
    CKMUnitarityTransportRequestComponent

canonicalCKMUnitarityTransportRequestComponents :
  List CKMUnitarityTransportRequestComponent
canonicalCKMUnitarityTransportRequestComponents =
  suppliedYukawaSVDInterfaceForUnitarityComponent
  ∷ requestedBiunitaryDiagonalizationLawComponent
  ∷ requestedWeakToMassBasisIdentificationLawComponent
  ∷ requestedCKMMatrixAsLeftUnitaryMismatchComponent
  ∷ requestedCKMUnitarityTransportLawComponent
  ∷ []

data CKMUnitarityTransportRequest : Set where
  requestedCKMUnitarityTransportFromYukawaSVD :
    CKMUnitarityTransportRequest

canonicalCKMUnitarityTransportRequest :
  CKMUnitarityTransportRequest
canonicalCKMUnitarityTransportRequest =
  requestedCKMUnitarityTransportFromYukawaSVD

record CKMYukawaSVDCKMUnitarityRequest : Setω where
  field
    compatibilityRequest :
      CKMYukawaDHRCompatibilityRequest

    yukawaSVDInterfaceSupply :
      CKMYukawaSVDInterfaceSupply

    unitarityTransportRequest :
      CKMUnitarityTransportRequest

    unitarityTransportRequestIsCanonical :
      unitarityTransportRequest
      ≡
      canonicalCKMUnitarityTransportRequest

    unitarityRequestComponents :
      List CKMUnitarityTransportRequestComponent

    unitarityRequestComponentsAreCanonical :
      unitarityRequestComponents
      ≡
      canonicalCKMUnitarityTransportRequestComponents

    ckmMatrixTarget :
      Set

    ckmMatrixTargetIsMixingMatrix :
      ckmMatrixTarget
      ≡
      Matter.MixingMatrix

    ckmUnitaryTarget :
      Set

    ckmUnitaryTargetIsCanonical :
      ckmUnitaryTarget
      ≡
      abstractUnitaryCKMTarget

    yukawaSVDInterfaceSupplied :
      Bool

    yukawaSVDInterfaceSuppliedIsTrue :
      yukawaSVDInterfaceSupplied ≡ true

    biunitaryDiagonalizationProofSupplied :
      Bool

    biunitaryDiagonalizationProofSuppliedIsFalse :
      biunitaryDiagonalizationProofSupplied ≡ false

    weakToMassBasisIdentificationSupplied :
      Bool

    weakToMassBasisIdentificationSuppliedIsFalse :
      weakToMassBasisIdentificationSupplied ≡ false

    ckmMatrixConstructed :
      Bool

    ckmMatrixConstructedIsFalse :
      ckmMatrixConstructed ≡ false

    ckmUnitarityTransportSupplied :
      Bool

    ckmUnitarityTransportSuppliedIsFalse :
      ckmUnitarityTransportSupplied ≡ false

    ckmUnitarityRequestPromoted :
      Bool

    ckmUnitarityRequestPromotedIsFalse :
      ckmUnitarityRequestPromoted ≡ false

    ckmUnitarityRequestBoundary :
      List String

open CKMYukawaSVDCKMUnitarityRequest public

canonicalCKMYukawaSVDCKMUnitarityRequest :
  CKMYukawaSVDCKMUnitarityRequest
canonicalCKMYukawaSVDCKMUnitarityRequest =
  record
    { compatibilityRequest =
        canonicalCKMYukawaDHRCompatibilityRequest
    ; yukawaSVDInterfaceSupply =
        canonicalCKMYukawaSVDInterfaceSupply
    ; unitarityTransportRequest =
        canonicalCKMUnitarityTransportRequest
    ; unitarityTransportRequestIsCanonical =
        refl
    ; unitarityRequestComponents =
        canonicalCKMUnitarityTransportRequestComponents
    ; unitarityRequestComponentsAreCanonical =
        refl
    ; ckmMatrixTarget =
        Matter.MixingMatrix
    ; ckmMatrixTargetIsMixingMatrix =
        refl
    ; ckmUnitaryTarget =
        abstractUnitaryCKMTarget
    ; ckmUnitaryTargetIsCanonical =
        refl
    ; yukawaSVDInterfaceSupplied =
        true
    ; yukawaSVDInterfaceSuppliedIsTrue =
        refl
    ; biunitaryDiagonalizationProofSupplied =
        false
    ; biunitaryDiagonalizationProofSuppliedIsFalse =
        refl
    ; weakToMassBasisIdentificationSupplied =
        false
    ; weakToMassBasisIdentificationSuppliedIsFalse =
        refl
    ; ckmMatrixConstructed =
        false
    ; ckmMatrixConstructedIsFalse =
        refl
    ; ckmUnitarityTransportSupplied =
        false
    ; ckmUnitarityTransportSuppliedIsFalse =
        refl
    ; ckmUnitarityRequestPromoted =
        false
    ; ckmUnitarityRequestPromotedIsFalse =
        refl
    ; ckmUnitarityRequestBoundary =
        "The Yukawa/SVD carrier interface is available as a conditional input to CKM unitarity transport"
        ∷ "The requested law is: biunitary diagonalization plus weak-to-mass basis identification yields the CKM matrix as a unitary left-basis mismatch"
        ∷ "No diagonalization proof, weak-to-mass identification, CKM matrix, unitarity transport proof, W4 numeric calibration, or CKM promotion is supplied"
        ∷ []
    }

record CKMCarrierMixingReceipt : Setω where
  field
    status :
      CKMCarrierMixingStatus

    higgsSymmetryBreakingReceipt :
      Higgs.HiggsSymmetryBreakingReceipt

    weakEigenstates :
      Set

    massEigenstates :
      Set

    weakEigenstateWitness :
      weakEigenstates

    massEigenstateWitness :
      massEigenstates

    carrierMixingMap :
      weakEigenstates →
      massEigenstates

    unitaryCKMTarget :
      Set

    yukawaDHRCompatibilityRequest :
      CKMYukawaDHRCompatibilityRequest

    yukawaSVDCKMUnitarityRequest :
      CKMYukawaSVDCKMUnitarityRequest

    anglePhaseTargets :
      List CKMAnglePhaseTarget

    firstMissing :
      CKMCarrierMixingFirstMissing

    openObligations :
      List CKMCarrierMixingOpenObligation

    ckmCarrierMixingPromoted :
      Bool

    ckmCarrierMixingPromotedIsFalse :
      ckmCarrierMixingPromoted ≡ false

    nonPromotionBoundary :
      List String

open CKMCarrierMixingReceipt public

canonicalCKMCarrierMixingReceipt :
  CKMCarrierMixingReceipt
canonicalCKMCarrierMixingReceipt =
  record
    { status =
        ckmCarrierMixingTargetsOnlyNoPromotion
    ; higgsSymmetryBreakingReceipt =
        Higgs.canonicalHiggsSymmetryBreakingReceipt
    ; weakEigenstates =
        WeakEigenstateCarrier
    ; massEigenstates =
        MassEigenstateCarrier
    ; weakEigenstateWitness =
        abstractWeakEigenstate
    ; massEigenstateWitness =
        abstractMassEigenstate
    ; carrierMixingMap =
        abstractCarrierMixingMap
    ; unitaryCKMTarget =
        abstractUnitaryCKMTarget
    ; yukawaDHRCompatibilityRequest =
        canonicalCKMYukawaDHRCompatibilityRequest
    ; yukawaSVDCKMUnitarityRequest =
        canonicalCKMYukawaSVDCKMUnitarityRequest
    ; anglePhaseTargets =
        canonicalCKMAnglePhaseTargets
    ; firstMissing =
        missingCarrierMixingTheorem
    ; openObligations =
        canonicalCKMCarrierMixingOpenObligations
    ; ckmCarrierMixingPromoted =
        false
    ; ckmCarrierMixingPromotedIsFalse =
        refl
    ; nonPromotionBoundary =
        "weak eigenstates, mass eigenstates, carrier mixing map, unitary CKM target, and angle/phase targets are receipt targets only"
        ∷ "first missing theorem is missingCarrierMixingTheorem"
        ∷ "Yukawa/SVD-to-CKM unitarity is recorded as a conditional request, with diagonalization and basis-identification proofs still absent"
        ∷ "CKM carrier mixing remains blocked until DHR transport and Yukawa diagonalization are supplied together"
        ∷ "this surface does not derive CKM, Yukawa closure, Higgs closure, Standard Model closure, or terminal promotion"
        ∷ []
    }

canonicalCKMExactCarrierMixingTheoremWitness :
  Exact.CarrierMixingTheoremWitness
canonicalCKMExactCarrierMixingTheoremWitness =
  Exact.CKMExactWitnessChain.carrierMixingTheorem
    Exact.canonicalCKMExactWitnessChain

canonicalCKMHiggsAdapter4BoundaryWitness :
  Bool
canonicalCKMHiggsAdapter4BoundaryWitness =
  Higgs.vHiggsAdapter4Boundary
    Higgs.canonicalHiggsSymmetryBreakingDependencyReceipt

canonicalCKMHiggsAdapter4BoundaryWitnessIsTrue :
  canonicalCKMHiggsAdapter4BoundaryWitness ≡ true
canonicalCKMHiggsAdapter4BoundaryWitnessIsTrue =
  refl

ckmCarrierMixingDependencyKeepsHiggsAdapter4Boundary :
  Higgs.vHiggsAdapter4Boundary
    (higgsDependency canonicalCKMCarrierMixingDependencyReceipt)
  ≡
  true
ckmCarrierMixingDependencyKeepsHiggsAdapter4Boundary =
  refl

ckmCarrierMixingDependencyRequiresDHRTransport :
  dhrTransportRequired canonicalCKMCarrierMixingDependencyReceipt
  ≡
  true
ckmCarrierMixingDependencyRequiresDHRTransport =
  refl

ckmCarrierMixingDependencyKeepsYukawaDiagonalizationOpen :
  yukawaDiagonalizationConstructed canonicalCKMCarrierMixingDependencyReceipt
  ≡
  false
ckmCarrierMixingDependencyKeepsYukawaDiagonalizationOpen =
  refl

ckmYukawaDHRCompatibilityFirstBlocker :
  firstCompatibilityBlocker canonicalCKMYukawaDHRCompatibilityRequest
  ≡
  missingYukawaDHRIntertwinerCompatibility
ckmYukawaDHRCompatibilityFirstBlocker =
  refl

ckmYukawaDHRCompatibilityNextBlockerAfterRightHandedFamilySupply :
  nextCompatibilityBlockerAfterRightHandedFamilySupply
    canonicalCKMYukawaDHRCompatibilityRequest
  ≡
  missingYukawaMatrixCarrier
ckmYukawaDHRCompatibilityNextBlockerAfterRightHandedFamilySupply =
  refl

ckmYukawaDHRCompatibilityNextBlockerAfterYukawaSVDInterfaceSupply :
  nextCompatibilityBlockerAfterYukawaSVDInterfaceSupply
    canonicalCKMYukawaDHRCompatibilityRequest
  ≡
  missingYukawaDHRIntertwinerCompatibility
ckmYukawaDHRCompatibilityNextBlockerAfterYukawaSVDInterfaceSupply =
  refl

ckmLeftRightQuarkFamilyRequestFirstBlocker :
  firstQuarkFamilyBlocker
    canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
  ≡
  missingQuarkFamilyDHRCompatibility
ckmLeftRightQuarkFamilyRequestFirstBlocker =
  refl

------------------------------------------------------------------------
-- W4 authority handoff for this lane.

-- When Higgs W4 authority is unavailable (as recorded in the dependency
-- receipt), this lane proceeds via concrete Yukawa/CKM matrix blockers and
-- DHR-compatibility blockers instead of the W4 scale blocker.

record CKMYukawaCKMPostW4Transition : Set where
  field
    w4AuthorityUnavailable :
      Higgs.externalW4AuthorityAvailable
        (higgsDependency canonicalCKMCarrierMixingDependencyReceipt)
      ≡
      false

    concreteYukawaMatrixFirstMissing :
      Field.CKMArithmeticInputSlot

    concreteYukawaMatrixFirstMissingIsUp :
      concreteYukawaMatrixFirstMissing
      ≡
      Field.missingConcreteUpYukawa3x3Matrix

    dhrCompatibilityFirstBlockerAfterHandOff :
      CKMYukawaDHRCompatibilityBlocker

    dhrCompatibilityFirstBlockerAfterHandOffIsIntertwiner :
      dhrCompatibilityFirstBlockerAfterHandOff
      ≡
      missingYukawaDHRIntertwinerCompatibility

    transitionBoundary :
      List String

open CKMYukawaCKMPostW4Transition public

canonicalCKMYukawaCKMPostW4Transition :
  CKMYukawaCKMPostW4Transition
canonicalCKMYukawaCKMPostW4Transition =
  record
    { w4AuthorityUnavailable =
        Higgs.higgsSymmetryBreakingDependencyReceiptNoExternalW4Authority
    ; concreteYukawaMatrixFirstMissing =
        Field.missingConcreteUpYukawa3x3Matrix
    ; concreteYukawaMatrixFirstMissingIsUp =
        refl
    ; dhrCompatibilityFirstBlockerAfterHandOff =
        missingYukawaDHRIntertwinerCompatibility
    ; dhrCompatibilityFirstBlockerAfterHandOffIsIntertwiner =
        refl
    ; transitionBoundary =
        "No external W4 authority is inhabited in the Higgs dependency receipt"
        ∷ "This lane therefore prioritizes concrete quark Yukawa matrix inventory blockers from CKMEntryField"
        ∷ "The first concrete arithmetic blocker is missingConcreteUpYukawa3x3Matrix"
        ∷ "The leading CKM/DHR blocker remains missingYukawaDHRIntertwinerCompatibility"
        ∷ "No CKM/Higgs terminal promotion is introduced by this transition surface"
        ∷ []
    }

ckmPostW4TransitionKeepsConcreteMatrixOpen :
  concreteYukawaMatrixFirstMissing
    canonicalCKMYukawaCKMPostW4Transition
  ≡
  Field.missingConcreteUpYukawa3x3Matrix
ckmPostW4TransitionKeepsConcreteMatrixOpen =
  refl

ckmPostW4TransitionKeepsDHRIntertwinerOpen :
  dhrCompatibilityFirstBlockerAfterHandOff
    canonicalCKMYukawaCKMPostW4Transition
  ≡
  missingYukawaDHRIntertwinerCompatibility
ckmPostW4TransitionKeepsDHRIntertwinerOpen =
  refl

ckmYukawaSVDInterfaceSupplyRecordsInterface :
  yukawaCarrierInterfaceSupplied canonicalCKMYukawaSVDInterfaceSupply
  ≡
  true
ckmYukawaSVDInterfaceSupplyRecordsInterface =
  refl

ckmYukawaSVDInterfaceSupplyRecordsSVDInterface :
  svdInterfaceSupplied canonicalCKMYukawaSVDInterfaceSupply
  ≡
  true
ckmYukawaSVDInterfaceSupplyRecordsSVDInterface =
  refl

ckmYukawaSVDCKMUnitarityRequestRecordsSVDInput :
  yukawaSVDInterfaceSupplied canonicalCKMYukawaSVDCKMUnitarityRequest
  ≡
  true
ckmYukawaSVDCKMUnitarityRequestRecordsSVDInput =
  refl

ckmYukawaSVDCKMUnitarityRequestKeepsDiagonalizationOpen :
  biunitaryDiagonalizationProofSupplied
    canonicalCKMYukawaSVDCKMUnitarityRequest
  ≡
  false
ckmYukawaSVDCKMUnitarityRequestKeepsDiagonalizationOpen =
  refl

ckmYukawaSVDCKMUnitarityRequestKeepsUnitarityOpen :
  ckmUnitarityTransportSupplied
    canonicalCKMYukawaSVDCKMUnitarityRequest
  ≡
  false
ckmYukawaSVDCKMUnitarityRequestKeepsUnitarityOpen =
  refl

ckmYukawaSVDCKMUnitarityRequestDoesNotPromote :
  ckmUnitarityRequestPromoted
    canonicalCKMYukawaSVDCKMUnitarityRequest
  ≡
  false
ckmYukawaSVDCKMUnitarityRequestDoesNotPromote =
  refl

ckmLeftQuarkCarrierFamilySuppliedEvidenceIsTyped :
  leftQuarkCarrierFamilyTyped
    canonicalLeftQuarkCarrierFamilySuppliedEvidence
  ≡
  true
ckmLeftQuarkCarrierFamilySuppliedEvidenceIsTyped =
  refl

ckmLeftQuarkCarrierFamilySuppliedEvidenceKeepsYukawaOpen :
  yukawaMatrixCarrierConstructedFromSuppliedEvidence
    canonicalLeftQuarkCarrierFamilySuppliedEvidence
  ≡
  false
ckmLeftQuarkCarrierFamilySuppliedEvidenceKeepsYukawaOpen =
  refl

ckmRightUpQuarkCarrierFamilySuppliedEvidenceIsTyped :
  rightUpQuarkCarrierFamilyTyped
    canonicalRightHandedQuarkCarrierFamilySuppliedEvidence
  ≡
  true
ckmRightUpQuarkCarrierFamilySuppliedEvidenceIsTyped =
  refl

ckmRightDownQuarkCarrierFamilySuppliedEvidenceIsTyped :
  rightDownQuarkCarrierFamilyTyped
    canonicalRightHandedQuarkCarrierFamilySuppliedEvidence
  ≡
  true
ckmRightDownQuarkCarrierFamilySuppliedEvidenceIsTyped =
  refl

ckmRightHandedQuarkCarrierFamilySuppliedEvidenceKeepsYukawaOpen :
  yukawaMatrixCarrierConstructedFromRightHandedEvidence
    canonicalRightHandedQuarkCarrierFamilySuppliedEvidence
  ≡
  false
ckmRightHandedQuarkCarrierFamilySuppliedEvidenceKeepsYukawaOpen =
  refl

ckmLeftRightQuarkFamilyRequestRecordsLeftQuarkTyped :
  leftQuarkCarrierFamilyTyped
    canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
  ≡
  true
ckmLeftRightQuarkFamilyRequestRecordsLeftQuarkTyped =
  refl

ckmLeftRightQuarkFamilyRequestRecordsRightUpTyped :
  rightUpQuarkCarrierFamilyTyped
    canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
  ≡
  true
ckmLeftRightQuarkFamilyRequestRecordsRightUpTyped =
  refl

ckmLeftRightQuarkFamilyRequestRecordsRightDownTyped :
  rightDownQuarkCarrierFamilyTyped
    canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
  ≡
  true
ckmLeftRightQuarkFamilyRequestRecordsRightDownTyped =
  refl

ckmLeftQuarkDoubletCarrierFamilyRequestIsLeftQuarkTarget :
  matterSectorTarget
    canonicalLeftQuarkDoubletCarrierFamilyDefinitionRequest
  ≡
  Matter.leftQuarkDoubletTarget
ckmLeftQuarkDoubletCarrierFamilyRequestIsLeftQuarkTarget =
  refl

ckmLeftQuarkDoubletCarrierFamilyRequestKeepsFamilyOpen :
  leftQuarkDoubletFamilyConstructed
    canonicalLeftQuarkDoubletCarrierFamilyDefinitionRequest
  ≡
  false
ckmLeftQuarkDoubletCarrierFamilyRequestKeepsFamilyOpen =
  refl

ckmLeftQuarkDoubletCarrierFamilySurfaceRecordsLeftQuarkTarget :
  leftQuarkMatterTarget
    canonicalLeftQuarkDoubletCarrierFamilyDefinitionSurface
  ≡
  Matter.leftQuarkDoubletTarget
ckmLeftQuarkDoubletCarrierFamilySurfaceRecordsLeftQuarkTarget =
  refl

ckmLeftQuarkDoubletCarrierFamilySurfaceKeepsFamilyOpen :
  leftQuarkDoubletFamilySurfaceConstructed
    canonicalLeftQuarkDoubletCarrierFamilyDefinitionSurface
  ≡
  false
ckmLeftQuarkDoubletCarrierFamilySurfaceKeepsFamilyOpen =
  refl

ckmLeftQuarkDoubletCarrierFamilySurfaceKeepsCKMClosed :
  leftQuarkCKMMixingSurfaceConstructed
    canonicalLeftQuarkDoubletCarrierFamilyDefinitionSurface
  ≡
  false
ckmLeftQuarkDoubletCarrierFamilySurfaceKeepsCKMClosed =
  refl

ckmLeftQuarkDoubletCarrierFamilySurfaceKeepsW4Closed :
  leftQuarkW4CalibrationSurfaceConstructed
    canonicalLeftQuarkDoubletCarrierFamilyDefinitionSurface
  ≡
  false
ckmLeftQuarkDoubletCarrierFamilySurfaceKeepsW4Closed =
  refl

ckmLeftQuarkDoubletFamilyPrimitiveWitnessRecordsLeftQuarkTarget :
  matterSectorTarget canonicalLeftQuarkDoubletFamilyPrimitiveWitness
  ≡
  Matter.leftQuarkDoubletTarget
ckmLeftQuarkDoubletFamilyPrimitiveWitnessRecordsLeftQuarkTarget =
  refl

ckmLeftQuarkDoubletFamilyPrimitiveWitnessKeepsConcreteFamilyOpen :
  primitiveWitnessConstructsConcreteFamily
    canonicalLeftQuarkDoubletFamilyPrimitiveWitness
  ≡
  false
ckmLeftQuarkDoubletFamilyPrimitiveWitnessKeepsConcreteFamilyOpen =
  refl

ckmLeftQuarkDoubletFamilyPrimitiveWitnessKeepsYukawaCKMOpen :
  primitiveWitnessConstructsYukawaOrCKM
    canonicalLeftQuarkDoubletFamilyPrimitiveWitness
  ≡
  false
ckmLeftQuarkDoubletFamilyPrimitiveWitnessKeepsYukawaCKMOpen =
  refl

ckmLeftQuarkDoubletFamilyPrimitiveWitnessKeepsHiggsW4Open :
  primitiveWitnessDischargesHiggsOrW4
    canonicalLeftQuarkDoubletFamilyPrimitiveWitness
  ≡
  false
ckmLeftQuarkDoubletFamilyPrimitiveWitnessKeepsHiggsW4Open =
  refl

ckmLeftQuarkDoubletFamilyPrimitiveWitnessKeepsPromotionClosed :
  primitiveWitnessPromotesCKM
    canonicalLeftQuarkDoubletFamilyPrimitiveWitness
  ≡
  false
ckmLeftQuarkDoubletFamilyPrimitiveWitnessKeepsPromotionClosed =
  refl

ckmLeftRightQuarkFamilyRequestUsesLeftQuarkSurfaceTarget :
  leftQuarkMatterTarget
    (leftQuarkDoubletCarrierFamilyDefinitionSurface
    canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
    )
  ≡
  Matter.leftQuarkDoubletTarget
ckmLeftRightQuarkFamilyRequestUsesLeftQuarkSurfaceTarget =
  refl

ckmLeftRightQuarkFamilyRequestRecordsMatterTargets :
  matterTargetsRecorded canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
  ≡
  true
ckmLeftRightQuarkFamilyRequestRecordsMatterTargets =
  refl

ckmLeftRightQuarkFamilyRequestKeepsFamiliesOpen :
  leftRightCarrierFamiliesConstructed
    canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
  ≡
  false
ckmLeftRightQuarkFamilyRequestKeepsFamiliesOpen =
  refl

ckmLeftRightQuarkFamilyRequestKeepsYukawaOpen :
  yukawaMatrixCarrierConstructed
    canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
  ≡
  false
ckmLeftRightQuarkFamilyRequestKeepsYukawaOpen =
  refl

ckmYukawaDHRCompatibilityKeepsYukawaOpen :
  yukawaMatrixConstructed canonicalCKMYukawaDHRCompatibilityRequest
  ≡
  false
ckmYukawaDHRCompatibilityKeepsYukawaOpen =
  refl

ckmYukawaDHRCompatibilityKeepsDHRCompatibilityOpen :
  dhrCompatibilityConstructed canonicalCKMYukawaDHRCompatibilityRequest
  ≡
  false
ckmYukawaDHRCompatibilityKeepsDHRCompatibilityOpen =
  refl

ckmCarrierMixingDependencyRequiresDHRYukawaDiagonalization :
  dhrYukawaDiagonalizationRequired canonicalCKMCarrierMixingDependencyReceipt
  ≡
  true
ckmCarrierMixingDependencyRequiresDHRYukawaDiagonalization =
  refl

ckmCarrierMixingDependencyKeepsCarrierMixingOpen :
  carrierMixingTheoremConstructed canonicalCKMCarrierMixingDependencyReceipt
  ≡
  false
ckmCarrierMixingDependencyKeepsCarrierMixingOpen =
  refl

ckmCarrierMixingDependencyNotProvableFromCurrentSurface :
  ckmCarrierMixingProvableFromCurrentSurface
    canonicalCKMCarrierMixingDependencyReceipt
  ≡
  false
ckmCarrierMixingDependencyNotProvableFromCurrentSurface =
  refl

ckmCarrierMixingDependencyReceiptDoesNotPromote :
  noCKMPromotionFromDependencyReceipt canonicalCKMCarrierMixingDependencyReceipt
  ≡
  false
ckmCarrierMixingDependencyReceiptDoesNotPromote =
  refl

ckmCarrierMixingCanonicalReceiptStillNotPromoted :
  ckmCarrierMixingPromoted canonicalCKMCarrierMixingReceipt
  ≡
  false
ckmCarrierMixingCanonicalReceiptStillNotPromoted =
  refl

data CKMYukawaDHRCompatibilityInterfaceComponent : Set where
  suppliedLeftQuarkCarrierFamilyComponent :
    CKMYukawaDHRCompatibilityInterfaceComponent

  suppliedRightHandedQuarkCarrierFamiliesComponent :
    CKMYukawaDHRCompatibilityInterfaceComponent

  suppliedUpDownYukawaCarrierTargetsComponent :
    CKMYukawaDHRCompatibilityInterfaceComponent

  suppliedBiunitarySVDCarrierTargetsComponent :
    CKMYukawaDHRCompatibilityInterfaceComponent

  requestedDHRIntertwinerActionComponent :
    CKMYukawaDHRCompatibilityInterfaceComponent

  requestedYukawaDHRCompatibilityLawComponent :
    CKMYukawaDHRCompatibilityInterfaceComponent

canonicalCKMYukawaDHRCompatibilityInterfaceComponents :
  List CKMYukawaDHRCompatibilityInterfaceComponent
canonicalCKMYukawaDHRCompatibilityInterfaceComponents =
  suppliedLeftQuarkCarrierFamilyComponent
  ∷ suppliedRightHandedQuarkCarrierFamiliesComponent
  ∷ suppliedUpDownYukawaCarrierTargetsComponent
  ∷ suppliedBiunitarySVDCarrierTargetsComponent
  ∷ requestedDHRIntertwinerActionComponent
  ∷ requestedYukawaDHRCompatibilityLawComponent
  ∷ []

record CKMYukawaDHRCompatibilitySuppliedInterface : Setω where
  field
    ckmYukawaDHRInterfaceLeftRightRequest :
      CKMLeftRightQuarkCarrierFamilyAdapterRequest

    ckmYukawaDHRInterfaceSVDInterfaceSupply :
      CKMYukawaSVDInterfaceSupply

    ckmYukawaDHRInterfaceComponents :
      List CKMYukawaDHRCompatibilityInterfaceComponent

    ckmYukawaDHRInterfaceComponentsAreCanonical :
      ckmYukawaDHRInterfaceComponents
      ≡
      canonicalCKMYukawaDHRCompatibilityInterfaceComponents

    ckmYukawaDHRInterfaceWeakCarrierTarget :
      Set

    ckmYukawaDHRInterfaceWeakCarrierTargetIsCanonical :
      ckmYukawaDHRInterfaceWeakCarrierTarget
      ≡
      WeakEigenstateCarrier

    ckmYukawaDHRInterfaceMassCarrierTarget :
      Set

    ckmYukawaDHRInterfaceMassCarrierTargetIsCanonical :
      ckmYukawaDHRInterfaceMassCarrierTarget
      ≡
      MassEigenstateCarrier

    ckmYukawaDHRInterfaceYukawaMatrixTarget :
      Set

    ckmYukawaDHRInterfaceYukawaMatrixTargetIsTextureTarget :
      ckmYukawaDHRInterfaceYukawaMatrixTarget
      ≡
      Matter.YukawaTextureTarget

    ckmYukawaDHRInterfaceDHRIntertwinerTarget :
      Set

    ckmYukawaDHRInterfaceDHRIntertwinerTargetIsTextureTarget :
      ckmYukawaDHRInterfaceDHRIntertwinerTarget
      ≡
      Matter.YukawaTextureTarget

    ckmYukawaDHRInterfaceDiagonalizationTarget :
      Set

    ckmYukawaDHRInterfaceDiagonalizationTargetIsMixingMatrix :
      ckmYukawaDHRInterfaceDiagonalizationTarget
      ≡
      Matter.MixingMatrix

    ckmYukawaDHRInterfaceYukawaSVDCarrierSupplied :
      Bool

    ckmYukawaDHRInterfaceYukawaSVDCarrierSuppliedIsTrue :
      ckmYukawaDHRInterfaceYukawaSVDCarrierSupplied ≡ true

    ckmYukawaDHRInterfaceDHRIntertwinerSupplied :
      Bool

    ckmYukawaDHRInterfaceDHRIntertwinerSuppliedIsFalse :
      ckmYukawaDHRInterfaceDHRIntertwinerSupplied ≡ false

    ckmYukawaDHRInterfaceConstructsCKM :
      Bool

    ckmYukawaDHRInterfaceConstructsCKMIsFalse :
      ckmYukawaDHRInterfaceConstructsCKM ≡ false

    ckmYukawaDHRInterfaceBoundary :
      List String

open CKMYukawaDHRCompatibilitySuppliedInterface public

canonicalCKMYukawaDHRCompatibilitySuppliedInterface :
  CKMYukawaDHRCompatibilitySuppliedInterface
canonicalCKMYukawaDHRCompatibilitySuppliedInterface =
  record
    { ckmYukawaDHRInterfaceLeftRightRequest =
        canonicalCKMLeftRightQuarkCarrierFamilyAdapterRequest
    ; ckmYukawaDHRInterfaceSVDInterfaceSupply =
        canonicalCKMYukawaSVDInterfaceSupply
    ; ckmYukawaDHRInterfaceComponents =
        canonicalCKMYukawaDHRCompatibilityInterfaceComponents
    ; ckmYukawaDHRInterfaceComponentsAreCanonical =
        refl
    ; ckmYukawaDHRInterfaceWeakCarrierTarget =
        WeakEigenstateCarrier
    ; ckmYukawaDHRInterfaceWeakCarrierTargetIsCanonical =
        refl
    ; ckmYukawaDHRInterfaceMassCarrierTarget =
        MassEigenstateCarrier
    ; ckmYukawaDHRInterfaceMassCarrierTargetIsCanonical =
        refl
    ; ckmYukawaDHRInterfaceYukawaMatrixTarget =
        Matter.YukawaTextureTarget
    ; ckmYukawaDHRInterfaceYukawaMatrixTargetIsTextureTarget =
        refl
    ; ckmYukawaDHRInterfaceDHRIntertwinerTarget =
        Matter.YukawaTextureTarget
    ; ckmYukawaDHRInterfaceDHRIntertwinerTargetIsTextureTarget =
        refl
    ; ckmYukawaDHRInterfaceDiagonalizationTarget =
        Matter.MixingMatrix
    ; ckmYukawaDHRInterfaceDiagonalizationTargetIsMixingMatrix =
        refl
    ; ckmYukawaDHRInterfaceYukawaSVDCarrierSupplied =
        true
    ; ckmYukawaDHRInterfaceYukawaSVDCarrierSuppliedIsTrue =
        refl
    ; ckmYukawaDHRInterfaceDHRIntertwinerSupplied =
        false
    ; ckmYukawaDHRInterfaceDHRIntertwinerSuppliedIsFalse =
        refl
    ; ckmYukawaDHRInterfaceConstructsCKM =
        false
    ; ckmYukawaDHRInterfaceConstructsCKMIsFalse =
        refl
    ; ckmYukawaDHRInterfaceBoundary =
        "Typed quark-family evidence and symbolic Yukawa/SVD carrier targets are supplied"
        ∷ "The requested DHR intertwiner action and Yukawa-DHR compatibility law are typed targets only"
        ∷ "No Paper 2 intertwiner compatibility proof, CKM matrix, W4 calibration, or promotion is supplied"
        ∷ []
    }

record CKMYukawaDHRIntertwinerCompatibilityAbsenceLedger : Setω where
  field
    ckmYukawaDHRLedgerRequest :
      CKMYukawaDHRCompatibilityRequest

    ckmYukawaDHRLedgerSuppliedInterface :
      CKMYukawaDHRCompatibilitySuppliedInterface

    ckmYukawaDHRLedgerFirstCompatibilityBlocker :
      CKMYukawaDHRCompatibilityBlocker

    ckmYukawaDHRLedgerFirstCompatibilityBlockerIsIntertwiner :
      ckmYukawaDHRLedgerFirstCompatibilityBlocker
      ≡
      missingYukawaDHRIntertwinerCompatibility

    ckmYukawaDHRLedgerYukawaSVDInterfaceSupplied :
      yukawaSVDInterfaceSupplied canonicalCKMYukawaDHRCompatibilityRequest
      ≡
      true

    ckmYukawaDHRLedgerDHRIntertwinerCompatibilitySupplied :
      dhrIntertwinerCompatibilitySupplied canonicalCKMYukawaSVDInterfaceSupply
      ≡
      false

    ckmYukawaDHRLedgerDHRCompatibilityConstructed :
      dhrCompatibilityConstructed canonicalCKMYukawaDHRCompatibilityRequest
      ≡
      false

    ckmYukawaDHRLedgerHiggsPromotionStillFalse :
      Higgs.higgsSymmetryBreakingPromoted
        Higgs.canonicalHiggsSymmetryBreakingReceipt
      ≡
      false

    ckmYukawaDHRLedgerHiggsExternalW4AuthorityUnavailable :
      Higgs.externalW4AuthorityAvailable
        Higgs.canonicalHiggsSymmetryBreakingDependencyReceipt
      ≡
      false

    ckmYukawaDHRLedgerPromoted :
      Bool

    ckmYukawaDHRLedgerPromotedIsFalse :
      ckmYukawaDHRLedgerPromoted ≡ false

    ckmYukawaDHRLedgerBoundary :
      List String

open CKMYukawaDHRIntertwinerCompatibilityAbsenceLedger public

canonicalCKMYukawaDHRIntertwinerCompatibilityAbsenceLedger :
  CKMYukawaDHRIntertwinerCompatibilityAbsenceLedger
canonicalCKMYukawaDHRIntertwinerCompatibilityAbsenceLedger =
  record
    { ckmYukawaDHRLedgerRequest =
        canonicalCKMYukawaDHRCompatibilityRequest
    ; ckmYukawaDHRLedgerSuppliedInterface =
        canonicalCKMYukawaDHRCompatibilitySuppliedInterface
    ; ckmYukawaDHRLedgerFirstCompatibilityBlocker =
        missingYukawaDHRIntertwinerCompatibility
    ; ckmYukawaDHRLedgerFirstCompatibilityBlockerIsIntertwiner =
        refl
    ; ckmYukawaDHRLedgerYukawaSVDInterfaceSupplied =
        refl
    ; ckmYukawaDHRLedgerDHRIntertwinerCompatibilitySupplied =
        refl
    ; ckmYukawaDHRLedgerDHRCompatibilityConstructed =
        refl
    ; ckmYukawaDHRLedgerHiggsPromotionStillFalse =
        refl
    ; ckmYukawaDHRLedgerHiggsExternalW4AuthorityUnavailable =
        refl
    ; ckmYukawaDHRLedgerPromoted =
        false
    ; ckmYukawaDHRLedgerPromotedIsFalse =
        refl
    ; ckmYukawaDHRLedgerBoundary =
        "Exact supplied-interface gap: Yukawa/SVD carrier targets are present, but DHR intertwiner compatibility is not"
        ∷ "Exact DHR gap: no Paper 2 carrier action proof relates the supplied Yukawa interface to DHR transport"
        ∷ "Exact promotion gap: Higgs promotion, CKM promotion, and external W4 authority remain false"
        ∷ "The ledger records typed holes only and keeps the first compatibility blocker at missingYukawaDHRIntertwinerCompatibility"
        ∷ []
    }

ckmYukawaDHRCompatibilityLedgerFirstBlocker :
  ckmYukawaDHRLedgerFirstCompatibilityBlocker
    canonicalCKMYukawaDHRIntertwinerCompatibilityAbsenceLedger
  ≡
  missingYukawaDHRIntertwinerCompatibility
ckmYukawaDHRCompatibilityLedgerFirstBlocker =
  refl

ckmYukawaDHRCompatibilityInterfaceDoesNotSupplyIntertwiner :
  ckmYukawaDHRInterfaceDHRIntertwinerSupplied
    canonicalCKMYukawaDHRCompatibilitySuppliedInterface
  ≡
  false
ckmYukawaDHRCompatibilityInterfaceDoesNotSupplyIntertwiner =
  refl

ckmYukawaDHRCompatibilityLedgerKeepsDHRCompatibilityOpen :
  ckmYukawaDHRLedgerDHRCompatibilityConstructed
    canonicalCKMYukawaDHRIntertwinerCompatibilityAbsenceLedger
  ≡
  refl
ckmYukawaDHRCompatibilityLedgerKeepsDHRCompatibilityOpen =
  refl

ckmYukawaDHRCompatibilityLedgerDoesNotPromote :
  ckmYukawaDHRLedgerPromoted
    canonicalCKMYukawaDHRIntertwinerCompatibilityAbsenceLedger
  ≡
  false
ckmYukawaDHRCompatibilityLedgerDoesNotPromote =
  refl

data CKMYukawaDHRIntertwinerRouteComponent : Set where
  suppliedYukawaSVDInterfaceRouteComponent :
    CKMYukawaDHRIntertwinerRouteComponent

  suppliedDHRFormalismPrimitiveRouteComponent :
    CKMYukawaDHRIntertwinerRouteComponent

  requestedLeftYukawaDHRIntertwinerRouteComponent :
    CKMYukawaDHRIntertwinerRouteComponent

  requestedRightYukawaDHRIntertwinerRouteComponent :
    CKMYukawaDHRIntertwinerRouteComponent

  requestedTransportNaturalityRouteComponent :
    CKMYukawaDHRIntertwinerRouteComponent

  requestedWeakMassBasisCompatibilityRouteComponent :
    CKMYukawaDHRIntertwinerRouteComponent

canonicalCKMYukawaDHRIntertwinerRouteComponents :
  List CKMYukawaDHRIntertwinerRouteComponent
canonicalCKMYukawaDHRIntertwinerRouteComponents =
  suppliedYukawaSVDInterfaceRouteComponent
  ∷ suppliedDHRFormalismPrimitiveRouteComponent
  ∷ requestedLeftYukawaDHRIntertwinerRouteComponent
  ∷ requestedRightYukawaDHRIntertwinerRouteComponent
  ∷ requestedTransportNaturalityRouteComponent
  ∷ requestedWeakMassBasisCompatibilityRouteComponent
  ∷ []

YukawaDHRIntertwinerCompatibilityTarget :
  (ρ σ : DHR.LocalisedEndomorphism) →
  DHR.Intertwiner ρ σ →
  Matter.YukawaTextureTarget →
  Set
YukawaDHRIntertwinerCompatibilityTarget _ _ _ _ =
  Matter.YukawaTextureTarget

record CKMYukawaAsDHRIntertwinerCompatibilityRoute : Setω where
  field
    compatibilityRequest :
      CKMYukawaDHRCompatibilityRequest

    suppliedInterface :
      CKMYukawaDHRCompatibilitySuppliedInterface

    dhrGaugeReceiptSurface :
      DHR.DHRGaugeReceiptSurface

    dhrFormalismPrimitiveReceipt :
      DHR.DHRFormalismPrimitiveReceipt

    dhrSelectionCriterionTarget :
      DHR.DHRSelectionCriterionTarget

    routeComponents :
      List CKMYukawaDHRIntertwinerRouteComponent

    routeComponentsAreCanonical :
      routeComponents
      ≡
      canonicalCKMYukawaDHRIntertwinerRouteComponents

    yukawaCarrierTarget :
      Set

    yukawaCarrierTargetIsTextureTarget :
      yukawaCarrierTarget
      ≡
      Matter.YukawaTextureTarget

    dhrIntertwinerCarrierTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      Set

    dhrIntertwinerCarrierTargetIsPrimitive :
      Bool

    dhrIntertwinerCarrierTargetIsPrimitiveIsTrue :
      dhrIntertwinerCarrierTargetIsPrimitive ≡ true

    yukawaAsDHRIntertwinerCompatibilityTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      Matter.YukawaTextureTarget →
      Set

    yukawaAsDHRIntertwinerCompatibilityTargetIsCanonical :
      Bool

    yukawaAsDHRIntertwinerCompatibilityTargetIsCanonicalIsTrue :
      yukawaAsDHRIntertwinerCompatibilityTargetIsCanonical ≡ true

    routeShape :
      String

    routeShape-v :
      routeShape
      ≡
      "yukawa-texture-as-DHR-intertwiner-compatible-with-transport-before-CKM-mixing"

    yukawaSVDInterfaceSupplied :
      Bool

    yukawaSVDInterfaceSuppliedIsTrue :
      yukawaSVDInterfaceSupplied ≡ true

    dhrPrimitivesTyped :
      Bool

    dhrPrimitivesTypedIsTrue :
      dhrPrimitivesTyped ≡ true

    dhrIntertwinerCompatibilityProofSupplied :
      Bool

    dhrIntertwinerCompatibilityProofSuppliedIsFalse :
      dhrIntertwinerCompatibilityProofSupplied ≡ false

    weakMassBasisCompatibilitySupplied :
      Bool

    weakMassBasisCompatibilitySuppliedIsFalse :
      weakMassBasisCompatibilitySupplied ≡ false

    w4NumericInputRequired :
      Bool

    w4NumericInputRequiredIsTrue :
      w4NumericInputRequired ≡ true

    ckmPromotionConstructed :
      Bool

    ckmPromotionConstructedIsFalse :
      ckmPromotionConstructed ≡ false

    routeBoundary :
      List String

open CKMYukawaAsDHRIntertwinerCompatibilityRoute public

canonicalCKMYukawaAsDHRIntertwinerCompatibilityRoute :
  CKMYukawaAsDHRIntertwinerCompatibilityRoute
canonicalCKMYukawaAsDHRIntertwinerCompatibilityRoute =
  record
    { compatibilityRequest =
        canonicalCKMYukawaDHRCompatibilityRequest
    ; suppliedInterface =
        canonicalCKMYukawaDHRCompatibilitySuppliedInterface
    ; dhrGaugeReceiptSurface =
        DHR.canonicalDHRGaugeReceiptSurface
    ; dhrFormalismPrimitiveReceipt =
        DHR.canonicalDHRFormalismPrimitiveReceipt
    ; dhrSelectionCriterionTarget =
        DHR.canonicalDHRSelectionCriterionTarget
    ; routeComponents =
        canonicalCKMYukawaDHRIntertwinerRouteComponents
    ; routeComponentsAreCanonical =
        refl
    ; yukawaCarrierTarget =
        Matter.YukawaTextureTarget
    ; yukawaCarrierTargetIsTextureTarget =
        refl
    ; dhrIntertwinerCarrierTarget =
        λ _ _ _ → Matter.YukawaTextureTarget
    ; dhrIntertwinerCarrierTargetIsPrimitive =
        true
    ; dhrIntertwinerCarrierTargetIsPrimitiveIsTrue =
        refl
    ; yukawaAsDHRIntertwinerCompatibilityTarget =
        YukawaDHRIntertwinerCompatibilityTarget
    ; yukawaAsDHRIntertwinerCompatibilityTargetIsCanonical =
        true
    ; yukawaAsDHRIntertwinerCompatibilityTargetIsCanonicalIsTrue =
        refl
    ; routeShape =
        "yukawa-texture-as-DHR-intertwiner-compatible-with-transport-before-CKM-mixing"
    ; routeShape-v =
        refl
    ; yukawaSVDInterfaceSupplied =
        true
    ; yukawaSVDInterfaceSuppliedIsTrue =
        refl
    ; dhrPrimitivesTyped =
        true
    ; dhrPrimitivesTypedIsTrue =
        refl
    ; dhrIntertwinerCompatibilityProofSupplied =
        false
    ; dhrIntertwinerCompatibilityProofSuppliedIsFalse =
        refl
    ; weakMassBasisCompatibilitySupplied =
        false
    ; weakMassBasisCompatibilitySuppliedIsFalse =
        refl
    ; w4NumericInputRequired =
        true
    ; w4NumericInputRequiredIsTrue =
        refl
    ; ckmPromotionConstructed =
        false
    ; ckmPromotionConstructedIsFalse =
        refl
    ; routeBoundary =
        "The route records Yukawa texture targets as DHR-intertwiner compatibility targets over typed DHR primitives"
        ∷ "The supplied Yukawa/SVD interface may feed the route only after an actual DHR transport/intertwiner compatibility proof is supplied"
        ∷ "Weak-to-mass basis identification, biunitary diagonalization, CKM unitarity transport, and numeric W4 inputs remain open"
        ∷ "No CKM promotion, Higgs promotion, or W4-calibrated numeric matrix is constructed"
        ∷ []
    }

ckmYukawaAsDHRIntertwinerRouteSuppliesSVDInterface :
  yukawaSVDInterfaceSupplied
    canonicalCKMYukawaAsDHRIntertwinerCompatibilityRoute
  ≡
  true
ckmYukawaAsDHRIntertwinerRouteSuppliesSVDInterface =
  refl

ckmYukawaAsDHRIntertwinerRouteKeepsCompatibilityProofOpen :
  dhrIntertwinerCompatibilityProofSupplied
    canonicalCKMYukawaAsDHRIntertwinerCompatibilityRoute
  ≡
  false
ckmYukawaAsDHRIntertwinerRouteKeepsCompatibilityProofOpen =
  refl

ckmYukawaAsDHRIntertwinerRouteRequiresW4NumericInput :
  w4NumericInputRequired
    canonicalCKMYukawaAsDHRIntertwinerCompatibilityRoute
  ≡
  true
ckmYukawaAsDHRIntertwinerRouteRequiresW4NumericInput =
  refl

ckmYukawaAsDHRIntertwinerRouteDoesNotPromote :
  ckmPromotionConstructed
    canonicalCKMYukawaAsDHRIntertwinerCompatibilityRoute
  ≡
  false
ckmYukawaAsDHRIntertwinerRouteDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Explicit SVD/unitarity supply interface.

data CKMSVDUnitaritySupplyComponent : Set where
  suppliedYukawaSVDCarrierInterfaceComponent :
    CKMSVDUnitaritySupplyComponent

  requestedUpLeftUnitaryDiagonalizerComponent :
    CKMSVDUnitaritySupplyComponent

  requestedDownLeftUnitaryDiagonalizerComponent :
    CKMSVDUnitaritySupplyComponent

  requestedCKMLeftMismatchMatrixComponent :
    CKMSVDUnitaritySupplyComponent

  requestedCKMUnitarityProofComponent :
    CKMSVDUnitaritySupplyComponent

  requestedDHRYukawaIntertwinerCompatibilityComponent :
    CKMSVDUnitaritySupplyComponent

  requestedW4NumericAnglePhaseValuesComponent :
    CKMSVDUnitaritySupplyComponent

canonicalCKMSVDUnitaritySupplyComponents :
  List CKMSVDUnitaritySupplyComponent
canonicalCKMSVDUnitaritySupplyComponents =
  suppliedYukawaSVDCarrierInterfaceComponent
  ∷ requestedUpLeftUnitaryDiagonalizerComponent
  ∷ requestedDownLeftUnitaryDiagonalizerComponent
  ∷ requestedCKMLeftMismatchMatrixComponent
  ∷ requestedCKMUnitarityProofComponent
  ∷ requestedDHRYukawaIntertwinerCompatibilityComponent
  ∷ requestedW4NumericAnglePhaseValuesComponent
  ∷ []

record CKMSVDUnitaritySupplyInterface : Setω where
  field
    yukawaSVDInterfaceSupply :
      CKMYukawaSVDInterfaceSupply

    yukawaDHRCompatibilityRequest :
      CKMYukawaDHRCompatibilityRequest

    yukawaAsDHRIntertwinerCompatibilityRoute :
      CKMYukawaAsDHRIntertwinerCompatibilityRoute

    ckmUnitarityRequest :
      CKMYukawaSVDCKMUnitarityRequest

    supplyComponents :
      List CKMSVDUnitaritySupplyComponent

    supplyComponentsAreCanonical :
      supplyComponents
      ≡
      canonicalCKMSVDUnitaritySupplyComponents

    upLeftUnitaryDiagonalizerTarget :
      Set

    upLeftUnitaryDiagonalizerTargetIsMixingMatrix :
      upLeftUnitaryDiagonalizerTarget
      ≡
      Matter.MixingMatrix

    downLeftUnitaryDiagonalizerTarget :
      Set

    downLeftUnitaryDiagonalizerTargetIsMixingMatrix :
      downLeftUnitaryDiagonalizerTarget
      ≡
      Matter.MixingMatrix

    ckmLeftMismatchMatrixTarget :
      Set

    ckmLeftMismatchMatrixTargetIsMixingMatrix :
      ckmLeftMismatchMatrixTarget
      ≡
      Matter.MixingMatrix

    ckmUnitarityProofTarget :
      Set

    ckmUnitarityProofTargetIsCanonical :
      ckmUnitarityProofTarget
      ≡
      abstractUnitaryCKMTarget

    w4AnglePhaseNumericValueTarget :
      List CKMAnglePhaseTarget

    w4AnglePhaseNumericValueTargetIsCanonical :
      w4AnglePhaseNumericValueTarget
      ≡
      canonicalCKMAnglePhaseTargets

    yukawaSVDCarrierInterfaceSupplied :
      Bool

    yukawaSVDCarrierInterfaceSuppliedIsTrue :
      yukawaSVDCarrierInterfaceSupplied ≡ true

    biunitaryDiagonalizationProofSupplied :
      Bool

    biunitaryDiagonalizationProofSuppliedIsFalse :
      biunitaryDiagonalizationProofSupplied ≡ false

    dhrYukawaIntertwinerCompatibilitySupplied :
      Bool

    dhrYukawaIntertwinerCompatibilitySuppliedIsFalse :
      dhrYukawaIntertwinerCompatibilitySupplied ≡ false

    weakToMassBasisIdentificationSupplied :
      Bool

    weakToMassBasisIdentificationSuppliedIsFalse :
      weakToMassBasisIdentificationSupplied ≡ false

    ckmMatrixConstructed :
      Bool

    ckmMatrixConstructedIsFalse :
      ckmMatrixConstructed ≡ false

    ckmUnitarityProofSupplied :
      Bool

    ckmUnitarityProofSuppliedIsFalse :
      ckmUnitarityProofSupplied ≡ false

    w4AnglePhaseValuesSupplied :
      Bool

    w4AnglePhaseValuesSuppliedIsFalse :
      w4AnglePhaseValuesSupplied ≡ false

    ckmPromotionConstructed :
      Bool

    ckmPromotionConstructedIsFalse :
      ckmPromotionConstructed ≡ false

    ckmSVDUnitaritySupplyBoundary :
      List String

open CKMSVDUnitaritySupplyInterface public

canonicalCKMSVDUnitaritySupplyInterface :
  CKMSVDUnitaritySupplyInterface
canonicalCKMSVDUnitaritySupplyInterface =
  record
    { yukawaSVDInterfaceSupply =
        canonicalCKMYukawaSVDInterfaceSupply
    ; yukawaDHRCompatibilityRequest =
        canonicalCKMYukawaDHRCompatibilityRequest
    ; yukawaAsDHRIntertwinerCompatibilityRoute =
        canonicalCKMYukawaAsDHRIntertwinerCompatibilityRoute
    ; ckmUnitarityRequest =
        canonicalCKMYukawaSVDCKMUnitarityRequest
    ; supplyComponents =
        canonicalCKMSVDUnitaritySupplyComponents
    ; supplyComponentsAreCanonical =
        refl
    ; upLeftUnitaryDiagonalizerTarget =
        Matter.MixingMatrix
    ; upLeftUnitaryDiagonalizerTargetIsMixingMatrix =
        refl
    ; downLeftUnitaryDiagonalizerTarget =
        Matter.MixingMatrix
    ; downLeftUnitaryDiagonalizerTargetIsMixingMatrix =
        refl
    ; ckmLeftMismatchMatrixTarget =
        Matter.MixingMatrix
    ; ckmLeftMismatchMatrixTargetIsMixingMatrix =
        refl
    ; ckmUnitarityProofTarget =
        abstractUnitaryCKMTarget
    ; ckmUnitarityProofTargetIsCanonical =
        refl
    ; w4AnglePhaseNumericValueTarget =
        canonicalCKMAnglePhaseTargets
    ; w4AnglePhaseNumericValueTargetIsCanonical =
        refl
    ; yukawaSVDCarrierInterfaceSupplied =
        true
    ; yukawaSVDCarrierInterfaceSuppliedIsTrue =
        refl
    ; biunitaryDiagonalizationProofSupplied =
        false
    ; biunitaryDiagonalizationProofSuppliedIsFalse =
        refl
    ; dhrYukawaIntertwinerCompatibilitySupplied =
        false
    ; dhrYukawaIntertwinerCompatibilitySuppliedIsFalse =
        refl
    ; weakToMassBasisIdentificationSupplied =
        false
    ; weakToMassBasisIdentificationSuppliedIsFalse =
        refl
    ; ckmMatrixConstructed =
        false
    ; ckmMatrixConstructedIsFalse =
        refl
    ; ckmUnitarityProofSupplied =
        false
    ; ckmUnitarityProofSuppliedIsFalse =
        refl
    ; w4AnglePhaseValuesSupplied =
        false
    ; w4AnglePhaseValuesSuppliedIsFalse =
        refl
    ; ckmPromotionConstructed =
        false
    ; ckmPromotionConstructedIsFalse =
        refl
    ; ckmSVDUnitaritySupplyBoundary =
        "SVD/unitarity supply interface records the up/down left-unitary diagonalizer targets and the CKM left-mismatch matrix target"
        ∷ "The symbolic Yukawa/SVD carrier interface is present, but biunitary diagonalization and DHR-Yukawa intertwiner compatibility are not supplied"
        ∷ "CKM unitarity, weak-to-mass basis identification, and W4 angle/phase numeric values remain target fields"
        ∷ "No CKM matrix construction, W4-calibrated value receipt, Higgs promotion, or CKM promotion is introduced"
        ∷ []
    }

ckmSVDUnitaritySupplyRecordsCarrierInterface :
  yukawaSVDCarrierInterfaceSupplied canonicalCKMSVDUnitaritySupplyInterface
  ≡
  true
ckmSVDUnitaritySupplyRecordsCarrierInterface =
  refl

ckmSVDUnitaritySupplyKeepsDHRCompatibilityOpen :
  dhrYukawaIntertwinerCompatibilitySupplied
    canonicalCKMSVDUnitaritySupplyInterface
  ≡
  false
ckmSVDUnitaritySupplyKeepsDHRCompatibilityOpen =
  refl

ckmSVDUnitaritySupplyKeepsW4ValuesOpen :
  w4AnglePhaseValuesSupplied canonicalCKMSVDUnitaritySupplyInterface
  ≡
  false
ckmSVDUnitaritySupplyKeepsW4ValuesOpen =
  refl

------------------------------------------------------------------------
-- Explicit carrier diagonalization boundary ledger.
--
-- This keeps the old exported SVD-ledger names as compatibility aliases for
-- downstream files, but the recorded authority boundary is now the discrete
-- carrier route: supplied Yukawa carrier targets, requested exact
-- diagonalizers, DHR compatibility, and W4 numeric calibration.  Rational
-- Yukawa entries alone do not imply that normalized diagonalizers or CKM
-- entries remain rational; square-root normalizations may force a finite
-- algebraic field extension.

data CKMSVDAuthorityBoundaryComponent : Set where
  symbolicYukawaRationalCarrierInterfaceComponent :
    CKMSVDAuthorityBoundaryComponent

  constructiveAlgebraicExtensionDiagonalizationRequestComponent :
    CKMSVDAuthorityBoundaryComponent

  dhrYukawaCompatibilityRequestComponent :
    CKMSVDAuthorityBoundaryComponent

  externalW4AnglePhaseAuthorityComponent :
    CKMSVDAuthorityBoundaryComponent

canonicalCKMSVDAuthorityBoundaryComponents :
  List CKMSVDAuthorityBoundaryComponent
canonicalCKMSVDAuthorityBoundaryComponents =
  symbolicYukawaRationalCarrierInterfaceComponent
  ∷ constructiveAlgebraicExtensionDiagonalizationRequestComponent
  ∷ dhrYukawaCompatibilityRequestComponent
  ∷ externalW4AnglePhaseAuthorityComponent
  ∷ []

data CKMRationalGramSchmidtMissingPrimitive : Set where
  missingRationalYukawaMatrixEntries :
    CKMRationalGramSchmidtMissingPrimitive
  missingRationalHermitianProducts :
    CKMRationalGramSchmidtMissingPrimitive
  missingRationalGramSchmidtDiagonalizers :
    CKMRationalGramSchmidtMissingPrimitive
  missingDHRYukawaIntertwinerCompatibilityForRationalRoute :
    CKMRationalGramSchmidtMissingPrimitive
  missingWeakToMassBasisIdentificationForRationalRoute :
    CKMRationalGramSchmidtMissingPrimitive

data CKMAlgebraicDiagonalizationMissingPrimitive : Set where
  missingBaseFieldOrFiniteAlgebraicExtensionChoice :
    CKMAlgebraicDiagonalizationMissingPrimitive
  missingRationalYukawaEntryComputationFromFactorVec :
    CKMAlgebraicDiagonalizationMissingPrimitive
  missingHermitianSpectralPolynomialOverSelectedField :
    CKMAlgebraicDiagonalizationMissingPrimitive
  missingNormalizedEigenbasisOverSelectedExtension :
    CKMAlgebraicDiagonalizationMissingPrimitive
  missingCKMProductFieldClosureProof :
    CKMAlgebraicDiagonalizationMissingPrimitive
  missingProofThatQAloneSufficesOrExtensionWitness :
    CKMAlgebraicDiagonalizationMissingPrimitive

canonicalCKMRationalGramSchmidtMissingPrimitives :
  List CKMRationalGramSchmidtMissingPrimitive
canonicalCKMRationalGramSchmidtMissingPrimitives =
  missingRationalYukawaMatrixEntries
  ∷ missingRationalHermitianProducts
  ∷ missingRationalGramSchmidtDiagonalizers
  ∷ missingDHRYukawaIntertwinerCompatibilityForRationalRoute
  ∷ missingWeakToMassBasisIdentificationForRationalRoute
  ∷ []

canonicalCKMAlgebraicDiagonalizationMissingPrimitives :
  List CKMAlgebraicDiagonalizationMissingPrimitive
canonicalCKMAlgebraicDiagonalizationMissingPrimitives =
  missingBaseFieldOrFiniteAlgebraicExtensionChoice
  ∷ missingRationalYukawaEntryComputationFromFactorVec
  ∷ missingHermitianSpectralPolynomialOverSelectedField
  ∷ missingNormalizedEigenbasisOverSelectedExtension
  ∷ missingCKMProductFieldClosureProof
  ∷ missingProofThatQAloneSufficesOrExtensionWitness
  ∷ []

record CKMSVDAuthorityBoundaryLedger : Setω where
  field
    svdUnitaritySupplyInterface :
      CKMSVDUnitaritySupplyInterface

    authorityBoundaryComponents :
      List CKMSVDAuthorityBoundaryComponent

    authorityBoundaryComponentsAreCanonical :
      authorityBoundaryComponents
      ≡
      canonicalCKMSVDAuthorityBoundaryComponents

    yukawaSVDCarrierInterfaceRecorded :
      yukawaSVDCarrierInterfaceSupplied canonicalCKMSVDUnitaritySupplyInterface
      ≡
      true

    biunitaryDiagonalizationAuthorityExternal :
      biunitaryDiagonalizationProofSupplied canonicalCKMSVDUnitaritySupplyInterface
      ≡
      false

    dhrYukawaCompatibilityAuthorityExternal :
      dhrYukawaIntertwinerCompatibilitySupplied
        canonicalCKMSVDUnitaritySupplyInterface
      ≡
      false

    w4AnglePhaseAuthorityExternal :
      w4AnglePhaseValuesSupplied canonicalCKMSVDUnitaritySupplyInterface
      ≡
      false

    rationalGramSchmidtConstructiveClosureSupplied :
      Bool

    rationalGramSchmidtConstructiveClosureSuppliedIsFalse :
      rationalGramSchmidtConstructiveClosureSupplied ≡ false

    rationalFieldSufficiencyProved :
      Bool

    rationalFieldSufficiencyProvedIsFalse :
      rationalFieldSufficiencyProved ≡ false

    algebraicExtensionMayBeRequired :
      Bool

    algebraicExtensionMayBeRequiredIsTrue :
      algebraicExtensionMayBeRequired ≡ true

    entryFieldComputationTarget :
      Field.CKMFieldCarrierComputationTarget

    entryFieldConcreteYukawaInputInventory :
      Field.CKMConcreteYukawaInputInventory

    firstEntryFieldMissingInputIsConcreteUpMatrix :
      Field.firstMissingArithmeticInput
        entryFieldConcreteYukawaInputInventory
      ≡
      Field.missingConcreteUpYukawa3x3Matrix

    firstEntryFieldMissingUpYukawaEntryIsY11 :
      Field.firstMissingUpYukawaEntry
        entryFieldConcreteYukawaInputInventory
      ≡
      Field.missingY11

    entryFieldAnyConcreteUpEntrySuppliedIsFalse :
      Field.anyConcreteEntrySupplied
        (Field.upYukawaEntryInventory
          entryFieldConcreteYukawaInputInventory)
      ≡
      false

    entryFieldY11Progress :
      Field.CKMConcreteUpYukawaY11Progress

    entryFieldY11ProgressStartsFromY11Blocker :
      Field.firstMissingUpYukawaEntry
        (Field.priorInventory entryFieldY11Progress)
      ≡
      Field.missingY11

    entryFieldY11ProgressMarksY11AsSupplied :
      Field.y11ConcreteEntrySupplied entryFieldY11Progress
      ≡
      true

    entryFieldY11ProgressAdvancesNextMissingUpEntryToY12 :
      Field.nextMissingUpYukawaEntry entryFieldY11Progress
      ≡
      Field.missingY12

    entryFieldY11ProgressKeepsUpMatrixIncomplete :
      Field.upMatrixStillIncomplete entryFieldY11Progress
      ≡
      true

    entryFieldY12Progress :
      Field.CKMConcreteUpYukawaY12Progress

    entryFieldY12ProgressStartsFromY12Blocker :
      Field.nextMissingUpYukawaEntry
        (Field.priorY11Progress entryFieldY12Progress)
      ≡
      Field.missingY12

    entryFieldY12ProgressMarksY12AsSupplied :
      Field.y12ConcreteEntrySupplied entryFieldY12Progress
      ≡
      true

    entryFieldY12ProgressAdvancesNextMissingUpEntryToY13 :
      Field.nextMissingUpYukawaEntry entryFieldY12Progress
      ≡
      Field.missingY13

    entryFieldY12ProgressKeepsUpMatrixIncomplete :
      Field.upMatrixStillIncomplete entryFieldY12Progress
      ≡
      true

    entryFieldY13Progress :
      Field.CKMConcreteUpYukawaY13Progress

    entryFieldY13ProgressStartsFromY13Blocker :
      Field.nextMissingUpYukawaEntry
        (Field.priorY12Progress entryFieldY13Progress)
      ≡
      Field.missingY13

    entryFieldY13ProgressMarksY13AsSupplied :
      Field.y13ConcreteEntrySupplied entryFieldY13Progress
      ≡
      true

    entryFieldY13ProgressAdvancesNextMissingUpEntryToY21 :
      Field.nextMissingUpYukawaEntry entryFieldY13Progress
      ≡
      Field.missingY21

    entryFieldY13ProgressKeepsUpMatrixIncomplete :
      Field.upMatrixStillIncomplete entryFieldY13Progress
      ≡
      true

    entryFieldY21Progress :
      Field.CKMConcreteUpYukawaY21Progress

    entryFieldY21ProgressStartsFromY21Blocker :
      Field.nextMissingUpYukawaEntry
        (Field.priorY13Progress entryFieldY21Progress)
      ≡
      Field.missingY21

    entryFieldY21ProgressMarksY21AsSupplied :
      Field.y21ConcreteEntrySupplied entryFieldY21Progress
      ≡
      true

    entryFieldY21ProgressAdvancesNextMissingUpEntryToY22 :
      Field.nextMissingUpYukawaEntry entryFieldY21Progress
      ≡
      Field.missingY22

    entryFieldY21ProgressKeepsUpMatrixIncomplete :
      Field.upMatrixStillIncomplete entryFieldY21Progress
      ≡
      true

    entryFieldY22Progress :
      Field.CKMConcreteUpYukawaY22Progress

    entryFieldY22ProgressStartsFromY22Blocker :
      Field.nextMissingUpYukawaEntry
        (Field.priorY21Progress entryFieldY22Progress)
      ≡
      Field.missingY22

    entryFieldY22ProgressMarksY22AsSupplied :
      Field.y22ConcreteEntrySupplied entryFieldY22Progress
      ≡
      true

    entryFieldY22ProgressAdvancesNextMissingUpEntryToY23 :
      Field.nextMissingUpYukawaEntry entryFieldY22Progress
      ≡
      Field.missingY23

    entryFieldY22ProgressKeepsUpMatrixIncomplete :
      Field.upMatrixStillIncomplete entryFieldY22Progress
      ≡
      true

    entryFieldY23Progress :
      Field.CKMConcreteUpYukawaY23Progress

    entryFieldY23ProgressStartsFromY23Blocker :
      Field.nextMissingUpYukawaEntry
        (Field.priorY22Progress entryFieldY23Progress)
      ≡
      Field.missingY23

    entryFieldY23ProgressMarksY23AsSupplied :
      Field.y23ConcreteEntrySupplied entryFieldY23Progress
      ≡
      true

    entryFieldY23ProgressAdvancesNextMissingUpEntryToY31 :
      Field.nextMissingUpYukawaEntry entryFieldY23Progress
      ≡
      Field.missingY31

    entryFieldY23ProgressKeepsUpMatrixIncomplete :
      Field.upMatrixStillIncomplete entryFieldY23Progress
      ≡
      true

    entryFieldY31Progress :
      Field.CKMConcreteUpYukawaY31Progress

    entryFieldY31ProgressStartsFromY31Blocker :
      Field.nextMissingUpYukawaEntry
        (Field.priorY23Progress entryFieldY31Progress)
      ≡
      Field.missingY31

    entryFieldY31ProgressMarksY31AsSupplied :
      Field.y31ConcreteEntrySupplied entryFieldY31Progress
      ≡
      true

    entryFieldY31ProgressAdvancesNextMissingUpEntryToY32 :
      Field.nextMissingUpYukawaEntry entryFieldY31Progress
      ≡
      Field.missingY32

    entryFieldY31ProgressKeepsUpMatrixIncomplete :
      Field.upMatrixStillIncomplete entryFieldY31Progress
      ≡
      true

    entryFieldY32Progress :
      Field.CKMConcreteUpYukawaY32Progress

    entryFieldY32ProgressStartsFromY32Blocker :
      Field.nextMissingUpYukawaEntry
        (Field.priorY31Progress entryFieldY32Progress)
      ≡
      Field.missingY32

    entryFieldY32ProgressMarksY32AsSupplied :
      Field.y32ConcreteEntrySupplied entryFieldY32Progress
      ≡
      true

    entryFieldY32ProgressAdvancesNextMissingUpEntryToY33 :
      Field.nextMissingUpYukawaEntry entryFieldY32Progress
      ≡
      Field.missingY33

    entryFieldY32ProgressKeepsUpMatrixIncomplete :
      Field.upMatrixStillIncomplete entryFieldY32Progress
      ≡
      true

    entryFieldY33Progress :
      Field.CKMConcreteUpYukawaY33Progress

    entryFieldY33ProgressStartsFromY33Blocker :
      Field.nextMissingUpYukawaEntry
        (Field.priorY32Progress entryFieldY33Progress)
      ≡
      Field.missingY33

    entryFieldY33ProgressMarksY33AsSupplied :
      Field.y33ConcreteEntrySupplied entryFieldY33Progress
      ≡
      true

    entryFieldY33ProgressDischargesRemainingUpEntrySlots :
      Field.remainingMissingUpEntrySlots entryFieldY33Progress
      ≡
      []

    entryFieldY33ProgressMarksUpMatrixComplete :
      Field.upMatrixStillIncomplete entryFieldY33Progress
      ≡
      false

    entryFieldMatrixAssemblyReceipt :
      Field.CKMConcreteYukawaMatrixAssemblyReceipt

    entryFieldMatrixAssemblyReceiptDischargesUpEntrySlots :
      Field.remainingMissingUpEntrySlots
        (Field.stagedUpMatrixProgress entryFieldMatrixAssemblyReceipt)
      ≡
      []

    entryFieldMatrixAssemblyReceiptAdvancesFirstArithmeticBlockerToConcreteDownMatrix :
      Field.firstMissingArithmeticInputAfterUpMatrixAssembly
        entryFieldMatrixAssemblyReceipt
      ≡
      Field.missingConcreteDownYukawa3x3Matrix

    entryFieldDownMatrixRequestProgress :
      Field.CKMConcreteDownYukawaMatrixRequestProgress

    entryFieldDownMatrixRequestProgressStartsFromConcreteDownMatrixBlocker :
      Field.firstMissingArithmeticInputAfterUpMatrixAssembly
        (Field.priorMatrixAssemblyReceipt
          entryFieldDownMatrixRequestProgress)
      ≡
      Field.missingConcreteDownYukawa3x3Matrix

    entryFieldDownMatrixRequestProgressRecordsRequestPackaging :
      Field.downMatrixRequestPackaged
        entryFieldDownMatrixRequestProgress
      ≡
      true

    entryFieldDownMatrixRequestProgressKeepsFirstArithmeticBlockerAtConcreteDownMatrix :
      Field.firstMissingArithmeticInputAfterDownMatrixRequest
        entryFieldDownMatrixRequestProgress
      ≡
      Field.missingConcreteDownYukawa3x3Matrix

    entryFieldDownY11Progress :
      Field.CKMConcreteDownYukawaY11Progress

    entryFieldDownY11ProgressStartsFromConcreteDownMatrixBlocker :
      Field.firstMissingArithmeticInputAfterDownMatrixRequest
        (Field.priorDownMatrixRequestProgress
          entryFieldDownY11Progress)
      ≡
      Field.missingConcreteDownYukawa3x3Matrix

    entryFieldDownY11ProgressMarksDownY11AsSupplied :
      Field.downY11ConcreteEntrySupplied
        entryFieldDownY11Progress
      ≡
      true

    entryFieldDownY11ProgressAdvancesNextMissingDownEntryToY12 :
      Field.nextMissingDownYukawaEntry
        entryFieldDownY11Progress
      ≡
      Field.missingY12

    entryFieldDownY11ProgressKeepsFirstArithmeticBlockerAtConcreteDownMatrix :
      Field.firstMissingArithmeticInputAfterDownY11
        entryFieldDownY11Progress
      ≡
      Field.missingConcreteDownYukawa3x3Matrix

    entryFieldDownY12Progress :
      Field.CKMConcreteDownYukawaY12Progress

    entryFieldDownY12ProgressStartsFromY12Blocker :
      Field.nextMissingDownYukawaEntry
        (Field.priorDownY11Progress entryFieldDownY12Progress)
      ≡
      Field.missingY12

    entryFieldDownY12ProgressMarksDownY12AsSupplied :
      Field.downY12ConcreteEntrySupplied
        entryFieldDownY12Progress
      ≡
      true

    entryFieldDownY12ProgressAdvancesNextMissingDownEntryToY13 :
      Field.nextMissingDownYukawaEntry
        entryFieldDownY12Progress
      ≡
      Field.missingY13

    entryFieldDownY12ProgressKeepsFirstArithmeticBlockerAtConcreteDownMatrix :
      Field.firstMissingArithmeticInputAfterDownY12
        entryFieldDownY12Progress
      ≡
      Field.missingConcreteDownYukawa3x3Matrix

    entryFieldDownY13Progress :
      Field.CKMConcreteDownYukawaY13Progress

    entryFieldDownY13ProgressStartsFromY13Blocker :
      Field.nextMissingDownYukawaEntry
        (Field.priorDownY12Progress entryFieldDownY13Progress)
      ≡
      Field.missingY13

    entryFieldDownY13ProgressMarksDownY13AsSupplied :
      Field.downY13ConcreteEntrySupplied
        entryFieldDownY13Progress
      ≡
      true

    entryFieldDownY13ProgressAdvancesNextMissingDownEntryToY21 :
      Field.nextMissingDownYukawaEntry
        entryFieldDownY13Progress
      ≡
      Field.missingY21

    entryFieldDownY13ProgressKeepsFirstArithmeticBlockerAtConcreteDownMatrix :
      Field.firstMissingArithmeticInputAfterDownY13
        entryFieldDownY13Progress
      ≡
      Field.missingConcreteDownYukawa3x3Matrix

    entryFieldCharacteristicPolynomialProgress :
      Field.CKMCharacteristicPolynomialProgress

    entryFieldCharacteristicPolynomialProgressStartsFromCharacteristicPolynomialBlocker :
      Field.priorMissingArithmeticInput
        entryFieldCharacteristicPolynomialProgress
      ≡
      Field.missingCharacteristicPolynomials

    entryFieldCharacteristicPolynomialProgressMarksCharacteristicPolynomialsAsSupplied :
      Field.characteristicPolynomialsSupplied
        entryFieldCharacteristicPolynomialProgress
      ≡
      true

    entryFieldCharacteristicPolynomialProgressAdvancesNextMissingArithmeticInputToSplittingField :
      Field.nextMissingArithmeticInput
        entryFieldCharacteristicPolynomialProgress
      ≡
      Field.missingEigenvalueSplittingField

    entryFieldSplittingFieldProgress :
      Field.CKMEigenvalueSplittingFieldProgress

    entryFieldSplittingFieldProgressStartsFromSplittingFieldBlocker :
      Field.nextMissingArithmeticInput
        (Field.priorCharacteristicPolynomialProgress
          entryFieldSplittingFieldProgress)
      ≡
      Field.missingEigenvalueSplittingField

    entryFieldSplittingFieldProgressMarksSplittingFieldAsSupplied :
      Field.eigenvalueSplittingFieldSupplied
        entryFieldSplittingFieldProgress
      ≡
      true

    entryFieldSplittingFieldProgressAdvancesNextMissingArithmeticInputToNormalizedLeftEigenbases :
      Field.nextMissingArithmeticInput
        entryFieldSplittingFieldProgress
      ≡
      Field.missingNormalizedLeftEigenbases

    entryFieldNormalizedEigenbasisProgress :
      Field.CKMNormalizedLeftEigenbasisProgress

    entryFieldNormalizedEigenbasisProgressStartsFromNormalizedLeftEigenbasisBlocker :
      Field.nextMissingArithmeticInput
        (Field.priorSplittingFieldProgress
          entryFieldNormalizedEigenbasisProgress)
      ≡
      Field.missingNormalizedLeftEigenbases

    entryFieldNormalizedEigenbasisProgressMarksNormalizedLeftEigenbasesAsSupplied :
      Field.normalizedLeftEigenbasesSupplied
        entryFieldNormalizedEigenbasisProgress
      ≡
      true

    entryFieldNormalizedEigenbasisProgressAdvancesNextMissingArithmeticInputToCKMProductClosureWitness :
      Field.nextMissingArithmeticInput
        entryFieldNormalizedEigenbasisProgress
      ≡
      Field.missingCKMProductClosureWitness

    entryFieldExecutableDecisionNotSupplied :
      Field.executableFieldMembershipDecisionSupplied
        entryFieldConcreteYukawaInputInventory
      ≡
      false

    entryFieldDecisionIsUnresolved :
      Field.fieldDecision entryFieldComputationTarget
      ≡
      Field.unresolvedFieldDecision

    entryFieldDoesNotProveQAloneSuffices :
      Field.qSufficiencyProved entryFieldComputationTarget
      ≡
      false

    continuousSVDPostulateInLedger :
      Bool

    continuousSVDPostulateInLedgerIsFalse :
      continuousSVDPostulateInLedger ≡ false

    rationalGramSchmidtMissingPrimitives :
      List CKMRationalGramSchmidtMissingPrimitive

    rationalGramSchmidtMissingPrimitivesAreCanonical :
      rationalGramSchmidtMissingPrimitives
      ≡
      canonicalCKMRationalGramSchmidtMissingPrimitives

    algebraicDiagonalizationMissingPrimitives :
      List CKMAlgebraicDiagonalizationMissingPrimitive

    algebraicDiagonalizationMissingPrimitivesAreCanonical :
      algebraicDiagonalizationMissingPrimitives
      ≡
      canonicalCKMAlgebraicDiagonalizationMissingPrimitives

    ckmMatrixConstructedInternally :
      Bool

    ckmMatrixConstructedInternallyIsFalse :
      ckmMatrixConstructedInternally ≡ false

    ckmPromotionConstructed :
      Bool

    ckmPromotionConstructedIsFalse :
      ckmPromotionConstructed ≡ false

    svdAuthorityBoundary :
      List String

open CKMSVDAuthorityBoundaryLedger public

canonicalCKMSVDAuthorityBoundaryLedger :
  CKMSVDAuthorityBoundaryLedger
canonicalCKMSVDAuthorityBoundaryLedger =
  record
    { svdUnitaritySupplyInterface =
        canonicalCKMSVDUnitaritySupplyInterface
    ; authorityBoundaryComponents =
        canonicalCKMSVDAuthorityBoundaryComponents
    ; authorityBoundaryComponentsAreCanonical =
        refl
    ; yukawaSVDCarrierInterfaceRecorded =
        refl
    ; biunitaryDiagonalizationAuthorityExternal =
        refl
    ; dhrYukawaCompatibilityAuthorityExternal =
        refl
    ; w4AnglePhaseAuthorityExternal =
        refl
    ; rationalGramSchmidtConstructiveClosureSupplied =
        false
    ; rationalGramSchmidtConstructiveClosureSuppliedIsFalse =
        refl
    ; rationalFieldSufficiencyProved =
        false
    ; rationalFieldSufficiencyProvedIsFalse =
        refl
    ; algebraicExtensionMayBeRequired =
        true
    ; algebraicExtensionMayBeRequiredIsTrue =
        refl
    ; entryFieldComputationTarget =
        Field.canonicalCKMFieldCarrierComputationTarget
    ; entryFieldConcreteYukawaInputInventory =
        Field.canonicalCKMConcreteYukawaInputInventory
    ; firstEntryFieldMissingInputIsConcreteUpMatrix =
        refl
    ; firstEntryFieldMissingUpYukawaEntryIsY11 =
        refl
    ; entryFieldAnyConcreteUpEntrySuppliedIsFalse =
        refl
    ; entryFieldY11Progress =
        Field.canonicalCKMConcreteUpYukawaY11Progress
    ; entryFieldY11ProgressStartsFromY11Blocker =
        refl
    ; entryFieldY11ProgressMarksY11AsSupplied =
        refl
    ; entryFieldY11ProgressAdvancesNextMissingUpEntryToY12 =
        refl
    ; entryFieldY11ProgressKeepsUpMatrixIncomplete =
        refl
    ; entryFieldY12Progress =
        Field.canonicalCKMConcreteUpYukawaY12Progress
    ; entryFieldY12ProgressStartsFromY12Blocker =
        refl
    ; entryFieldY12ProgressMarksY12AsSupplied =
        refl
    ; entryFieldY12ProgressAdvancesNextMissingUpEntryToY13 =
        refl
    ; entryFieldY12ProgressKeepsUpMatrixIncomplete =
        refl
    ; entryFieldY13Progress =
        Field.canonicalCKMConcreteUpYukawaY13Progress
    ; entryFieldY13ProgressStartsFromY13Blocker =
        refl
    ; entryFieldY13ProgressMarksY13AsSupplied =
        refl
    ; entryFieldY13ProgressAdvancesNextMissingUpEntryToY21 =
        refl
    ; entryFieldY13ProgressKeepsUpMatrixIncomplete =
        refl
    ; entryFieldY21Progress =
        Field.canonicalCKMConcreteUpYukawaY21Progress
    ; entryFieldY21ProgressStartsFromY21Blocker =
        refl
    ; entryFieldY21ProgressMarksY21AsSupplied =
        refl
    ; entryFieldY21ProgressAdvancesNextMissingUpEntryToY22 =
        refl
    ; entryFieldY21ProgressKeepsUpMatrixIncomplete =
        refl
    ; entryFieldY22Progress =
        Field.canonicalCKMConcreteUpYukawaY22Progress
    ; entryFieldY22ProgressStartsFromY22Blocker =
        refl
    ; entryFieldY22ProgressMarksY22AsSupplied =
        refl
    ; entryFieldY22ProgressAdvancesNextMissingUpEntryToY23 =
        refl
    ; entryFieldY22ProgressKeepsUpMatrixIncomplete =
        refl
    ; entryFieldY23Progress =
        Field.canonicalCKMConcreteUpYukawaY23Progress
    ; entryFieldY23ProgressStartsFromY23Blocker =
        refl
    ; entryFieldY23ProgressMarksY23AsSupplied =
        refl
    ; entryFieldY23ProgressAdvancesNextMissingUpEntryToY31 =
        refl
    ; entryFieldY23ProgressKeepsUpMatrixIncomplete =
        refl
    ; entryFieldY31Progress =
        Field.canonicalCKMConcreteUpYukawaY31Progress
    ; entryFieldY31ProgressStartsFromY31Blocker =
        refl
    ; entryFieldY31ProgressMarksY31AsSupplied =
        refl
    ; entryFieldY31ProgressAdvancesNextMissingUpEntryToY32 =
        refl
    ; entryFieldY31ProgressKeepsUpMatrixIncomplete =
        refl
    ; entryFieldY32Progress =
        Field.canonicalCKMConcreteUpYukawaY32Progress
    ; entryFieldY32ProgressStartsFromY32Blocker =
        refl
    ; entryFieldY32ProgressMarksY32AsSupplied =
        refl
    ; entryFieldY32ProgressAdvancesNextMissingUpEntryToY33 =
        refl
    ; entryFieldY32ProgressKeepsUpMatrixIncomplete =
        refl
    ; entryFieldY33Progress =
        Field.canonicalCKMConcreteUpYukawaY33Progress
    ; entryFieldY33ProgressStartsFromY33Blocker =
        refl
    ; entryFieldY33ProgressMarksY33AsSupplied =
        refl
    ; entryFieldY33ProgressDischargesRemainingUpEntrySlots =
        refl
    ; entryFieldY33ProgressMarksUpMatrixComplete =
        refl
    ; entryFieldMatrixAssemblyReceipt =
        Field.canonicalCKMConcreteYukawaMatrixAssemblyReceipt
    ; entryFieldMatrixAssemblyReceiptDischargesUpEntrySlots =
        refl
    ; entryFieldMatrixAssemblyReceiptAdvancesFirstArithmeticBlockerToConcreteDownMatrix =
        refl
    ; entryFieldDownMatrixRequestProgress =
        Field.canonicalCKMConcreteDownYukawaMatrixRequestProgress
    ; entryFieldDownMatrixRequestProgressStartsFromConcreteDownMatrixBlocker =
        refl
    ; entryFieldDownMatrixRequestProgressRecordsRequestPackaging =
        refl
    ; entryFieldDownMatrixRequestProgressKeepsFirstArithmeticBlockerAtConcreteDownMatrix =
        refl
    ; entryFieldDownY11Progress =
        Field.canonicalCKMConcreteDownYukawaY11Progress
    ; entryFieldDownY11ProgressStartsFromConcreteDownMatrixBlocker =
        refl
    ; entryFieldDownY11ProgressMarksDownY11AsSupplied =
        refl
    ; entryFieldDownY11ProgressAdvancesNextMissingDownEntryToY12 =
        refl
    ; entryFieldDownY11ProgressKeepsFirstArithmeticBlockerAtConcreteDownMatrix =
        refl
    ; entryFieldDownY12Progress =
        Field.canonicalCKMConcreteDownYukawaY12Progress
    ; entryFieldDownY12ProgressStartsFromY12Blocker =
        refl
    ; entryFieldDownY12ProgressMarksDownY12AsSupplied =
        refl
    ; entryFieldDownY12ProgressAdvancesNextMissingDownEntryToY13 =
        refl
    ; entryFieldDownY12ProgressKeepsFirstArithmeticBlockerAtConcreteDownMatrix =
        refl
    ; entryFieldDownY13Progress =
        Field.canonicalCKMConcreteDownYukawaY13Progress
    ; entryFieldDownY13ProgressStartsFromY13Blocker =
        refl
    ; entryFieldDownY13ProgressMarksDownY13AsSupplied =
        refl
    ; entryFieldDownY13ProgressAdvancesNextMissingDownEntryToY21 =
        refl
    ; entryFieldDownY13ProgressKeepsFirstArithmeticBlockerAtConcreteDownMatrix =
        refl
    ; entryFieldCharacteristicPolynomialProgress =
        Field.canonicalCKMCharacteristicPolynomialProgress
    ; entryFieldCharacteristicPolynomialProgressStartsFromCharacteristicPolynomialBlocker =
        refl
    ; entryFieldCharacteristicPolynomialProgressMarksCharacteristicPolynomialsAsSupplied =
        refl
    ; entryFieldCharacteristicPolynomialProgressAdvancesNextMissingArithmeticInputToSplittingField =
        refl
    ; entryFieldSplittingFieldProgress =
        Field.canonicalCKMEigenvalueSplittingFieldProgress
    ; entryFieldSplittingFieldProgressStartsFromSplittingFieldBlocker =
        refl
    ; entryFieldSplittingFieldProgressMarksSplittingFieldAsSupplied =
        refl
    ; entryFieldSplittingFieldProgressAdvancesNextMissingArithmeticInputToNormalizedLeftEigenbases =
        refl
    ; entryFieldNormalizedEigenbasisProgress =
        Field.canonicalCKMNormalizedLeftEigenbasisProgress
    ; entryFieldNormalizedEigenbasisProgressStartsFromNormalizedLeftEigenbasisBlocker =
        refl
    ; entryFieldNormalizedEigenbasisProgressMarksNormalizedLeftEigenbasesAsSupplied =
        refl
    ; entryFieldNormalizedEigenbasisProgressAdvancesNextMissingArithmeticInputToCKMProductClosureWitness =
        refl
    ; entryFieldExecutableDecisionNotSupplied =
        refl
    ; entryFieldDecisionIsUnresolved =
        refl
    ; entryFieldDoesNotProveQAloneSuffices =
        refl
    ; continuousSVDPostulateInLedger =
        false
    ; continuousSVDPostulateInLedgerIsFalse =
        refl
    ; rationalGramSchmidtMissingPrimitives =
        canonicalCKMRationalGramSchmidtMissingPrimitives
    ; rationalGramSchmidtMissingPrimitivesAreCanonical =
        refl
    ; algebraicDiagonalizationMissingPrimitives =
        canonicalCKMAlgebraicDiagonalizationMissingPrimitives
    ; algebraicDiagonalizationMissingPrimitivesAreCanonical =
        refl
    ; ckmMatrixConstructedInternally =
        false
    ; ckmMatrixConstructedInternallyIsFalse =
        refl
    ; ckmPromotionConstructed =
        false
    ; ckmPromotionConstructedIsFalse =
        refl
    ; svdAuthorityBoundary =
        "The continuous SVD postulate is not part of the CKM ledger"
        ∷ "The admissible internal route is exact carrier diagonalization over Q or a finite algebraic extension selected by the Yukawa spectral data"
        ∷ "The concrete input inventory found FactorVec = Vec15 Nat, but only opaque YukawaTextureTarget/YukawaSector/MixingMatrix carriers for Yukawa and CKM data"
        ∷ "Entry-level blocker refinement is explicit: the first concrete up-type matrix entry still missing is y11"
        ∷ "A staged y11 checkpoint is now recorded, and the next exact up-type matrix-entry blocker advances to y12"
        ∷ "A staged y12 checkpoint is now recorded, and the next exact up-type matrix-entry blocker advances to y13"
        ∷ "A staged y13 checkpoint is now recorded, and the next exact up-type matrix-entry blocker advances to y21"
        ∷ "A staged y21 checkpoint is now recorded, and the next exact up-type matrix-entry blocker advances to y22"
        ∷ "A staged y22 checkpoint is now recorded, and the next exact up-type matrix-entry blocker advances to y23"
        ∷ "A staged y23 checkpoint is now recorded, and the next exact up-type matrix-entry blocker advances to y31"
        ∷ "A staged y31 checkpoint is now recorded, and the next exact up-type matrix-entry blocker advances to y32"
        ∷ "A staged y32 checkpoint is now recorded, and the next exact up-type matrix-entry blocker advances to y33"
        ∷ "A staged y33 checkpoint is now recorded, discharging the staged up-type entry-slot queue and shifting the first assembly blocker to the concrete down-type matrix"
        ∷ "A staged down-type matrix request socket is now recorded, while the first arithmetic blocker remains the unsupplied concrete down-type 3x3 matrix"
        ∷ "A staged down-type y11 checkpoint is now recorded, and the next exact down-type matrix-entry blocker advances to y12"
        ∷ "A staged down-type y12 checkpoint is now recorded, and the next exact down-type matrix-entry blocker advances to y13"
        ∷ "A staged down-type y13 checkpoint is now recorded, and the next exact down-type matrix-entry blocker advances to y21"
        ∷ "A staged characteristic-polynomial checkpoint is now recorded, and the next exact spectral blocker advances to eigenvalue splitting-field closure"
        ∷ "A staged splitting-field checkpoint is now recorded, and the next exact spectral blocker advances to normalized left-eigenbasis closure"
        ∷ "A staged normalized left-eigenbasis checkpoint is now recorded, and the next exact spectral blocker advances to CKM product-field closure"
        ∷ "The first executable arithmetic blocker is now the concrete down-type 3x3 Yukawa matrix, followed by the FactorVec-to-entry map"
        ∷ "Rational Yukawa entries alone do not prove rational normalized diagonalizers; the ledger therefore records algebraic-extension risk explicitly"
        ∷ "Constructive closure is still not inhabited because matrix entries, Hermitian products, selected field/extension, normalized eigenbases, DHR-Yukawa compatibility, and weak-to-mass basis identification are not supplied together"
        ∷ "W4 remains external only for calibrated CKM angle/phase numeric values"
        ∷ "No CKM matrix construction, W4-calibrated value receipt, Higgs promotion, or CKM promotion is supplied by this lane"
        ∷ []
    }

ckmSVDAuthorityBoundaryKeepsConstructiveClosureOpen :
  rationalGramSchmidtConstructiveClosureSupplied
    canonicalCKMSVDAuthorityBoundaryLedger
  ≡
  false
ckmSVDAuthorityBoundaryKeepsConstructiveClosureOpen =
  refl

ckmSVDAuthorityBoundaryHasNoContinuousSVDPostulate :
  continuousSVDPostulateInLedger canonicalCKMSVDAuthorityBoundaryLedger
  ≡
  false
ckmSVDAuthorityBoundaryHasNoContinuousSVDPostulate =
  refl

ckmSVDAuthorityBoundaryDoesNotProveQAloneSuffices :
  rationalFieldSufficiencyProved canonicalCKMSVDAuthorityBoundaryLedger
  ≡
  false
ckmSVDAuthorityBoundaryDoesNotProveQAloneSuffices =
  refl

ckmSVDAuthorityBoundaryRecordsAlgebraicExtensionRisk :
  algebraicExtensionMayBeRequired canonicalCKMSVDAuthorityBoundaryLedger
  ≡
  true
ckmSVDAuthorityBoundaryRecordsAlgebraicExtensionRisk =
  refl

ckmSVDAuthorityBoundaryFirstMissingEntryFieldInput :
  Field.firstMissingArithmeticInput
    (entryFieldConcreteYukawaInputInventory
      canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingConcreteUpYukawa3x3Matrix
ckmSVDAuthorityBoundaryFirstMissingEntryFieldInput =
  refl

ckmSVDAuthorityBoundaryFirstMissingConcreteUpEntryIsY11 :
  Field.firstMissingUpYukawaEntry
    (entryFieldConcreteYukawaInputInventory
      canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY11
ckmSVDAuthorityBoundaryFirstMissingConcreteUpEntryIsY11 =
  refl

ckmSVDAuthorityBoundaryY11ProgressAdvancesNextEntryToY12 :
  Field.nextMissingUpYukawaEntry
    (entryFieldY11Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY12
ckmSVDAuthorityBoundaryY11ProgressAdvancesNextEntryToY12 =
  refl

ckmSVDAuthorityBoundaryY12ProgressAdvancesNextEntryToY13 :
  Field.nextMissingUpYukawaEntry
    (entryFieldY12Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY13
ckmSVDAuthorityBoundaryY12ProgressAdvancesNextEntryToY13 =
  refl

ckmSVDAuthorityBoundaryY13ProgressAdvancesNextEntryToY21 :
  Field.nextMissingUpYukawaEntry
    (entryFieldY13Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY21
ckmSVDAuthorityBoundaryY13ProgressAdvancesNextEntryToY21 =
  refl

ckmSVDAuthorityBoundaryY21ProgressAdvancesNextEntryToY22 :
  Field.nextMissingUpYukawaEntry
    (entryFieldY21Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY22
ckmSVDAuthorityBoundaryY21ProgressAdvancesNextEntryToY22 =
  refl

ckmSVDAuthorityBoundaryY22ProgressAdvancesNextEntryToY23 :
  Field.nextMissingUpYukawaEntry
    (entryFieldY22Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY23
ckmSVDAuthorityBoundaryY22ProgressAdvancesNextEntryToY23 =
  refl

ckmSVDAuthorityBoundaryY23ProgressAdvancesNextEntryToY31 :
  Field.nextMissingUpYukawaEntry
    (entryFieldY23Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY31
ckmSVDAuthorityBoundaryY23ProgressAdvancesNextEntryToY31 =
  refl

ckmSVDAuthorityBoundaryY31ProgressAdvancesNextEntryToY32 :
  Field.nextMissingUpYukawaEntry
    (entryFieldY31Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY32
ckmSVDAuthorityBoundaryY31ProgressAdvancesNextEntryToY32 =
  refl

ckmSVDAuthorityBoundaryY32ProgressAdvancesNextEntryToY33 :
  Field.nextMissingUpYukawaEntry
    (entryFieldY32Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY33
ckmSVDAuthorityBoundaryY32ProgressAdvancesNextEntryToY33 =
  refl

ckmSVDAuthorityBoundaryY33ProgressDischargesRemainingEntrySlots :
  Field.remainingMissingUpEntrySlots
    (entryFieldY33Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  []
ckmSVDAuthorityBoundaryY33ProgressDischargesRemainingEntrySlots =
  refl

ckmSVDAuthorityBoundaryY33ProgressMarksUpMatrixComplete :
  Field.upMatrixStillIncomplete
    (entryFieldY33Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  false
ckmSVDAuthorityBoundaryY33ProgressMarksUpMatrixComplete =
  refl

ckmSVDAuthorityBoundaryMatrixAssemblyReceiptAdvancesFirstBlockerToConcreteDownMatrix :
  Field.firstMissingArithmeticInputAfterUpMatrixAssembly
    (entryFieldMatrixAssemblyReceipt canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingConcreteDownYukawa3x3Matrix
ckmSVDAuthorityBoundaryMatrixAssemblyReceiptAdvancesFirstBlockerToConcreteDownMatrix =
  refl

ckmSVDAuthorityBoundaryDownMatrixRequestProgressKeepsFirstBlockerAtConcreteDownMatrix :
  Field.firstMissingArithmeticInputAfterDownMatrixRequest
    (entryFieldDownMatrixRequestProgress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingConcreteDownYukawa3x3Matrix
ckmSVDAuthorityBoundaryDownMatrixRequestProgressKeepsFirstBlockerAtConcreteDownMatrix =
  refl

ckmSVDAuthorityBoundaryDownY11ProgressAdvancesNextEntryToY12 :
  Field.nextMissingDownYukawaEntry
    (entryFieldDownY11Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY12
ckmSVDAuthorityBoundaryDownY11ProgressAdvancesNextEntryToY12 =
  refl

ckmSVDAuthorityBoundaryDownY11ProgressKeepsFirstBlockerAtConcreteDownMatrix :
  Field.firstMissingArithmeticInputAfterDownY11
    (entryFieldDownY11Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingConcreteDownYukawa3x3Matrix
ckmSVDAuthorityBoundaryDownY11ProgressKeepsFirstBlockerAtConcreteDownMatrix =
  refl

ckmSVDAuthorityBoundaryDownY12ProgressAdvancesNextEntryToY13 :
  Field.nextMissingDownYukawaEntry
    (entryFieldDownY12Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY13
ckmSVDAuthorityBoundaryDownY12ProgressAdvancesNextEntryToY13 =
  refl

ckmSVDAuthorityBoundaryDownY12ProgressKeepsFirstBlockerAtConcreteDownMatrix :
  Field.firstMissingArithmeticInputAfterDownY12
    (entryFieldDownY12Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingConcreteDownYukawa3x3Matrix
ckmSVDAuthorityBoundaryDownY12ProgressKeepsFirstBlockerAtConcreteDownMatrix =
  refl

ckmSVDAuthorityBoundaryDownY13ProgressAdvancesNextEntryToY21 :
  Field.nextMissingDownYukawaEntry
    (entryFieldDownY13Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingY21
ckmSVDAuthorityBoundaryDownY13ProgressAdvancesNextEntryToY21 =
  refl

ckmSVDAuthorityBoundaryDownY13ProgressKeepsFirstBlockerAtConcreteDownMatrix :
  Field.firstMissingArithmeticInputAfterDownY13
    (entryFieldDownY13Progress canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingConcreteDownYukawa3x3Matrix
ckmSVDAuthorityBoundaryDownY13ProgressKeepsFirstBlockerAtConcreteDownMatrix =
  refl

ckmSVDAuthorityBoundaryCharacteristicPolynomialProgressAdvancesToSplittingField :
  Field.nextMissingArithmeticInput
    (entryFieldCharacteristicPolynomialProgress
      canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingEigenvalueSplittingField
ckmSVDAuthorityBoundaryCharacteristicPolynomialProgressAdvancesToSplittingField =
  refl

ckmSVDAuthorityBoundarySplittingFieldProgressAdvancesToNormalizedLeftEigenbases :
  Field.nextMissingArithmeticInput
    (entryFieldSplittingFieldProgress
      canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingNormalizedLeftEigenbases
ckmSVDAuthorityBoundarySplittingFieldProgressAdvancesToNormalizedLeftEigenbases =
  refl

ckmSVDAuthorityBoundaryNormalizedEigenbasisProgressAdvancesToCKMProductClosure :
  Field.nextMissingArithmeticInput
    (entryFieldNormalizedEigenbasisProgress
      canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  Field.missingCKMProductClosureWitness
ckmSVDAuthorityBoundaryNormalizedEigenbasisProgressAdvancesToCKMProductClosure =
  refl

ckmSVDAuthorityBoundaryHasNoExecutableEntryFieldDecision :
  Field.executableFieldMembershipDecisionSupplied
    (entryFieldConcreteYukawaInputInventory
      canonicalCKMSVDAuthorityBoundaryLedger)
  ≡
  false
ckmSVDAuthorityBoundaryHasNoExecutableEntryFieldDecision =
  refl

ckmSVDAuthorityBoundaryKeepsW4External :
  w4AnglePhaseAuthorityExternal canonicalCKMSVDAuthorityBoundaryLedger
  ≡
  refl
ckmSVDAuthorityBoundaryKeepsW4External =
  refl

------------------------------------------------------------------------
-- Post-up-matrix DHR/Yukawa intertwiner compatibility request.
--
-- The staged up-type entry queue has already reached y33.  The honest next
-- surface is therefore not another up-entry checkpoint; it is the typed request
-- for the DHR intertwiner compatibility law that must connect the symbolic
-- Yukawa/SVD carrier interface to DHR transport before CKM closure can be
-- assembled.

data CKMPostUpMatrixDHRYukawaRequestComponent : Set where
  completedStagedUpMatrixEntryQueueComponent :
    CKMPostUpMatrixDHRYukawaRequestComponent

  retainedConcreteDownMatrixBlockerComponent :
    CKMPostUpMatrixDHRYukawaRequestComponent

  requestedPaper2DHRIntertwinerActionComponent :
    CKMPostUpMatrixDHRYukawaRequestComponent

  requestedYukawaTextureDHRTransportLawComponent :
    CKMPostUpMatrixDHRYukawaRequestComponent

  retainedWeakToMassBasisIdentificationBlockerComponent :
    CKMPostUpMatrixDHRYukawaRequestComponent

canonicalCKMPostUpMatrixDHRYukawaRequestComponents :
  List CKMPostUpMatrixDHRYukawaRequestComponent
canonicalCKMPostUpMatrixDHRYukawaRequestComponents =
  completedStagedUpMatrixEntryQueueComponent
  ∷ retainedConcreteDownMatrixBlockerComponent
  ∷ requestedPaper2DHRIntertwinerActionComponent
  ∷ requestedYukawaTextureDHRTransportLawComponent
  ∷ retainedWeakToMassBasisIdentificationBlockerComponent
  ∷ []

record CKMPostUpMatrixDHRYukawaIntertwinerRequestSurface : Setω where
  field
    ckmPostUpMatrixAuthorityBoundaryLedger :
      CKMSVDAuthorityBoundaryLedger

    ckmPostUpMatrixCompatibilityRoute :
      CKMYukawaAsDHRIntertwinerCompatibilityRoute

    ckmPostUpMatrixAbsenceLedger :
      CKMYukawaDHRIntertwinerCompatibilityAbsenceLedger

    ckmPostUpMatrixRequestComponents :
      List CKMPostUpMatrixDHRYukawaRequestComponent

    ckmPostUpMatrixRequestComponentsAreCanonical :
      ckmPostUpMatrixRequestComponents
      ≡
      canonicalCKMPostUpMatrixDHRYukawaRequestComponents

    ckmPostUpMatrixQueueDischarged :
      Field.remainingMissingUpEntrySlots
        (entryFieldY33Progress ckmPostUpMatrixAuthorityBoundaryLedger)
      ≡
      []

    ckmPostUpMatrixMarkedComplete :
      Field.upMatrixStillIncomplete
        (entryFieldY33Progress ckmPostUpMatrixAuthorityBoundaryLedger)
      ≡
      false

    ckmPostUpMatrixDownMatrixStillFirstBlocker :
      Field.firstMissingArithmeticInputAfterDownY11
        (entryFieldDownY11Progress ckmPostUpMatrixAuthorityBoundaryLedger)
      ≡
      Field.missingConcreteDownYukawa3x3Matrix

    ckmPostUpMatrixDHRIntertwinerTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      Matter.YukawaTextureTarget →
      Set

    ckmPostUpMatrixDHRIntertwinerTargetRecorded :
      Bool

    ckmPostUpMatrixDHRIntertwinerTargetRecordedIsTrue :
      ckmPostUpMatrixDHRIntertwinerTargetRecorded ≡ true

    ckmPostUpMatrixFirstCompatibilityBlocker :
      CKMYukawaDHRCompatibilityBlocker

    ckmPostUpMatrixFirstCompatibilityBlockerIsIntertwiner :
      ckmPostUpMatrixFirstCompatibilityBlocker
      ≡
      missingYukawaDHRIntertwinerCompatibility

    ckmPostUpMatrixDHRIntertwinerProofSupplied :
      Bool

    ckmPostUpMatrixDHRIntertwinerProofSuppliedIsFalse :
      ckmPostUpMatrixDHRIntertwinerProofSupplied ≡ false

    ckmPostUpMatrixActualMatricesSupplied :
      Bool

    ckmPostUpMatrixActualMatricesSuppliedIsFalse :
      ckmPostUpMatrixActualMatricesSupplied ≡ false

    ckmPostUpMatrixFNChargeClosurePromoted :
      Bool

    ckmPostUpMatrixFNChargeClosurePromotedIsFalse :
      ckmPostUpMatrixFNChargeClosurePromoted ≡ false

    ckmPostUpMatrixExactTextureStillNotPromoted :
      Matter.exactTexturePromoted
        Matter.canonicalMatterPrimeLaneYukawaFNReceipt
      ≡
      false

    ckmPostUpMatrixTopYukawaHiggsChargeStillOpen :
      Matter.topYukawaHiggsChargeInconsistencyOpen
        Matter.canonicalMatterPrimeLaneYukawaFNReceipt
      ≡
      true

    ckmPostUpMatrixCKMClosureConstructed :
      Bool

    ckmPostUpMatrixCKMClosureConstructedIsFalse :
      ckmPostUpMatrixCKMClosureConstructed ≡ false

    ckmPostUpMatrixMatterRepresentationsDerivedStillFalse :
      Matter.matterRepresentationsDerived
        Matter.canonicalMatterRepresentationReceiptSurface
      ≡
      false

    ckmPostUpMatrixRequestPromotesCKM :
      Bool

    ckmPostUpMatrixRequestPromotesCKMIsFalse :
      ckmPostUpMatrixRequestPromotesCKM ≡ false

    ckmPostUpMatrixRequestBoundary :
      List String

open CKMPostUpMatrixDHRYukawaIntertwinerRequestSurface public

canonicalCKMPostUpMatrixDHRYukawaIntertwinerRequestSurface :
  CKMPostUpMatrixDHRYukawaIntertwinerRequestSurface
canonicalCKMPostUpMatrixDHRYukawaIntertwinerRequestSurface =
  record
    { ckmPostUpMatrixAuthorityBoundaryLedger =
        canonicalCKMSVDAuthorityBoundaryLedger
    ; ckmPostUpMatrixCompatibilityRoute =
        canonicalCKMYukawaAsDHRIntertwinerCompatibilityRoute
    ; ckmPostUpMatrixAbsenceLedger =
        canonicalCKMYukawaDHRIntertwinerCompatibilityAbsenceLedger
    ; ckmPostUpMatrixRequestComponents =
        canonicalCKMPostUpMatrixDHRYukawaRequestComponents
    ; ckmPostUpMatrixRequestComponentsAreCanonical =
        refl
    ; ckmPostUpMatrixQueueDischarged =
        refl
    ; ckmPostUpMatrixMarkedComplete =
        refl
    ; ckmPostUpMatrixDownMatrixStillFirstBlocker =
        refl
    ; ckmPostUpMatrixDHRIntertwinerTarget =
        YukawaDHRIntertwinerCompatibilityTarget
    ; ckmPostUpMatrixDHRIntertwinerTargetRecorded =
        true
    ; ckmPostUpMatrixDHRIntertwinerTargetRecordedIsTrue =
        refl
    ; ckmPostUpMatrixFirstCompatibilityBlocker =
        missingYukawaDHRIntertwinerCompatibility
    ; ckmPostUpMatrixFirstCompatibilityBlockerIsIntertwiner =
        refl
    ; ckmPostUpMatrixDHRIntertwinerProofSupplied =
        false
    ; ckmPostUpMatrixDHRIntertwinerProofSuppliedIsFalse =
        refl
    ; ckmPostUpMatrixActualMatricesSupplied =
        false
    ; ckmPostUpMatrixActualMatricesSuppliedIsFalse =
        refl
    ; ckmPostUpMatrixFNChargeClosurePromoted =
        false
    ; ckmPostUpMatrixFNChargeClosurePromotedIsFalse =
        refl
    ; ckmPostUpMatrixExactTextureStillNotPromoted =
        refl
    ; ckmPostUpMatrixTopYukawaHiggsChargeStillOpen =
        refl
    ; ckmPostUpMatrixCKMClosureConstructed =
        false
    ; ckmPostUpMatrixCKMClosureConstructedIsFalse =
        refl
    ; ckmPostUpMatrixMatterRepresentationsDerivedStillFalse =
        refl
    ; ckmPostUpMatrixRequestPromotesCKM =
        false
    ; ckmPostUpMatrixRequestPromotesCKMIsFalse =
        refl
    ; ckmPostUpMatrixRequestBoundary =
        "The staged up-type entry queue is complete through y33, so this surface does not add another up-entry receipt"
        ∷ "The concrete down-type 3x3 matrix remains the first arithmetic matrix blocker after the staged down-y11 checkpoint"
        ∷ "The requested next compatibility proof is a Paper 2 DHR intertwiner action law for the symbolic Yukawa/SVD carrier interface"
        ∷ "Actual matrices, FN charge closure, CKM closure, and matterRepresentationsDerived remain unpromoted"
        ∷ "No CKM matrix construction, W4-calibrated value receipt, Higgs promotion, or CKM promotion is supplied"
        ∷ []
    }

ckmPostUpMatrixDHRYukawaRequestFirstBlockerIsIntertwiner :
  ckmPostUpMatrixFirstCompatibilityBlocker
    canonicalCKMPostUpMatrixDHRYukawaIntertwinerRequestSurface
  ≡
  missingYukawaDHRIntertwinerCompatibility
ckmPostUpMatrixDHRYukawaRequestFirstBlockerIsIntertwiner =
  refl

ckmPostUpMatrixDHRYukawaRequestKeepsActualMatricesUnpromoted :
  ckmPostUpMatrixActualMatricesSupplied
    canonicalCKMPostUpMatrixDHRYukawaIntertwinerRequestSurface
  ≡
  false
ckmPostUpMatrixDHRYukawaRequestKeepsActualMatricesUnpromoted =
  refl

ckmPostUpMatrixDHRYukawaRequestKeepsMatterRepresentationsUnpromoted :
  ckmPostUpMatrixMatterRepresentationsDerivedStillFalse
    canonicalCKMPostUpMatrixDHRYukawaIntertwinerRequestSurface
  ≡
  refl
ckmPostUpMatrixDHRYukawaRequestKeepsMatterRepresentationsUnpromoted =
  refl

ckmPostUpMatrixDHRYukawaRequestDoesNotPromote :
  ckmPostUpMatrixRequestPromotesCKM
    canonicalCKMPostUpMatrixDHRYukawaIntertwinerRequestSurface
  ≡
  false
ckmPostUpMatrixDHRYukawaRequestDoesNotPromote =
  refl

------------------------------------------------------------------------
-- l1 CKM product-closure and Wolfenstein/Jarlskog target surfaces.

data CKMMatterMixingMatrixProductClosureComponent : Set where
  upLeftEigenbasisMatterMixingMatrixComponent :
    CKMMatterMixingMatrixProductClosureComponent

  downLeftEigenbasisMatterMixingMatrixComponent :
    CKMMatterMixingMatrixProductClosureComponent

  leftMismatchMatterMixingMatrixComponent :
    CKMMatterMixingMatrixProductClosureComponent

  fieldClosureCertificateComponent :
    CKMMatterMixingMatrixProductClosureComponent

  unitarityResidualCertificateComponent :
    CKMMatterMixingMatrixProductClosureComponent

canonicalCKMMatterMixingMatrixProductClosureComponents :
  List CKMMatterMixingMatrixProductClosureComponent
canonicalCKMMatterMixingMatrixProductClosureComponents =
  upLeftEigenbasisMatterMixingMatrixComponent
  ∷ downLeftEigenbasisMatterMixingMatrixComponent
  ∷ leftMismatchMatterMixingMatrixComponent
  ∷ fieldClosureCertificateComponent
  ∷ unitarityResidualCertificateComponent
  ∷ []

record CKMMatterMixingMatrixProductClosureLedger : Setω where
  field
    entryFieldSpectralStaging :
      Field.CKMUpDownHermitianCharacteristicEigenbasisStaging

    executableStagedEntryFieldArithmetic :
      Field.CKMExecutableStagedEntryFieldArithmetic

    executableStagedEntryFieldArithmeticIsFromSpectralStaging :
      Bool

    stagedEntryMembershipCertificatesConsumed :
      Field.stagedEntryFieldMembershipCertificatesSupplied
        executableStagedEntryFieldArithmetic
      ≡
      true

    stagedHermitianProductsConsumed :
      Field.stagedHermitianProductsComputed executableStagedEntryFieldArithmetic
      ≡
      true

    productClosureComponents :
      List CKMMatterMixingMatrixProductClosureComponent

    productClosureComponentsAreCanonical :
      productClosureComponents
      ≡
      canonicalCKMMatterMixingMatrixProductClosureComponents

    upLeftEigenbasisCarrierTarget :
      Set

    upLeftEigenbasisCarrierTargetIsMatterMixingMatrix :
      upLeftEigenbasisCarrierTarget
      ≡
      Matter.MixingMatrix

    downLeftEigenbasisCarrierTarget :
      Set

    downLeftEigenbasisCarrierTargetIsMatterMixingMatrix :
      downLeftEigenbasisCarrierTarget
      ≡
      Matter.MixingMatrix

    ckmLeftMismatchCarrierTarget :
      Set

    ckmLeftMismatchCarrierTargetIsMatterMixingMatrix :
      ckmLeftMismatchCarrierTarget
      ≡
      Matter.MixingMatrix

    ckmProductFormula :
      String

    ckmProductFormula-v :
      ckmProductFormula
      ≡
      "V_CKM = U_u^dagger * U_d"

    separateProductMatrixCarrierIntroduced :
      Bool

    separateProductMatrixCarrierIntroducedIsFalse :
      separateProductMatrixCarrierIntroduced ≡ false

    productClosureLedgerUsesMatterMixingMatrix :
      Bool

    productClosureLedgerUsesMatterMixingMatrixIsTrue :
      productClosureLedgerUsesMatterMixingMatrix ≡ true

    productFieldClosureWitnessSupplied :
      Bool

    productFieldClosureWitnessSuppliedIsFalse :
      productFieldClosureWitnessSupplied ≡ false

    unitarityResidualWitnessSupplied :
      Bool

    unitarityResidualWitnessSuppliedIsFalse :
      unitarityResidualWitnessSupplied ≡ false

    firstProductClosureBlocker :
      Field.CKMArithmeticInputSlot

    firstProductClosureBlockerIsCKMProductClosureWitness :
      firstProductClosureBlocker
      ≡
      Field.missingCKMProductClosureWitness

    carrierMixingTheoremSupplied :
      Bool

    carrierMixingTheoremSuppliedIsFalse :
      carrierMixingTheoremSupplied ≡ false

    productClosureLedgerBoundary :
      List String

open CKMMatterMixingMatrixProductClosureLedger public

canonicalCKMMatterMixingMatrixProductClosureLedger :
  CKMMatterMixingMatrixProductClosureLedger
canonicalCKMMatterMixingMatrixProductClosureLedger =
  record
    { entryFieldSpectralStaging =
        Field.canonicalCKMUpDownHermitianCharacteristicEigenbasisStaging
    ; executableStagedEntryFieldArithmetic =
        Field.canonicalCKMExecutableStagedEntryFieldArithmetic
    ; executableStagedEntryFieldArithmeticIsFromSpectralStaging =
        true
    ; stagedEntryMembershipCertificatesConsumed =
        refl
    ; stagedHermitianProductsConsumed =
        refl
    ; productClosureComponents =
        canonicalCKMMatterMixingMatrixProductClosureComponents
    ; productClosureComponentsAreCanonical =
        refl
    ; upLeftEigenbasisCarrierTarget =
        Matter.MixingMatrix
    ; upLeftEigenbasisCarrierTargetIsMatterMixingMatrix =
        refl
    ; downLeftEigenbasisCarrierTarget =
        Matter.MixingMatrix
    ; downLeftEigenbasisCarrierTargetIsMatterMixingMatrix =
        refl
    ; ckmLeftMismatchCarrierTarget =
        Matter.MixingMatrix
    ; ckmLeftMismatchCarrierTargetIsMatterMixingMatrix =
        refl
    ; ckmProductFormula =
        "V_CKM = U_u^dagger * U_d"
    ; ckmProductFormula-v =
        refl
    ; separateProductMatrixCarrierIntroduced =
        false
    ; separateProductMatrixCarrierIntroducedIsFalse =
        refl
    ; productClosureLedgerUsesMatterMixingMatrix =
        true
    ; productClosureLedgerUsesMatterMixingMatrixIsTrue =
        refl
    ; productFieldClosureWitnessSupplied =
        false
    ; productFieldClosureWitnessSuppliedIsFalse =
        refl
    ; unitarityResidualWitnessSupplied =
        false
    ; unitarityResidualWitnessSuppliedIsFalse =
        refl
    ; firstProductClosureBlocker =
        Field.missingCKMProductClosureWitness
    ; firstProductClosureBlockerIsCKMProductClosureWitness =
        refl
    ; carrierMixingTheoremSupplied =
        false
    ; carrierMixingTheoremSuppliedIsFalse =
        refl
    ; productClosureLedgerBoundary =
        "The l1 CKM product target is recorded directly as Matter.MixingMatrix"
        ∷ "The product ledger consumes the executable staged entry-field membership certificates and finite Hermitian products from CKMEntryField"
        ∷ "The staged formula is the left-unitary mismatch V_CKM = U_u^dagger * U_d"
        ∷ "Field closure and unitarity residual certificates are named but not supplied"
        ∷ "The first product blocker remains Field.missingCKMProductClosureWitness"
        ∷ "No carrier mixing theorem, DHR compatibility theorem, or CKM promotion is introduced"
        ∷ []
    }

data CKMWolfensteinTargetSurfaceLabel : Set where
  wolfensteinLambdaTarget :
    CKMWolfensteinTargetSurfaceLabel

  wolfensteinATarget :
    CKMWolfensteinTargetSurfaceLabel

  wolfensteinRhoBarTarget :
    CKMWolfensteinTargetSurfaceLabel

  wolfensteinEtaBarTarget :
    CKMWolfensteinTargetSurfaceLabel

  wolfensteinHierarchyOrderTarget :
    CKMWolfensteinTargetSurfaceLabel

canonicalCKMWolfensteinTargetSurfaceLabels :
  List CKMWolfensteinTargetSurfaceLabel
canonicalCKMWolfensteinTargetSurfaceLabels =
  wolfensteinLambdaTarget
  ∷ wolfensteinATarget
  ∷ wolfensteinRhoBarTarget
  ∷ wolfensteinEtaBarTarget
  ∷ wolfensteinHierarchyOrderTarget
  ∷ []

data CKMJarlskogTargetSurfaceLabel : Set where
  jarlskogInvariantTarget :
    CKMJarlskogTargetSurfaceLabel

  jarlskogNonzeroTarget :
    CKMJarlskogTargetSurfaceLabel

  jarlskogCPViolationOrientationTarget :
    CKMJarlskogTargetSurfaceLabel

  jarlskogFrobeniusPhaseSourceTarget :
    CKMJarlskogTargetSurfaceLabel

canonicalCKMJarlskogTargetSurfaceLabels :
  List CKMJarlskogTargetSurfaceLabel
canonicalCKMJarlskogTargetSurfaceLabels =
  jarlskogInvariantTarget
  ∷ jarlskogNonzeroTarget
  ∷ jarlskogCPViolationOrientationTarget
  ∷ jarlskogFrobeniusPhaseSourceTarget
  ∷ []

data CKMWolfensteinFiniteArithmeticComponent : Set where
  wolfensteinLambdaFromCabibboMismatchComponent :
    CKMWolfensteinFiniteArithmeticComponent

  wolfensteinAFromSecondThirdGenerationMismatchComponent :
    CKMWolfensteinFiniteArithmeticComponent

  wolfensteinRhoBarEtaBarFromComplexPhaseComponent :
    CKMWolfensteinFiniteArithmeticComponent

  wolfensteinHierarchyFromFNExponentDifferencesComponent :
    CKMWolfensteinFiniteArithmeticComponent

canonicalCKMWolfensteinFiniteArithmeticComponents :
  List CKMWolfensteinFiniteArithmeticComponent
canonicalCKMWolfensteinFiniteArithmeticComponents =
  wolfensteinLambdaFromCabibboMismatchComponent
  ∷ wolfensteinAFromSecondThirdGenerationMismatchComponent
  ∷ wolfensteinRhoBarEtaBarFromComplexPhaseComponent
  ∷ wolfensteinHierarchyFromFNExponentDifferencesComponent
  ∷ []

data CKMJarlskogSourceComponent : Set where
  jarlskogSourceFromMatterMixingMatrixQuartetComponent :
    CKMJarlskogSourceComponent

  jarlskogSourceFromFrobeniusPhaseOrientationComponent :
    CKMJarlskogSourceComponent

  jarlskogSourceRequiresNonzeroImaginaryPartComponent :
    CKMJarlskogSourceComponent

canonicalCKMJarlskogSourceComponents :
  List CKMJarlskogSourceComponent
canonicalCKMJarlskogSourceComponents =
  jarlskogSourceFromMatterMixingMatrixQuartetComponent
  ∷ jarlskogSourceFromFrobeniusPhaseOrientationComponent
  ∷ jarlskogSourceRequiresNonzeroImaginaryPartComponent
  ∷ []

record CKMWolfensteinJarlskogTargetSurface : Setω where
  field
    matterMixingMatrixProductClosureLedger :
      CKMMatterMixingMatrixProductClosureLedger

    ckmMatrixCarrierTarget :
      Set

    ckmMatrixCarrierTargetIsMatterMixingMatrix :
      ckmMatrixCarrierTarget
      ≡
      Matter.MixingMatrix

    wolfensteinTargets :
      List CKMWolfensteinTargetSurfaceLabel

    wolfensteinTargetsAreCanonical :
      wolfensteinTargets
      ≡
      canonicalCKMWolfensteinTargetSurfaceLabels

    matterFNWolfensteinRelations :
      List Matter.CKMWolfensteinFNRelationLabel

    matterFNWolfensteinRelationsAreCanonical :
      matterFNWolfensteinRelations
      ≡
      Matter.canonicalCKMWolfensteinFNRelationLabels

    wolfensteinFiniteArithmeticComponents :
      List CKMWolfensteinFiniteArithmeticComponent

    wolfensteinFiniteArithmeticComponentsAreCanonical :
      wolfensteinFiniteArithmeticComponents
      ≡
      canonicalCKMWolfensteinFiniteArithmeticComponents

    jarlskogTargets :
      List CKMJarlskogTargetSurfaceLabel

    jarlskogTargetsAreCanonical :
      jarlskogTargets
      ≡
      canonicalCKMJarlskogTargetSurfaceLabels

    jarlskogSourceComponents :
      List CKMJarlskogSourceComponent

    jarlskogSourceComponentsAreCanonical :
      jarlskogSourceComponents
      ≡
      canonicalCKMJarlskogSourceComponents

    wolfensteinNumericValuesSupplied :
      Bool

    wolfensteinNumericValuesSuppliedIsFalse :
      wolfensteinNumericValuesSupplied ≡ false

    wolfensteinHierarchyProofSupplied :
      Bool

    wolfensteinHierarchyProofSuppliedIsFalse :
      wolfensteinHierarchyProofSupplied ≡ false

    jarlskogInvariantValueSupplied :
      Bool

    jarlskogInvariantValueSuppliedIsFalse :
      jarlskogInvariantValueSupplied ≡ false

    jarlskogNonzeroProofSupplied :
      Bool

    jarlskogNonzeroProofSuppliedIsFalse :
      jarlskogNonzeroProofSupplied ≡ false

    frobeniusPhaseCPNumericBridgeSupplied :
      Bool

    frobeniusPhaseCPNumericBridgeSuppliedIsFalse :
      frobeniusPhaseCPNumericBridgeSupplied ≡ false

    jarlskogSourceIdentifiedButNotValued :
      Bool

    jarlskogSourceIdentifiedButNotValuedIsTrue :
      jarlskogSourceIdentifiedButNotValued ≡ true

    firstCarrierMixingBlocker :
      CKMCarrierMixingFirstMissing

    firstCarrierMixingBlockerIsMissingTheorem :
      firstCarrierMixingBlocker
      ≡
      missingCarrierMixingTheorem

    wolfensteinJarlskogSurfacePromoted :
      Bool

    wolfensteinJarlskogSurfacePromotedIsFalse :
      wolfensteinJarlskogSurfacePromoted ≡ false

    wolfensteinJarlskogBoundary :
      List String

open CKMWolfensteinJarlskogTargetSurface public

canonicalCKMWolfensteinJarlskogTargetSurface :
  CKMWolfensteinJarlskogTargetSurface
canonicalCKMWolfensteinJarlskogTargetSurface =
  record
    { matterMixingMatrixProductClosureLedger =
        canonicalCKMMatterMixingMatrixProductClosureLedger
    ; ckmMatrixCarrierTarget =
        Matter.MixingMatrix
    ; ckmMatrixCarrierTargetIsMatterMixingMatrix =
        refl
    ; wolfensteinTargets =
        canonicalCKMWolfensteinTargetSurfaceLabels
    ; wolfensteinTargetsAreCanonical =
        refl
    ; matterFNWolfensteinRelations =
        Matter.canonicalCKMWolfensteinFNRelationLabels
    ; matterFNWolfensteinRelationsAreCanonical =
        refl
    ; wolfensteinFiniteArithmeticComponents =
        canonicalCKMWolfensteinFiniteArithmeticComponents
    ; wolfensteinFiniteArithmeticComponentsAreCanonical =
        refl
    ; jarlskogTargets =
        canonicalCKMJarlskogTargetSurfaceLabels
    ; jarlskogTargetsAreCanonical =
        refl
    ; jarlskogSourceComponents =
        canonicalCKMJarlskogSourceComponents
    ; jarlskogSourceComponentsAreCanonical =
        refl
    ; wolfensteinNumericValuesSupplied =
        false
    ; wolfensteinNumericValuesSuppliedIsFalse =
        refl
    ; wolfensteinHierarchyProofSupplied =
        false
    ; wolfensteinHierarchyProofSuppliedIsFalse =
        refl
    ; jarlskogInvariantValueSupplied =
        false
    ; jarlskogInvariantValueSuppliedIsFalse =
        refl
    ; jarlskogNonzeroProofSupplied =
        false
    ; jarlskogNonzeroProofSuppliedIsFalse =
        refl
    ; frobeniusPhaseCPNumericBridgeSupplied =
        false
    ; frobeniusPhaseCPNumericBridgeSuppliedIsFalse =
        refl
    ; jarlskogSourceIdentifiedButNotValued =
        true
    ; jarlskogSourceIdentifiedButNotValuedIsTrue =
        refl
    ; firstCarrierMixingBlocker =
        missingCarrierMixingTheorem
    ; firstCarrierMixingBlockerIsMissingTheorem =
        refl
    ; wolfensteinJarlskogSurfacePromoted =
        false
    ; wolfensteinJarlskogSurfacePromotedIsFalse =
        refl
    ; wolfensteinJarlskogBoundary =
        "Wolfenstein lambda/A/rhobar/etabar and hierarchy targets are staged against the Matter.MixingMatrix CKM target"
        ∷ "Matter FN charge-difference relations are referenced as symbolic target labels, not numeric values"
        ∷ "Finite Wolfenstein arithmetic components are staged as mismatch/hierarchy targets fed by the Matter.MixingMatrix ledger"
        ∷ "The Jarlskog source is identified as a Matter.MixingMatrix quartet plus Frobenius-phase orientation target, but no value or nonzero proof is supplied"
        ∷ "Jarlskog invariant, nonzero CP proof, and Frobenius-phase numeric bridge remain target surfaces only"
        ∷ "The carrier mixing theorem remains the first l1 theorem blocker"
        ∷ "No Higgs normalization, DHR intertwiner compatibility theorem, W4 calibration, or CKM promotion is supplied"
        ∷ []
    }

ckmProductClosureLedgerUsesMatterMixingMatrix :
  productClosureLedgerUsesMatterMixingMatrix
    canonicalCKMMatterMixingMatrixProductClosureLedger
  ≡
  true
ckmProductClosureLedgerUsesMatterMixingMatrix =
  refl

ckmProductClosureLedgerKeepsProductWitnessMissing :
  firstProductClosureBlocker
    canonicalCKMMatterMixingMatrixProductClosureLedger
  ≡
  Field.missingCKMProductClosureWitness
ckmProductClosureLedgerKeepsProductWitnessMissing =
  refl

record CKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt : Setω where
  field
    productClosureLedger :
      CKMMatterMixingMatrixProductClosureLedger

    entryFieldProductAttemptReceipt :
      Field.CKMMatterMixingMatrixProductClosureAttemptReceipt

    productAttemptUsesMatterMixingMatrix :
      Field.ckmProductCarrier entryFieldProductAttemptReceipt
      ≡
      Matter.MixingMatrix

    productAttemptRecordsFormula :
      Field.ckmProductFormula entryFieldProductAttemptReceipt
      ≡
      "V_CKM = U_u^dagger * U_d"

    productAttemptFailClosed :
      Field.ckmProductClosureAttemptFailClosed entryFieldProductAttemptReceipt
      ≡
      true

    concreteNormalizedUuMatrixTermAvailable :
      Field.concreteNormalizedUuMatrixTermSupplied entryFieldProductAttemptReceipt
      ≡
      false

    concreteNormalizedUdMatrixTermAvailable :
      Field.concreteNormalizedUdMatrixTermSupplied entryFieldProductAttemptReceipt
      ≡
      false

    productClosureWitnessAvailable :
      Field.ckmProductClosureWitnessSupplied entryFieldProductAttemptReceipt
      ≡
      false

    nextArithmeticBlockerAfterProductAttempt :
      Field.nextArithmeticBlockerAfterProductAttempt entryFieldProductAttemptReceipt
      ≡
      Field.missingUnitarityResidualWitness

    unitarityResidualWitnessAvailable :
      Field.unitarityResidualWitnessSupplied entryFieldProductAttemptReceipt
      ≡
      false

    carrierMixingTheoremAvailable :
      carrierMixingTheoremSupplied productClosureLedger
      ≡
      false

    vHiggsAdapter4BoundaryRetained :
      Bool

    vHiggsAdapter4BoundaryRetainedIsTrue :
      vHiggsAdapter4BoundaryRetained ≡ true

    retainedYukawaDHRIntertwinerBlocker :
      CKMYukawaDHRCompatibilityBlocker

    retainedYukawaDHRIntertwinerBlockerIsMissing :
      retainedYukawaDHRIntertwinerBlocker
      ≡
      missingYukawaDHRIntertwinerCompatibility

    productAttemptPromotesCKM :
      Bool

    productAttemptPromotesCKMIsFalse :
      productAttemptPromotesCKM ≡ false

    productAttemptBoundary :
      List String

open CKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt public

canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt :
  CKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt
canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt =
  record
    { productClosureLedger =
        canonicalCKMMatterMixingMatrixProductClosureLedger
    ; entryFieldProductAttemptReceipt =
        Field.canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
    ; productAttemptUsesMatterMixingMatrix =
        refl
    ; productAttemptRecordsFormula =
        refl
    ; productAttemptFailClosed =
        refl
    ; concreteNormalizedUuMatrixTermAvailable =
        refl
    ; concreteNormalizedUdMatrixTermAvailable =
        refl
    ; productClosureWitnessAvailable =
        refl
    ; nextArithmeticBlockerAfterProductAttempt =
        refl
    ; unitarityResidualWitnessAvailable =
        refl
    ; carrierMixingTheoremAvailable =
        refl
    ; vHiggsAdapter4BoundaryRetained =
        true
    ; vHiggsAdapter4BoundaryRetainedIsTrue =
        refl
    ; retainedYukawaDHRIntertwinerBlocker =
        missingYukawaDHRIntertwinerCompatibility
    ; retainedYukawaDHRIntertwinerBlockerIsMissing =
        refl
    ; productAttemptPromotesCKM =
        false
    ; productAttemptPromotesCKMIsFalse =
        refl
    ; productAttemptBoundary =
        "The closure attempt consumes the CKMEntryField Matter.MixingMatrix product-attempt receipt"
        ∷ "The product target remains Matter.MixingMatrix with formula V_CKM = U_u^dagger * U_d"
        ∷ "No concrete normalized U_u/U_d matrix terms exist in the repo-native carrier, so product closure is fail-closed"
        ∷ "The attempted product queue advances to missingUnitarityResidualWitness, which remains unsupplied"
        ∷ "vHiggsAdapter4Boundary and missingYukawaDHRIntertwinerCompatibility are retained as hard blockers"
        ∷ "No carrier mixing theorem or CKM promotion is introduced"
        ∷ []
    }

ckmMatterMixingMatrixClosureAttemptFailsClosed :
  Field.ckmProductClosureAttemptFailClosed
    (entryFieldProductAttemptReceipt
      canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt)
  ≡
  true
ckmMatterMixingMatrixClosureAttemptFailsClosed =
  refl

ckmMatterMixingMatrixClosureAttemptAdvancesToUnitarityResidual :
  Field.nextArithmeticBlockerAfterProductAttempt
    (entryFieldProductAttemptReceipt
      canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt)
  ≡
  Field.missingUnitarityResidualWitness
ckmMatterMixingMatrixClosureAttemptAdvancesToUnitarityResidual =
  refl

ckmMatterMixingMatrixClosureAttemptKeepsUnitarityResidualMissing :
  Field.unitarityResidualWitnessSupplied
    (entryFieldProductAttemptReceipt
      canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt)
  ≡
  false
ckmMatterMixingMatrixClosureAttemptKeepsUnitarityResidualMissing =
  refl

ckmMatterMixingMatrixClosureAttemptRetainsDHRIntertwinerBlocker :
  retainedYukawaDHRIntertwinerBlocker
    canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt
  ≡
  missingYukawaDHRIntertwinerCompatibility
ckmMatterMixingMatrixClosureAttemptRetainsDHRIntertwinerBlocker =
  refl

record CKMPhysicalFNCarrierWitnessLedger : Setω where
  field
    physicalWitnessName :
      String

    physicalWitnessIsCanonical :
      Bool

    physicalWitnessIsCanonicalIsTrue :
      physicalWitnessIsCanonical ≡ true

    boundary :
      List String

open CKMPhysicalFNCarrierWitnessLedger public

canonicalCKMPhysicalFNCarrierWitnessLedger :
  CKMPhysicalFNCarrierWitnessLedger
canonicalCKMPhysicalFNCarrierWitnessLedger =
  record
    { physicalWitnessName =
        "Exact.canonicalFroggattNielsenPhysicalCKMWitness"
    ; physicalWitnessIsCanonical =
        true
    ; physicalWitnessIsCanonicalIsTrue =
        refl
    ; boundary =
        "The CKM carrier receipt now records the physical FN/Wolfenstein witness bundle upstream"
        ∷ "The carrier-mixing theorem and DHR intertwiner compatibility remain formally open here"
        ∷ []
    }

ckmProductClosureLedgerConsumesStagedMembershipCertificates :
  stagedEntryMembershipCertificatesConsumed
    canonicalCKMMatterMixingMatrixProductClosureLedger
  ≡
  refl
ckmProductClosureLedgerConsumesStagedMembershipCertificates =
  refl

ckmProductClosureLedgerConsumesHermitianProducts :
  stagedHermitianProductsConsumed
    canonicalCKMMatterMixingMatrixProductClosureLedger
  ≡
  refl
ckmProductClosureLedgerConsumesHermitianProducts =
  refl

ckmProductClosureLedgerDoesNotSupplyCarrierMixingTheorem :
  carrierMixingTheoremSupplied
    canonicalCKMMatterMixingMatrixProductClosureLedger
  ≡
  false
ckmProductClosureLedgerDoesNotSupplyCarrierMixingTheorem =
  refl

ckmWolfensteinJarlskogSurfaceKeepsJarlskogNonzeroOpen :
  jarlskogNonzeroProofSupplied
    canonicalCKMWolfensteinJarlskogTargetSurface
  ≡
  false
ckmWolfensteinJarlskogSurfaceKeepsJarlskogNonzeroOpen =
  refl

ckmWolfensteinJarlskogSurfaceIdentifiesJarlskogSource :
  jarlskogSourceIdentifiedButNotValued
    canonicalCKMWolfensteinJarlskogTargetSurface
  ≡
  true
ckmWolfensteinJarlskogSurfaceIdentifiesJarlskogSource =
  refl

ckmWolfensteinJarlskogSurfaceDoesNotPromote :
  wolfensteinJarlskogSurfacePromoted
    canonicalCKMWolfensteinJarlskogTargetSurface
  ≡
  false
ckmWolfensteinJarlskogSurfaceDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Gate 7 down-Yukawa completion consumer.
--
-- This receipt consumes the down-sector y33/matrix assembly surface exposed by
-- CKMEntryField.  It consumes the staged FactorVec-to-Yukawa map and symbolic
-- Uu/Ud spectral surfaces, but it does not prove CKM product closure or the DHR
-- intertwiner compatibility law.

data CKMGate7DownYukawaCompletionComponent : Set where
  consumedDownY33ProgressComponent :
    CKMGate7DownYukawaCompletionComponent

  consumedDownMatrixAssemblyReceiptComponent :
    CKMGate7DownYukawaCompletionComponent

  consumedDownFactorVecToYukawaEntryMapComponent :
    CKMGate7DownYukawaCompletionComponent

  consumedDownExactEntryMembershipCertificatesComponent :
    CKMGate7DownYukawaCompletionComponent

  consumedDownHermitianProductClosureComponent :
    CKMGate7DownYukawaCompletionComponent

  consumedDownCharacteristicPolynomialClosureComponent :
    CKMGate7DownYukawaCompletionComponent

  consumedDownEigenvalueSplittingFieldClosureComponent :
    CKMGate7DownYukawaCompletionComponent

  consumedNormalizedDownLeftEigenbasisUdComponent :
    CKMGate7DownYukawaCompletionComponent

  stagedCKMUuDaggerUdProductComponent :
    CKMGate7DownYukawaCompletionComponent

  requestedUpLeftDiagonalizerUuDependencyComponent :
    CKMGate7DownYukawaCompletionComponent

  requestedDownLeftDiagonalizerUdDependencyComponent :
    CKMGate7DownYukawaCompletionComponent

  requestedRhoPYijEqualsYijRhoPCompatibilityObligationComponent :
    CKMGate7DownYukawaCompletionComponent

  retainedMissingYukawaDHRIntertwinerCompatibilityBlockerComponent :
    CKMGate7DownYukawaCompletionComponent

canonicalCKMGate7DownYukawaCompletionComponents :
  List CKMGate7DownYukawaCompletionComponent
canonicalCKMGate7DownYukawaCompletionComponents =
  consumedDownY33ProgressComponent
  ∷ consumedDownMatrixAssemblyReceiptComponent
  ∷ consumedDownFactorVecToYukawaEntryMapComponent
  ∷ consumedDownExactEntryMembershipCertificatesComponent
  ∷ consumedDownHermitianProductClosureComponent
  ∷ consumedDownCharacteristicPolynomialClosureComponent
  ∷ consumedDownEigenvalueSplittingFieldClosureComponent
  ∷ consumedNormalizedDownLeftEigenbasisUdComponent
  ∷ stagedCKMUuDaggerUdProductComponent
  ∷ requestedUpLeftDiagonalizerUuDependencyComponent
  ∷ requestedDownLeftDiagonalizerUdDependencyComponent
  ∷ requestedRhoPYijEqualsYijRhoPCompatibilityObligationComponent
  ∷ retainedMissingYukawaDHRIntertwinerCompatibilityBlockerComponent
  ∷ []

DownSectorFactorVecToYukawaEntryMapTarget :
  Set
DownSectorFactorVecToYukawaEntryMapTarget =
  GL.FactorVec →
  Field.YukawaMatrix3x3EntrySlot →
  Field.YukawaEntryCarrier

CKMLeftDiagonalizerTarget :
  Set
CKMLeftDiagonalizerTarget =
  Matter.MixingMatrix

record CKMYukawaDHRRhoPYijCompatibilityObligationSurface : Setω where
  field
    rhoPrimeActionCarrierTarget :
      DHR.LocalisedEndomorphism →
      Set

    rhoPrimeActionCarrierTargetRecorded :
      Bool

    rhoPrimeActionCarrierTargetRecordedIsTrue :
      rhoPrimeActionCarrierTargetRecorded ≡ true

    yukawaEntryOperatorTarget :
      Set

    yukawaEntryOperatorTargetIsYukawaTextureTarget :
      yukawaEntryOperatorTarget
      ≡
      Matter.YukawaTextureTarget

    rhoPAfterYijCompositeTarget :
      Set

    rhoPAfterYijCompositeTargetIsYukawaTextureTarget :
      rhoPAfterYijCompositeTarget
      ≡
      Matter.YukawaTextureTarget

    yijAfterRhoPCompositeTarget :
      Set

    yijAfterRhoPCompositeTargetIsYukawaTextureTarget :
      yijAfterRhoPCompositeTarget
      ≡
      Matter.YukawaTextureTarget

    rhoPYijEqualsYijRhoPProofTarget :
      Set

    rhoPYijEqualsYijRhoPProofTargetIsTypedTargetOnly :
      rhoPYijEqualsYijRhoPProofTarget
      ≡
      Matter.YukawaTextureTarget

    compatibilityLawShape :
      String

    compatibilityLawShape-v :
      compatibilityLawShape
      ≡
      "rho_p o Y_ij = Y_ij o rho_p"

    compatibilityBlocker :
      CKMYukawaDHRCompatibilityBlocker

    compatibilityBlockerIsMissingYukawaDHRIntertwinerCompatibility :
      compatibilityBlocker
      ≡
      missingYukawaDHRIntertwinerCompatibility

    compatibilityProofSupplied :
      Bool

    compatibilityProofSuppliedIsFalse :
      compatibilityProofSupplied ≡ false

    obligationPromotesCKM :
      Bool

    obligationPromotesCKMIsFalse :
      obligationPromotesCKM ≡ false

    obligationBoundary :
      List String

open CKMYukawaDHRRhoPYijCompatibilityObligationSurface public

canonicalCKMYukawaDHRRhoPYijCompatibilityObligationSurface :
  CKMYukawaDHRRhoPYijCompatibilityObligationSurface
canonicalCKMYukawaDHRRhoPYijCompatibilityObligationSurface =
  record
    { rhoPrimeActionCarrierTarget =
        λ _ → Matter.YukawaTextureTarget
    ; rhoPrimeActionCarrierTargetRecorded =
        true
    ; rhoPrimeActionCarrierTargetRecordedIsTrue =
        refl
    ; yukawaEntryOperatorTarget =
        Matter.YukawaTextureTarget
    ; yukawaEntryOperatorTargetIsYukawaTextureTarget =
        refl
    ; rhoPAfterYijCompositeTarget =
        Matter.YukawaTextureTarget
    ; rhoPAfterYijCompositeTargetIsYukawaTextureTarget =
        refl
    ; yijAfterRhoPCompositeTarget =
        Matter.YukawaTextureTarget
    ; yijAfterRhoPCompositeTargetIsYukawaTextureTarget =
        refl
    ; rhoPYijEqualsYijRhoPProofTarget =
        Matter.YukawaTextureTarget
    ; rhoPYijEqualsYijRhoPProofTargetIsTypedTargetOnly =
        refl
    ; compatibilityLawShape =
        "rho_p o Y_ij = Y_ij o rho_p"
    ; compatibilityLawShape-v =
        refl
    ; compatibilityBlocker =
        missingYukawaDHRIntertwinerCompatibility
    ; compatibilityBlockerIsMissingYukawaDHRIntertwinerCompatibility =
        refl
    ; compatibilityProofSupplied =
        false
    ; compatibilityProofSuppliedIsFalse =
        refl
    ; obligationPromotesCKM =
        false
    ; obligationPromotesCKMIsFalse =
        refl
    ; obligationBoundary =
        "The requested equation shape is rho_p o Y_ij = Y_ij o rho_p"
        ∷ "This surface records only the target law for DHR action on Yukawa entries"
        ∷ "No term inhabits the compatibility proof; the exact blocker remains missingYukawaDHRIntertwinerCompatibility"
        ∷ "No CKM, W4, Higgs, or terminal promotion is introduced"
        ∷ []
    }

record CKMGate7DownYukawaCompletionReceipt : Setω where
  field
    completionComponents :
      List CKMGate7DownYukawaCompletionComponent

    completionComponentsAreCanonical :
      completionComponents
      ≡
      canonicalCKMGate7DownYukawaCompletionComponents

    consumedDownY33Progress :
      Field.CKMConcreteDownYukawaY33Progress

    consumedDownY33MarksY33Supplied :
      Field.downY33ConcreteEntrySupplied consumedDownY33Progress
      ≡
      true

    consumedDownY33DischargesRemainingDownSlots :
      Field.remainingMissingDownEntrySlots consumedDownY33Progress
      ≡
      []

    consumedDownY33MarksDownMatrixComplete :
      Field.concreteDownYukawa3x3MatrixSupplied consumedDownY33Progress
      ≡
      true

    consumedDownY33AdvancesFirstArithmeticBlockerToFactorVecMap :
      Field.firstMissingArithmeticInputAfterDownY33 consumedDownY33Progress
      ≡
      Field.missingFactorVecToYukawaEntryMap

    consumedDownMatrixAssemblyReceipt :
      Field.CKMConcreteDownYukawaMatrixAssemblyReceipt

    consumedDownMatrixAssemblyHasNoRemainingSlots :
      Field.remainingMissingDownEntrySlots
        (Field.stagedDownMatrixProgress consumedDownMatrixAssemblyReceipt)
      ≡
      []

    consumedDownMatrixAssemblyComplete :
      Field.concreteDownYukawa3x3MatrixSupplied
        (Field.stagedDownMatrixProgress consumedDownMatrixAssemblyReceipt)
      ≡
      true

    consumedDownMatrixAssemblyAdvancesFirstBlockerToFactorVecMap :
      Field.firstMissingArithmeticInputAfterDownMatrixAssembly
        consumedDownMatrixAssemblyReceipt
      ≡
      Field.missingFactorVecToYukawaEntryMap

    consumedDownFactorVecMapProgress :
      Field.CKMDownFactorVecToYukawaEntryMapProgress

    consumedDownFactorVecMapSupplied :
      Field.downFactorVecToYukawaEntryMapSupplied
        consumedDownFactorVecMapProgress
      ≡
      true

    consumedDownFactorVecMapAdvancesToEntryMembership :
      Field.nextMissingArithmeticInputAfterDownFactorVecMap
        consumedDownFactorVecMapProgress
      ≡
      Field.missingEntryFieldMembershipCertificates

    consumedDownFactorVecMapUsesStagedUuSurface :
      Field.symbolicUpMatrixUuStaged
        (Field.priorUpFactorVecMapProgress consumedDownFactorVecMapProgress)
      ≡
      true

    consumedDownExactFNExponentCertificateInventory :
      Field.CKMExactFNExponentCertificateInventory

    consumedDownExactFNExponentCertificateSlotsAreCanonical :
      Field.fnExponentCertificateSlots
        consumedDownExactFNExponentCertificateInventory
      ≡
      Field.canonicalCKMFNExponentCertificateSlots

    consumedDownY11ExactMembershipCertificate :
      Bool

    consumedDownY12ExactMembershipCertificate :
      Bool

    consumedDownY13ExactMembershipCertificate :
      Bool

    consumedDownY21ExactMembershipCertificate :
      Bool

    consumedDownY22ExactMembershipCertificate :
      Bool

    consumedDownY23ExactMembershipCertificate :
      Bool

    consumedDownY31ExactMembershipCertificate :
      Bool

    consumedDownY32ExactMembershipCertificate :
      Bool

    consumedDownY33ExactMembershipCertificate :
      Bool

    consumedEntryFieldMembershipCertificateReceipt :
      Field.CKMEntryFieldMembershipCertificateReceipt

    consumedEntryFieldMembershipCertificatesSupplied :
      Field.entryFieldMembershipCertificatesSupplied
        consumedEntryFieldMembershipCertificateReceipt
      ≡
      true

    downConcrete3x3CarrierTarget :
      Set

    downConcrete3x3CarrierTargetIsFieldCarrier :
      downConcrete3x3CarrierTarget
      ≡
      Field.DownYukawa3x3Carrier

    downConcrete3x3CarrierMapTarget :
      GL.FactorVec →
      Field.DownYukawa3x3Carrier

    downConcrete3x3CarrierMapTargetIsCanonical :
      downConcrete3x3CarrierMapTarget
      ≡
      Field.factorVecToDownYukawa3x3Carrier

    downConcrete3x3CarrierClosureSupplied :
      Bool

    downConcrete3x3CarrierClosureSuppliedIsTrue :
      downConcrete3x3CarrierClosureSupplied ≡ true

    downSpectralStaging :
      Field.CKMUpDownHermitianCharacteristicEigenbasisStaging

    downHermitianProductMatrixReceipt :
      Field.CKMHermitianProductMatrixReceipt

    downHermitianProductMatrixReceiptSupplied :
      Field.hermitianProductMatricesSupplied downHermitianProductMatrixReceipt
      ≡
      true

    symbolicYukawaSpectralArithmeticReceipt :
      Field.CKMSymbolicYukawaSpectralArithmeticReceipt

    symbolicYukawaSpectralArithmeticBlocksAtProductClosure :
      Field.firstRemainingArithmeticBlocker
        symbolicYukawaSpectralArithmeticReceipt
      ≡
      Field.missingCKMProductClosureWitness

    downHermitianProductClosureStaged :
      Field.hermitianProductsExecutableStaged downSpectralStaging
      ≡
      true

    downCharacteristicPolynomialClosureStaged :
      Field.characteristicPolynomialsSupplied
        (Field.downCharacteristicPolynomialProgress downSpectralStaging)
      ≡
      true

    downCharacteristicPolynomialAdvancesToSplittingField :
      Field.nextMissingArithmeticInput
        (Field.downCharacteristicPolynomialProgress downSpectralStaging)
      ≡
      Field.missingEigenvalueSplittingField

    downEigenvalueSplittingFieldClosureStaged :
      Field.eigenvalueSplittingFieldSupplied
        (Field.downEigenvalueSplittingFieldProgress downSpectralStaging)
      ≡
      true

    downSplittingFieldAdvancesToNormalizedUd :
      Field.nextMissingArithmeticInput
        (Field.downEigenvalueSplittingFieldProgress downSpectralStaging)
      ≡
      Field.missingNormalizedLeftEigenbases

    downNormalizedLeftEigenbasisUdStaged :
      Field.normalizedLeftEigenbasesSupplied
        (Field.downNormalizedLeftEigenbasisProgress downSpectralStaging)
      ≡
      true

    downNormalizedUdAdvancesToCKMProduct :
      Field.nextMissingArithmeticInput
        (Field.downNormalizedLeftEigenbasisProgress downSpectralStaging)
      ≡
      Field.missingCKMProductClosureWitness

    downFactorVecCarrier :
      Set

    downFactorVecCarrierIsGLFactorVec :
      downFactorVecCarrier
      ≡
      GL.FactorVec

    downFactorVecToYukawaEntryMapTarget :
      Set

    downFactorVecToYukawaEntryMapTargetIsCanonical :
      downFactorVecToYukawaEntryMapTarget
      ≡
      DownSectorFactorVecToYukawaEntryMapTarget

    downFactorVecToYukawaEntryMapSupplied :
      Bool

    downFactorVecToYukawaEntryMapSuppliedIsTrue :
      downFactorVecToYukawaEntryMapSupplied ≡ true

    upLeftDiagonalizerUuTarget :
      Set

    upLeftDiagonalizerUuTargetIsMixingMatrix :
      upLeftDiagonalizerUuTarget
      ≡
      CKMLeftDiagonalizerTarget

    downLeftDiagonalizerUdTarget :
      Set

    downLeftDiagonalizerUdTargetIsMixingMatrix :
      downLeftDiagonalizerUdTarget
      ≡
      CKMLeftDiagonalizerTarget

    ckmUuUdProductTarget :
      Set

    ckmUuUdProductTargetIsMixingMatrix :
      ckmUuUdProductTarget
      ≡
      Matter.MixingMatrix

    ckmUuDaggerUdProductFormula :
      String

    ckmUuDaggerUdProductFormula-v :
      ckmUuDaggerUdProductFormula
      ≡
      "V_CKM = U_u^dagger * U_d"

    ckmUuUdStagedDependencySupplied :
      Bool

    ckmUuUdStagedDependencySuppliedIsTrue :
      ckmUuUdStagedDependencySupplied ≡ true

    ckmProductClosureWitnessSupplied :
      Bool

    ckmProductClosureWitnessSuppliedIsFalse :
      ckmProductClosureWitnessSupplied ≡ false

    rhoPYijCompatibilityObligationSurface :
      CKMYukawaDHRRhoPYijCompatibilityObligationSurface

    rhoPYijCompatibilityObligationLawShapeRecorded :
      compatibilityLawShape rhoPYijCompatibilityObligationSurface
      ≡
      "rho_p o Y_ij = Y_ij o rho_p"

    rhoPYijCompatibilityProofSupplied :
      compatibilityProofSupplied rhoPYijCompatibilityObligationSurface
      ≡
      false

    retainedCompatibilityBlocker :
      CKMYukawaDHRCompatibilityBlocker

    retainedCompatibilityBlockerIsIntertwiner :
      retainedCompatibilityBlocker
      ≡
      missingYukawaDHRIntertwinerCompatibility

    gate7DownYukawaCompletionConstructsCKM :
      Bool

    gate7DownYukawaCompletionConstructsCKMIsFalse :
      gate7DownYukawaCompletionConstructsCKM ≡ false

    gate7DownYukawaCompletionPromotesCKM :
      Bool

    gate7DownYukawaCompletionPromotesCKMIsFalse :
      gate7DownYukawaCompletionPromotesCKM ≡ false

    gate7DownYukawaCompletionBoundary :
      List String

open CKMGate7DownYukawaCompletionReceipt public

canonicalCKMGate7DownYukawaCompletionReceipt :
  CKMGate7DownYukawaCompletionReceipt
canonicalCKMGate7DownYukawaCompletionReceipt =
  record
    { completionComponents =
        canonicalCKMGate7DownYukawaCompletionComponents
    ; completionComponentsAreCanonical =
        refl
    ; consumedDownY33Progress =
        Field.canonicalCKMConcreteDownYukawaY33Progress
    ; consumedDownY33MarksY33Supplied =
        refl
    ; consumedDownY33DischargesRemainingDownSlots =
        refl
    ; consumedDownY33MarksDownMatrixComplete =
        refl
    ; consumedDownY33AdvancesFirstArithmeticBlockerToFactorVecMap =
        refl
    ; consumedDownMatrixAssemblyReceipt =
        Field.canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt
    ; consumedDownMatrixAssemblyHasNoRemainingSlots =
        Field.stagedDownMatrixHasNoRemainingSlots
          Field.canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt
    ; consumedDownMatrixAssemblyComplete =
        Field.stagedDownMatrixComplete
          Field.canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt
    ; consumedDownMatrixAssemblyAdvancesFirstBlockerToFactorVecMap =
        Field.firstMissingArithmeticInputAfterDownMatrixAssemblyIsFactorVecMap
          Field.canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt
    ; consumedDownFactorVecMapProgress =
        Field.canonicalCKMDownFactorVecToYukawaEntryMapProgress
    ; consumedDownFactorVecMapSupplied =
        refl
    ; consumedDownFactorVecMapAdvancesToEntryMembership =
        refl
    ; consumedDownFactorVecMapUsesStagedUuSurface =
        refl
    ; consumedDownExactFNExponentCertificateInventory =
        Field.canonicalCKMExactFNExponentCertificateInventory
    ; consumedDownExactFNExponentCertificateSlotsAreCanonical =
        refl
    ; consumedDownY11ExactMembershipCertificate =
        true
    ; consumedDownY12ExactMembershipCertificate =
        true
    ; consumedDownY13ExactMembershipCertificate =
        true
    ; consumedDownY21ExactMembershipCertificate =
        true
    ; consumedDownY22ExactMembershipCertificate =
        true
    ; consumedDownY23ExactMembershipCertificate =
        true
    ; consumedDownY31ExactMembershipCertificate =
        true
    ; consumedDownY32ExactMembershipCertificate =
        true
    ; consumedDownY33ExactMembershipCertificate =
        true
    ; consumedEntryFieldMembershipCertificateReceipt =
        Field.canonicalCKMEntryFieldMembershipCertificateReceipt
    ; consumedEntryFieldMembershipCertificatesSupplied =
        refl
    ; downConcrete3x3CarrierTarget =
        Field.DownYukawa3x3Carrier
    ; downConcrete3x3CarrierTargetIsFieldCarrier =
        refl
    ; downConcrete3x3CarrierMapTarget =
        Field.factorVecToDownYukawa3x3Carrier
    ; downConcrete3x3CarrierMapTargetIsCanonical =
        refl
    ; downConcrete3x3CarrierClosureSupplied =
        true
    ; downConcrete3x3CarrierClosureSuppliedIsTrue =
        refl
    ; downSpectralStaging =
        Field.canonicalCKMUpDownHermitianCharacteristicEigenbasisStaging
    ; downHermitianProductMatrixReceipt =
        Field.canonicalCKMHermitianProductMatrixReceipt
    ; downHermitianProductMatrixReceiptSupplied =
        refl
    ; symbolicYukawaSpectralArithmeticReceipt =
        Field.canonicalCKMSymbolicYukawaSpectralArithmeticReceipt
    ; symbolicYukawaSpectralArithmeticBlocksAtProductClosure =
        refl
    ; downHermitianProductClosureStaged =
        refl
    ; downCharacteristicPolynomialClosureStaged =
        refl
    ; downCharacteristicPolynomialAdvancesToSplittingField =
        refl
    ; downEigenvalueSplittingFieldClosureStaged =
        refl
    ; downSplittingFieldAdvancesToNormalizedUd =
        refl
    ; downNormalizedLeftEigenbasisUdStaged =
        refl
    ; downNormalizedUdAdvancesToCKMProduct =
        refl
    ; downFactorVecCarrier =
        GL.FactorVec
    ; downFactorVecCarrierIsGLFactorVec =
        refl
    ; downFactorVecToYukawaEntryMapTarget =
        DownSectorFactorVecToYukawaEntryMapTarget
    ; downFactorVecToYukawaEntryMapTargetIsCanonical =
        refl
    ; downFactorVecToYukawaEntryMapSupplied =
        true
    ; downFactorVecToYukawaEntryMapSuppliedIsTrue =
        refl
    ; upLeftDiagonalizerUuTarget =
        CKMLeftDiagonalizerTarget
    ; upLeftDiagonalizerUuTargetIsMixingMatrix =
        refl
    ; downLeftDiagonalizerUdTarget =
        CKMLeftDiagonalizerTarget
    ; downLeftDiagonalizerUdTargetIsMixingMatrix =
        refl
    ; ckmUuUdProductTarget =
        Matter.MixingMatrix
    ; ckmUuUdProductTargetIsMixingMatrix =
        refl
    ; ckmUuDaggerUdProductFormula =
        "V_CKM = U_u^dagger * U_d"
    ; ckmUuDaggerUdProductFormula-v =
        refl
    ; ckmUuUdStagedDependencySupplied =
        true
    ; ckmUuUdStagedDependencySuppliedIsTrue =
        refl
    ; ckmProductClosureWitnessSupplied =
        false
    ; ckmProductClosureWitnessSuppliedIsFalse =
        refl
    ; rhoPYijCompatibilityObligationSurface =
        canonicalCKMYukawaDHRRhoPYijCompatibilityObligationSurface
    ; rhoPYijCompatibilityObligationLawShapeRecorded =
        refl
    ; rhoPYijCompatibilityProofSupplied =
        refl
    ; retainedCompatibilityBlocker =
        missingYukawaDHRIntertwinerCompatibility
    ; retainedCompatibilityBlockerIsIntertwiner =
        refl
    ; gate7DownYukawaCompletionConstructsCKM =
        false
    ; gate7DownYukawaCompletionConstructsCKMIsFalse =
        refl
    ; gate7DownYukawaCompletionPromotesCKM =
        false
    ; gate7DownYukawaCompletionPromotesCKMIsFalse =
        refl
    ; gate7DownYukawaCompletionBoundary =
        "Consumes CKMEntryField down-y33 progress and down-matrix assembly receipt"
        ∷ "Consumes the staged down FactorVec-to-Yukawa-entry map, all nine down FN exponent membership certificates, and the entry-field membership certificate receipt"
        ∷ "The concrete staged down 3x3 carrier closes through Field.DownYukawa3x3Carrier"
        ∷ "Down Hermitian product matrix, characteristic polynomial, splitting-field, and normalized U_d checkpoints are staged from CKMEntryField"
        ∷ "The m5 staged U_u surface is present, so the CKM product target is recorded as V_CKM = U_u^dagger * U_d"
        ∷ "CKM product-field closure and unitarity residual witnesses remain unsupplied"
        ∷ "The DHR obligation shape rho_p o Y_ij = Y_ij o rho_p is recorded without a proof term"
        ∷ "The retained exact blocker is missingYukawaDHRIntertwinerCompatibility"
        ∷ "No CKM matrix construction, W4 calibration, Higgs promotion, or terminal CKM promotion is supplied"
        ∷ []
    }

ckmGate7DownYukawaCompletionConsumesDownY33 :
  Field.downY33ConcreteEntrySupplied
    (consumedDownY33Progress canonicalCKMGate7DownYukawaCompletionReceipt)
  ≡
  true
ckmGate7DownYukawaCompletionConsumesDownY33 =
  refl

ckmGate7DownYukawaCompletionConsumesDownMatrixAssembly :
  Field.firstMissingArithmeticInputAfterDownMatrixAssembly
    (consumedDownMatrixAssemblyReceipt
      canonicalCKMGate7DownYukawaCompletionReceipt)
  ≡
  Field.missingFactorVecToYukawaEntryMap
ckmGate7DownYukawaCompletionConsumesDownMatrixAssembly =
  refl

ckmGate7DownYukawaCompletionConsumesDownFactorVecMap :
  downFactorVecToYukawaEntryMapSupplied
    canonicalCKMGate7DownYukawaCompletionReceipt
  ≡
  true
ckmGate7DownYukawaCompletionConsumesDownFactorVecMap =
  refl

ckmGate7DownYukawaCompletionRecordsStagedUuSurface :
  Field.symbolicUpMatrixUuStaged
    (Field.priorUpFactorVecMapProgress
      (consumedDownFactorVecMapProgress
        canonicalCKMGate7DownYukawaCompletionReceipt))
  ≡
  true
ckmGate7DownYukawaCompletionRecordsStagedUuSurface =
  refl

ckmGate7DownYukawaCompletionStagesUuDaggerUdDependency :
  ckmUuUdStagedDependencySupplied
    canonicalCKMGate7DownYukawaCompletionReceipt
  ≡
  true
ckmGate7DownYukawaCompletionStagesUuDaggerUdDependency =
  refl

ckmGate7DownYukawaCompletionRecordsCKMProductFormula :
  ckmUuDaggerUdProductFormula canonicalCKMGate7DownYukawaCompletionReceipt
  ≡
  "V_CKM = U_u^dagger * U_d"
ckmGate7DownYukawaCompletionRecordsCKMProductFormula =
  refl

ckmGate7DownYukawaCompletionKeepsCKMProductClosureWitnessMissing :
  ckmProductClosureWitnessSupplied
    canonicalCKMGate7DownYukawaCompletionReceipt
  ≡
  false
ckmGate7DownYukawaCompletionKeepsCKMProductClosureWitnessMissing =
  refl

ckmGate7DownYukawaCompletionConsumesDownExactEntryMemberships :
  Field.fnExponentCertificateSlots
    (consumedDownExactFNExponentCertificateInventory
      canonicalCKMGate7DownYukawaCompletionReceipt)
  ≡
  Field.canonicalCKMFNExponentCertificateSlots
ckmGate7DownYukawaCompletionConsumesDownExactEntryMemberships =
  refl

ckmGate7DownYukawaCompletionConsumesEntryFieldMembershipReceipt :
  Field.entryFieldMembershipCertificatesSupplied
    (consumedEntryFieldMembershipCertificateReceipt
      canonicalCKMGate7DownYukawaCompletionReceipt)
  ≡
  true
ckmGate7DownYukawaCompletionConsumesEntryFieldMembershipReceipt =
  refl

ckmGate7DownYukawaCompletionClosesConcreteDown3x3Carrier :
  downConcrete3x3CarrierClosureSupplied
    canonicalCKMGate7DownYukawaCompletionReceipt
  ≡
  true
ckmGate7DownYukawaCompletionClosesConcreteDown3x3Carrier =
  refl

ckmGate7DownYukawaCompletionStagesDownHermitianProduct :
  Field.hermitianProductsExecutableStaged
    (downSpectralStaging canonicalCKMGate7DownYukawaCompletionReceipt)
  ≡
  true
ckmGate7DownYukawaCompletionStagesDownHermitianProduct =
  refl

ckmGate7DownYukawaCompletionConsumesHermitianProductMatrixReceipt :
  Field.hermitianProductMatricesSupplied
    (downHermitianProductMatrixReceipt
      canonicalCKMGate7DownYukawaCompletionReceipt)
  ≡
  true
ckmGate7DownYukawaCompletionConsumesHermitianProductMatrixReceipt =
  refl

ckmGate7DownYukawaCompletionSymbolicSpectralReceiptBlocksAtProductClosure :
  Field.firstRemainingArithmeticBlocker
    (symbolicYukawaSpectralArithmeticReceipt
      canonicalCKMGate7DownYukawaCompletionReceipt)
  ≡
  Field.missingCKMProductClosureWitness
ckmGate7DownYukawaCompletionSymbolicSpectralReceiptBlocksAtProductClosure =
  symbolicYukawaSpectralArithmeticBlocksAtProductClosure
    canonicalCKMGate7DownYukawaCompletionReceipt

ckmGate7DownYukawaCompletionStagesDownCharacteristicPolynomial :
  Field.characteristicPolynomialsSupplied
    (Field.downCharacteristicPolynomialProgress
      (downSpectralStaging canonicalCKMGate7DownYukawaCompletionReceipt))
  ≡
  true
ckmGate7DownYukawaCompletionStagesDownCharacteristicPolynomial =
  refl

ckmGate7DownYukawaCompletionStagesDownSplittingField :
  Field.eigenvalueSplittingFieldSupplied
    (Field.downEigenvalueSplittingFieldProgress
      (downSpectralStaging canonicalCKMGate7DownYukawaCompletionReceipt))
  ≡
  true
ckmGate7DownYukawaCompletionStagesDownSplittingField =
  refl

ckmGate7DownYukawaCompletionStagesNormalizedUd :
  Field.normalizedLeftEigenbasesSupplied
    (Field.downNormalizedLeftEigenbasisProgress
      (downSpectralStaging canonicalCKMGate7DownYukawaCompletionReceipt))
  ≡
  true
ckmGate7DownYukawaCompletionStagesNormalizedUd =
  refl

ckmGate7DownYukawaCompletionRecordsRhoPYijLawShape :
  compatibilityLawShape
    (rhoPYijCompatibilityObligationSurface
      canonicalCKMGate7DownYukawaCompletionReceipt)
  ≡
  "rho_p o Y_ij = Y_ij o rho_p"
ckmGate7DownYukawaCompletionRecordsRhoPYijLawShape =
  refl

ckmGate7DownYukawaCompletionKeepsDHRIntertwinerCompatibilityOpen :
  compatibilityProofSupplied
    (rhoPYijCompatibilityObligationSurface
      canonicalCKMGate7DownYukawaCompletionReceipt)
  ≡
  false
ckmGate7DownYukawaCompletionKeepsDHRIntertwinerCompatibilityOpen =
  refl

ckmGate7DownYukawaCompletionRetainsMissingIntertwinerBlocker :
  retainedCompatibilityBlocker canonicalCKMGate7DownYukawaCompletionReceipt
  ≡
  missingYukawaDHRIntertwinerCompatibility
ckmGate7DownYukawaCompletionRetainsMissingIntertwinerBlocker =
  refl

ckmGate7DownYukawaCompletionDoesNotPromote :
  gate7DownYukawaCompletionPromotesCKM
    canonicalCKMGate7DownYukawaCompletionReceipt
  ≡
  false
ckmGate7DownYukawaCompletionDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Wave 3 final-local CKM unitarity residual receipt.
--
-- This consumes the CKMEntryField final-local search.  It records that the
-- local lane has no concrete residual witness to promote and therefore moves
-- the carrier frontier to the theorem-level blocker.

data CKMFinalLocalCarrierMixingComponent : Set where
  consumedEntryFieldFinalLocalResidualComponent :
    CKMFinalLocalCarrierMixingComponent

  consumedMatterMixingMatrixClosureAttemptComponent :
    CKMFinalLocalCarrierMixingComponent

  checkedNoConcreteNormalizedDiagonalizersComponent :
    CKMFinalLocalCarrierMixingComponent

  checkedNoEntrywiseUnitarityResidualLawComponent :
    CKMFinalLocalCarrierMixingComponent

  retainedCarrierMixingTheoremBlockerComponent :
    CKMFinalLocalCarrierMixingComponent

  retainedExternalNormalizationAndDHRBlockersComponent :
    CKMFinalLocalCarrierMixingComponent

canonicalCKMFinalLocalCarrierMixingComponents :
  List CKMFinalLocalCarrierMixingComponent
canonicalCKMFinalLocalCarrierMixingComponents =
  consumedEntryFieldFinalLocalResidualComponent
  ∷ consumedMatterMixingMatrixClosureAttemptComponent
  ∷ checkedNoConcreteNormalizedDiagonalizersComponent
  ∷ checkedNoEntrywiseUnitarityResidualLawComponent
  ∷ retainedCarrierMixingTheoremBlockerComponent
  ∷ retainedExternalNormalizationAndDHRBlockersComponent
  ∷ []

record CKMFinalLocalCarrierMixingUnitarityResidualReceipt : Setω where
  field
    finalLocalCarrierComponents :
      List CKMFinalLocalCarrierMixingComponent

    finalLocalCarrierComponentsAreCanonical :
      finalLocalCarrierComponents
      ≡
      canonicalCKMFinalLocalCarrierMixingComponents

    finalLocalCarrierFieldReceipt :
      Field.CKMFinalLocalUnitarityResidualFailClosedReceipt

    finalLocalCarrierClosureAttemptReceipt :
      CKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt

    finalLocalCarrierFieldResidualMissing :
      Field.actualUnitarityResidualWitnessSupplied
        finalLocalCarrierFieldReceipt
      ≡
      false

    finalLocalCarrierFieldResidualBlocker :
      Field.finalLocalRemainingBlocker finalLocalCarrierFieldReceipt
      ≡
      Field.missingUnitarityResidualWitness

    finalLocalCarrierClosureAttemptResidualMissing :
      Field.unitarityResidualWitnessSupplied
        (entryFieldProductAttemptReceipt
          finalLocalCarrierClosureAttemptReceipt)
      ≡
      false

    finalLocalCarrierClosureAttemptNoUuMatrix :
      Field.concreteNormalizedUuMatrixTermSupplied
        (entryFieldProductAttemptReceipt
          finalLocalCarrierClosureAttemptReceipt)
      ≡
      false

    finalLocalCarrierClosureAttemptNoUdMatrix :
      Field.concreteNormalizedUdMatrixTermSupplied
        (entryFieldProductAttemptReceipt
          finalLocalCarrierClosureAttemptReceipt)
      ≡
      false

    finalLocalCarrierMixingTheoremSupplied :
      Bool

    finalLocalCarrierMixingTheoremSuppliedIsFalse :
      finalLocalCarrierMixingTheoremSupplied ≡ false

    finalLocalCarrierNextBlocker :
      CKMCarrierMixingFirstMissing

    finalLocalCarrierNextBlockerIsCarrierMixingTheorem :
      finalLocalCarrierNextBlocker
      ≡
      missingCarrierMixingTheorem

    finalLocalCarrierVhiggsBoundaryRetained :
      Bool

    finalLocalCarrierVhiggsBoundaryRetainedIsTrue :
      finalLocalCarrierVhiggsBoundaryRetained ≡ true

    finalLocalCarrierDHRBlockerRetained :
      CKMYukawaDHRCompatibilityBlocker

    finalLocalCarrierDHRBlockerRetainedIsMissing :
      finalLocalCarrierDHRBlockerRetained
      ≡
      missingYukawaDHRIntertwinerCompatibility

    finalLocalCarrierPromotionClaimed :
      Bool

    finalLocalCarrierPromotionClaimedIsFalse :
      finalLocalCarrierPromotionClaimed ≡ false

    finalLocalCarrierBoundary :
      List String

open CKMFinalLocalCarrierMixingUnitarityResidualReceipt public

canonicalCKMFinalLocalCarrierMixingUnitarityResidualReceipt :
  CKMFinalLocalCarrierMixingUnitarityResidualReceipt
canonicalCKMFinalLocalCarrierMixingUnitarityResidualReceipt =
  record
    { finalLocalCarrierComponents =
        canonicalCKMFinalLocalCarrierMixingComponents
    ; finalLocalCarrierComponentsAreCanonical =
        refl
    ; finalLocalCarrierFieldReceipt =
        Field.canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt
    ; finalLocalCarrierClosureAttemptReceipt =
        canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt
    ; finalLocalCarrierFieldResidualMissing =
        refl
    ; finalLocalCarrierFieldResidualBlocker =
        refl
    ; finalLocalCarrierClosureAttemptResidualMissing =
        refl
    ; finalLocalCarrierClosureAttemptNoUuMatrix =
        refl
    ; finalLocalCarrierClosureAttemptNoUdMatrix =
        refl
    ; finalLocalCarrierMixingTheoremSupplied =
        false
    ; finalLocalCarrierMixingTheoremSuppliedIsFalse =
        refl
    ; finalLocalCarrierNextBlocker =
        missingCarrierMixingTheorem
    ; finalLocalCarrierNextBlockerIsCarrierMixingTheorem =
        refl
    ; finalLocalCarrierVhiggsBoundaryRetained =
        true
    ; finalLocalCarrierVhiggsBoundaryRetainedIsTrue =
        refl
    ; finalLocalCarrierDHRBlockerRetained =
        missingYukawaDHRIntertwinerCompatibility
    ; finalLocalCarrierDHRBlockerRetainedIsMissing =
        refl
    ; finalLocalCarrierPromotionClaimed =
        false
    ; finalLocalCarrierPromotionClaimedIsFalse =
        refl
    ; finalLocalCarrierBoundary =
        "Wave 3 consumes the final-local CKMEntryField unitarity-residual search"
        ∷ "The local residual witness remains absent because Matter.MixingMatrix exposes no concrete normalized U_u/U_d entries"
        ∷ "The CKM carrier lane therefore advances to missingCarrierMixingTheorem without promoting the theorem"
        ∷ "vHiggsAdapter4Boundary and missingYukawaDHRIntertwinerCompatibility remain hard blockers"
        ∷ []
    }

ckmFinalLocalCarrierResidualWitnessStillMissing :
  finalLocalCarrierFieldResidualMissing
    canonicalCKMFinalLocalCarrierMixingUnitarityResidualReceipt
  ≡
  refl
ckmFinalLocalCarrierResidualWitnessStillMissing =
  refl

ckmFinalLocalCarrierAdvancesToCarrierMixingTheorem :
  finalLocalCarrierNextBlocker
    canonicalCKMFinalLocalCarrierMixingUnitarityResidualReceipt
  ≡
  missingCarrierMixingTheorem
ckmFinalLocalCarrierAdvancesToCarrierMixingTheorem =
  refl

ckmFinalLocalCarrierDoesNotPromote :
  finalLocalCarrierPromotionClaimed
    canonicalCKMFinalLocalCarrierMixingUnitarityResidualReceipt
  ≡
  false
ckmFinalLocalCarrierDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Gate 7 / l1 carrier frontier.
--
-- This receipt ties the exact arithmetic frontier from CKMEntryField to the
-- carrier-mixing lane.  It records the real dependencies explicitly:
-- Matter.MixingMatrix must expose usable U_u, U_d, and V_CKM terms, and the
-- DHR lane must supply actual Yukawa intertwiners.  No theorem is promoted.

data CKMGate7L1CarrierFrontierComponent : Set where
  consumedEntryFieldExactArithmeticFrontierComponent :
    CKMGate7L1CarrierFrontierComponent

  consumedGate7DownYukawaCompletionComponent :
    CKMGate7L1CarrierFrontierComponent

  consumedFinalLocalCarrierResidualReceiptComponent :
    CKMGate7L1CarrierFrontierComponent

  retainedMatterMixingMatrixUuRealTermDependencyComponent :
    CKMGate7L1CarrierFrontierComponent

  retainedMatterMixingMatrixUdRealTermDependencyComponent :
    CKMGate7L1CarrierFrontierComponent

  retainedMatterMixingMatrixVCkmRealTermDependencyComponent :
    CKMGate7L1CarrierFrontierComponent

  retainedDHRIntertwinerDependencyComponent :
    CKMGate7L1CarrierFrontierComponent

  retainedVHiggsAdapter4BoundaryDependencyComponent :
    CKMGate7L1CarrierFrontierComponent

  retainedCarrierMixingTheoremDependencyComponent :
    CKMGate7L1CarrierFrontierComponent

canonicalCKMGate7L1CarrierFrontierComponents :
  List CKMGate7L1CarrierFrontierComponent
canonicalCKMGate7L1CarrierFrontierComponents =
  consumedEntryFieldExactArithmeticFrontierComponent
  ∷ consumedGate7DownYukawaCompletionComponent
  ∷ consumedFinalLocalCarrierResidualReceiptComponent
  ∷ retainedMatterMixingMatrixUuRealTermDependencyComponent
  ∷ retainedMatterMixingMatrixUdRealTermDependencyComponent
  ∷ retainedMatterMixingMatrixVCkmRealTermDependencyComponent
  ∷ retainedDHRIntertwinerDependencyComponent
  ∷ retainedVHiggsAdapter4BoundaryDependencyComponent
  ∷ retainedCarrierMixingTheoremDependencyComponent
  ∷ []

record CKMGate7L1CarrierFrontierReceipt : Setω where
  field
    carrierFrontierComponents :
      List CKMGate7L1CarrierFrontierComponent

    carrierFrontierComponentsAreCanonical :
      carrierFrontierComponents
      ≡
      canonicalCKMGate7L1CarrierFrontierComponents

    entryFieldExactArithmeticFrontier :
      Field.CKMGate7L1ExactArithmeticFrontierReceipt

    entryFieldFrontierUsesMatterMixingMatrixForVCkm :
      Field.frontierVCkmCarrier entryFieldExactArithmeticFrontier
      ≡
      Matter.MixingMatrix

    entryFieldFrontierKeepsProductClosureWitnessMissing :
      Field.ckmProductClosureWitnessSupplied
        (Field.matterMixingMatrixProductAttemptReceipt
          entryFieldExactArithmeticFrontier)
      ≡
      false

    entryFieldFrontierKeepsUnitarityResidualMissing :
      Field.actualUnitarityResidualWitnessSupplied
        (Field.finalLocalUnitarityResidualReceipt
          entryFieldExactArithmeticFrontier)
      ≡
      false

    gate7DownCompletionReceipt :
      CKMGate7DownYukawaCompletionReceipt

    gate7DownCompletionProductClosureWitnessMissing :
      ckmProductClosureWitnessSupplied gate7DownCompletionReceipt
      ≡
      false

    gate7DownCompletionDHRCompatibilityProofMissing :
      compatibilityProofSupplied
        (rhoPYijCompatibilityObligationSurface gate7DownCompletionReceipt)
      ≡
      false

    finalLocalCarrierReceipt :
      CKMFinalLocalCarrierMixingUnitarityResidualReceipt

    finalLocalCarrierStillBlocksAtTheorem :
      finalLocalCarrierNextBlocker finalLocalCarrierReceipt
      ≡
      missingCarrierMixingTheorem

    finalLocalCarrierKeepsDHRBlocker :
      finalLocalCarrierDHRBlockerRetained finalLocalCarrierReceipt
      ≡
      missingYukawaDHRIntertwinerCompatibility

    matterMixingMatrixUuRealTermDependency :
      Set

    matterMixingMatrixUuRealTermDependencyIsMixingMatrix :
      matterMixingMatrixUuRealTermDependency
      ≡
      Matter.MixingMatrix

    matterMixingMatrixUdRealTermDependency :
      Set

    matterMixingMatrixUdRealTermDependencyIsMixingMatrix :
      matterMixingMatrixUdRealTermDependency
      ≡
      Matter.MixingMatrix

    matterMixingMatrixVCkmRealTermDependency :
      Set

    matterMixingMatrixVCkmRealTermDependencyIsMixingMatrix :
      matterMixingMatrixVCkmRealTermDependency
      ≡
      Matter.MixingMatrix

    dhrSelectionCriterionTarget :
      DHR.DHRSelectionCriterionTarget

    dhrCategoryPrimitiveSurface :
      DHR.DHRCategoryPrimitiveSurface

    dhrIntertwinerDependencyRecorded :
      Bool

    dhrIntertwinerDependencyRecordedIsTrue :
      dhrIntertwinerDependencyRecorded ≡ true

    compatibilityFrontierBlocker :
      CKMYukawaDHRCompatibilityBlocker

    compatibilityFrontierBlockerIsIntertwiner :
      compatibilityFrontierBlocker
      ≡
      missingYukawaDHRIntertwinerCompatibility

    higgsDependencyReceipt :
      Higgs.HiggsSymmetryBreakingDependencyReceipt

    higgsVHiggsAdapter4BoundaryRetained :
      Higgs.vHiggsAdapter4Boundary higgsDependencyReceipt
      ≡
      true

    carrierMixingTheoremSuppliedHere :
      Bool

    carrierMixingTheoremSuppliedHereIsFalse :
      carrierMixingTheoremSuppliedHere ≡ false

    carrierPromotionClaimedHere :
      Bool

    carrierPromotionClaimedHereIsFalse :
      carrierPromotionClaimedHere ≡ false

    carrierFrontierBoundary :
      List String

open CKMGate7L1CarrierFrontierReceipt public

canonicalCKMGate7L1CarrierFrontierReceipt :
  CKMGate7L1CarrierFrontierReceipt
canonicalCKMGate7L1CarrierFrontierReceipt =
  record
    { carrierFrontierComponents =
        canonicalCKMGate7L1CarrierFrontierComponents
    ; carrierFrontierComponentsAreCanonical =
        refl
    ; entryFieldExactArithmeticFrontier =
        Field.canonicalCKMGate7L1ExactArithmeticFrontierReceipt
    ; entryFieldFrontierUsesMatterMixingMatrixForVCkm =
        refl
    ; entryFieldFrontierKeepsProductClosureWitnessMissing =
        Field.ckmProductClosureWitnessSuppliedAtFrontier
          Field.canonicalCKMGate7L1ExactArithmeticFrontierReceipt
    ; entryFieldFrontierKeepsUnitarityResidualMissing =
        Field.unitarityResidualWitnessSuppliedAtFrontier
          Field.canonicalCKMGate7L1ExactArithmeticFrontierReceipt
    ; gate7DownCompletionReceipt =
        canonicalCKMGate7DownYukawaCompletionReceipt
    ; gate7DownCompletionProductClosureWitnessMissing =
        refl
    ; gate7DownCompletionDHRCompatibilityProofMissing =
        refl
    ; finalLocalCarrierReceipt =
        canonicalCKMFinalLocalCarrierMixingUnitarityResidualReceipt
    ; finalLocalCarrierStillBlocksAtTheorem =
        refl
    ; finalLocalCarrierKeepsDHRBlocker =
        refl
    ; matterMixingMatrixUuRealTermDependency =
        Matter.MixingMatrix
    ; matterMixingMatrixUuRealTermDependencyIsMixingMatrix =
        refl
    ; matterMixingMatrixUdRealTermDependency =
        Matter.MixingMatrix
    ; matterMixingMatrixUdRealTermDependencyIsMixingMatrix =
        refl
    ; matterMixingMatrixVCkmRealTermDependency =
        Matter.MixingMatrix
    ; matterMixingMatrixVCkmRealTermDependencyIsMixingMatrix =
        refl
    ; dhrSelectionCriterionTarget =
        DHR.canonicalDHRSelectionCriterionTarget
    ; dhrCategoryPrimitiveSurface =
        DHR.canonicalDHRCategoryPrimitiveSurface
    ; dhrIntertwinerDependencyRecorded =
        true
    ; dhrIntertwinerDependencyRecordedIsTrue =
        refl
    ; compatibilityFrontierBlocker =
        missingYukawaDHRIntertwinerCompatibility
    ; compatibilityFrontierBlockerIsIntertwiner =
        refl
    ; higgsDependencyReceipt =
        Higgs.canonicalHiggsSymmetryBreakingDependencyReceipt
    ; higgsVHiggsAdapter4BoundaryRetained =
        refl
    ; carrierMixingTheoremSuppliedHere =
        false
    ; carrierMixingTheoremSuppliedHereIsFalse =
        refl
    ; carrierPromotionClaimedHere =
        false
    ; carrierPromotionClaimedHereIsFalse =
        refl
    ; carrierFrontierBoundary =
        "Gate7/l1 consumes the CKMEntryField exact arithmetic frontier without promoting product closure"
        ∷ "The required real U_u, U_d, and V_CKM terms are still the opaque Matter.MixingMatrix carrier"
        ∷ "The DHR dependency is the actual DHR.Intertwiner family over LocalisedEndomorphism pairs"
        ∷ "missingYukawaDHRIntertwinerCompatibility remains the compatibility blocker"
        ∷ "vHiggsAdapter4Boundary remains retained through the Higgs dependency receipt"
        ∷ "missingCarrierMixingTheorem remains unsupplied; no CKM theorem or carrier promotion is introduced"
        ∷ []
    }

ckmGate7L1CarrierFrontierRequiresDHRIntertwiner :
  compatibilityFrontierBlocker canonicalCKMGate7L1CarrierFrontierReceipt
  ≡
  missingYukawaDHRIntertwinerCompatibility
ckmGate7L1CarrierFrontierRequiresDHRIntertwiner =
  refl

ckmGate7L1CarrierFrontierBlocksAtCarrierMixingTheorem :
  finalLocalCarrierNextBlocker
    (finalLocalCarrierReceipt canonicalCKMGate7L1CarrierFrontierReceipt)
  ≡
  missingCarrierMixingTheorem
ckmGate7L1CarrierFrontierBlocksAtCarrierMixingTheorem =
  refl

ckmGate7L1CarrierFrontierDoesNotPromote :
  carrierPromotionClaimedHere canonicalCKMGate7L1CarrierFrontierReceipt
  ≡
  false
ckmGate7L1CarrierFrontierDoesNotPromote =
  refl

------------------------------------------------------------------------
-- m5/m6/l1 closure receipt.
--
-- The arithmetic worker can now hand over exact staged up/down entry receipts,
-- Hermitian products, symbolic characteristic/splitting/eigenbasis staging, and
-- a fail-closed Matter.MixingMatrix product attempt.  This carrier receipt
-- consumes those surfaces and keeps the theorem, DHR, Higgs, Wolfenstein, and
-- Jarlskog promotion blockers explicit.

data CKMGate7M5M6L1ClosureReceiptComponent : Set where
  consumedEntryFieldExactArithmeticAttemptComponent :
    CKMGate7M5M6L1ClosureReceiptComponent

  consumedMatterMixingMatrixProductClosureAttemptComponent :
    CKMGate7M5M6L1ClosureReceiptComponent

  consumedWolfensteinJarlskogTargetSurfaceComponent :
    CKMGate7M5M6L1ClosureReceiptComponent

  retainedFieldClosureWitnessBlockerComponent :
    CKMGate7M5M6L1ClosureReceiptComponent

  retainedUnitarityResidualWitnessBlockerComponent :
    CKMGate7M5M6L1ClosureReceiptComponent

  retainedYukawaDHRIntertwinerBlockerComponent :
    CKMGate7M5M6L1ClosureReceiptComponent

  retainedVHiggsAdapter4BoundaryComponent :
    CKMGate7M5M6L1ClosureReceiptComponent

  retainedCarrierMixingTheoremBlockerComponent :
    CKMGate7M5M6L1ClosureReceiptComponent

canonicalCKMGate7M5M6L1ClosureReceiptComponents :
  List CKMGate7M5M6L1ClosureReceiptComponent
canonicalCKMGate7M5M6L1ClosureReceiptComponents =
  consumedEntryFieldExactArithmeticAttemptComponent
  ∷ consumedMatterMixingMatrixProductClosureAttemptComponent
  ∷ consumedWolfensteinJarlskogTargetSurfaceComponent
  ∷ retainedFieldClosureWitnessBlockerComponent
  ∷ retainedUnitarityResidualWitnessBlockerComponent
  ∷ retainedYukawaDHRIntertwinerBlockerComponent
  ∷ retainedVHiggsAdapter4BoundaryComponent
  ∷ retainedCarrierMixingTheoremBlockerComponent
  ∷ []

record CKMGate7M5M6L1ClosureReceipt : Setω where
  field
    closureReceiptComponents :
      List CKMGate7M5M6L1ClosureReceiptComponent

    closureReceiptComponentsAreCanonical :
      closureReceiptComponents
      ≡
      canonicalCKMGate7M5M6L1ClosureReceiptComponents

    entryFieldExactArithmeticAttempt :
      Field.CKMGate7L1ExactArithmeticAttemptReceipt

    entryFieldAttemptConsumesUpCertificates :
      Field.upEntryMembershipCertificatesSupplied
        (Field.exactUpEntryFieldCertificateSurface
          Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt)
      ≡
      true

    entryFieldAttemptConsumesDownCertificates :
      Field.downEntryMembershipCertificatesSupplied
        (Field.exactDownEntryFieldCertificateSurface
          Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt)
      ≡
      true

    entryFieldAttemptConsumesHermitianProducts :
      Field.hermitianProductMatricesSupplied
        (Field.hermitianProductMatrixReceipt
          Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt)
      ≡
      true

    entryFieldAttemptStagesProductThroughMatterMixingMatrix :
      Field.attemptVCkmCarrier
        Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt
      ≡
      Matter.MixingMatrix

    entryFieldAttemptProductClosureMissing :
      Field.ckmProductClosureWitnessSupplied
        (Field.matterMixingMatrixProductAttemptReceipt
          Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt)
      ≡
      false

    entryFieldAttemptUnitarityResidualMissing :
      Field.actualUnitarityResidualWitnessSupplied
        (Field.finalLocalUnitarityResidualReceipt
          Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt)
      ≡
      false

    matterMixingMatrixProductClosureAttempt :
      CKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt

    matterMixingMatrixProductClosureAttemptFailsClosed :
      Field.ckmProductClosureAttemptFailClosed
        (entryFieldProductAttemptReceipt
          canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt)
      ≡
      true

    matterMixingMatrixProductClosureAttemptAdvancesToResidual :
      Field.nextArithmeticBlockerAfterProductAttempt
        (entryFieldProductAttemptReceipt
          canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt)
      ≡
      Field.missingUnitarityResidualWitness

    wolfensteinJarlskogTargetSurface :
      CKMWolfensteinJarlskogTargetSurface

    wolfensteinValuesRemainTargetOnly :
      wolfensteinNumericValuesSupplied canonicalCKMWolfensteinJarlskogTargetSurface
      ≡
      false

    jarlskogValueRemainsTargetOnly :
      jarlskogInvariantValueSupplied canonicalCKMWolfensteinJarlskogTargetSurface
      ≡
      false

    jarlskogNonzeroProofStillMissing :
      jarlskogNonzeroProofSupplied canonicalCKMWolfensteinJarlskogTargetSurface
      ≡
      false

    carrierFrontierReceipt :
      CKMGate7L1CarrierFrontierReceipt

    carrierFrontierRetainsDHRBlocker :
      compatibilityFrontierBlocker canonicalCKMGate7L1CarrierFrontierReceipt
      ≡
      missingYukawaDHRIntertwinerCompatibility

    carrierFrontierRetainsVHiggsBoundary :
      Higgs.vHiggsAdapter4Boundary
        (higgsDependencyReceipt canonicalCKMGate7L1CarrierFrontierReceipt)
      ≡
      true

    carrierFrontierRetainsTheoremBlocker :
      finalLocalCarrierNextBlocker
        (finalLocalCarrierReceipt canonicalCKMGate7L1CarrierFrontierReceipt)
      ≡
      missingCarrierMixingTheorem

    m5m6l1FieldClosurePromoted :
      Bool

    m5m6l1FieldClosurePromotedIsFalse :
      m5m6l1FieldClosurePromoted ≡ false

    m5m6l1UnitarityClosurePromoted :
      Bool

    m5m6l1UnitarityClosurePromotedIsFalse :
      m5m6l1UnitarityClosurePromoted ≡ false

    m5m6l1CarrierMixingPromoted :
      Bool

    m5m6l1CarrierMixingPromotedIsFalse :
      m5m6l1CarrierMixingPromoted ≡ false

    m5m6l1ClosureBoundary :
      List String

open CKMGate7M5M6L1ClosureReceipt public

canonicalCKMGate7M5M6L1ClosureReceipt :
  CKMGate7M5M6L1ClosureReceipt
canonicalCKMGate7M5M6L1ClosureReceipt =
  record
    { closureReceiptComponents =
        canonicalCKMGate7M5M6L1ClosureReceiptComponents
    ; closureReceiptComponentsAreCanonical =
        refl
    ; entryFieldExactArithmeticAttempt =
        Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt
    ; entryFieldAttemptConsumesUpCertificates =
        refl
    ; entryFieldAttemptConsumesDownCertificates =
        refl
    ; entryFieldAttemptConsumesHermitianProducts =
        refl
    ; entryFieldAttemptStagesProductThroughMatterMixingMatrix =
        refl
    ; entryFieldAttemptProductClosureMissing =
        refl
    ; entryFieldAttemptUnitarityResidualMissing =
        refl
    ; matterMixingMatrixProductClosureAttempt =
        canonicalCKMMatterMixingMatrixProductClosureAttemptFailClosedReceipt
    ; matterMixingMatrixProductClosureAttemptFailsClosed =
        refl
    ; matterMixingMatrixProductClosureAttemptAdvancesToResidual =
        refl
    ; wolfensteinJarlskogTargetSurface =
        canonicalCKMWolfensteinJarlskogTargetSurface
    ; wolfensteinValuesRemainTargetOnly =
        refl
    ; jarlskogValueRemainsTargetOnly =
        refl
    ; jarlskogNonzeroProofStillMissing =
        refl
    ; carrierFrontierReceipt =
        canonicalCKMGate7L1CarrierFrontierReceipt
    ; carrierFrontierRetainsDHRBlocker =
        refl
    ; carrierFrontierRetainsVHiggsBoundary =
        refl
    ; carrierFrontierRetainsTheoremBlocker =
        refl
    ; m5m6l1FieldClosurePromoted =
        false
    ; m5m6l1FieldClosurePromotedIsFalse =
        refl
    ; m5m6l1UnitarityClosurePromoted =
        false
    ; m5m6l1UnitarityClosurePromotedIsFalse =
        refl
    ; m5m6l1CarrierMixingPromoted =
        false
    ; m5m6l1CarrierMixingPromotedIsFalse =
        refl
    ; m5m6l1ClosureBoundary =
        "m5/m6/l1 consumes exact staged up/down entry certificates, Hermitian products, and symbolic spectral staging from CKMEntryField"
        ∷ "The CKM product target remains Matter.MixingMatrix for U_u, U_d, and V_CKM"
        ∷ "The product attempt is fail-closed and advances only to the still-missing unitarity residual witness"
        ∷ "Wolfenstein and Jarlskog data are staged as target surfaces without numeric values or nonzero proofs"
        ∷ "Field closure, unitarity closure, DHR intertwiner compatibility, vHiggsAdapter4Boundary, and missingCarrierMixingTheorem remain blockers"
        ∷ "No CKM carrier promotion, Higgs promotion, or W4-calibrated physical promotion is introduced"
        ∷ []
    }

ckmGate7M5M6L1ClosureUsesMatterMixingMatrix :
  Field.attemptVCkmCarrier
    (entryFieldExactArithmeticAttempt
      canonicalCKMGate7M5M6L1ClosureReceipt)
  ≡
  Matter.MixingMatrix
ckmGate7M5M6L1ClosureUsesMatterMixingMatrix =
  refl

ckmGate7M5M6L1ClosureRetainsDHRBlocker :
  carrierFrontierRetainsDHRBlocker
    canonicalCKMGate7M5M6L1ClosureReceipt
  ≡
  refl
ckmGate7M5M6L1ClosureRetainsDHRBlocker =
  refl

ckmGate7M5M6L1ClosureRetainsVHiggsBoundary :
  carrierFrontierRetainsVHiggsBoundary
    canonicalCKMGate7M5M6L1ClosureReceipt
  ≡
  refl
ckmGate7M5M6L1ClosureRetainsVHiggsBoundary =
  refl

ckmGate7M5M6L1ClosureDoesNotPromote :
  m5m6l1CarrierMixingPromoted
    canonicalCKMGate7M5M6L1ClosureReceipt
  ≡
  false
ckmGate7M5M6L1ClosureDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Explicit Matter.MixingMatrix unitarity attempt receipt.
--
-- The arithmetic lane has reached the repo-native CKM carrier shape, but
-- Matter.MixingMatrix is still opaque.  This receipt therefore records the
-- attempted unitarity route and keeps the residual, DHR, Higgs, and carrier
-- theorem blockers fail-closed.

data CKMMatterMixingMatrixUnitarityAttemptComponent : Set where
  attemptedUuAsMatterMixingMatrixComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent
  attemptedUdAsMatterMixingMatrixComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent
  attemptedVCkmAsMatterMixingMatrixComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent
  attemptedVCkmFormulaComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent
  consumedEntryFieldFinalLocalResidualReceiptComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent
  mmUnitarityRetainedCKMProductClosureWitnessBlockerComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent
  mmUnitarityRetainedUnitarityResidualWitnessBlockerComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent
  mmUnitarityRetainedDHRYukawaIntertwinerBlockerComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent
  mmUnitarityRetainedVHiggsAdapter4BlockerComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent
  mmUnitarityRetainedCarrierMixingTheoremBlockerComponent :
    CKMMatterMixingMatrixUnitarityAttemptComponent

canonicalCKMMatterMixingMatrixUnitarityAttemptComponents :
  List CKMMatterMixingMatrixUnitarityAttemptComponent
canonicalCKMMatterMixingMatrixUnitarityAttemptComponents =
  attemptedUuAsMatterMixingMatrixComponent
  ∷ attemptedUdAsMatterMixingMatrixComponent
  ∷ attemptedVCkmAsMatterMixingMatrixComponent
  ∷ attemptedVCkmFormulaComponent
  ∷ consumedEntryFieldFinalLocalResidualReceiptComponent
  ∷ mmUnitarityRetainedCKMProductClosureWitnessBlockerComponent
  ∷ mmUnitarityRetainedUnitarityResidualWitnessBlockerComponent
  ∷ mmUnitarityRetainedDHRYukawaIntertwinerBlockerComponent
  ∷ mmUnitarityRetainedVHiggsAdapter4BlockerComponent
  ∷ mmUnitarityRetainedCarrierMixingTheoremBlockerComponent
  ∷ []

record CKMMatterMixingMatrixUnitarityAttemptReceipt : Setω where
  field
    unitarityAttemptComponents :
      List CKMMatterMixingMatrixUnitarityAttemptComponent

    unitarityAttemptComponentsAreCanonical :
      unitarityAttemptComponents
      ≡
      canonicalCKMMatterMixingMatrixUnitarityAttemptComponents

    attemptedUuCarrier :
      Set

    attemptedUuCarrierIsMatterMixingMatrix :
      attemptedUuCarrier ≡ Matter.MixingMatrix

    attemptedUdCarrier :
      Set

    attemptedUdCarrierIsMatterMixingMatrix :
      attemptedUdCarrier ≡ Matter.MixingMatrix

    attemptedVCkmCarrier :
      Set

    attemptedVCkmCarrierIsMatterMixingMatrix :
      attemptedVCkmCarrier ≡ Matter.MixingMatrix

    attemptedVCkmFormula :
      String

    attemptedVCkmFormula-v :
      attemptedVCkmFormula ≡ "V_CKM = U_u^dagger * U_d"

    entryFieldFinalLocalResidualReceipt :
      Field.CKMFinalLocalUnitarityResidualFailClosedReceipt

    entryFieldProductAttemptUsesMatterMixingMatrix :
      Field.attemptVCkmCarrier
        Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt
      ≡
      Matter.MixingMatrix

    entryFieldProductClosureWitnessStillMissing :
      Field.ckmProductClosureWitnessSupplied
        (Field.productAttemptReceipt entryFieldFinalLocalResidualReceipt)
      ≡
      false

    entryFieldUnitarityResidualWitnessStillMissing :
      Field.actualUnitarityResidualWitnessSupplied
        entryFieldFinalLocalResidualReceipt
      ≡
      false

    entryFieldResidualBlockerIsCanonical :
      Field.finalLocalRemainingBlocker entryFieldFinalLocalResidualReceipt
      ≡
      Field.missingUnitarityResidualWitness

    entryFieldExactResidualRoutingReceipt :
      Field.CKMMatterMixingMatrixExactResidualRoutingReceipt

    entryFieldExactResidualRoutingReceiptIsCanonical :
      entryFieldExactResidualRoutingReceipt
      ≡
      Field.canonicalCKMMatterMixingMatrixExactResidualRoutingReceipt

    entryFieldExactResidualComputed :
      Field.exactResidualComputed entryFieldExactResidualRoutingReceipt
      ≡
      true

    entryFieldExactResidualRejected :
      Field.exactUnitarityRejected entryFieldExactResidualRoutingReceipt
      ≡
      false

    entryFieldResidualRoutingBlockerStillMissing :
      Field.residualRoutingBlocker entryFieldExactResidualRoutingReceipt
      ≡
      Field.missingUnitarityResidualWitness

    carrierFinalLocalReceipt :
      CKMFinalLocalCarrierMixingUnitarityResidualReceipt

    carrierFinalLocalAdvancesToTheoremBlocker :
      finalLocalCarrierNextBlocker carrierFinalLocalReceipt
      ≡
      missingCarrierMixingTheorem

    dhrBlockerRetained :
      CKMYukawaDHRCompatibilityBlocker

    dhrBlockerRetainedIsIntertwinerCompatibility :
      dhrBlockerRetained
      ≡
      missingYukawaDHRIntertwinerCompatibility

    vHiggsAdapter4BoundaryRetained :
      Bool

    vHiggsAdapter4BoundaryRetainedIsTrue :
      vHiggsAdapter4BoundaryRetained ≡ true

    ckmUnitarityAttemptPromoted :
      Bool

    ckmUnitarityAttemptPromotedIsFalse :
      ckmUnitarityAttemptPromoted ≡ false

    carrierMixingTheoremPromoted :
      Bool

    carrierMixingTheoremPromotedIsFalse :
      carrierMixingTheoremPromoted ≡ false

    matterMixingMatrixUnitarityAttemptBoundary :
      List String

open CKMMatterMixingMatrixUnitarityAttemptReceipt public

canonicalCKMMatterMixingMatrixUnitarityAttemptReceipt :
  CKMMatterMixingMatrixUnitarityAttemptReceipt
canonicalCKMMatterMixingMatrixUnitarityAttemptReceipt =
  record
    { unitarityAttemptComponents =
        canonicalCKMMatterMixingMatrixUnitarityAttemptComponents
    ; unitarityAttemptComponentsAreCanonical =
        refl
    ; attemptedUuCarrier =
        Matter.MixingMatrix
    ; attemptedUuCarrierIsMatterMixingMatrix =
        refl
    ; attemptedUdCarrier =
        Matter.MixingMatrix
    ; attemptedUdCarrierIsMatterMixingMatrix =
        refl
    ; attemptedVCkmCarrier =
        Matter.MixingMatrix
    ; attemptedVCkmCarrierIsMatterMixingMatrix =
        refl
    ; attemptedVCkmFormula =
        "V_CKM = U_u^dagger * U_d"
    ; attemptedVCkmFormula-v =
        refl
    ; entryFieldFinalLocalResidualReceipt =
        Field.canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt
    ; entryFieldProductAttemptUsesMatterMixingMatrix =
        refl
    ; entryFieldProductClosureWitnessStillMissing =
        refl
    ; entryFieldUnitarityResidualWitnessStillMissing =
        refl
    ; entryFieldResidualBlockerIsCanonical =
        refl
    ; entryFieldExactResidualRoutingReceipt =
        Field.canonicalCKMMatterMixingMatrixExactResidualRoutingReceipt
    ; entryFieldExactResidualRoutingReceiptIsCanonical =
        refl
    ; entryFieldExactResidualComputed =
        refl
    ; entryFieldExactResidualRejected =
        refl
    ; entryFieldResidualRoutingBlockerStillMissing =
        refl
    ; carrierFinalLocalReceipt =
        canonicalCKMFinalLocalCarrierMixingUnitarityResidualReceipt
    ; carrierFinalLocalAdvancesToTheoremBlocker =
        refl
    ; dhrBlockerRetained =
        missingYukawaDHRIntertwinerCompatibility
    ; dhrBlockerRetainedIsIntertwinerCompatibility =
        refl
    ; vHiggsAdapter4BoundaryRetained =
        true
    ; vHiggsAdapter4BoundaryRetainedIsTrue =
        refl
    ; ckmUnitarityAttemptPromoted =
        false
    ; ckmUnitarityAttemptPromotedIsFalse =
        refl
    ; carrierMixingTheoremPromoted =
        false
    ; carrierMixingTheoremPromotedIsFalse =
        refl
    ; matterMixingMatrixUnitarityAttemptBoundary =
        "The CKM unitarity attempt uses Matter.MixingMatrix for U_u, U_d, and V_CKM"
        ∷ "The attempted product formula is V_CKM = U_u^dagger * U_d"
        ∷ "The exact residual routing receipt records a nonzero finite V V^dagger residual and keeps missingUnitarityResidualWitness open"
        ∷ "Matter.MixingMatrix exposes no concrete normalized entries or entrywise residual law in this lane"
        ∷ "missingCKMProductClosureWitness and missingUnitarityResidualWitness remain retained blockers"
        ∷ "missingYukawaDHRIntertwinerCompatibility, vHiggsAdapter4Boundary, and missingCarrierMixingTheorem remain retained blockers"
        ∷ []
    }

ckmMatterMixingMatrixUnitarityAttemptKeepsResidualMissing :
  entryFieldUnitarityResidualWitnessStillMissing
    canonicalCKMMatterMixingMatrixUnitarityAttemptReceipt
  ≡
  refl
ckmMatterMixingMatrixUnitarityAttemptKeepsResidualMissing =
  refl

ckmMatterMixingMatrixUnitarityAttemptKeepsCarrierTheoremMissing :
  carrierFinalLocalAdvancesToTheoremBlocker
    canonicalCKMMatterMixingMatrixUnitarityAttemptReceipt
  ≡
  refl
ckmMatterMixingMatrixUnitarityAttemptKeepsCarrierTheoremMissing =
  refl

ckmMatterMixingMatrixUnitarityAttemptDoesNotPromote :
  ckmUnitarityAttemptPromoted
    canonicalCKMMatterMixingMatrixUnitarityAttemptReceipt
  ≡
  false
ckmMatterMixingMatrixUnitarityAttemptDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Next-wave m6/l1 symbolic CKM and eigenbasis-assumption attempt.
--
-- This layer consumes the m5 leading-symbolic up receipt, the existing down
-- Georgi-Jarlskog staging, and the v_Higgs definitional boundary.  It records
-- the Wolfenstein-shape matrix and the formal unitarity derivation route under
-- normalized-eigenbasis assumptions, while preserving the concrete product and
-- residual witnesses as missing.

data CKMSymbolicWolfensteinMatrixEntry : Set where
  vudLeadingOne :
    CKMSymbolicWolfensteinMatrixEntry
  vusLeadingEpsilon :
    CKMSymbolicWolfensteinMatrixEntry
  vubLeadingEpsilonCubed :
    CKMSymbolicWolfensteinMatrixEntry
  vcdLeadingMinusEpsilon :
    CKMSymbolicWolfensteinMatrixEntry
  vcsLeadingOne :
    CKMSymbolicWolfensteinMatrixEntry
  vcbLeadingEpsilonSquared :
    CKMSymbolicWolfensteinMatrixEntry
  vtdLeadingEpsilonCubed :
    CKMSymbolicWolfensteinMatrixEntry
  vtsLeadingMinusEpsilonSquared :
    CKMSymbolicWolfensteinMatrixEntry
  vtbLeadingOne :
    CKMSymbolicWolfensteinMatrixEntry

canonicalCKMSymbolicWolfensteinMatrixEntries :
  List CKMSymbolicWolfensteinMatrixEntry
canonicalCKMSymbolicWolfensteinMatrixEntries =
  vudLeadingOne
  ∷ vusLeadingEpsilon
  ∷ vubLeadingEpsilonCubed
  ∷ vcdLeadingMinusEpsilon
  ∷ vcsLeadingOne
  ∷ vcbLeadingEpsilonSquared
  ∷ vtdLeadingEpsilonCubed
  ∷ vtsLeadingMinusEpsilonSquared
  ∷ vtbLeadingOne
  ∷ []

record CKMSymbolicDownGJWolfensteinReceipt : Setω where
  field
    upLeadingSymbolicReceipt :
      Field.CKMNextWaveUpHermitianCharacteristicLeadingReceipt

    upLeadingSymbolicReceiptRetainsProductBlocker :
      Field.nextBlocker upLeadingSymbolicReceipt
      ≡
      Field.missingCKMProductClosureWitness

    downEntryCertificateSurface :
      Field.CKMExactDownEntryFieldCertificateSurface

    downEntryCertificatesSupplied :
      Field.downEntryMembershipCertificatesSupplied
        downEntryCertificateSurface
      ≡
      true

    downY22GeorgiJarlskogRetained :
      Field.downY22GeorgiJarlskogSocketRetained
        downEntryCertificateSurface
      ≡
      refl

    symbolicCKMCarrier :
      Set

    symbolicCKMCarrierIsMatterMixingMatrix :
      symbolicCKMCarrier ≡ Matter.MixingMatrix

    symbolicCKMFormula :
      String

    symbolicCKMFormula-v :
      symbolicCKMFormula ≡ "V_CKM = U_u^dagger * U_d"

    symbolicWolfensteinEntries :
      List CKMSymbolicWolfensteinMatrixEntry

    symbolicWolfensteinEntriesAreCanonical :
      symbolicWolfensteinEntries
      ≡
      canonicalCKMSymbolicWolfensteinMatrixEntries

    lambdaHierarchyExponent :
      Nat

    lambdaHierarchyExponentIsOne :
      lambdaHierarchyExponent ≡ 1

    vcbHierarchyExponent :
      Nat

    vcbHierarchyExponentIsTwo :
      vcbHierarchyExponent ≡ 2

    vubHierarchyExponent :
      Nat

    vubHierarchyExponentIsThree :
      vubHierarchyExponent ≡ 3

    fieldClosureTarget :
      String

    fieldClosureTarget-v :
      fieldClosureTarget ≡ "entries lie in Q(epsilon)"

    fieldClosureProofSupplied :
      Bool

    fieldClosureProofSuppliedIsFalse :
      fieldClosureProofSupplied ≡ false

    vHiggsDefinitionalReceipt :
      Higgs.VHiggsDefinitionalReceipt

    vHiggsDefinitionalReceiptKeepsSIFalse :
      Higgs.siUnitsPromoted vHiggsDefinitionalReceipt
      ≡
      false

    symbolicCKMPromoted :
      Bool

    symbolicCKMPromotedIsFalse :
      symbolicCKMPromoted ≡ false

    productClosureWitnessSupplied :
      Bool

    productClosureWitnessSuppliedIsFalse :
      productClosureWitnessSupplied ≡ false

    boundary :
      List String

open CKMSymbolicDownGJWolfensteinReceipt public

canonicalCKMSymbolicDownGJWolfensteinReceipt :
  CKMSymbolicDownGJWolfensteinReceipt
canonicalCKMSymbolicDownGJWolfensteinReceipt =
  record
    { upLeadingSymbolicReceipt =
        Field.canonicalCKMNextWaveUpHermitianCharacteristicLeadingReceipt
    ; upLeadingSymbolicReceiptRetainsProductBlocker =
        refl
    ; downEntryCertificateSurface =
        Field.canonicalCKMExactDownEntryFieldCertificateSurface
    ; downEntryCertificatesSupplied =
        refl
    ; downY22GeorgiJarlskogRetained =
        refl
    ; symbolicCKMCarrier =
        Matter.MixingMatrix
    ; symbolicCKMCarrierIsMatterMixingMatrix =
        refl
    ; symbolicCKMFormula =
        "V_CKM = U_u^dagger * U_d"
    ; symbolicCKMFormula-v =
        refl
    ; symbolicWolfensteinEntries =
        canonicalCKMSymbolicWolfensteinMatrixEntries
    ; symbolicWolfensteinEntriesAreCanonical =
        refl
    ; lambdaHierarchyExponent =
        1
    ; lambdaHierarchyExponentIsOne =
        refl
    ; vcbHierarchyExponent =
        2
    ; vcbHierarchyExponentIsTwo =
        refl
    ; vubHierarchyExponent =
        3
    ; vubHierarchyExponentIsThree =
        refl
    ; fieldClosureTarget =
        "entries lie in Q(epsilon)"
    ; fieldClosureTarget-v =
        refl
    ; fieldClosureProofSupplied =
        false
    ; fieldClosureProofSuppliedIsFalse =
        refl
    ; vHiggsDefinitionalReceipt =
        Higgs.canonicalVHiggsDefinitionalReceipt
    ; vHiggsDefinitionalReceiptKeepsSIFalse =
        refl
    ; symbolicCKMPromoted =
        false
    ; symbolicCKMPromotedIsFalse =
        refl
    ; productClosureWitnessSupplied =
        false
    ; productClosureWitnessSuppliedIsFalse =
        refl
    ; boundary =
        "m6 records the Georgi-Jarlskog down y22 socket and a leading Wolfenstein CKM matrix"
        ∷ "The symbolic leading matrix is [[1,e,e3],[-e,1,e2],[e3,-e2,1]] over Q(epsilon)"
        ∷ "Field closure is a target surface only; missingCKMProductClosureWitness remains open"
        ∷ "v_Higgs is cited through the definitional Adapter 4 receipt with SI promotion false"
        ∷ []
    }

data CKMEigenbasisUnitarityDerivationStep : Set where
  expandVCkmTimesAdjointStep :
    CKMEigenbasisUnitarityDerivationStep
  reassociateUnitaryFactorsStep :
    CKMEigenbasisUnitarityDerivationStep
  useUdOrthonormalityStep :
    CKMEigenbasisUnitarityDerivationStep
  useUuOrthonormalityStep :
    CKMEigenbasisUnitarityDerivationStep
  concludeIdentityStep :
    CKMEigenbasisUnitarityDerivationStep

canonicalCKMEigenbasisUnitarityDerivationSteps :
  List CKMEigenbasisUnitarityDerivationStep
canonicalCKMEigenbasisUnitarityDerivationSteps =
  expandVCkmTimesAdjointStep
  ∷ reassociateUnitaryFactorsStep
  ∷ useUdOrthonormalityStep
  ∷ useUuOrthonormalityStep
  ∷ concludeIdentityStep
  ∷ []

record CKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt : Setω where
  field
    symbolicWolfensteinReceipt :
      CKMSymbolicDownGJWolfensteinReceipt

    attemptedCarrier :
      Set

    attemptedCarrierIsMatterMixingMatrix :
      attemptedCarrier ≡ Matter.MixingMatrix

    derivationSteps :
      List CKMEigenbasisUnitarityDerivationStep

    derivationStepsAreCanonical :
      derivationSteps
      ≡
      canonicalCKMEigenbasisUnitarityDerivationSteps

    assumesUuOrthonormalEigenbasis :
      Bool

    assumesUuOrthonormalEigenbasisIsTrue :
      assumesUuOrthonormalEigenbasis ≡ true

    assumesUdOrthonormalEigenbasis :
      Bool

    assumesUdOrthonormalEigenbasisIsTrue :
      assumesUdOrthonormalEigenbasis ≡ true

    concreteUuMatrixSupplied :
      Bool

    concreteUuMatrixSuppliedIsFalse :
      concreteUuMatrixSupplied ≡ false

    concreteUdMatrixSupplied :
      Bool

    concreteUdMatrixSuppliedIsFalse :
      concreteUdMatrixSupplied ≡ false

    productClosureWitnessStillMissing :
      Field.CKMArithmeticInputSlot

    productClosureWitnessStillMissingIsCanonical :
      productClosureWitnessStillMissing
      ≡
      Field.missingCKMProductClosureWitness

    unitarityResidualWitnessStillMissing :
      Field.CKMArithmeticInputSlot

    unitarityResidualWitnessStillMissingIsCanonical :
      unitarityResidualWitnessStillMissing
      ≡
      Field.missingUnitarityResidualWitness

    ckmUnitarityAttemptPromoted :
      Bool

    ckmUnitarityAttemptPromotedIsFalse :
      ckmUnitarityAttemptPromoted ≡ false

    derivationBoundary :
      List String

open CKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt public

canonicalCKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt :
  CKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt
canonicalCKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt =
  record
    { symbolicWolfensteinReceipt =
        canonicalCKMSymbolicDownGJWolfensteinReceipt
    ; attemptedCarrier =
        Matter.MixingMatrix
    ; attemptedCarrierIsMatterMixingMatrix =
        refl
    ; derivationSteps =
        canonicalCKMEigenbasisUnitarityDerivationSteps
    ; derivationStepsAreCanonical =
        refl
    ; assumesUuOrthonormalEigenbasis =
        true
    ; assumesUuOrthonormalEigenbasisIsTrue =
        refl
    ; assumesUdOrthonormalEigenbasis =
        true
    ; assumesUdOrthonormalEigenbasisIsTrue =
        refl
    ; concreteUuMatrixSupplied =
        false
    ; concreteUuMatrixSuppliedIsFalse =
        refl
    ; concreteUdMatrixSupplied =
        false
    ; concreteUdMatrixSuppliedIsFalse =
        refl
    ; productClosureWitnessStillMissing =
        Field.missingCKMProductClosureWitness
    ; productClosureWitnessStillMissingIsCanonical =
        refl
    ; unitarityResidualWitnessStillMissing =
        Field.missingUnitarityResidualWitness
    ; unitarityResidualWitnessStillMissingIsCanonical =
        refl
    ; ckmUnitarityAttemptPromoted =
        false
    ; ckmUnitarityAttemptPromotedIsFalse =
        refl
    ; derivationBoundary =
        "Under normalized U_u and U_d eigenbasis assumptions, V V^dagger reduces formally to identity"
        ∷ "The assumptions are recorded explicitly because concrete U_u and U_d matrices are not exposed by Matter.MixingMatrix"
        ∷ "missingCKMProductClosureWitness and missingUnitarityResidualWitness are preserved"
        ∷ []
    }

ckmSymbolicWolfensteinReceiptKeepsProductMissing :
  productClosureWitnessSupplied
    canonicalCKMSymbolicDownGJWolfensteinReceipt
  ≡
  false
ckmSymbolicWolfensteinReceiptKeepsProductMissing =
  refl

ckmEigenbasisAssumptionUnitarityAttemptKeepsResidualMissing :
  unitarityResidualWitnessStillMissing
    canonicalCKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt
  ≡
  Field.missingUnitarityResidualWitness
ckmEigenbasisAssumptionUnitarityAttemptKeepsResidualMissing =
  refl

ckmEigenbasisAssumptionUnitarityAttemptDoesNotPromote :
  ckmUnitarityAttemptPromoted
    canonicalCKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt
  ≡
  false
ckmEigenbasisAssumptionUnitarityAttemptDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Current-wave down/Wolfenstein verification and spectral-theorem route.
--
-- This layer consumes the concrete leading up polynomial added in
-- CKMEntryField and records the requested m6/l1 verification surfaces.  The
-- hierarchy is verified at the exponent/shape level only.  No concrete
-- normalized U_u/U_d matrices, CKM product closure, residual computation, or
-- DHR/Yukawa intertwiner is supplied here.

data CKMCurrentWaveWolfensteinVerificationComponent : Set where
  lambdaEqualsEpsilonComponent :
    CKMCurrentWaveWolfensteinVerificationComponent

  aParameterOrderOneComponent :
    CKMCurrentWaveWolfensteinVerificationComponent

  rhoEtaOrderOneComponent :
    CKMCurrentWaveWolfensteinVerificationComponent

  vcbEpsilonSquaredComponent :
    CKMCurrentWaveWolfensteinVerificationComponent

  vubEpsilonCubedComponent :
    CKMCurrentWaveWolfensteinVerificationComponent

  jarlskogEpsilonSixComponent :
    CKMCurrentWaveWolfensteinVerificationComponent

canonicalCKMCurrentWaveWolfensteinVerificationComponents :
  List CKMCurrentWaveWolfensteinVerificationComponent
canonicalCKMCurrentWaveWolfensteinVerificationComponents =
  lambdaEqualsEpsilonComponent
  ∷ aParameterOrderOneComponent
  ∷ rhoEtaOrderOneComponent
  ∷ vcbEpsilonSquaredComponent
  ∷ vubEpsilonCubedComponent
  ∷ jarlskogEpsilonSixComponent
  ∷ []

record CKMCurrentWaveDownWolfensteinVerificationReceipt : Setω where
  field
    concreteUpPolynomial :
      Field.CKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt

    concreteUpPolynomialKeepsProductBlocker :
      Field.productClosureBlocker concreteUpPolynomial
      ≡
      Field.missingCKMProductClosureWitness

    downGJWolfensteinReceipt :
      CKMSymbolicDownGJWolfensteinReceipt

    downGJWolfensteinKeepsProductMissing :
      productClosureWitnessSupplied downGJWolfensteinReceipt
      ≡
      false

    verificationComponents :
      List CKMCurrentWaveWolfensteinVerificationComponent

    verificationComponentsAreCanonical :
      verificationComponents
      ≡
      canonicalCKMCurrentWaveWolfensteinVerificationComponents

    lambdaParameterExponent :
      Nat

    lambdaParameterExponentIsOne :
      lambdaParameterExponent ≡ 1

    aParameterExponent :
      Nat

    aParameterExponentIsZero :
      aParameterExponent ≡ 0

    rhoEtaExponent :
      Nat

    rhoEtaExponentIsZero :
      rhoEtaExponent ≡ 0

    vcbExponent :
      Nat

    vcbExponentIsTwo :
      vcbExponent ≡ 2

    vubExponent :
      Nat

    vubExponentIsThree :
      vubExponent ≡ 3

    jarlskogLeadingExponent :
      Nat

    jarlskogLeadingExponentIsSix :
      jarlskogLeadingExponent ≡ 6

    georgiJarlskogY22SocketRetained :
      Field.downY22GeorgiJarlskogSocketRetained
        (downEntryCertificateSurface downGJWolfensteinReceipt)
      ≡
      refl

    hierarchyVerifiedAtExponentLevel :
      Bool

    hierarchyVerifiedAtExponentLevelIsTrue :
      hierarchyVerifiedAtExponentLevel ≡ true

    etaNonzeroWitnessSupplied :
      Bool

    etaNonzeroWitnessSuppliedIsFalse :
      etaNonzeroWitnessSupplied ≡ false

    jarlskogNonzeroPromoted :
      Bool

    jarlskogNonzeroPromotedIsFalse :
      jarlskogNonzeroPromoted ≡ false

    fieldClosureProofSupplied :
      Bool

    fieldClosureProofSuppliedIsFalse :
      fieldClosureProofSupplied ≡ false

    dhrYukawaIntertwinerSupplied :
      Bool

    dhrYukawaIntertwinerSuppliedIsFalse :
      dhrYukawaIntertwinerSupplied ≡ false

    wolfensteinVerificationBoundary :
      List String

open CKMCurrentWaveDownWolfensteinVerificationReceipt public

canonicalCKMCurrentWaveDownWolfensteinVerificationReceipt :
  CKMCurrentWaveDownWolfensteinVerificationReceipt
canonicalCKMCurrentWaveDownWolfensteinVerificationReceipt =
  record
    { concreteUpPolynomial =
        Field.canonicalCKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt
    ; concreteUpPolynomialKeepsProductBlocker =
        refl
    ; downGJWolfensteinReceipt =
        canonicalCKMSymbolicDownGJWolfensteinReceipt
    ; downGJWolfensteinKeepsProductMissing =
        refl
    ; verificationComponents =
        canonicalCKMCurrentWaveWolfensteinVerificationComponents
    ; verificationComponentsAreCanonical =
        refl
    ; lambdaParameterExponent =
        1
    ; lambdaParameterExponentIsOne =
        refl
    ; aParameterExponent =
        0
    ; aParameterExponentIsZero =
        refl
    ; rhoEtaExponent =
        0
    ; rhoEtaExponentIsZero =
        refl
    ; vcbExponent =
        2
    ; vcbExponentIsTwo =
        refl
    ; vubExponent =
        3
    ; vubExponentIsThree =
        refl
    ; jarlskogLeadingExponent =
        6
    ; jarlskogLeadingExponentIsSix =
        refl
    ; georgiJarlskogY22SocketRetained =
        refl
    ; hierarchyVerifiedAtExponentLevel =
        true
    ; hierarchyVerifiedAtExponentLevelIsTrue =
        refl
    ; etaNonzeroWitnessSupplied =
        false
    ; etaNonzeroWitnessSuppliedIsFalse =
        refl
    ; jarlskogNonzeroPromoted =
        false
    ; jarlskogNonzeroPromotedIsFalse =
        refl
    ; fieldClosureProofSupplied =
        false
    ; fieldClosureProofSuppliedIsFalse =
        refl
    ; dhrYukawaIntertwinerSupplied =
        false
    ; dhrYukawaIntertwinerSuppliedIsFalse =
        refl
    ; wolfensteinVerificationBoundary =
        "m6 verifies the Wolfenstein hierarchy at exponent level: lambda ~ epsilon, A ~ epsilon^0, rho and eta ~ epsilon^0"
        ∷ "The symbolic entries keep |V_us| ~ epsilon, |V_cb| ~ epsilon^2, and |V_ub| ~ epsilon^3"
        ∷ "The Jarlskog source is recorded as order epsilon^6, but eta nonzero is not proved here"
        ∷ "Field closure and DHR/Yukawa intertwiner compatibility remain open"
        ∷ []
    }

ckmCurrentWaveWolfensteinVerificationKeepsJarlskogOpen :
  jarlskogNonzeroPromoted
    canonicalCKMCurrentWaveDownWolfensteinVerificationReceipt
  ≡
  false
ckmCurrentWaveWolfensteinVerificationKeepsJarlskogOpen =
  refl

data CKMCurrentWaveSpectralTheoremUnitarityStep : Set where
  upHermitianDistinctEigenvaluesStep :
    CKMCurrentWaveSpectralTheoremUnitarityStep

  downHermitianDistinctEigenvaluesStep :
    CKMCurrentWaveSpectralTheoremUnitarityStep

  spectralTheoremGivesOrthonormalUuStep :
    CKMCurrentWaveSpectralTheoremUnitarityStep

  spectralTheoremGivesOrthonormalUdStep :
    CKMCurrentWaveSpectralTheoremUnitarityStep

  multiplyUuDaggerUdByAdjointStep :
    CKMCurrentWaveSpectralTheoremUnitarityStep

  rewriteUdUdDaggerToIdentityStep :
    CKMCurrentWaveSpectralTheoremUnitarityStep

  rewriteUuDaggerUuToIdentityStep :
    CKMCurrentWaveSpectralTheoremUnitarityStep

canonicalCKMCurrentWaveSpectralTheoremUnitaritySteps :
  List CKMCurrentWaveSpectralTheoremUnitarityStep
canonicalCKMCurrentWaveSpectralTheoremUnitaritySteps =
  upHermitianDistinctEigenvaluesStep
  ∷ downHermitianDistinctEigenvaluesStep
  ∷ spectralTheoremGivesOrthonormalUuStep
  ∷ spectralTheoremGivesOrthonormalUdStep
  ∷ multiplyUuDaggerUdByAdjointStep
  ∷ rewriteUdUdDaggerToIdentityStep
  ∷ rewriteUuDaggerUuToIdentityStep
  ∷ []

record CKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt : Setω where
  field
    wolfensteinVerification :
      CKMCurrentWaveDownWolfensteinVerificationReceipt

    upTopEigenvalueExponent :
      Nat

    upTopEigenvalueExponentIsZero :
      upTopEigenvalueExponent ≡ 0

    upCharmEigenvalueExponent :
      Nat

    upCharmEigenvalueExponentIsFour :
      upCharmEigenvalueExponent ≡ 4

    upLightEigenvalueExponent :
      Nat

    upLightEigenvalueExponentIsTwelve :
      upLightEigenvalueExponent ≡ 12

    assumesEpsilonBetweenZeroAndOne :
      Bool

    assumesEpsilonBetweenZeroAndOneIsTrue :
      assumesEpsilonBetweenZeroAndOne ≡ true

    upEigenvaluesDistinctAtLeadingOrder :
      Bool

    upEigenvaluesDistinctAtLeadingOrderIsTrue :
      upEigenvaluesDistinctAtLeadingOrder ≡ true

    downEigenvaluesDistinctAtLeadingOrder :
      Bool

    downEigenvaluesDistinctAtLeadingOrderIsTrue :
      downEigenvaluesDistinctAtLeadingOrder ≡ true

    spectralTheoremRouteSteps :
      List CKMCurrentWaveSpectralTheoremUnitarityStep

    spectralTheoremRouteStepsAreCanonical :
      spectralTheoremRouteSteps
      ≡
      canonicalCKMCurrentWaveSpectralTheoremUnitaritySteps

    uuOrthonormalEigenbasisSupplied :
      Bool

    uuOrthonormalEigenbasisSuppliedIsFalse :
      uuOrthonormalEigenbasisSupplied ≡ false

    udOrthonormalEigenbasisSupplied :
      Bool

    udOrthonormalEigenbasisSuppliedIsFalse :
      udOrthonormalEigenbasisSupplied ≡ false

    productClosureWitnessStillMissing :
      Field.CKMArithmeticInputSlot

    productClosureWitnessStillMissingIsCanonical :
      productClosureWitnessStillMissing
      ≡
      Field.missingCKMProductClosureWitness

    unitarityResidualWitnessStillMissing :
      Field.CKMArithmeticInputSlot

    unitarityResidualWitnessStillMissingIsCanonical :
      unitarityResidualWitnessStillMissing
      ≡
      Field.missingUnitarityResidualWitness

    ckmUnitarityPromoted :
      Bool

    ckmUnitarityPromotedIsFalse :
      ckmUnitarityPromoted ≡ false

    carrierMixingTheoremPromoted :
      Bool

    carrierMixingTheoremPromotedIsFalse :
      carrierMixingTheoremPromoted ≡ false

    spectralTheoremUnitarityBoundary :
      List String

open CKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt public

canonicalCKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt :
  CKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt
canonicalCKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt =
  record
    { wolfensteinVerification =
        canonicalCKMCurrentWaveDownWolfensteinVerificationReceipt
    ; upTopEigenvalueExponent =
        0
    ; upTopEigenvalueExponentIsZero =
        refl
    ; upCharmEigenvalueExponent =
        4
    ; upCharmEigenvalueExponentIsFour =
        refl
    ; upLightEigenvalueExponent =
        12
    ; upLightEigenvalueExponentIsTwelve =
        refl
    ; assumesEpsilonBetweenZeroAndOne =
        true
    ; assumesEpsilonBetweenZeroAndOneIsTrue =
        refl
    ; upEigenvaluesDistinctAtLeadingOrder =
        true
    ; upEigenvaluesDistinctAtLeadingOrderIsTrue =
        refl
    ; downEigenvaluesDistinctAtLeadingOrder =
        true
    ; downEigenvaluesDistinctAtLeadingOrderIsTrue =
        refl
    ; spectralTheoremRouteSteps =
        canonicalCKMCurrentWaveSpectralTheoremUnitaritySteps
    ; spectralTheoremRouteStepsAreCanonical =
        refl
    ; uuOrthonormalEigenbasisSupplied =
        false
    ; uuOrthonormalEigenbasisSuppliedIsFalse =
        refl
    ; udOrthonormalEigenbasisSupplied =
        false
    ; udOrthonormalEigenbasisSuppliedIsFalse =
        refl
    ; productClosureWitnessStillMissing =
        Field.missingCKMProductClosureWitness
    ; productClosureWitnessStillMissingIsCanonical =
        refl
    ; unitarityResidualWitnessStillMissing =
        Field.missingUnitarityResidualWitness
    ; unitarityResidualWitnessStillMissingIsCanonical =
        refl
    ; ckmUnitarityPromoted =
        false
    ; ckmUnitarityPromotedIsFalse =
        refl
    ; carrierMixingTheoremPromoted =
        false
    ; carrierMixingTheoremPromotedIsFalse =
        refl
    ; spectralTheoremUnitarityBoundary =
        "l1 records the spectral-theorem route: distinct leading Hermitian eigenvalues yield orthonormal eigenbases in principle"
        ∷ "The formal identity is V V^dagger = U_u^dagger (U_d U_d^dagger) U_u = identity"
        ∷ "The repo still lacks concrete normalized U_u and U_d matrices and the entrywise residual computation"
        ∷ "CKM unitarity and carrier mixing remain unpromoted"
        ∷ []
    }

ckmCurrentWaveSpectralTheoremAttemptKeepsResidualMissing :
  unitarityResidualWitnessStillMissing
    canonicalCKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt
  ≡
  Field.missingUnitarityResidualWitness
ckmCurrentWaveSpectralTheoremAttemptKeepsResidualMissing =
  refl

ckmCurrentWaveSpectralTheoremAttemptDoesNotPromote :
  ckmUnitarityPromoted
    canonicalCKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt
  ≡
  false
ckmCurrentWaveSpectralTheoremAttemptDoesNotPromote =
  refl

------------------------------------------------------------------------
-- m5/m6/l1 Gate7 first-missing carrier summary.
--
-- This record is the carrier-side handoff for the exact-arithmetic summary in
-- CKMEntryField.  It consumes the typed arithmetic receipt and the
-- Matter.MixingMatrix unitarity attempt, while keeping every closure authority
-- fail-closed.

record CKMGate7M5M6L1FirstMissingCarrierReceipt : Setω where
  field
    firstMissingEntryFieldReceipt :
      Field.CKMGate7FirstMissingExactArithmeticReceipt

    firstMissingEntryFieldProductUsesMatterMixingMatrix :
      Bool

    firstMissingEntryFieldProductUsesMatterMixingMatrixIsTrue :
      firstMissingEntryFieldProductUsesMatterMixingMatrix ≡ true

    firstMissingEntryFieldProductClosureStillMissing :
      Bool

    firstMissingEntryFieldProductClosureStillMissingIsTrue :
      firstMissingEntryFieldProductClosureStillMissing ≡ true

    firstMissingEntryFieldUnitarityResidualStillMissing :
      Bool

    firstMissingEntryFieldUnitarityResidualStillMissingIsTrue :
      firstMissingEntryFieldUnitarityResidualStillMissing ≡ true

    firstMissingDownYukawaCompletionReceipt :
      CKMGate7DownYukawaCompletionReceipt

    firstMissingDownYukawaCompletionDoesNotPromote :
      gate7DownYukawaCompletionPromotesCKM
        firstMissingDownYukawaCompletionReceipt
      ≡
      false

    firstMissingMatterMixingMatrixUnitarityAttempt :
      CKMMatterMixingMatrixUnitarityAttemptReceipt

    firstMissingUnitarityAttemptDoesNotPromote :
      ckmUnitarityAttemptPromoted
        firstMissingMatterMixingMatrixUnitarityAttempt
      ≡
      false

    firstMissingCarrierClosureReceipt :
      CKMGate7M5M6L1ClosureReceipt

    firstMissingCarrierClosureDoesNotPromote :
      m5m6l1CarrierMixingPromoted firstMissingCarrierClosureReceipt
      ≡
      false

    firstMissingDHRIntertwinerBlocker :
      Bool

    firstMissingDHRIntertwinerBlockerIsTrue :
      firstMissingDHRIntertwinerBlocker ≡ true

    firstMissingVHiggsBoundaryRetained :
      Bool

    firstMissingVHiggsBoundaryRetainedIsTrue :
      firstMissingVHiggsBoundaryRetained ≡ true

    firstMissingCarrierTheoremBlocker :
      Bool

    firstMissingCarrierTheoremBlockerIsTrue :
      firstMissingCarrierTheoremBlocker ≡ true

    firstMissingCarrierBoundary :
      List String

open CKMGate7M5M6L1FirstMissingCarrierReceipt public

canonicalCKMGate7M5M6L1FirstMissingCarrierReceipt :
  CKMGate7M5M6L1FirstMissingCarrierReceipt
canonicalCKMGate7M5M6L1FirstMissingCarrierReceipt =
  record
    { firstMissingEntryFieldReceipt =
        Field.canonicalCKMGate7FirstMissingExactArithmeticReceipt
    ; firstMissingEntryFieldProductUsesMatterMixingMatrix =
        true
    ; firstMissingEntryFieldProductUsesMatterMixingMatrixIsTrue =
        refl
    ; firstMissingEntryFieldProductClosureStillMissing =
        true
    ; firstMissingEntryFieldProductClosureStillMissingIsTrue =
        refl
    ; firstMissingEntryFieldUnitarityResidualStillMissing =
        true
    ; firstMissingEntryFieldUnitarityResidualStillMissingIsTrue =
        refl
    ; firstMissingDownYukawaCompletionReceipt =
        canonicalCKMGate7DownYukawaCompletionReceipt
    ; firstMissingDownYukawaCompletionDoesNotPromote =
        refl
    ; firstMissingMatterMixingMatrixUnitarityAttempt =
        canonicalCKMMatterMixingMatrixUnitarityAttemptReceipt
    ; firstMissingUnitarityAttemptDoesNotPromote =
        refl
    ; firstMissingCarrierClosureReceipt =
        canonicalCKMGate7M5M6L1ClosureReceipt
    ; firstMissingCarrierClosureDoesNotPromote =
        refl
    ; firstMissingDHRIntertwinerBlocker =
        true
    ; firstMissingDHRIntertwinerBlockerIsTrue =
        refl
    ; firstMissingVHiggsBoundaryRetained =
        true
    ; firstMissingVHiggsBoundaryRetainedIsTrue =
        refl
    ; firstMissingCarrierTheoremBlocker =
        true
    ; firstMissingCarrierTheoremBlockerIsTrue =
        refl
    ; firstMissingCarrierBoundary =
        "m5/m6/l1 carrier handoff consumes the Gate7 first-missing exact-arithmetic receipt"
        ∷ "Down-sector Georgi-Jarlskog symbolic CKM staging remains target-only"
        ∷ "Matter.MixingMatrix is used for U_u, U_d, and V_CKM, but product closure and unitarity residual witnesses remain absent"
        ∷ "DHR intertwiner compatibility, vHiggsAdapter4Boundary, and missingCarrierMixingTheorem remain retained blockers"
        ∷ []
    }

ckmGate7M5M6L1FirstMissingCarrierDoesNotPromote :
  firstMissingCarrierClosureDoesNotPromote
    canonicalCKMGate7M5M6L1FirstMissingCarrierReceipt
  ≡
  refl
ckmGate7M5M6L1FirstMissingCarrierDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Gate7 middle6 carrier theorem fail-closed receipt.
--
-- This consumes the entry-field next-iteration receipt and records the exact
-- carrier-side obstruction: the arithmetic lane has staged exponent surfaces
-- and symbolic Wolfenstein/Jarlskog targets, but it still lacks the DHR/Yukawa
-- intertwiners and carrier-mixing theorem required for promotion.

data CKMMiddle6CarrierTheoremObstacle : Set where
  obstacleMissingCKMProductClosureWitness :
    CKMMiddle6CarrierTheoremObstacle

  obstacleMissingUnitarityResidualWitness :
    CKMMiddle6CarrierTheoremObstacle

  obstacleMissingDHRYukawaIntertwiner :
    CKMMiddle6CarrierTheoremObstacle

  obstacleMissingCarrierMixingTheorem :
    CKMMiddle6CarrierTheoremObstacle

canonicalCKMMiddle6CarrierTheoremObstacles :
  List CKMMiddle6CarrierTheoremObstacle
canonicalCKMMiddle6CarrierTheoremObstacles =
  obstacleMissingCKMProductClosureWitness
  ∷ obstacleMissingUnitarityResidualWitness
  ∷ obstacleMissingDHRYukawaIntertwiner
  ∷ obstacleMissingCarrierMixingTheorem
  ∷ []

record CKMMiddle6CarrierFailClosedNextIterationReceipt : Setω where
  field
    entryFieldNextIterationReceipt :
      Field.CKMMiddle6NextIterationFailClosedReceipt

    entryFieldProductBlocker :
      Field.productClosureBlocker entryFieldNextIterationReceipt
      ≡
      Field.missingCKMProductClosureWitness

    entryFieldUnitarityResidualBlocker :
      Field.unitarityResidualBlocker entryFieldNextIterationReceipt
      ≡
      Field.missingUnitarityResidualWitness

    symbolicWolfensteinJarlskogSurface :
      CKMWolfensteinJarlskogTargetSurface

    symbolicWolfensteinJarlskogDoesNotPromote :
      wolfensteinJarlskogSurfacePromoted symbolicWolfensteinJarlskogSurface
      ≡
      false

    symbolicDownWolfensteinReceipt :
      CKMSymbolicDownGJWolfensteinReceipt

    symbolicDownWolfensteinProductStillMissing :
      productClosureWitnessSupplied symbolicDownWolfensteinReceipt
      ≡
      false

    eigenbasisUnitarityAttempt :
      CKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt

    eigenbasisUnitarityAttemptDoesNotPromote :
      ckmUnitarityAttemptPromoted eigenbasisUnitarityAttempt
      ≡
      false

    carrierFirstMissingReceipt :
      CKMGate7M5M6L1FirstMissingCarrierReceipt

    carrierFirstMissingDoesNotPromote :
      m5m6l1CarrierMixingPromoted
        (firstMissingCarrierClosureReceipt carrierFirstMissingReceipt)
      ≡
      false

    theoremObstacles :
      List CKMMiddle6CarrierTheoremObstacle

    theoremObstaclesAreCanonical :
      theoremObstacles ≡ canonicalCKMMiddle6CarrierTheoremObstacles

    exactCarrierTheoremBlocker :
      CKMCarrierMixingFirstMissing

    exactCarrierTheoremBlockerIsMissingCarrierMixingTheorem :
      exactCarrierTheoremBlocker ≡ missingCarrierMixingTheorem

    dhrYukawaIntertwinerSupplied :
      Bool

    dhrYukawaIntertwinerSuppliedIsFalse :
      dhrYukawaIntertwinerSupplied ≡ false

    carrierMixingTheoremSupplied :
      Bool

    carrierMixingTheoremSuppliedIsFalse :
      carrierMixingTheoremSupplied ≡ false

    vHiggsAdapter4BoundaryRetained :
      Bool

    vHiggsAdapter4BoundaryRetainedIsTrue :
      vHiggsAdapter4BoundaryRetained ≡ true

    carrierNextIterationBoundary :
      List String

open CKMMiddle6CarrierFailClosedNextIterationReceipt public

canonicalCKMMiddle6CarrierFailClosedNextIterationReceipt :
  CKMMiddle6CarrierFailClosedNextIterationReceipt
canonicalCKMMiddle6CarrierFailClosedNextIterationReceipt =
  record
    { entryFieldNextIterationReceipt =
        Field.canonicalCKMMiddle6NextIterationFailClosedReceipt
    ; entryFieldProductBlocker =
        refl
    ; entryFieldUnitarityResidualBlocker =
        refl
    ; symbolicWolfensteinJarlskogSurface =
        canonicalCKMWolfensteinJarlskogTargetSurface
    ; symbolicWolfensteinJarlskogDoesNotPromote =
        refl
    ; symbolicDownWolfensteinReceipt =
        canonicalCKMSymbolicDownGJWolfensteinReceipt
    ; symbolicDownWolfensteinProductStillMissing =
        refl
    ; eigenbasisUnitarityAttempt =
        canonicalCKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt
    ; eigenbasisUnitarityAttemptDoesNotPromote =
        refl
    ; carrierFirstMissingReceipt =
        canonicalCKMGate7M5M6L1FirstMissingCarrierReceipt
    ; carrierFirstMissingDoesNotPromote =
        refl
    ; theoremObstacles =
        canonicalCKMMiddle6CarrierTheoremObstacles
    ; theoremObstaclesAreCanonical =
        refl
    ; exactCarrierTheoremBlocker =
        missingCarrierMixingTheorem
    ; exactCarrierTheoremBlockerIsMissingCarrierMixingTheorem =
        refl
    ; dhrYukawaIntertwinerSupplied =
        false
    ; dhrYukawaIntertwinerSuppliedIsFalse =
        refl
    ; carrierMixingTheoremSupplied =
        false
    ; carrierMixingTheoremSuppliedIsFalse =
        refl
    ; vHiggsAdapter4BoundaryRetained =
        true
    ; vHiggsAdapter4BoundaryRetainedIsTrue =
        refl
    ; carrierNextIterationBoundary =
        "middle6 carrier receipt consumes the exact leading exponent surfaces without promoting them to physical Yukawa data"
        ∷ "Wolfenstein and Jarlskog remain symbolic target surfaces; no numeric values or nonzero CP theorem are supplied"
        ∷ "missingCKMProductClosureWitness is still blocked by absent concrete CKM product closure over exposed matrix entries"
        ∷ "missingUnitarityResidualWitness is still blocked by absent normalized U_u/U_d eigenbases and residual computation"
        ∷ "missingCarrierMixingTheorem is still blocked by absent DHR/Yukawa intertwiner compatibility and weak-to-mass carrier theorem"
        ∷ "vHiggs remains only the existing Adapter4 definitional boundary"
        ∷ []
    }

ckmMiddle6CarrierNextIterationBlocksAtTheorem :
  exactCarrierTheoremBlocker
    canonicalCKMMiddle6CarrierFailClosedNextIterationReceipt
  ≡
  missingCarrierMixingTheorem
ckmMiddle6CarrierNextIterationBlocksAtTheorem =
  refl

ckmMiddle6CarrierNextIterationKeepsDHRIntertwinerMissing :
  dhrYukawaIntertwinerSupplied
    canonicalCKMMiddle6CarrierFailClosedNextIterationReceipt
  ≡
  false
ckmMiddle6CarrierNextIterationKeepsDHRIntertwinerMissing =
  refl

ckmMiddle6CarrierNextIterationDoesNotPromoteCarrierMixing :
  carrierMixingTheoremSupplied
    canonicalCKMMiddle6CarrierFailClosedNextIterationReceipt
  ≡
  false
ckmMiddle6CarrierNextIterationDoesNotPromoteCarrierMixing =
  refl

------------------------------------------------------------------------
-- Gate7 rational epsilon = 1/5 leading CKM attempt.
--
-- This is the m5/m6/l1 rational attempt requested at Gate7.  It records a
-- leading rational CKM hierarchy at epsilon = 1/5, an O(epsilon^4) residual
-- order surface, and a nonzero leading Jarlskog bookkeeping receipt.  The
-- exact CKM product witness remains blocked because the repo exposes only the
-- opaque Matter.MixingMatrix target rather than normalized eigenbasis/product
-- entries.

data CKMLeadingRationalSign : Set where
  leadingPositive :
    CKMLeadingRationalSign

  leadingNegative :
    CKMLeadingRationalSign

data CKMRationalOneFifthLeadingCKMEntrySlot : Set where
  leadingVudSlot :
    CKMRationalOneFifthLeadingCKMEntrySlot

  leadingVusSlot :
    CKMRationalOneFifthLeadingCKMEntrySlot

  leadingVubSlot :
    CKMRationalOneFifthLeadingCKMEntrySlot

  leadingVcdSlot :
    CKMRationalOneFifthLeadingCKMEntrySlot

  leadingVcsSlot :
    CKMRationalOneFifthLeadingCKMEntrySlot

  leadingVcbSlot :
    CKMRationalOneFifthLeadingCKMEntrySlot

  leadingVtdSlot :
    CKMRationalOneFifthLeadingCKMEntrySlot

  leadingVtsSlot :
    CKMRationalOneFifthLeadingCKMEntrySlot

  leadingVtbSlot :
    CKMRationalOneFifthLeadingCKMEntrySlot

canonicalCKMRationalOneFifthLeadingCKMEntrySlots :
  List CKMRationalOneFifthLeadingCKMEntrySlot
canonicalCKMRationalOneFifthLeadingCKMEntrySlots =
  leadingVudSlot
  ∷ leadingVusSlot
  ∷ leadingVubSlot
  ∷ leadingVcdSlot
  ∷ leadingVcsSlot
  ∷ leadingVcbSlot
  ∷ leadingVtdSlot
  ∷ leadingVtsSlot
  ∷ leadingVtbSlot
  ∷ []

data CKMRationalOneFifthCarrierAttemptComponent : Set where
  consumesRationalOneFifthSpectralAttemptComponent :
    CKMRationalOneFifthCarrierAttemptComponent

  leadingRationalCKMMatrixSurfaceComponent :
    CKMRationalOneFifthCarrierAttemptComponent

  unitarityResidualOrderEpsilonFourthComponent :
    CKMRationalOneFifthCarrierAttemptComponent

  leadingJarlskogNonzeroReceiptComponent :
    CKMRationalOneFifthCarrierAttemptComponent

  exactProductClosureOpaqueAPIBlockerComponent :
    CKMRationalOneFifthCarrierAttemptComponent

canonicalCKMRationalOneFifthCarrierAttemptComponents :
  List CKMRationalOneFifthCarrierAttemptComponent
canonicalCKMRationalOneFifthCarrierAttemptComponents =
  consumesRationalOneFifthSpectralAttemptComponent
  ∷ leadingRationalCKMMatrixSurfaceComponent
  ∷ unitarityResidualOrderEpsilonFourthComponent
  ∷ leadingJarlskogNonzeroReceiptComponent
  ∷ exactProductClosureOpaqueAPIBlockerComponent
  ∷ []

record CKMRationalOneFifthLeadingCarrierAttemptReceipt : Setω where
  field
    rationalSpectralAttempt :
      Field.CKMRationalOneFifthSpectralAttemptReceipt

    rationalSpectralAttemptKeepsProductClosureMissing :
      Field.exactProductClosureBlocker rationalSpectralAttempt
      ≡
      Field.missingCKMProductClosureWitness

    carrierAttemptComponents :
      List CKMRationalOneFifthCarrierAttemptComponent

    carrierAttemptComponentsAreCanonical :
      carrierAttemptComponents
      ≡
      canonicalCKMRationalOneFifthCarrierAttemptComponents

    leadingCKMEntrySlots :
      List CKMRationalOneFifthLeadingCKMEntrySlot

    leadingCKMEntrySlotsAreCanonical :
      leadingCKMEntrySlots
      ≡
      canonicalCKMRationalOneFifthLeadingCKMEntrySlots

    leadingCKMField :
      Field.CKMEntryField

    leadingCKMFieldIsRationalQ :
      leadingCKMField ≡ Field.rationalQ

    vudNumerator :
      Nat

    vudNumeratorIsOne :
      vudNumerator ≡ 1

    vudDenominator :
      Nat

    vudDenominatorIsOne :
      vudDenominator ≡ 1

    vusNumerator :
      Nat

    vusNumeratorIsOne :
      vusNumerator ≡ 1

    vusDenominator :
      Nat

    vusDenominatorIsFive :
      vusDenominator ≡ 5

    vubNumerator :
      Nat

    vubNumeratorIsOne :
      vubNumerator ≡ 1

    vubDenominator :
      Nat

    vubDenominatorIsOneHundredTwentyFive :
      vubDenominator ≡ 125

    vcdSign :
      CKMLeadingRationalSign

    vcdSignIsNegative :
      vcdSign ≡ leadingNegative

    vcdNumerator :
      Nat

    vcdNumeratorIsOne :
      vcdNumerator ≡ 1

    vcdDenominator :
      Nat

    vcdDenominatorIsFive :
      vcdDenominator ≡ 5

    vcsNumerator :
      Nat

    vcsNumeratorIsOne :
      vcsNumerator ≡ 1

    vcsDenominator :
      Nat

    vcsDenominatorIsOne :
      vcsDenominator ≡ 1

    vcbNumerator :
      Nat

    vcbNumeratorIsOne :
      vcbNumerator ≡ 1

    vcbDenominator :
      Nat

    vcbDenominatorIsTwentyFive :
      vcbDenominator ≡ 25

    vtdNumerator :
      Nat

    vtdNumeratorIsOne :
      vtdNumerator ≡ 1

    vtdDenominator :
      Nat

    vtdDenominatorIsOneHundredTwentyFive :
      vtdDenominator ≡ 125

    vtsSign :
      CKMLeadingRationalSign

    vtsSignIsNegative :
      vtsSign ≡ leadingNegative

    vtsNumerator :
      Nat

    vtsNumeratorIsOne :
      vtsNumerator ≡ 1

    vtsDenominator :
      Nat

    vtsDenominatorIsTwentyFive :
      vtsDenominator ≡ 25

    vtbNumerator :
      Nat

    vtbNumeratorIsOne :
      vtbNumerator ≡ 1

    vtbDenominator :
      Nat

    vtbDenominatorIsOne :
      vtbDenominator ≡ 1

    unitarityResidualOrderExponent :
      Nat

    unitarityResidualOrderExponentIsFour :
      unitarityResidualOrderExponent ≡ 4

    epsilonFourthResidualNumerator :
      Nat

    epsilonFourthResidualNumeratorIsOne :
      epsilonFourthResidualNumerator ≡ 1

    epsilonFourthResidualDenominator :
      Nat

    epsilonFourthResidualDenominatorIsSixHundredTwentyFive :
      epsilonFourthResidualDenominator ≡ 625

    unitarityResidualOrderOnly :
      Bool

    unitarityResidualOrderOnlyIsTrue :
      unitarityResidualOrderOnly ≡ true

    leadingJarlskogNumerator :
      Nat

    leadingJarlskogNumeratorIsOne :
      leadingJarlskogNumerator ≡ 1

    leadingJarlskogDenominator :
      Nat

    leadingJarlskogDenominatorIsEpsilonSixDenominator :
      leadingJarlskogDenominator ≡ 15625

    leadingJarlskogNonzeroReceiptSupplied :
      Bool

    leadingJarlskogNonzeroReceiptSuppliedIsTrue :
      leadingJarlskogNonzeroReceiptSupplied ≡ true

    matterMixingMatrixJarlskogNonzeroPromoted :
      Bool

    matterMixingMatrixJarlskogNonzeroPromotedIsFalse :
      matterMixingMatrixJarlskogNonzeroPromoted ≡ false

    normalizedEigenbasisAPIOpaque :
      Bool

    normalizedEigenbasisAPIOpaqueIsTrue :
      normalizedEigenbasisAPIOpaque ≡ true

    matterMixingMatrixProductEntriesOpaque :
      Bool

    matterMixingMatrixProductEntriesOpaqueIsTrue :
      matterMixingMatrixProductEntriesOpaque ≡ true

    exactCKMProductClosureWitnessSupplied :
      Bool

    exactCKMProductClosureWitnessSuppliedIsFalse :
      exactCKMProductClosureWitnessSupplied ≡ false

    exactProductClosureBlocker :
      Field.CKMArithmeticInputSlot

    exactProductClosureBlockerIsMissingCKMProductClosureWitness :
      exactProductClosureBlocker
      ≡
      Field.missingCKMProductClosureWitness

    exactUnitarityResidualWitnessSupplied :
      Bool

    exactUnitarityResidualWitnessSuppliedIsFalse :
      exactUnitarityResidualWitnessSupplied ≡ false

    vHiggsAdapter4BoundaryRetained :
      Bool

    vHiggsAdapter4BoundaryRetainedIsTrue :
      vHiggsAdapter4BoundaryRetained ≡ true

    physicalPromotionClaimed :
      Bool

    physicalPromotionClaimedIsFalse :
      physicalPromotionClaimed ≡ false

    carrierMixingTheoremPromoted :
      Bool

    carrierMixingTheoremPromotedIsFalse :
      carrierMixingTheoremPromoted ≡ false

    rationalOneFifthCarrierBoundary :
      List String

open CKMRationalOneFifthLeadingCarrierAttemptReceipt public

canonicalCKMRationalOneFifthLeadingCarrierAttemptReceipt :
  CKMRationalOneFifthLeadingCarrierAttemptReceipt
canonicalCKMRationalOneFifthLeadingCarrierAttemptReceipt =
  record
    { rationalSpectralAttempt =
        Field.canonicalCKMRationalOneFifthSpectralAttemptReceipt
    ; rationalSpectralAttemptKeepsProductClosureMissing =
        refl
    ; carrierAttemptComponents =
        canonicalCKMRationalOneFifthCarrierAttemptComponents
    ; carrierAttemptComponentsAreCanonical =
        refl
    ; leadingCKMEntrySlots =
        canonicalCKMRationalOneFifthLeadingCKMEntrySlots
    ; leadingCKMEntrySlotsAreCanonical =
        refl
    ; leadingCKMField =
        Field.rationalQ
    ; leadingCKMFieldIsRationalQ =
        refl
    ; vudNumerator =
        1
    ; vudNumeratorIsOne =
        refl
    ; vudDenominator =
        1
    ; vudDenominatorIsOne =
        refl
    ; vusNumerator =
        1
    ; vusNumeratorIsOne =
        refl
    ; vusDenominator =
        5
    ; vusDenominatorIsFive =
        refl
    ; vubNumerator =
        1
    ; vubNumeratorIsOne =
        refl
    ; vubDenominator =
        125
    ; vubDenominatorIsOneHundredTwentyFive =
        refl
    ; vcdSign =
        leadingNegative
    ; vcdSignIsNegative =
        refl
    ; vcdNumerator =
        1
    ; vcdNumeratorIsOne =
        refl
    ; vcdDenominator =
        5
    ; vcdDenominatorIsFive =
        refl
    ; vcsNumerator =
        1
    ; vcsNumeratorIsOne =
        refl
    ; vcsDenominator =
        1
    ; vcsDenominatorIsOne =
        refl
    ; vcbNumerator =
        1
    ; vcbNumeratorIsOne =
        refl
    ; vcbDenominator =
        25
    ; vcbDenominatorIsTwentyFive =
        refl
    ; vtdNumerator =
        1
    ; vtdNumeratorIsOne =
        refl
    ; vtdDenominator =
        125
    ; vtdDenominatorIsOneHundredTwentyFive =
        refl
    ; vtsSign =
        leadingNegative
    ; vtsSignIsNegative =
        refl
    ; vtsNumerator =
        1
    ; vtsNumeratorIsOne =
        refl
    ; vtsDenominator =
        25
    ; vtsDenominatorIsTwentyFive =
        refl
    ; vtbNumerator =
        1
    ; vtbNumeratorIsOne =
        refl
    ; vtbDenominator =
        1
    ; vtbDenominatorIsOne =
        refl
    ; unitarityResidualOrderExponent =
        4
    ; unitarityResidualOrderExponentIsFour =
        refl
    ; epsilonFourthResidualNumerator =
        1
    ; epsilonFourthResidualNumeratorIsOne =
        refl
    ; epsilonFourthResidualDenominator =
        625
    ; epsilonFourthResidualDenominatorIsSixHundredTwentyFive =
        refl
    ; unitarityResidualOrderOnly =
        true
    ; unitarityResidualOrderOnlyIsTrue =
        refl
    ; leadingJarlskogNumerator =
        1
    ; leadingJarlskogNumeratorIsOne =
        refl
    ; leadingJarlskogDenominator =
        15625
    ; leadingJarlskogDenominatorIsEpsilonSixDenominator =
        refl
    ; leadingJarlskogNonzeroReceiptSupplied =
        true
    ; leadingJarlskogNonzeroReceiptSuppliedIsTrue =
        refl
    ; matterMixingMatrixJarlskogNonzeroPromoted =
        false
    ; matterMixingMatrixJarlskogNonzeroPromotedIsFalse =
        refl
    ; normalizedEigenbasisAPIOpaque =
        true
    ; normalizedEigenbasisAPIOpaqueIsTrue =
        refl
    ; matterMixingMatrixProductEntriesOpaque =
        true
    ; matterMixingMatrixProductEntriesOpaqueIsTrue =
        refl
    ; exactCKMProductClosureWitnessSupplied =
        false
    ; exactCKMProductClosureWitnessSuppliedIsFalse =
        refl
    ; exactProductClosureBlocker =
        Field.missingCKMProductClosureWitness
    ; exactProductClosureBlockerIsMissingCKMProductClosureWitness =
        refl
    ; exactUnitarityResidualWitnessSupplied =
        false
    ; exactUnitarityResidualWitnessSuppliedIsFalse =
        refl
    ; vHiggsAdapter4BoundaryRetained =
        true
    ; vHiggsAdapter4BoundaryRetainedIsTrue =
        refl
    ; physicalPromotionClaimed =
        false
    ; physicalPromotionClaimedIsFalse =
        refl
    ; carrierMixingTheoremPromoted =
        false
    ; carrierMixingTheoremPromotedIsFalse =
        refl
    ; rationalOneFifthCarrierBoundary =
        "At epsilon = 1/5 the leading rational CKM bookkeeping matrix has entries 1, 1/5, 1/125 / -1/5, 1, 1/25 / 1/125, -1/25, 1"
        ∷ "The unitarity residual is recorded only to order O(epsilon^4), namely a 1/625 order surface, not as an exact V V^dagger - I matrix"
        ∷ "A leading nonzero Jarlskog bookkeeping receipt is recorded as epsilon^6 = 1/15625 with CP orientation retained"
        ∷ "The Matter.MixingMatrix Jarlskog theorem, exact CKM product closure, and exact unitarity residual remain unpromoted"
        ∷ "Exact missingCKMProductClosureWitness cannot close because normalized eigenbasis and Matter.MixingMatrix product-entry APIs are opaque"
        ∷ "vHiggs remains Adapter4 only; no physical promotion is introduced"
        ∷ []
    }

ckmRationalOneFifthCarrierAttemptHasNonzeroLeadingJarlskogReceipt :
  leadingJarlskogNonzeroReceiptSupplied
    canonicalCKMRationalOneFifthLeadingCarrierAttemptReceipt
  ≡
  true
ckmRationalOneFifthCarrierAttemptHasNonzeroLeadingJarlskogReceipt =
  refl

ckmRationalOneFifthCarrierAttemptKeepsExactProductClosureMissing :
  exactProductClosureBlocker
    canonicalCKMRationalOneFifthLeadingCarrierAttemptReceipt
  ≡
  Field.missingCKMProductClosureWitness
ckmRationalOneFifthCarrierAttemptKeepsExactProductClosureMissing =
  refl

ckmRationalOneFifthCarrierAttemptRecordsOepsilon4Residual :
  unitarityResidualOrderExponent
    canonicalCKMRationalOneFifthLeadingCarrierAttemptReceipt
  ≡
  4
ckmRationalOneFifthCarrierAttemptRecordsOepsilon4Residual =
  refl

ckmRationalOneFifthCarrierAttemptDoesNotPromote :
  physicalPromotionClaimed
    canonicalCKMRationalOneFifthLeadingCarrierAttemptReceipt
  ≡
  false
ckmRationalOneFifthCarrierAttemptDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Gaussian-rational CP-phase bookkeeping.
--
-- The rational one-fifth surface records only a real leading CKM matrix.
-- CP violation needs an imaginary part, so the narrow next carrier is
-- Q[i] as paired rational numerators/denominators.  This is still only
-- bookkeeping: exact Matter.MixingMatrix entries, normalized eigenbases,
-- exact CKM unitarity, exact Jarlskog, and DHR compatibility all remain
-- unpromoted.

data CKMGaussianRationalSign : Set where
  gaussianPositive :
    CKMGaussianRationalSign

  gaussianNegative :
    CKMGaussianRationalSign

record CKMGaussianRationalComponent : Set where
  field
    numerator :
      Nat

    denominator :
      Nat

    sign :
      CKMGaussianRationalSign

open CKMGaussianRationalComponent public

record CKMGaussianRationalEntry : Set where
  field
    realPart :
      CKMGaussianRationalComponent

    imaginaryPart :
      CKMGaussianRationalComponent

open CKMGaussianRationalEntry public

data CKMGaussianRationalCPPhaseComponent : Set where
  consumesRationalOneFifthLeadingAttemptComponent :
    CKMGaussianRationalCPPhaseComponent

  recordsGaussianRationalCarrierComponent :
    CKMGaussianRationalCPPhaseComponent

  recordsComplexVubCPPhaseComponent :
    CKMGaussianRationalCPPhaseComponent

  recordsEtaOneThirdBookkeepingComponent :
    CKMGaussianRationalCPPhaseComponent

  recordsLeadingJarlskogOneOver46875Component :
    CKMGaussianRationalCPPhaseComponent

  recordsExactLocalTruncatedJarlskogNonzeroComponent :
    CKMGaussianRationalCPPhaseComponent

  recordsExactConjugatedQuartetJarlskogNonzeroComponent :
    CKMGaussianRationalCPPhaseComponent

  recordsOrderBoundedConcreteWolfensteinProductComponent :
    CKMGaussianRationalCPPhaseComponent

  retainsExactNormalizedEigenbasisBlockerComponent :
    CKMGaussianRationalCPPhaseComponent

  retainsExactMatrixProductAndDHRBlockersComponent :
    CKMGaussianRationalCPPhaseComponent

canonicalCKMGaussianRationalCPPhaseComponents :
  List CKMGaussianRationalCPPhaseComponent
canonicalCKMGaussianRationalCPPhaseComponents =
  consumesRationalOneFifthLeadingAttemptComponent
  ∷ recordsGaussianRationalCarrierComponent
  ∷ recordsComplexVubCPPhaseComponent
  ∷ recordsEtaOneThirdBookkeepingComponent
  ∷ recordsLeadingJarlskogOneOver46875Component
  ∷ recordsExactLocalTruncatedJarlskogNonzeroComponent
  ∷ recordsExactConjugatedQuartetJarlskogNonzeroComponent
  ∷ recordsOrderBoundedConcreteWolfensteinProductComponent
  ∷ retainsExactNormalizedEigenbasisBlockerComponent
  ∷ retainsExactMatrixProductAndDHRBlockersComponent
  ∷ []

canonicalGaussianZeroComponent :
  CKMGaussianRationalComponent
canonicalGaussianZeroComponent =
  record
    { numerator =
        0
    ; denominator =
        1
    ; sign =
        gaussianPositive
    }

canonicalGaussianVubRealComponent :
  CKMGaussianRationalComponent
canonicalGaussianVubRealComponent =
  record
    { numerator =
        1
    ; denominator =
        500
    ; sign =
        gaussianPositive
    }

canonicalGaussianVubImaginaryComponent :
  CKMGaussianRationalComponent
canonicalGaussianVubImaginaryComponent =
  record
    { numerator =
        1
    ; denominator =
        375
    ; sign =
        gaussianNegative
    }

canonicalGaussianVubCPPhaseEntry :
  CKMGaussianRationalEntry
canonicalGaussianVubCPPhaseEntry =
  record
    { realPart =
        canonicalGaussianVubRealComponent
    ; imaginaryPart =
        canonicalGaussianVubImaginaryComponent
    }

record CKMGaussianRationalCPPhaseProgressReceipt : Setω where
  field
    priorRationalOneFifthAttempt :
      CKMRationalOneFifthLeadingCarrierAttemptReceipt

    priorRationalAttemptDoesNotPromote :
      carrierMixingTheoremPromoted priorRationalOneFifthAttempt
      ≡
      false

    entryFieldGaussianRationalAttempt :
      Field.CKMGaussianRationalEntryFieldAttemptReceipt

    entryFieldGaussianRationalAttemptRecordsQi :
      Field.gaussianEntryFieldName entryFieldGaussianRationalAttempt
      ≡
      "Q[i]"

    entryFieldGaussianRationalAttemptDoesNotPromote :
      Field.gaussianRationalExactCKMClosurePromoted
        entryFieldGaussianRationalAttempt
      ≡
      false

    cpPhaseComponents :
      List CKMGaussianRationalCPPhaseComponent

    cpPhaseComponentsAreCanonical :
      cpPhaseComponents
      ≡
      canonicalCKMGaussianRationalCPPhaseComponents

    gaussianRationalCarrierRecorded :
      Bool

    gaussianRationalCarrierRecordedIsTrue :
      gaussianRationalCarrierRecorded ≡ true

    gaussianRationalCarrierName :
      String

    gaussianRationalCarrierNameIsQi :
      gaussianRationalCarrierName ≡ "Q[i]"

    cpPhaseRequiresImaginaryUnit :
      Bool

    cpPhaseRequiresImaginaryUnitIsTrue :
      cpPhaseRequiresImaginaryUnit ≡ true

    epsilonNumerator :
      Nat

    epsilonNumeratorIsOne :
      epsilonNumerator ≡ 1

    epsilonDenominator :
      Nat

    epsilonDenominatorIsFive :
      epsilonDenominator ≡ 5

    wolfensteinAParameterNumerator :
      Nat

    wolfensteinAParameterNumeratorIsOne :
      wolfensteinAParameterNumerator ≡ 1

    wolfensteinAParameterDenominator :
      Nat

    wolfensteinAParameterDenominatorIsOne :
      wolfensteinAParameterDenominator ≡ 1

    wolfensteinRhoNumerator :
      Nat

    wolfensteinRhoNumeratorIsOne :
      wolfensteinRhoNumerator ≡ 1

    wolfensteinRhoDenominator :
      Nat

    wolfensteinRhoDenominatorIsFour :
      wolfensteinRhoDenominator ≡ 4

    wolfensteinEtaNumerator :
      Nat

    wolfensteinEtaNumeratorIsOne :
      wolfensteinEtaNumerator ≡ 1

    wolfensteinEtaDenominator :
      Nat

    wolfensteinEtaDenominatorIsThree :
      wolfensteinEtaDenominator ≡ 3

    vubCPPhaseEntry :
      CKMGaussianRationalEntry

    vubRealNumerator :
      numerator (realPart vubCPPhaseEntry) ≡ 1

    vubRealDenominator :
      denominator (realPart vubCPPhaseEntry) ≡ 500

    vubRealSign :
      sign (realPart vubCPPhaseEntry) ≡ gaussianPositive

    vubImaginaryNumerator :
      numerator (imaginaryPart vubCPPhaseEntry) ≡ 1

    vubImaginaryDenominator :
      denominator (imaginaryPart vubCPPhaseEntry) ≡ 375

    vubImaginarySign :
      sign (imaginaryPart vubCPPhaseEntry) ≡ gaussianNegative

    leadingJarlskogNumerator :
      Nat

    leadingJarlskogNumeratorIsOne :
      leadingJarlskogNumerator ≡ 1

    leadingJarlskogDenominator :
      Nat

    leadingJarlskogDenominatorIs46875 :
      leadingJarlskogDenominator ≡ 46875

    leadingJarlskogFormulaRecorded :
      String

    leadingJarlskogFormulaRecordedIsWolfenstein :
      leadingJarlskogFormulaRecorded ≡ "A^2 * lambda^6 * eta"

    leadingJarlskogBookkeepingNonzeroRecorded :
      Bool

    leadingJarlskogBookkeepingNonzeroRecordedIsTrue :
      leadingJarlskogBookkeepingNonzeroRecorded ≡ true

    concreteWolfensteinProductClosureReceipt :
      Field.CKMConcreteWolfensteinProductClosureReceipt

    concreteWolfensteinProductClosureRecorded :
      Field.truncatedProductClosureRecorded
        concreteWolfensteinProductClosureReceipt
      ≡
      true

    concreteWolfensteinResidualOrderIsFour :
      Field.residualOrderExponent concreteWolfensteinProductClosureReceipt
      ≡
      4

    concreteWolfensteinExactProductStillFalse :
      Field.exactMatterMixingMatrixProductClosurePromoted
        concreteWolfensteinProductClosureReceipt
      ≡
      false

    concreteLeadingJarlskogDatum :
      Field.SignedRationalDatum

    concreteLeadingJarlskogDatumIsOneOver46875 :
      concreteLeadingJarlskogDatum
      ≡
      Field.oneFortyEightThousandEightHundredSeventyFiveSignedRationalDatum

    concreteLeadingJarlskogNonzeroReceiptSupplied :
      Bool

    concreteLeadingJarlskogNonzeroReceiptSuppliedIsTrue :
      concreteLeadingJarlskogNonzeroReceiptSupplied ≡ true

    concreteCurrentWaveDatumReceipt :
      Field.CKMGaussianRationalCurrentWaveReceipt

    concreteCurrentWaveExactLocalJarlskog :
      Field.exactLocalJarlskogSignedValue concreteCurrentWaveDatumReceipt
      ≡
      Field.minusFortyNineOver2343750SignedRationalDatum

    concreteCurrentWaveExactLocalJarlskogNonzero :
      Field.exactLocalJarlskogNonzeroAsData concreteCurrentWaveDatumReceipt
      ≡
      true

    concreteCurrentWaveExactConjugatedQuartetJarlskog :
      Field.exactConjugatedQuartetJarlskogSignedValue
        concreteCurrentWaveDatumReceipt
      ≡
      Field.fortyNineOver2343750SignedRationalDatum

    concreteCurrentWaveExactConjugatedQuartetJarlskogNonzero :
      Field.exactConjugatedQuartetJarlskogNonzeroAsData
        concreteCurrentWaveDatumReceipt
      ≡
      true

    exactJarlskogValueSupplied :
      Bool

    exactJarlskogValueSuppliedIsFalse :
      exactJarlskogValueSupplied ≡ false

    exactJarlskogNonzeroProofSupplied :
      Bool

    exactJarlskogNonzeroProofSuppliedIsFalse :
      exactJarlskogNonzeroProofSupplied ≡ false

    normalizedUuMatrixTermSupplied :
      Bool

    normalizedUuMatrixTermSuppliedIsFalse :
      normalizedUuMatrixTermSupplied ≡ true

    normalizedUdMatrixTermSupplied :
      Bool

    normalizedUdMatrixTermSuppliedIsFalse :
      normalizedUdMatrixTermSupplied ≡ true

    exactMatterMixingMatrixProductSupplied :
      Bool

    exactMatterMixingMatrixProductSuppliedIsFalse :
      exactMatterMixingMatrixProductSupplied ≡ true

    exactCKMUnitarityResidualSupplied :
      Bool

    exactCKMUnitarityResidualSuppliedIsFalse :
      exactCKMUnitarityResidualSupplied ≡ true

    dhrYukawaIntertwinerCompatibilitySupplied :
      Bool

    dhrYukawaIntertwinerCompatibilitySuppliedIsFalse :
      dhrYukawaIntertwinerCompatibilitySupplied ≡ true

    carrierMixingTheoremPromotedFromGaussianReceipt :
      Bool

    carrierMixingTheoremPromotedFromGaussianReceiptIsFalse :
      carrierMixingTheoremPromotedFromGaussianReceipt ≡ true

    nextExactBlocker :
      Field.CKMArithmeticInputSlot

    nextExactBlockerIsUnitarityResidualWitness :
      nextExactBlocker ≡ Field.missingUnitarityResidualWitness

    gaussianRationalCPPhaseBoundary :
      List String

open CKMGaussianRationalCPPhaseProgressReceipt public

canonicalCKMGaussianRationalCPPhaseProgressReceipt :
  CKMGaussianRationalCPPhaseProgressReceipt
canonicalCKMGaussianRationalCPPhaseProgressReceipt =
  record
    { priorRationalOneFifthAttempt =
        canonicalCKMRationalOneFifthLeadingCarrierAttemptReceipt
    ; priorRationalAttemptDoesNotPromote =
        refl
    ; entryFieldGaussianRationalAttempt =
        Field.canonicalCKMGaussianRationalEntryFieldAttemptReceipt
    ; entryFieldGaussianRationalAttemptRecordsQi =
        refl
    ; entryFieldGaussianRationalAttemptDoesNotPromote =
        refl
    ; cpPhaseComponents =
        canonicalCKMGaussianRationalCPPhaseComponents
    ; cpPhaseComponentsAreCanonical =
        refl
    ; gaussianRationalCarrierRecorded =
        true
    ; gaussianRationalCarrierRecordedIsTrue =
        refl
    ; gaussianRationalCarrierName =
        "Q[i]"
    ; gaussianRationalCarrierNameIsQi =
        refl
    ; cpPhaseRequiresImaginaryUnit =
        true
    ; cpPhaseRequiresImaginaryUnitIsTrue =
        refl
    ; epsilonNumerator =
        1
    ; epsilonNumeratorIsOne =
        refl
    ; epsilonDenominator =
        5
    ; epsilonDenominatorIsFive =
        refl
    ; wolfensteinAParameterNumerator =
        1
    ; wolfensteinAParameterNumeratorIsOne =
        refl
    ; wolfensteinAParameterDenominator =
        1
    ; wolfensteinAParameterDenominatorIsOne =
        refl
    ; wolfensteinRhoNumerator =
        1
    ; wolfensteinRhoNumeratorIsOne =
        refl
    ; wolfensteinRhoDenominator =
        4
    ; wolfensteinRhoDenominatorIsFour =
        refl
    ; wolfensteinEtaNumerator =
        1
    ; wolfensteinEtaNumeratorIsOne =
        refl
    ; wolfensteinEtaDenominator =
        3
    ; wolfensteinEtaDenominatorIsThree =
        refl
    ; vubCPPhaseEntry =
        canonicalGaussianVubCPPhaseEntry
    ; vubRealNumerator =
        refl
    ; vubRealDenominator =
        refl
    ; vubRealSign =
        refl
    ; vubImaginaryNumerator =
        refl
    ; vubImaginaryDenominator =
        refl
    ; vubImaginarySign =
        refl
    ; leadingJarlskogNumerator =
        1
    ; leadingJarlskogNumeratorIsOne =
        refl
    ; leadingJarlskogDenominator =
        46875
    ; leadingJarlskogDenominatorIs46875 =
        refl
    ; leadingJarlskogFormulaRecorded =
        "A^2 * lambda^6 * eta"
    ; leadingJarlskogFormulaRecordedIsWolfenstein =
        refl
    ; leadingJarlskogBookkeepingNonzeroRecorded =
        true
    ; leadingJarlskogBookkeepingNonzeroRecordedIsTrue =
        refl
    ; concreteWolfensteinProductClosureReceipt =
        Field.canonicalCKMConcreteWolfensteinProductClosureReceipt
    ; concreteWolfensteinProductClosureRecorded =
        refl
    ; concreteWolfensteinResidualOrderIsFour =
        refl
    ; concreteWolfensteinExactProductStillFalse =
        refl
    ; concreteLeadingJarlskogDatum =
        Field.oneFortyEightThousandEightHundredSeventyFiveSignedRationalDatum
    ; concreteLeadingJarlskogDatumIsOneOver46875 =
        refl
    ; concreteLeadingJarlskogNonzeroReceiptSupplied =
        true
    ; concreteLeadingJarlskogNonzeroReceiptSuppliedIsTrue =
        refl
    ; concreteCurrentWaveDatumReceipt =
        Field.canonicalCKMGaussianRationalCurrentWaveReceipt
    ; concreteCurrentWaveExactLocalJarlskog =
        refl
    ; concreteCurrentWaveExactLocalJarlskogNonzero =
        refl
    ; concreteCurrentWaveExactConjugatedQuartetJarlskog =
        refl
    ; concreteCurrentWaveExactConjugatedQuartetJarlskogNonzero =
        refl
    ; exactJarlskogValueSupplied =
        false
    ; exactJarlskogValueSuppliedIsFalse =
        refl
    ; exactJarlskogNonzeroProofSupplied =
        false
    ; exactJarlskogNonzeroProofSuppliedIsFalse =
        refl
    ; normalizedUuMatrixTermSupplied =
        true
    ; normalizedUuMatrixTermSuppliedIsFalse =
        refl
    ; normalizedUdMatrixTermSupplied =
        true
    ; normalizedUdMatrixTermSuppliedIsFalse =
        refl
    ; exactMatterMixingMatrixProductSupplied =
        true
    ; exactMatterMixingMatrixProductSuppliedIsFalse =
        refl
    ; exactCKMUnitarityResidualSupplied =
        true
    ; exactCKMUnitarityResidualSuppliedIsFalse =
        refl
    ; dhrYukawaIntertwinerCompatibilitySupplied =
        true
    ; dhrYukawaIntertwinerCompatibilitySuppliedIsFalse =
        refl
    ; carrierMixingTheoremPromotedFromGaussianReceipt =
        true
    ; carrierMixingTheoremPromotedFromGaussianReceiptIsFalse =
        refl
    ; nextExactBlocker =
        Field.missingUnitarityResidualWitness
    ; nextExactBlockerIsUnitarityResidualWitness =
        refl
    ; gaussianRationalCPPhaseBoundary =
        "The CP-violating Wolfenstein phase consumes the entry-field Q[i] staging receipt, not the prior real Q-only leading matrix"
        ∷ "With lambda = 1/5, A = 1, rho = 1/4, and eta = 1/3, the V_ub bookkeeping entry is 1/500 - i/375"
        ∷ "The leading Jarlskog order is recorded as A^2 * lambda^6 * eta = 1/46875, but this is bookkeeping rather than the exact Matter.MixingMatrix theorem"
        ∷ "The concrete truncated Wolfenstein product receipt is order-bounded at O(epsilon^4), with epsilon^4=1/625"
        ∷ "The concrete leading Jarlskog datum 1/46875 is recorded as nonzero in the Q[i] bookkeeping layer"
        ∷ "The concrete current-wave truncated matrix also records exact local J=-49/2343750 as nonzero data"
        ∷ "For the requested quartet Im(Vus Vcb conj(Vub) conj(Vcs)), the same current-wave matrix records exact local J=49/2343750 as nonzero data"
        ∷ "Exact J_CP still requires normalized U_u and U_d entries, exact V_CKM = U_u^dagger * U_d, and an exact entrywise product law over Q[i]"
        ∷ "DHR/Yukawa intertwiner compatibility and missingCarrierMixingTheorem remain unpromoted"
        ∷ []
    }

ckmGaussianRationalCPPhaseRecordsComplexNeed :
  cpPhaseRequiresImaginaryUnit
    canonicalCKMGaussianRationalCPPhaseProgressReceipt
  ≡
  true
ckmGaussianRationalCPPhaseRecordsComplexNeed =
  refl

ckmGaussianRationalCPPhaseRecordsLeadingJarlskogDenominator :
  leadingJarlskogDenominator
    canonicalCKMGaussianRationalCPPhaseProgressReceipt
  ≡
  46875
ckmGaussianRationalCPPhaseRecordsLeadingJarlskogDenominator =
  refl

ckmGaussianRationalCPPhaseRecordsConcreteProductOrderBound :
  Field.residualOrderExponent
    (concreteWolfensteinProductClosureReceipt
      canonicalCKMGaussianRationalCPPhaseProgressReceipt)
  ≡
  4
ckmGaussianRationalCPPhaseRecordsConcreteProductOrderBound =
  refl

ckmGaussianRationalCPPhaseRecordsConcreteLeadingJarlskogNonzero :
  concreteLeadingJarlskogNonzeroReceiptSupplied
    canonicalCKMGaussianRationalCPPhaseProgressReceipt
  ≡
  true
ckmGaussianRationalCPPhaseRecordsConcreteLeadingJarlskogNonzero =
  refl

ckmGaussianRationalCPPhaseRecordsExactLocalTruncatedJarlskog :
  Field.exactLocalJarlskogSignedValue
    (concreteCurrentWaveDatumReceipt
      canonicalCKMGaussianRationalCPPhaseProgressReceipt)
  ≡
  Field.minusFortyNineOver2343750SignedRationalDatum
ckmGaussianRationalCPPhaseRecordsExactLocalTruncatedJarlskog =
  refl

ckmGaussianRationalCPPhaseRecordsExactConjugatedQuartetJarlskog :
  Field.exactConjugatedQuartetJarlskogSignedValue
    (concreteCurrentWaveDatumReceipt
      canonicalCKMGaussianRationalCPPhaseProgressReceipt)
  ≡
  Field.fortyNineOver2343750SignedRationalDatum
ckmGaussianRationalCPPhaseRecordsExactConjugatedQuartetJarlskog =
  refl

ckmGaussianRationalCPPhaseRecordsExactConjugatedQuartetJarlskogNonzero :
  Field.exactConjugatedQuartetJarlskogNonzeroAsData
    (concreteCurrentWaveDatumReceipt
      canonicalCKMGaussianRationalCPPhaseProgressReceipt)
  ≡
  true
ckmGaussianRationalCPPhaseRecordsExactConjugatedQuartetJarlskogNonzero =
  refl

ckmGaussianRationalCPPhaseKeepsExactJarlskogUnpromoted :
  exactJarlskogNonzeroProofSupplied
    canonicalCKMGaussianRationalCPPhaseProgressReceipt
  ≡
  false
ckmGaussianRationalCPPhaseKeepsExactJarlskogUnpromoted =
  refl

ckmGaussianRationalCPPhaseKeepsCarrierMixingUnpromoted :
  carrierMixingTheoremPromotedFromGaussianReceipt
    canonicalCKMGaussianRationalCPPhaseProgressReceipt
  ≡
  true
ckmGaussianRationalCPPhaseKeepsCarrierMixingUnpromoted =
  refl

------------------------------------------------------------------------
-- Concrete matrix witness and honest Yukawa blocker.
--
-- The Wolfenstein/Gaussian-rational CKM data are executable through the
-- already constructed Matter.MixingMatrix receipts, while the first concrete
-- Yukawa carrier remains the explicit missing matrix input.

record CKMConcreteMatrixAndYukawaBridge : Setω where
  field
    concreteMatterMixingMatrixResidualReceipt :
      Field.CKMMatterMixingMatrixExactVVdaggerResidualReceipt

    concreteMatterMixingMatrixResidualReceiptIsCanonical :
      concreteMatterMixingMatrixResidualReceipt
      ≡
      Field.canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt

    exactCKMProductClosurePromoted :
      Bool

    exactCKMProductClosurePromotedIsFalse :
      exactCKMProductClosurePromoted ≡ false

    exactUnitarityResidualStillFalse :
      Bool

    exactUnitarityResidualStillFalseIsFalse :
      exactUnitarityResidualStillFalse ≡ false

    firstConcreteYukawaBlocker :
      Field.CKMArithmeticInputSlot

    firstConcreteYukawaBlockerIsConcreteUpMatrix :
      firstConcreteYukawaBlocker
      ≡
      Field.missingConcreteUpYukawa3x3Matrix

    concreteMatrixBridgeBoundary :
      List String

open CKMConcreteMatrixAndYukawaBridge public

canonicalCKMConcreteMatrixAndYukawaBridge :
  CKMConcreteMatrixAndYukawaBridge
canonicalCKMConcreteMatrixAndYukawaBridge =
  record
    { concreteMatterMixingMatrixResidualReceipt =
        Field.canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
    ; concreteMatterMixingMatrixResidualReceiptIsCanonical =
        refl
    ; exactCKMProductClosurePromoted =
        false
    ; exactCKMProductClosurePromotedIsFalse =
        refl
    ; exactUnitarityResidualStillFalse =
        false
    ; exactUnitarityResidualStillFalseIsFalse =
        refl
    ; firstConcreteYukawaBlocker =
        Field.missingConcreteUpYukawa3x3Matrix
    ; firstConcreteYukawaBlockerIsConcreteUpMatrix =
        refl
    ; concreteMatrixBridgeBoundary =
        "The executable CKM side is the canonical Wolfenstein Matter.MixingMatrix residual receipt"
        ∷ "That receipt supplies concrete V, V V^dagger, and V V^dagger - I data, but it does not promote exact CKM product closure"
        ∷ "The first concrete Yukawa blocker remains missingConcreteUpYukawa3x3Matrix"
        ∷ "No false promotion is introduced for the exact CKM or Yukawa theorem"
        ∷ []
    }

ckmConcreteMatrixBridgeUsesCanonicalWolfensteinResidualReceipt :
  concreteMatterMixingMatrixResidualReceipt
    canonicalCKMConcreteMatrixAndYukawaBridge
  ≡
  Field.canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
ckmConcreteMatrixBridgeUsesCanonicalWolfensteinResidualReceipt =
  refl

ckmConcreteMatrixBridgeKeepsExactCKMClosureFalse :
  exactCKMProductClosurePromoted
    canonicalCKMConcreteMatrixAndYukawaBridge
  ≡
  false
ckmConcreteMatrixBridgeKeepsExactCKMClosureFalse =
  refl

ckmConcreteMatrixBridgeKeepsYukawaBlockerOpen :
  firstConcreteYukawaBlocker
    canonicalCKMConcreteMatrixAndYukawaBridge
  ≡
  Field.missingConcreteUpYukawa3x3Matrix
ckmConcreteMatrixBridgeKeepsYukawaBlockerOpen =
  refl

------------------------------------------------------------------------
-- lower6 exact CKM/Jarlskog hard blocker.
--
-- Consumes the entry-field rational-epsilon blocker and the current
-- Wolfenstein/Jarlskog surfaces.  The only verified data are leading-order
-- exponents; no exact CKM entries, eta nonzero witness, or carrier-mixing
-- theorem is promoted.

data CKMLower6ExactCKMJarlskogDependency : Set where
  lower6ExactSplittingFieldDependency :
    CKMLower6ExactCKMJarlskogDependency

  lower6ExactNormalizedEigenbasisDependency :
    CKMLower6ExactCKMJarlskogDependency

  lower6ExactMatterMixingMatrixEntryDependency :
    CKMLower6ExactCKMJarlskogDependency

  lower6ExactCKMProductClosureDependency :
    CKMLower6ExactCKMJarlskogDependency

  lower6ExactJarlskogEtaNonzeroDependency :
    CKMLower6ExactCKMJarlskogDependency

  lower6ExactDHRYukawaIntertwinerDependency :
    CKMLower6ExactCKMJarlskogDependency

  lower6ExactCarrierMixingTheoremDependency :
    CKMLower6ExactCKMJarlskogDependency

canonicalCKMLower6ExactCKMJarlskogDependencies :
  List CKMLower6ExactCKMJarlskogDependency
canonicalCKMLower6ExactCKMJarlskogDependencies =
  lower6ExactSplittingFieldDependency
  ∷ lower6ExactNormalizedEigenbasisDependency
  ∷ lower6ExactMatterMixingMatrixEntryDependency
  ∷ lower6ExactCKMProductClosureDependency
  ∷ lower6ExactJarlskogEtaNonzeroDependency
  ∷ lower6ExactDHRYukawaIntertwinerDependency
  ∷ lower6ExactCarrierMixingTheoremDependency
  ∷ []

record CKMLower6ExactCKMJarlskogHardBlockerReceipt : Setω where
  field
    lower6ExactCKMEntryFieldBlocker :
      Field.CKMLower6ExactRationalEpsilonClosureBlockerReceipt

    lower6ExactCKMEntryFieldClosureStillFalse :
      Field.exactRationalEpsilonClosureProved
        lower6ExactCKMEntryFieldBlocker
      ≡
      false

    lower6ExactCKMDownWolfensteinVerification :
      CKMCurrentWaveDownWolfensteinVerificationReceipt

    lower6ExactCKMHierarchyOnlyAtExponentLevel :
      hierarchyVerifiedAtExponentLevel
        lower6ExactCKMDownWolfensteinVerification
      ≡
      true

    lower6ExactCKMEtaNonzeroWitnessMissing :
      etaNonzeroWitnessSupplied
        lower6ExactCKMDownWolfensteinVerification
      ≡
      false

    lower6ExactCKMJarlskogNonzeroStillFalse :
      jarlskogNonzeroPromoted
        lower6ExactCKMDownWolfensteinVerification
      ≡
      false

    lower6ExactCKMWolfensteinJarlskogTarget :
      CKMWolfensteinJarlskogTargetSurface

    lower6ExactCKMWolfensteinValuesMissing :
      wolfensteinNumericValuesSupplied
        lower6ExactCKMWolfensteinJarlskogTarget
      ≡
      false

    lower6ExactCKMJarlskogValueMissing :
      jarlskogInvariantValueSupplied
        lower6ExactCKMWolfensteinJarlskogTarget
      ≡
      false

    lower6ExactCKMJarlskogProofMissing :
      jarlskogNonzeroProofSupplied
        lower6ExactCKMWolfensteinJarlskogTarget
      ≡
      false

    lower6ExactCKMSpectralAttempt :
      CKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt

    lower6ExactCKMUuEigenbasisMissing :
      uuOrthonormalEigenbasisSupplied lower6ExactCKMSpectralAttempt
      ≡
      false

    lower6ExactCKMUdEigenbasisMissing :
      udOrthonormalEigenbasisSupplied lower6ExactCKMSpectralAttempt
      ≡
      false

    lower6ExactCKMResidualStillMissing :
      unitarityResidualWitnessStillMissing lower6ExactCKMSpectralAttempt
      ≡
      Field.missingUnitarityResidualWitness

    lower6ExactCKMDependencies :
      List CKMLower6ExactCKMJarlskogDependency

    lower6ExactCKMDependenciesAreCanonical :
      lower6ExactCKMDependencies
      ≡
      canonicalCKMLower6ExactCKMJarlskogDependencies

    lower6ExactCKMTheoremPromoted :
      Bool

    lower6ExactCKMTheoremPromotedIsFalse :
      lower6ExactCKMTheoremPromoted ≡ false

    lower6ExactJarlskogTheoremPromoted :
      Bool

    lower6ExactJarlskogTheoremPromotedIsFalse :
      lower6ExactJarlskogTheoremPromoted ≡ false

    lower6ExactCarrierMixingTheoremPromoted :
      Bool

    lower6ExactCarrierMixingTheoremPromotedIsFalse :
      lower6ExactCarrierMixingTheoremPromoted ≡ false

    lower6ExactCKMJarlskogBoundary :
      List String

open CKMLower6ExactCKMJarlskogHardBlockerReceipt public

canonicalCKMLower6ExactCKMJarlskogHardBlockerReceipt :
  CKMLower6ExactCKMJarlskogHardBlockerReceipt
canonicalCKMLower6ExactCKMJarlskogHardBlockerReceipt =
  record
    { lower6ExactCKMEntryFieldBlocker =
        Field.canonicalCKMLower6ExactRationalEpsilonClosureBlockerReceipt
    ; lower6ExactCKMEntryFieldClosureStillFalse =
        refl
    ; lower6ExactCKMDownWolfensteinVerification =
        canonicalCKMCurrentWaveDownWolfensteinVerificationReceipt
    ; lower6ExactCKMHierarchyOnlyAtExponentLevel =
        refl
    ; lower6ExactCKMEtaNonzeroWitnessMissing =
        refl
    ; lower6ExactCKMJarlskogNonzeroStillFalse =
        refl
    ; lower6ExactCKMWolfensteinJarlskogTarget =
        canonicalCKMWolfensteinJarlskogTargetSurface
    ; lower6ExactCKMWolfensteinValuesMissing =
        refl
    ; lower6ExactCKMJarlskogValueMissing =
        refl
    ; lower6ExactCKMJarlskogProofMissing =
        refl
    ; lower6ExactCKMSpectralAttempt =
        canonicalCKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt
    ; lower6ExactCKMUuEigenbasisMissing =
        refl
    ; lower6ExactCKMUdEigenbasisMissing =
        refl
    ; lower6ExactCKMResidualStillMissing =
        refl
    ; lower6ExactCKMDependencies =
        canonicalCKMLower6ExactCKMJarlskogDependencies
    ; lower6ExactCKMDependenciesAreCanonical =
        refl
    ; lower6ExactCKMTheoremPromoted =
        false
    ; lower6ExactCKMTheoremPromotedIsFalse =
        refl
    ; lower6ExactJarlskogTheoremPromoted =
        false
    ; lower6ExactJarlskogTheoremPromotedIsFalse =
        refl
    ; lower6ExactCarrierMixingTheoremPromoted =
        false
    ; lower6ExactCarrierMixingTheoremPromotedIsFalse =
        refl
    ; lower6ExactCKMJarlskogBoundary =
        "The exact rational-epsilon CKM request is blocked after the leading-order Wolfenstein hierarchy"
        ∷ "J_CP is recorded only as an epsilon^6 order target; eta nonzero and the Jarlskog nonzero theorem are not supplied"
        ∷ "Matter.MixingMatrix still hides the U_u, U_d, and V_CKM entries required for an exact product and residual computation"
        ∷ "DHR/Yukawa intertwiner compatibility and the carrier mixing theorem remain open dependencies"
        ∷ "No CKM, Jarlskog, Higgs, W4, or terminal promotion is introduced"
        ∷ []
    }

ckmLower6ExactCKMJarlskogHardBlockerDoesNotPromoteCKM :
  lower6ExactCKMTheoremPromoted
    canonicalCKMLower6ExactCKMJarlskogHardBlockerReceipt
  ≡
  false
ckmLower6ExactCKMJarlskogHardBlockerDoesNotPromoteCKM =
  refl

ckmLower6ExactCKMJarlskogHardBlockerDoesNotPromoteJarlskog :
  lower6ExactJarlskogTheoremPromoted
    canonicalCKMLower6ExactCKMJarlskogHardBlockerReceipt
  ≡
  false
ckmLower6ExactCKMJarlskogHardBlockerDoesNotPromoteJarlskog =
  refl

------------------------------------------------------------------------
-- downstream Gate7 physical Yukawa mass / DHR intertwiner surface.
--
-- This receipt sits after the v_Higgs Adapter 4 boundary and the typed DHR
-- sector/category sockets.  It records only target names for the physical
-- top/charm/up Yukawa masses because this module has no exact physical-mass
-- field API.  The DHR side is wired to the existing Intertwiner target socket,
-- but no sector selection, normalized eigenbasis, or Yukawa-DHR compatibility
-- theorem is promoted.

data CKMGate7PhysicalYukawaDHRComponent : Set where
  gate7PhysicalYukawaUsesVHiggsAdapter4BoundaryComponent :
    CKMGate7PhysicalYukawaDHRComponent

  gate7PhysicalYukawaUsesGDHRSectorSurfaceComponent :
    CKMGate7PhysicalYukawaDHRComponent

  gate7PhysicalYukawaRecordsApproxTopMassNameComponent :
    CKMGate7PhysicalYukawaDHRComponent

  gate7PhysicalYukawaRecordsApproxCharmMassNameComponent :
    CKMGate7PhysicalYukawaDHRComponent

  gate7PhysicalYukawaRecordsApproxUpMassNameComponent :
    CKMGate7PhysicalYukawaDHRComponent

  gate7PhysicalYukawaRetainsNormalizedEigenbasisBlockerComponent :
    CKMGate7PhysicalYukawaDHRComponent

  gate7PhysicalYukawaRetainsDHRIntertwinerBlockerComponent :
    CKMGate7PhysicalYukawaDHRComponent

canonicalCKMGate7PhysicalYukawaDHRComponents :
  List CKMGate7PhysicalYukawaDHRComponent
canonicalCKMGate7PhysicalYukawaDHRComponents =
  gate7PhysicalYukawaUsesVHiggsAdapter4BoundaryComponent
  ∷ gate7PhysicalYukawaUsesGDHRSectorSurfaceComponent
  ∷ gate7PhysicalYukawaRecordsApproxTopMassNameComponent
  ∷ gate7PhysicalYukawaRecordsApproxCharmMassNameComponent
  ∷ gate7PhysicalYukawaRecordsApproxUpMassNameComponent
  ∷ gate7PhysicalYukawaRetainsNormalizedEigenbasisBlockerComponent
  ∷ gate7PhysicalYukawaRetainsDHRIntertwinerBlockerComponent
  ∷ []

record CKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt : Setω where
  field
    gate7PhysicalYukawaComponents :
      List CKMGate7PhysicalYukawaDHRComponent

    gate7PhysicalYukawaComponentsAreCanonical :
      gate7PhysicalYukawaComponents
      ≡
      canonicalCKMGate7PhysicalYukawaDHRComponents

    gate7PhysicalYukawaVHiggsAuthorityNote :
      Higgs.VHiggsCurrentWaveAuthorityNoteReceipt

    gate7PhysicalYukawaVHiggsSICalibrationStillFalse :
      Higgs.siCalibrationPromoted gate7PhysicalYukawaVHiggsAuthorityNote
      ≡
      false

    gate7PhysicalYukawaVHiggsAdapter4BoundaryRetained :
      Higgs.adapter4BoundaryRetained
        (Higgs.definitionalReceipt gate7PhysicalYukawaVHiggsAuthorityNote)
      ≡
      true

    gate7PhysicalYukawaVHiggsPhysicalPromotionStillFalse :
      Higgs.physicalYukawaPromotionClaimed
        (Higgs.definitionalReceipt gate7PhysicalYukawaVHiggsAuthorityNote)
      ≡
      false

    gate7PhysicalYukawaDHRSelectionSurface :
      DHR.DHRSelectionCriterionTarget

    gate7PhysicalYukawaDHRSelectionCriterionStillFalse :
      Bool

    gate7PhysicalYukawaDHRCategorySurface :
      DHR.DHRCategoryPrimitiveSurface

    gate7PhysicalYukawaDHRCategoryLawsStillFalse :
      Bool

    gate7PhysicalYukawaIntertwinerTargetRecorded :
      Bool

    gate7PhysicalYukawaIntertwinerTargetRecordedIsTrue :
      gate7PhysicalYukawaIntertwinerTargetRecorded ≡ true

    gate7PhysicalYukawaIntertwinerTargetName :
      String

    gate7PhysicalYukawaIntertwinerTargetName-v :
      gate7PhysicalYukawaIntertwinerTargetName
      ≡
      "DHR.intertwinerPrimitiveTarget canonicalDHRSelectionCriterionTarget"

    gate7PhysicalTopMassApproxTargetName :
      String

    gate7PhysicalTopMassApproxTargetName-v :
      gate7PhysicalTopMassApproxTargetName
      ≡
      "approx-physical-top-yukawa-mass-target-after-vHiggsAdapter4Boundary"

    gate7PhysicalCharmMassApproxTargetName :
      String

    gate7PhysicalCharmMassApproxTargetName-v :
      gate7PhysicalCharmMassApproxTargetName
      ≡
      "approx-physical-charm-yukawa-mass-target-after-vHiggsAdapter4Boundary"

    gate7PhysicalUpMassApproxTargetName :
      String

    gate7PhysicalUpMassApproxTargetName-v :
      gate7PhysicalUpMassApproxTargetName
      ≡
      "approx-physical-up-yukawa-mass-target-after-vHiggsAdapter4Boundary"

    gate7PhysicalYukawaMassValuesSupplied :
      Bool

    gate7PhysicalYukawaMassValuesSuppliedIsFalse :
      gate7PhysicalYukawaMassValuesSupplied ≡ false

    gate7PhysicalYukawaSpectralAttempt :
      CKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt

    gate7PhysicalYukawaUuNormalizedEigenbasisStillMissing :
      uuOrthonormalEigenbasisSupplied gate7PhysicalYukawaSpectralAttempt
      ≡
      false

    gate7PhysicalYukawaUdNormalizedEigenbasisStillMissing :
      udOrthonormalEigenbasisSupplied gate7PhysicalYukawaSpectralAttempt
      ≡
      false

    gate7PhysicalYukawaIntertwinerCompatibilityBlocker :
      CKMYukawaDHRCompatibilityBlocker

    gate7PhysicalYukawaIntertwinerCompatibilityBlockerIsMissing :
      gate7PhysicalYukawaIntertwinerCompatibilityBlocker
      ≡
      missingYukawaDHRIntertwinerCompatibility

    gate7PhysicalYukawaDHRIntertwinerCompatibilitySupplied :
      Bool

    gate7PhysicalYukawaDHRIntertwinerCompatibilitySuppliedIsFalse :
      gate7PhysicalYukawaDHRIntertwinerCompatibilitySupplied ≡ false

    gate7PhysicalYukawaPromotionClaimed :
      Bool

    gate7PhysicalYukawaPromotionClaimedIsFalse :
      gate7PhysicalYukawaPromotionClaimed ≡ false

    gate7PhysicalYukawaDHRBoundary :
      List String

open CKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt public

canonicalCKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt :
  CKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt
canonicalCKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt =
  record
    { gate7PhysicalYukawaComponents =
        canonicalCKMGate7PhysicalYukawaDHRComponents
    ; gate7PhysicalYukawaComponentsAreCanonical =
        refl
    ; gate7PhysicalYukawaVHiggsAuthorityNote =
        Higgs.canonicalVHiggsCurrentWaveAuthorityNoteReceipt
    ; gate7PhysicalYukawaVHiggsSICalibrationStillFalse =
        refl
    ; gate7PhysicalYukawaVHiggsAdapter4BoundaryRetained =
        refl
    ; gate7PhysicalYukawaVHiggsPhysicalPromotionStillFalse =
        refl
    ; gate7PhysicalYukawaDHRSelectionSurface =
        DHR.canonicalDHRSelectionCriterionTarget
    ; gate7PhysicalYukawaDHRSelectionCriterionStillFalse =
        true
    ; gate7PhysicalYukawaDHRCategorySurface =
        DHR.canonicalDHRCategoryPrimitiveSurface
    ; gate7PhysicalYukawaDHRCategoryLawsStillFalse =
        true
    ; gate7PhysicalYukawaIntertwinerTargetRecorded =
        true
    ; gate7PhysicalYukawaIntertwinerTargetRecordedIsTrue =
        refl
    ; gate7PhysicalYukawaIntertwinerTargetName =
        "DHR.intertwinerPrimitiveTarget canonicalDHRSelectionCriterionTarget"
    ; gate7PhysicalYukawaIntertwinerTargetName-v =
        refl
    ; gate7PhysicalTopMassApproxTargetName =
        "approx-physical-top-yukawa-mass-target-after-vHiggsAdapter4Boundary"
    ; gate7PhysicalTopMassApproxTargetName-v =
        refl
    ; gate7PhysicalCharmMassApproxTargetName =
        "approx-physical-charm-yukawa-mass-target-after-vHiggsAdapter4Boundary"
    ; gate7PhysicalCharmMassApproxTargetName-v =
        refl
    ; gate7PhysicalUpMassApproxTargetName =
        "approx-physical-up-yukawa-mass-target-after-vHiggsAdapter4Boundary"
    ; gate7PhysicalUpMassApproxTargetName-v =
        refl
    ; gate7PhysicalYukawaMassValuesSupplied =
        false
    ; gate7PhysicalYukawaMassValuesSuppliedIsFalse =
        refl
    ; gate7PhysicalYukawaSpectralAttempt =
        canonicalCKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt
    ; gate7PhysicalYukawaUuNormalizedEigenbasisStillMissing =
        refl
    ; gate7PhysicalYukawaUdNormalizedEigenbasisStillMissing =
        refl
    ; gate7PhysicalYukawaIntertwinerCompatibilityBlocker =
        missingYukawaDHRIntertwinerCompatibility
    ; gate7PhysicalYukawaIntertwinerCompatibilityBlockerIsMissing =
        refl
    ; gate7PhysicalYukawaDHRIntertwinerCompatibilitySupplied =
        false
    ; gate7PhysicalYukawaDHRIntertwinerCompatibilitySuppliedIsFalse =
        refl
    ; gate7PhysicalYukawaPromotionClaimed =
        false
    ; gate7PhysicalYukawaPromotionClaimedIsFalse =
        refl
    ; gate7PhysicalYukawaDHRBoundary =
        "Gate7 records approximate top/charm/up physical Yukawa mass target names only as receipt strings"
        ∷ "v_Higgs is consumed only through the Adapter4 definitional boundary; SI calibration and physical Yukawa promotion remain false"
        ∷ "G_DHR sector and category sockets are cited through DHRSelectionCriterionTarget and DHRCategoryPrimitiveSurface, with their proof flags still false"
        ∷ "The DHR/Yukawa intertwiner target is the existing DHR Intertwiner primitive socket, not a compatibility theorem"
        ∷ "Normalized U_u/U_d eigenbases remain unsupplied, and missingYukawaDHRIntertwinerCompatibility stays the fail-closed blocker"
        ∷ []
    }

ckmGate7PhysicalYukawaDHRRetainsVHiggsNoPromotion :
  gate7PhysicalYukawaVHiggsPhysicalPromotionStillFalse
    canonicalCKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt
  ≡
  refl
ckmGate7PhysicalYukawaDHRRetainsVHiggsNoPromotion =
  refl

ckmGate7PhysicalYukawaDHRRetainsDHRSelectionOpen :
  gate7PhysicalYukawaDHRSelectionCriterionStillFalse
    canonicalCKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt
  ≡
  true
ckmGate7PhysicalYukawaDHRRetainsDHRSelectionOpen =
  refl

ckmGate7PhysicalYukawaDHRRetainsNormalizedEigenbasisOpen :
  gate7PhysicalYukawaUuNormalizedEigenbasisStillMissing
    canonicalCKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt
  ≡
  refl
ckmGate7PhysicalYukawaDHRRetainsNormalizedEigenbasisOpen =
  refl

ckmGate7PhysicalYukawaDHRRetainsIntertwinerCompatibilityBlocker :
  gate7PhysicalYukawaIntertwinerCompatibilityBlocker
    canonicalCKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt
  ≡
  missingYukawaDHRIntertwinerCompatibility
ckmGate7PhysicalYukawaDHRRetainsIntertwinerCompatibilityBlocker =
  refl

ckmGate7PhysicalYukawaDHRDoesNotPromote :
  gate7PhysicalYukawaPromotionClaimed
    canonicalCKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt
  ≡
  false
ckmGate7PhysicalYukawaDHRDoesNotPromote =
  refl

------------------------------------------------------------------------
-- lower6 m6/l1 Jarlskog nonzero bookkeeping surface.
--
-- This receipt consumes the rational/Gaussian-rational entry surface from
-- CKMEntryField.  It records a leading nonzero CP orientation target for the
-- Jarlskog source, while keeping exact Matter.MixingMatrix product closure and
-- theorem promotion false.

data CKMLower6JarlskogNonzeroBookkeepingComponent : Set where
  lower6JarlskogConsumesGaussianRationalEntrySurfaceComponent :
    CKMLower6JarlskogNonzeroBookkeepingComponent

  lower6JarlskogConsumesWolfensteinExponentSixComponent :
    CKMLower6JarlskogNonzeroBookkeepingComponent

  lower6JarlskogRecordsEtaOrientationNonzeroComponent :
    CKMLower6JarlskogNonzeroBookkeepingComponent

  lower6JarlskogRetainsExactProductClosureBlockerComponent :
    CKMLower6JarlskogNonzeroBookkeepingComponent

canonicalCKMLower6JarlskogNonzeroBookkeepingComponents :
  List CKMLower6JarlskogNonzeroBookkeepingComponent
canonicalCKMLower6JarlskogNonzeroBookkeepingComponents =
  lower6JarlskogConsumesGaussianRationalEntrySurfaceComponent
  ∷ lower6JarlskogConsumesWolfensteinExponentSixComponent
  ∷ lower6JarlskogRecordsEtaOrientationNonzeroComponent
  ∷ lower6JarlskogRetainsExactProductClosureBlockerComponent
  ∷ []

record CKMLower6JarlskogNonzeroBookkeepingReceipt : Setω where
  field
    lower6JarlskogEntryFieldReceipt :
      Field.CKMLower6RationalGaussianEntryFieldReceipt

    lower6JarlskogEntryFieldDoesNotPromote :
      Field.lower6EntryFieldPromotionClaimed lower6JarlskogEntryFieldReceipt
      ≡
      false

    lower6JarlskogWolfensteinVerification :
      CKMCurrentWaveDownWolfensteinVerificationReceipt

    lower6JarlskogExponentIsSix :
      jarlskogLeadingExponent lower6JarlskogWolfensteinVerification
      ≡
      6

    lower6JarlskogBookkeepingComponents :
      List CKMLower6JarlskogNonzeroBookkeepingComponent

    lower6JarlskogBookkeepingComponentsAreCanonical :
      lower6JarlskogBookkeepingComponents
      ≡
      canonicalCKMLower6JarlskogNonzeroBookkeepingComponents

    lower6LeadingJarlskogNonzeroReceiptSupplied :
      Bool

    lower6LeadingJarlskogNonzeroReceiptSuppliedIsTrue :
      lower6LeadingJarlskogNonzeroReceiptSupplied ≡ true

    lower6EtaOrientationNonzeroRecorded :
      Bool

    lower6EtaOrientationNonzeroRecordedIsTrue :
      lower6EtaOrientationNonzeroRecorded ≡ true

    lower6ExactMatterMixingMatrixEntriesSupplied :
      Bool

    lower6ExactMatterMixingMatrixEntriesSuppliedIsTrue :
      lower6ExactMatterMixingMatrixEntriesSupplied ≡ true

    lower6ExactCKMProductClosureSupplied :
      Bool

    lower6ExactCKMProductClosureSuppliedIsFalse :
      lower6ExactCKMProductClosureSupplied ≡ false

    lower6JarlskogTheoremPromoted :
      Bool

    lower6JarlskogTheoremPromotedIsFalse :
      lower6JarlskogTheoremPromoted ≡ false

    lower6CarrierMixingTheoremPromoted :
      Bool

    lower6CarrierMixingTheoremPromotedIsFalse :
      lower6CarrierMixingTheoremPromoted ≡ false

    lower6JarlskogBookkeepingBoundary :
      List String

open CKMLower6JarlskogNonzeroBookkeepingReceipt public

canonicalCKMLower6JarlskogNonzeroBookkeepingReceipt :
  CKMLower6JarlskogNonzeroBookkeepingReceipt
canonicalCKMLower6JarlskogNonzeroBookkeepingReceipt =
  record
    { lower6JarlskogEntryFieldReceipt =
        Field.canonicalCKMLower6RationalGaussianEntryFieldReceipt
    ; lower6JarlskogEntryFieldDoesNotPromote =
        refl
    ; lower6JarlskogWolfensteinVerification =
        canonicalCKMCurrentWaveDownWolfensteinVerificationReceipt
    ; lower6JarlskogExponentIsSix =
        refl
    ; lower6JarlskogBookkeepingComponents =
        canonicalCKMLower6JarlskogNonzeroBookkeepingComponents
    ; lower6JarlskogBookkeepingComponentsAreCanonical =
        refl
    ; lower6LeadingJarlskogNonzeroReceiptSupplied =
        true
    ; lower6LeadingJarlskogNonzeroReceiptSuppliedIsTrue =
        refl
    ; lower6EtaOrientationNonzeroRecorded =
        true
    ; lower6EtaOrientationNonzeroRecordedIsTrue =
        refl
    ; lower6ExactMatterMixingMatrixEntriesSupplied =
        true
    ; lower6ExactMatterMixingMatrixEntriesSuppliedIsTrue =
        refl
    ; lower6ExactCKMProductClosureSupplied =
        false
    ; lower6ExactCKMProductClosureSuppliedIsFalse =
        refl
    ; lower6JarlskogTheoremPromoted =
        false
    ; lower6JarlskogTheoremPromotedIsFalse =
        refl
    ; lower6CarrierMixingTheoremPromoted =
        false
    ; lower6CarrierMixingTheoremPromotedIsFalse =
        refl
    ; lower6JarlskogBookkeepingBoundary =
        "lower6 records leading Jarlskog nonzero bookkeeping from the Gaussian-rational CP orientation surface"
        ∷ "the Wolfenstein/Jarlskog exponent remains epsilon^6"
        ∷ "Matter.MixingMatrix exposes exact Gaussian-rational entries, but the canonical Wolfenstein V V^dagger residual is nonzero"
        ∷ "exact Jarlskog and carrier-mixing theorem promotions remain false"
        ∷ []
    }

ckmLower6LeadingJarlskogBookkeepingIsRecorded :
  lower6LeadingJarlskogNonzeroReceiptSupplied
    canonicalCKMLower6JarlskogNonzeroBookkeepingReceipt
  ≡
  true
ckmLower6LeadingJarlskogBookkeepingIsRecorded =
  refl

ckmLower6JarlskogTheoremStillNotPromoted :
  lower6JarlskogTheoremPromoted
    canonicalCKMLower6JarlskogNonzeroBookkeepingReceipt
  ≡
  false
ckmLower6JarlskogTheoremStillNotPromoted =
  refl

------------------------------------------------------------------------
-- CKM Matter.MixingMatrix API audit consumer.
--
-- This carrier-mixing surface consumes the entry-field audit rather than
-- promoting a theorem.  The audit now records a concrete 3x3 Q[i] entry
-- carrier and an exact V V^dagger - I residual for the leading Wolfenstein
-- datum; that residual is nonzero, so exact product closure remains false.

record CKMCarrierMixingMatterMixingMatrixAPIAuditReceipt : Setω where
  field
    entryFieldAPIAuditReceipt :
      Field.CKMMatterMixingMatrixAPIAuditFailClosedReceipt

    exactMatterMixingMatrixDefinition :
      Field.exactInspectedDefinition entryFieldAPIAuditReceipt
      ≡
      "record MixingMatrix : Set where constructor mixingMatrix3x3"

    firstMatterMixingMatrixAPIGap :
      Field.auditFirstBlocker entryFieldAPIAuditReceipt
      ≡
      Field.missingMatterMixingMatrixConjugateTranspose

    exactVVdaggerResidualComputed :
      Field.vvDaggerResidualComputed
        (Field.exactVVdaggerResidualReceipt entryFieldAPIAuditReceipt)
      ≡
      true

    exactWolfensteinUnitarityRejected :
      Field.exactUnitarityForConcreteWolfenstein
        (Field.exactVVdaggerResidualReceipt entryFieldAPIAuditReceipt)
      ≡
      false

    qIEntriesDoNotInstantiateMatterProductClosure :
      Field.qIEntriesCanInstantiateMatterProductClosure
        entryFieldAPIAuditReceipt
      ≡
      false

    exactProductClosureStillFalse :
      Field.exactCKMProductClosurePromoted entryFieldAPIAuditReceipt
      ≡
      false

    exactJarlskogTheoremStillFalse :
      Field.exactJarlskogTheoremPromoted entryFieldAPIAuditReceipt
      ≡
      false

    lower6JarlskogBookkeepingReceipt :
      CKMLower6JarlskogNonzeroBookkeepingReceipt

    lower6BookkeepingRecorded :
      lower6LeadingJarlskogNonzeroReceiptSupplied
        lower6JarlskogBookkeepingReceipt
      ≡
      true

    lower6MatterEntriesNowConcrete :
      lower6ExactMatterMixingMatrixEntriesSupplied
        lower6JarlskogBookkeepingReceipt
      ≡
      true

    lower6CarrierMixingTheoremStillFalse :
      lower6CarrierMixingTheoremPromoted
        lower6JarlskogBookkeepingReceipt
      ≡
      false

    carrierMixingTheoremPromoted :
      Bool

    carrierMixingTheoremPromotedIsFalse :
      carrierMixingTheoremPromoted ≡ false

    auditConsumerBoundary :
      List String

open CKMCarrierMixingMatterMixingMatrixAPIAuditReceipt public

canonicalCKMCarrierMixingMatterMixingMatrixAPIAuditReceipt :
  CKMCarrierMixingMatterMixingMatrixAPIAuditReceipt
canonicalCKMCarrierMixingMatterMixingMatrixAPIAuditReceipt =
  record
    { entryFieldAPIAuditReceipt =
        Field.canonicalCKMMatterMixingMatrixAPIAuditFailClosedReceipt
    ; exactMatterMixingMatrixDefinition =
        refl
    ; firstMatterMixingMatrixAPIGap =
        refl
    ; exactVVdaggerResidualComputed =
        refl
    ; exactWolfensteinUnitarityRejected =
        refl
    ; qIEntriesDoNotInstantiateMatterProductClosure =
        refl
    ; exactProductClosureStillFalse =
        refl
    ; exactJarlskogTheoremStillFalse =
        refl
    ; lower6JarlskogBookkeepingReceipt =
        canonicalCKMLower6JarlskogNonzeroBookkeepingReceipt
    ; lower6BookkeepingRecorded =
        refl
    ; lower6MatterEntriesNowConcrete =
        refl
    ; lower6CarrierMixingTheoremStillFalse =
        refl
    ; carrierMixingTheoremPromoted =
        false
    ; carrierMixingTheoremPromotedIsFalse =
        refl
    ; auditConsumerBoundary =
        "Carrier mixing consumes the CKMEntryField Matter.MixingMatrix API audit"
        ∷ "The exact inspected API is a concrete 3x3 Gaussian-rational MixingMatrix entry record"
        ∷ "CKMEntryField records V V^dagger - I for the canonical Wolfenstein datum and the residual is nonzero"
        ∷ "Q[i] Wolfenstein entries therefore do not instantiate exact product closure for this approximation"
        ∷ "Leading Jarlskog nonzero bookkeeping is recorded, but exact unitary CKM construction is still missing"
        ∷ "No carrier mixing theorem, exact CKM product closure, or exact Jarlskog promotion is introduced"
        ∷ []
    }

ckmCarrierMixingConsumesMatterMixingMatrixAPIAudit :
  Field.qIEntriesCanInstantiateMatterProductClosure
    (entryFieldAPIAuditReceipt
      canonicalCKMCarrierMixingMatterMixingMatrixAPIAuditReceipt)
  ≡
  false
ckmCarrierMixingConsumesMatterMixingMatrixAPIAudit =
  refl

ckmCarrierMixingAPIAuditKeepsTheoremFalse :
  carrierMixingTheoremPromoted
    canonicalCKMCarrierMixingMatterMixingMatrixAPIAuditReceipt
  ≡
  false
ckmCarrierMixingAPIAuditKeepsTheoremFalse =
  refl

------------------------------------------------------------------------
-- CKM explicit-entry approximate unitarity carrier consumer.
--
-- This is the carrier-level handoff for the entry-field receipt that consumes
-- explicit Q[i] entries.  It records approximate unitarity and exact local
-- Jarlskog nonzero data without converting either into exact CKM product
-- closure or a carrier-mixing theorem.

data CKMCarrierExplicitEntryApproxUnitarityComponent : Set where
  carrierConsumesExplicitEntryApproxReceiptComponent :
    CKMCarrierExplicitEntryApproxUnitarityComponent

  carrierConsumesApproxUnitarityResidualBoundComponent :
    CKMCarrierExplicitEntryApproxUnitarityComponent

  carrierConsumesExactLocalJarlskogNonzeroDatumComponent :
    CKMCarrierExplicitEntryApproxUnitarityComponent

  carrierConsumesExactConjugatedQuartetJarlskogNonzeroDatumComponent :
    CKMCarrierExplicitEntryApproxUnitarityComponent

  carrierRetainsExactCKMProductClosureBlockerComponent :
    CKMCarrierExplicitEntryApproxUnitarityComponent

  carrierRetainsCarrierMixingTheoremBlockerComponent :
    CKMCarrierExplicitEntryApproxUnitarityComponent

canonicalCKMCarrierExplicitEntryApproxUnitarityComponents :
  List CKMCarrierExplicitEntryApproxUnitarityComponent
canonicalCKMCarrierExplicitEntryApproxUnitarityComponents =
  carrierConsumesExplicitEntryApproxReceiptComponent
  ∷ carrierConsumesApproxUnitarityResidualBoundComponent
  ∷ carrierConsumesExactLocalJarlskogNonzeroDatumComponent
  ∷ carrierConsumesExactConjugatedQuartetJarlskogNonzeroDatumComponent
  ∷ carrierRetainsExactCKMProductClosureBlockerComponent
  ∷ carrierRetainsCarrierMixingTheoremBlockerComponent
  ∷ []

record CKMCarrierExplicitEntryApproxUnitarityReceipt : Setω where
  field
    explicitEntryApproxReceipt :
      Field.CKMExplicitEntryApproxUnitarityJarlskogReceipt

    carrierExplicitComponents :
      List CKMCarrierExplicitEntryApproxUnitarityComponent

    carrierExplicitComponentsAreCanonical :
      carrierExplicitComponents
      ≡
      canonicalCKMCarrierExplicitEntryApproxUnitarityComponents

    explicitVubEntryConsumed :
      Bool

    explicitVubEntryConsumedIsTrue :
      explicitVubEntryConsumed ≡ true

    explicitVtdEntryConsumed :
      Bool

    explicitVtdEntryConsumedIsTrue :
      explicitVtdEntryConsumed ≡ true

    approximateUnitarityBoundConsumed :
      Bool

    approximateUnitarityBoundConsumedIsTrue :
      approximateUnitarityBoundConsumed ≡ true

    approximateUnitarityBoundDenominatorConsumed :
      Bool

    approximateUnitarityBoundDenominatorConsumedIsTrue :
      approximateUnitarityBoundDenominatorConsumed ≡ true

    exactLocalJarlskogNonzeroDatumConsumed :
      Bool

    exactLocalJarlskogNonzeroDatumConsumedIsTrue :
      exactLocalJarlskogNonzeroDatumConsumed ≡ true

    exactConjugatedQuartetJarlskogNonzeroDatumConsumed :
      Bool

    exactConjugatedQuartetJarlskogNonzeroDatumConsumedIsTrue :
      exactConjugatedQuartetJarlskogNonzeroDatumConsumed ≡ true

    exactLocalJarlskogNumeratorConsumed :
      Bool

    exactLocalJarlskogNumeratorConsumedIsTrue :
      exactLocalJarlskogNumeratorConsumed ≡ true

    exactUnitarityRejectedForApproximationConsumed :
      Bool

    exactUnitarityRejectedForApproximationConsumedIsTrue :
      exactUnitarityRejectedForApproximationConsumed ≡ true

    exactCKMProductClosureStillFalse :
      Field.exactCKMProductClosureWitnessSupplied explicitEntryApproxReceipt
      ≡
      false

    exactJarlskogTheoremStillFalse :
      Field.exactJarlskogTheoremPromoted explicitEntryApproxReceipt
      ≡
      false

    exactProductClosureBlocker :
      Field.CKMArithmeticInputSlot

    exactProductClosureBlockerIsMissingCKMProductClosureWitness :
      exactProductClosureBlocker
      ≡
      Field.missingCKMProductClosureWitness

    carrierMixingTheoremPromoted :
      Bool

    carrierMixingTheoremPromotedIsFalse :
      carrierMixingTheoremPromoted ≡ false

    explicitEntryApproxCarrierBoundary :
      List String

open CKMCarrierExplicitEntryApproxUnitarityReceipt public

canonicalCKMCarrierExplicitEntryApproxUnitarityReceipt :
  CKMCarrierExplicitEntryApproxUnitarityReceipt
canonicalCKMCarrierExplicitEntryApproxUnitarityReceipt =
  record
    { explicitEntryApproxReceipt =
        Field.canonicalCKMExplicitEntryApproxUnitarityJarlskogReceipt
    ; carrierExplicitComponents =
        canonicalCKMCarrierExplicitEntryApproxUnitarityComponents
    ; carrierExplicitComponentsAreCanonical =
        refl
    ; explicitVubEntryConsumed =
        true
    ; explicitVubEntryConsumedIsTrue =
        refl
    ; explicitVtdEntryConsumed =
        true
    ; explicitVtdEntryConsumedIsTrue =
        refl
    ; approximateUnitarityBoundConsumed =
        true
    ; approximateUnitarityBoundConsumedIsTrue =
        refl
    ; approximateUnitarityBoundDenominatorConsumed =
        true
    ; approximateUnitarityBoundDenominatorConsumedIsTrue =
        refl
    ; exactLocalJarlskogNonzeroDatumConsumed =
        true
    ; exactLocalJarlskogNonzeroDatumConsumedIsTrue =
        refl
    ; exactConjugatedQuartetJarlskogNonzeroDatumConsumed =
        true
    ; exactConjugatedQuartetJarlskogNonzeroDatumConsumedIsTrue =
        refl
    ; exactLocalJarlskogNumeratorConsumed =
        true
    ; exactLocalJarlskogNumeratorConsumedIsTrue =
        refl
    ; exactUnitarityRejectedForApproximationConsumed =
        true
    ; exactUnitarityRejectedForApproximationConsumedIsTrue =
        refl
    ; exactCKMProductClosureStillFalse =
        refl
    ; exactJarlskogTheoremStillFalse =
        refl
    ; exactProductClosureBlocker =
        Field.missingCKMProductClosureWitness
    ; exactProductClosureBlockerIsMissingCKMProductClosureWitness =
        refl
    ; carrierMixingTheoremPromoted =
        false
    ; carrierMixingTheoremPromotedIsFalse =
        refl
    ; explicitEntryApproxCarrierBoundary =
        "Carrier mixing consumes the explicit-entry Q[i] approximate unitarity receipt"
        ∷ "The consumed residual is order-bounded at epsilon^4=1/625, not exact unitary closure"
        ∷ "The consumed local Jarlskog datum is exact and nonzero at J=-49/2343750"
        ∷ "The consumed requested quartet Im(Vus Vcb conj(Vub) conj(Vcs)) datum is exact and nonzero at J=49/2343750"
        ∷ "The exact CKM product closure blocker remains missingCKMProductClosureWitness"
        ∷ "No carrier mixing theorem or global exact Jarlskog theorem is promoted"
        ∷ []
    }

ckmCarrierExplicitEntryApproxUnitarityConsumesBound :
  Field.approximateUnitarityResidualOrderExponent
    (explicitEntryApproxReceipt
      canonicalCKMCarrierExplicitEntryApproxUnitarityReceipt)
  ≡
  4
ckmCarrierExplicitEntryApproxUnitarityConsumesBound =
  refl

ckmCarrierExplicitEntryApproxUnitarityConsumesJarlskogNonzero :
  Field.exactLocalJarlskogNonzeroDatumSupplied
    (explicitEntryApproxReceipt
      canonicalCKMCarrierExplicitEntryApproxUnitarityReceipt)
  ≡
  true
ckmCarrierExplicitEntryApproxUnitarityConsumesJarlskogNonzero =
  refl

ckmCarrierExplicitEntryApproxUnitarityConsumesConjugatedQuartetJarlskogNonzero :
  Field.exactConjugatedQuartetJarlskogNonzeroDatumSupplied
    (explicitEntryApproxReceipt
      canonicalCKMCarrierExplicitEntryApproxUnitarityReceipt)
  ≡
  true
ckmCarrierExplicitEntryApproxUnitarityConsumesConjugatedQuartetJarlskogNonzero =
  refl

ckmCarrierExplicitEntryApproxUnitarityDoesNotPromote :
  carrierMixingTheoremPromoted
    canonicalCKMCarrierExplicitEntryApproxUnitarityReceipt
  ≡
  false
ckmCarrierExplicitEntryApproxUnitarityDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Concrete exact-Jarlskog / unitarity-residual chain.
--
-- This bundles the already-recorded Gaussian-rational Jarlskog datum and the
-- computed Wolfenstein residual without promoting the missing exact product
-- closure or carrier-mixing theorem.

record CKMCarrierGaussianRationalExactJarlskogResidualChainReceipt : Setω where
  field
    explicitEntryApproxCarrierReceipt :
      CKMCarrierExplicitEntryApproxUnitarityReceipt

    explicitEntryApproxConsumesExactLocalJarlskogNonzeroDatum :
      exactLocalJarlskogNonzeroDatumConsumed
        explicitEntryApproxCarrierReceipt
      ≡
      true

    explicitEntryApproxConsumesExactConjugatedQuartetJarlskogNonzeroDatum :
      exactConjugatedQuartetJarlskogNonzeroDatumConsumed
        explicitEntryApproxCarrierReceipt
      ≡
      true

    exactVVdaggerResidualReceipt :
      Field.CKMMatterMixingMatrixExactVVdaggerResidualReceipt

    exactVVdaggerResidualComputed :
      Field.vvDaggerResidualComputed exactVVdaggerResidualReceipt
      ≡
      true

    exactWolfensteinUnitarityRejected :
      Field.exactUnitarityForConcreteWolfenstein
        exactVVdaggerResidualReceipt
      ≡
      false

    exactJarlskogBookkeepingReceipt :
      Field.CKMApproximateUnitarityJarlskogBookkeepingReceipt

    exactJarlskogBookkeepingConsumesApproximateUnitarity :
      Bool

    exactJarlskogBookkeepingConsumesExactLocalJarlskogNonzeroDatum :
      Bool

    exactJarlskogBookkeepingConsumesExactConjugatedQuartetJarlskogNonzeroDatum :
      Bool

    exactJarlskogTheoremStillFalse :
      Field.approxJarlskogExactTheoremPromoted
        exactJarlskogBookkeepingReceipt
      ≡
      false

    carrierMixingTheoremPromoted :
      Bool

    carrierMixingTheoremPromotedIsFalse :
      carrierMixingTheoremPromoted ≡ false

    chainBoundary :
      List String

open CKMCarrierGaussianRationalExactJarlskogResidualChainReceipt public

canonicalCKMCarrierGaussianRationalExactJarlskogResidualChainReceipt :
  CKMCarrierGaussianRationalExactJarlskogResidualChainReceipt
canonicalCKMCarrierGaussianRationalExactJarlskogResidualChainReceipt =
  record
    { explicitEntryApproxCarrierReceipt =
        canonicalCKMCarrierExplicitEntryApproxUnitarityReceipt
    ; explicitEntryApproxConsumesExactLocalJarlskogNonzeroDatum =
        refl
    ; explicitEntryApproxConsumesExactConjugatedQuartetJarlskogNonzeroDatum =
        refl
    ; exactVVdaggerResidualReceipt =
        Field.canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
    ; exactVVdaggerResidualComputed =
        refl
    ; exactWolfensteinUnitarityRejected =
        refl
    ; exactJarlskogBookkeepingReceipt =
        Field.canonicalCKMApproximateUnitarityJarlskogBookkeepingReceipt
    ; exactJarlskogBookkeepingConsumesApproximateUnitarity =
        true
    ; exactJarlskogBookkeepingConsumesExactLocalJarlskogNonzeroDatum =
        true
    ; exactJarlskogBookkeepingConsumesExactConjugatedQuartetJarlskogNonzeroDatum =
        true
    ; exactJarlskogTheoremStillFalse =
        refl
    ; carrierMixingTheoremPromoted =
        false
    ; carrierMixingTheoremPromotedIsFalse =
        refl
    ; chainBoundary =
        "Carrier mixing now threads the explicit-entry approximate unitarity receipt with its exact local Jarlskog datum"
        ∷ "The exact local Jarlskog datum is consumed as true, as is the conjugated-quartet nonzero datum"
        ∷ "The concrete Wolkenstein residual receipt computes V V^dagger - I and rejects exact unitarity for the finite datum"
        ∷ "The approximate Jarlskog bookkeeping receipt consumes the same local nonzero data, but the exact theorem remains false"
        ∷ "No exact CKM product closure, carrier-mixing theorem, or residual promotion is introduced"
        ∷ []
    }

------------------------------------------------------------------------
-- Gate7 carrier consumer for CKM approximate unitarity.
--
-- This receipt records the usable progress from CKMEntryField: an approximate
-- Wolfenstein unitarity target exists over Q[i], but the exact Q[i] residual
-- rejects product closure.  It also threads the exact-Jarlskog dependency path
-- already used by the lower6 hard blocker.

data CKMCarrierApproximateUnitarityComponent : Set where
  carrierApproximateUnitarityConsumesEntryFieldComponent :
    CKMCarrierApproximateUnitarityComponent

  carrierApproximateUnitarityRejectsExactQiComponent :
    CKMCarrierApproximateUnitarityComponent

  carrierApproximateUnitarityRecordsExactJarlskogPathComponent :
    CKMCarrierApproximateUnitarityComponent

  carrierApproximateUnitarityConsumesJarlskogBookkeepingComponent :
    CKMCarrierApproximateUnitarityComponent

  carrierApproximateUnitarityKeepsTheoremFalseComponent :
    CKMCarrierApproximateUnitarityComponent

canonicalCKMCarrierApproximateUnitarityComponents :
  List CKMCarrierApproximateUnitarityComponent
canonicalCKMCarrierApproximateUnitarityComponents =
  carrierApproximateUnitarityConsumesEntryFieldComponent
  ∷ carrierApproximateUnitarityRejectsExactQiComponent
  ∷ carrierApproximateUnitarityRecordsExactJarlskogPathComponent
  ∷ carrierApproximateUnitarityConsumesJarlskogBookkeepingComponent
  ∷ carrierApproximateUnitarityKeepsTheoremFalseComponent
  ∷ []

record CKMCarrierApproximateUnitarityReceipt : Setω where
  field
    entryApproximateUnitarityReceipt :
      Field.CKMApproximateUnitarityReceipt

    approximateTargetRecordedHere :
      Field.approximateTargetRecorded entryApproximateUnitarityReceipt
      ≡
      true

    approximateResidualOrderFourHere :
      Field.residualOrderExponent
        (Field.approximateProductReceipt entryApproximateUnitarityReceipt)
      ≡
      4

    exactQiUnitarityRejectedHere :
      Field.exactUnitarityForConcreteWolfenstein
        (Field.exactResidualReceipt entryApproximateUnitarityReceipt)
      ≡
      false

    exactQiProductClosureStillFalseHere :
      Field.exactCKMProductClosurePromoted
        (Field.exactResidualReceipt entryApproximateUnitarityReceipt)
      ≡
      false

    exactJarlskogPathReceipt :
      CKMLower6ExactCKMJarlskogHardBlockerReceipt

    exactJarlskogDependencyPath :
      List CKMLower6ExactCKMJarlskogDependency

    exactJarlskogDependencyPathIsCanonical :
      exactJarlskogDependencyPath
      ≡
      canonicalCKMLower6ExactCKMJarlskogDependencies

    exactJarlskogPathIncludesProductClosure :
      lower6ExactCKMDependencies exactJarlskogPathReceipt
      ≡
      canonicalCKMLower6ExactCKMJarlskogDependencies

    exactJarlskogTheoremStillFalseHere :
      lower6ExactJarlskogTheoremPromoted exactJarlskogPathReceipt
      ≡
      false

    entryJarlskogBookkeepingReceipt :
      Field.CKMApproximateUnitarityJarlskogBookkeepingReceipt

    entryJarlskogBookkeepingConsumesApproximateUnitarity :
      Field.approximateTargetRecorded
        (Field.approxUnitarityReceiptForJarlskog
          entryJarlskogBookkeepingReceipt)
      ≡
      true

    entryJarlskogBookkeepingRejectsExactQi :
      Field.exactUnitarityForConcreteWolfenstein
        (Field.exactResidualReceipt
          (Field.approxUnitarityReceiptForJarlskog
            entryJarlskogBookkeepingReceipt))
      ≡
      false

    entryJarlskogBookkeepingKeepsExactTheoremFalse :
      Field.approxJarlskogExactTheoremPromoted
        entryJarlskogBookkeepingReceipt
      ≡
      false

    carrierApproximateUnitarityComponents :
      List CKMCarrierApproximateUnitarityComponent

    carrierApproximateUnitarityComponentsAreCanonical :
      carrierApproximateUnitarityComponents
      ≡
      canonicalCKMCarrierApproximateUnitarityComponents

    carrierApproximateUnitarityTheoremPromoted :
      Bool

    carrierApproximateUnitarityTheoremPromotedIsFalse :
      carrierApproximateUnitarityTheoremPromoted ≡ false

    carrierApproximateUnitarityBoundary :
      List String

open CKMCarrierApproximateUnitarityReceipt public

canonicalCKMCarrierApproximateUnitarityReceipt :
  CKMCarrierApproximateUnitarityReceipt
canonicalCKMCarrierApproximateUnitarityReceipt =
  record
    { entryApproximateUnitarityReceipt =
        Field.canonicalCKMApproximateUnitarityReceipt
    ; approximateTargetRecordedHere =
        refl
    ; approximateResidualOrderFourHere =
        refl
    ; exactQiUnitarityRejectedHere =
        refl
    ; exactQiProductClosureStillFalseHere =
        refl
    ; exactJarlskogPathReceipt =
        canonicalCKMLower6ExactCKMJarlskogHardBlockerReceipt
    ; exactJarlskogDependencyPath =
        canonicalCKMLower6ExactCKMJarlskogDependencies
    ; exactJarlskogDependencyPathIsCanonical =
        refl
    ; exactJarlskogPathIncludesProductClosure =
        refl
    ; exactJarlskogTheoremStillFalseHere =
        refl
    ; entryJarlskogBookkeepingReceipt =
        Field.canonicalCKMApproximateUnitarityJarlskogBookkeepingReceipt
    ; entryJarlskogBookkeepingConsumesApproximateUnitarity =
        refl
    ; entryJarlskogBookkeepingRejectsExactQi =
        refl
    ; entryJarlskogBookkeepingKeepsExactTheoremFalse =
        refl
    ; carrierApproximateUnitarityComponents =
        canonicalCKMCarrierApproximateUnitarityComponents
    ; carrierApproximateUnitarityComponentsAreCanonical =
        refl
    ; carrierApproximateUnitarityTheoremPromoted =
        false
    ; carrierApproximateUnitarityTheoremPromotedIsFalse =
        refl
    ; carrierApproximateUnitarityBoundary =
        "Carrier mixing consumes CKMEntryField.canonicalCKMApproximateUnitarityReceipt"
        ∷ "Approximate Wolfenstein unitarity is recorded only as an epsilon^4 residual target over Q[i]"
        ∷ "The exact Q[i] V V^dagger residual rejects exact unitarity and exact product closure for the truncated datum"
        ∷ "The entry-field Jarlskog bookkeeping handoff is consumed, but its exact theorem promotion bit remains false"
        ∷ "The exact Jarlskog dependency path is splitting field, normalized eigenbasis, exact entries, exact product closure, eta nonzero, DHR/Yukawa compatibility, and carrier theorem"
        ∷ "No exact CKM unitarity, carrier mixing theorem, exact Jarlskog theorem, or terminal promotion is introduced"
        ∷ []
    }

ckmCarrierApproximateUnitarityRecordsTarget :
  Field.approximateTargetRecorded
    (entryApproximateUnitarityReceipt
      canonicalCKMCarrierApproximateUnitarityReceipt)
  ≡
  true
ckmCarrierApproximateUnitarityRecordsTarget =
  refl

ckmCarrierApproximateUnitarityRejectsExactQi :
  Field.exactUnitarityForConcreteWolfenstein
    (Field.exactResidualReceipt
      (entryApproximateUnitarityReceipt
        canonicalCKMCarrierApproximateUnitarityReceipt))
  ≡
  false
ckmCarrierApproximateUnitarityRejectsExactQi =
  refl

ckmCarrierApproximateUnitarityDoesNotPromote :
  carrierApproximateUnitarityTheoremPromoted
    canonicalCKMCarrierApproximateUnitarityReceipt
  ≡
  false
ckmCarrierApproximateUnitarityDoesNotPromote =
  refl

ckmCarrierApproximateUnitarityKeepsJarlskogTheoremFalse :
  Field.approxJarlskogExactTheoremPromoted
    (entryJarlskogBookkeepingReceipt
      canonicalCKMCarrierApproximateUnitarityReceipt)
  ≡
  false
ckmCarrierApproximateUnitarityKeepsJarlskogTheoremFalse =
  refl

------------------------------------------------------------------------
-- Upstream exact witness chain consumer.
--
-- This carrier surface consumes the exact identity-case CKM theorem chain
-- without promoting the physical off-diagonal carrier frontier.  It records
-- the carrier-mixing theorem and DHR/Yukawa intertwiner compatibility from
-- the upstream exact witness chain, while keeping the physical receipt false.

record CKMExactWitnessChainCarrierReceipt : Setω where
  field
    exactWitnessChain :
      Exact.CKMExactWitnessChain

    wolfensteinResidualChain :
      String

    wolfensteinResidualChainIsCanonical :
      Bool

    wolfensteinResidualChainIsCanonicalIsTrue :
      wolfensteinResidualChainIsCanonical ≡ true

    carrierMixingTheoremWitness :
      Exact.CarrierMixingTheoremWitness

    carrierMixingTheoremWitnessIsChainProjection :
      carrierMixingTheoremWitness
      ≡
      Exact.CKMExactWitnessChain.carrierMixingTheorem exactWitnessChain

    yukawaDHRIntertwinerCompatibilityWitness :
      Exact.YukawaDHRIntertwinerCompatibilityWitness

    yukawaDHRIntertwinerCompatibilityWitnessIsChainProjection :
      yukawaDHRIntertwinerCompatibilityWitness
      ≡
      Exact.CKMExactWitnessChain.yukawaDHRIntertwinerCompatibility exactWitnessChain

    exactWitnessChainConsumed :
      Bool

    exactWitnessChainConsumedIsTrue :
      exactWitnessChainConsumed ≡ true

    physicalOffDiagonalFrontierStillOpen :
      Bool

    physicalOffDiagonalFrontierStillOpenIsFalse :
      physicalOffDiagonalFrontierStillOpen ≡ false

    exactWitnessChainBoundary :
      List String

open CKMExactWitnessChainCarrierReceipt public

canonicalCKMExactWitnessChainCarrierReceipt :
  CKMExactWitnessChainCarrierReceipt
canonicalCKMExactWitnessChainCarrierReceipt = record
  { exactWitnessChain = Exact.canonicalCKMExactWitnessChain
  ; wolfensteinResidualChain =
      "canonicalCKMCarrierGaussianRationalExactJarlskogResidualChainReceipt"
  ; wolfensteinResidualChainIsCanonical =
      true
  ; wolfensteinResidualChainIsCanonicalIsTrue =
      refl
  ; carrierMixingTheoremWitness =
      Exact.CKMExactWitnessChain.carrierMixingTheorem
        Exact.canonicalCKMExactWitnessChain
  ; carrierMixingTheoremWitnessIsChainProjection =
      refl
  ; yukawaDHRIntertwinerCompatibilityWitness =
      Exact.CKMExactWitnessChain.yukawaDHRIntertwinerCompatibility
        Exact.canonicalCKMExactWitnessChain
  ; yukawaDHRIntertwinerCompatibilityWitnessIsChainProjection =
      refl
  ; exactWitnessChainConsumed =
      true
  ; exactWitnessChainConsumedIsTrue =
      refl
  ; physicalOffDiagonalFrontierStillOpen =
      false
  ; physicalOffDiagonalFrontierStillOpenIsFalse =
      refl
  ; exactWitnessChainBoundary =
      "The exact identity-case carrier-mixing theorem is threaded upstream"
      ∷ "The canonical Gaussian-rational Wolfenstein residual chain is retained as the explicit FN/Wolfenstein front"
      ∷ "Carrier-mixing theorem and Yukawa/DHR intertwiner compatibility are consumed from the canonical exact chain"
      ∷ "The physical off-diagonal CKM frontier remains open and is not promoted here"
      ∷ []
  }

exactCKMIdentityWitnessChain :
  Exact.CKMExactWitnessChain
exactCKMIdentityWitnessChain =
  exactWitnessChain canonicalCKMExactWitnessChainCarrierReceipt

exactCKMIdentityCarrierMixingTheoremWitness :
  Exact.CarrierMixingTheoremWitness
exactCKMIdentityCarrierMixingTheoremWitness =
  carrierMixingTheoremWitness canonicalCKMExactWitnessChainCarrierReceipt

exactCKMIdentityYukawaDHRIntertwinerCompatibilityWitness :
  Exact.YukawaDHRIntertwinerCompatibilityWitness
exactCKMIdentityYukawaDHRIntertwinerCompatibilityWitness =
  yukawaDHRIntertwinerCompatibilityWitness
    canonicalCKMExactWitnessChainCarrierReceipt

record CKMCarrierMixingGate7ExactBridgeReceipt : Setω where
  field
    exactWitnessChain :
      Exact.CKMExactWitnessChain

    exactWitnessChainIsCanonical :
      exactWitnessChain
      ≡
      Exact.canonicalCKMExactWitnessChain

    exactCarrierMixingTheoremWitness :
      Exact.CarrierMixingTheoremWitness

    exactCarrierMixingTheoremWitnessIsChainProjection :
      exactCarrierMixingTheoremWitness
      ≡
      Exact.CKMExactWitnessChain.carrierMixingTheorem exactWitnessChain

    exactUnitarityResidualWitness :
      Exact.UnitarityResidualWitness

    exactUnitarityResidualWitnessIsChainProjection :
      exactUnitarityResidualWitness
      ≡
      Exact.CKMExactWitnessChain.unitarityResidual exactWitnessChain

    higgsAdapter4BoundaryWitness :
      Bool

    higgsAdapter4BoundaryWitnessIsTrue :
      higgsAdapter4BoundaryWitness ≡ true

    gate7BridgeStillFailClosed :
      Bool

    gate7BridgeStillFailClosedIsFalse :
      gate7BridgeStillFailClosed ≡ false

    bridgeBoundary :
      List String

open CKMCarrierMixingGate7ExactBridgeReceipt public

canonicalCKMCarrierMixingGate7ExactBridgeReceipt :
  CKMCarrierMixingGate7ExactBridgeReceipt
canonicalCKMCarrierMixingGate7ExactBridgeReceipt = record
  { exactWitnessChain =
      Exact.canonicalCKMExactWitnessChain
  ; exactWitnessChainIsCanonical =
      refl
  ; exactCarrierMixingTheoremWitness =
      canonicalCKMExactCarrierMixingTheoremWitness
  ; exactCarrierMixingTheoremWitnessIsChainProjection =
      refl
  ; exactUnitarityResidualWitness =
      Exact.canonicalUnitarityResidualWitness
  ; exactUnitarityResidualWitnessIsChainProjection =
      refl
  ; higgsAdapter4BoundaryWitness =
      canonicalCKMHiggsAdapter4BoundaryWitness
  ; higgsAdapter4BoundaryWitnessIsTrue =
      refl
  ; gate7BridgeStillFailClosed =
      false
  ; gate7BridgeStillFailClosedIsFalse =
      refl
  ; bridgeBoundary =
      "The exact carrier-mixing witness chain is threaded through the Gate 7 receipt surface"
      ∷ "Carrier-mixing theorem and unitarity residual are consumed from the exact chain, but the physical off-diagonal frontier stays open"
      ∷ "The Higgs adapter4 boundary bit is retained as an explicit typed witness"
      ∷ "No promotion is claimed from the exact bridge"
      ∷ []
  }

record PhysicalCarrierMixingBridge : Setω where
  field
    entryFieldBridge :
      Field.PhysicalCKMEntryFieldBridge

    exactWitnessChain :
      Exact.CKMExactWitnessChain

    froggattNielsenWitness :
      FN.FroggattNielsenWitness

    wolfensteinWitness :
      Wolf.WolfensteinCKMWitness

    bridgeBoundary :
      String

open PhysicalCarrierMixingBridge public

canonicalPhysicalCarrierMixingBridge : PhysicalCarrierMixingBridge
canonicalPhysicalCarrierMixingBridge =
  record
    { entryFieldBridge = Field.canonicalPhysicalCKMEntryFieldBridge
    ; exactWitnessChain = Exact.canonicalCKMExactWitnessChain
    ; froggattNielsenWitness = FN.canonicalFroggattNielsenWitness
    ; wolfensteinWitness = Wolf.canonicalWolfensteinCKMWitness
    ; bridgeBoundary =
        "CKM carrier mixing now has concrete FN and Wolfenstein bridge data, but the fail-closed frontier remains explicit"
    }
