module DASHI.Physics.Chemistry.AmmoniaMonster3BRepresentationNativeCorrectionExact where

------------------------------------------------------------------------
-- REPRESENTATION-NATIVE CORRECTION FOR THE NH3 / MONSTER-3B 369 LANE
--
-- The exact finite chart
--
--   ZetaModelBasis = X6 x Fin90
--     <-> Kernel6 x (Completed10 x T^2)
--
-- is a theorem about BASIS LABELS / finite model coordinates.  It is not a
-- bijection between those 65610 labels and every vector of the literal linear
-- W_zeta eigenspace.  This module composes the native-369 chart with the
-- corrected `ActualZetaBasisRecognition` target and keeps the independent
-- representation-native H_zeta / S_zeta same-object obligations explicit.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierExact as Native369
import DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionExact as Basis
import DASHI.Moonshine.Monster3BProofRelevantRecognitionHardeningExact as Hardening
import DASHI.Moonshine.Monster3BHZetaCharacterTransportCompilerExact as HZetaCompiler

actualBasisToNative369 :
  ∀ {LiteralZetaSector : Set} →
  (recognition : Basis.ActualZetaBasisRecognition LiteralZetaSector) →
  Basis.ActualBasisLabel recognition →
  Native369.Native369ZetaCoordinate
actualBasisToNative369 recognition basis =
  Native369.modelToNative369 (Basis.toModelBasis recognition basis)

native369ToActualBasis :
  ∀ {LiteralZetaSector : Set} →
  (recognition : Basis.ActualZetaBasisRecognition LiteralZetaSector) →
  Native369.Native369ZetaCoordinate →
  Basis.ActualBasisLabel recognition
native369ToActualBasis recognition native =
  Basis.fromModelBasis recognition (Native369.native369ToModel native)

nativeAfterActualBasis :
  ∀ {LiteralZetaSector : Set}
    (recognition : Basis.ActualZetaBasisRecognition LiteralZetaSector) →
    (basis : Basis.ActualBasisLabel recognition) →
  native369ToActualBasis recognition (actualBasisToNative369 recognition basis)
  ≡ basis
nativeAfterActualBasis recognition basis =
  trans
    (cong (Basis.fromModelBasis recognition)
      (Native369.model369RoundTrip (Basis.toModelBasis recognition basis)))
    (Basis.fromAfterTo recognition basis)

actualBasisAfterNative :
  ∀ {LiteralZetaSector : Set}
    (recognition : Basis.ActualZetaBasisRecognition LiteralZetaSector) →
    (native : Native369.Native369ZetaCoordinate) →
  actualBasisToNative369 recognition (native369ToActualBasis recognition native)
  ≡ native
actualBasisAfterNative recognition native =
  trans
    (cong Native369.modelToNative369
      (Basis.toAfterFrom recognition (Native369.native369ToModel native)))
    (Native369.native369RoundTrip native)

record Native369ActualBasisChart (LiteralZetaSector : Set) : Set where
  constructor native369-actual-basis-chart
  field
    recognition : Basis.ActualZetaBasisRecognition LiteralZetaSector
    recognitionPaid : Hardening.PaidActualZetaBasisRecognition recognition

open Native369ActualBasisChart public

basisChartToNative :
  ∀ {LiteralZetaSector : Set} →
  (chart : Native369ActualBasisChart LiteralZetaSector) →
  Basis.ActualBasisLabel (recognition chart) →
  Native369.Native369ZetaCoordinate
basisChartToNative chart = actualBasisToNative369 (recognition chart)

------------------------------------------------------------------------
-- Physical promotion is a one-way same-object attachment plus action
-- equivariance.  A physical NH3 carrier need not be cardinality-equal to the
-- whole Monster basis, so no artificial bijection is demanded here.
------------------------------------------------------------------------

record PhysicalNH3MonsterBasisAttachment
    (NH3State LiteralZetaSector : Set) : Set₁ where
  field
    basisChart : Native369ActualBasisChart LiteralZetaSector
    nh3ToMonsterBasis :
      NH3State → Basis.ActualBasisLabel (recognition basisChart)

    Action : Set
    nh3Action : Action → NH3State → NH3State
    monsterBasisAction :
      Action →
      Basis.ActualBasisLabel (recognition basisChart) →
      Basis.ActualBasisLabel (recognition basisChart)

    actionIntertwines :
      (action : Action) →
      (state : NH3State) →
      nh3ToMonsterBasis (nh3Action action state)
      ≡ monsterBasisAction action (nh3ToMonsterBasis state)

    PhysicalSameObjectAuthority : Set
    physicalSameObjectAuthorityWitness : PhysicalSameObjectAuthority

open PhysicalNH3MonsterBasisAttachment public

physicalNH3ToNative369 :
  ∀ {NH3State LiteralZetaSector : Set} →
  (attachment : PhysicalNH3MonsterBasisAttachment NH3State LiteralZetaSector) →
  NH3State → Native369.Native369ZetaCoordinate
physicalNH3ToNative369 attachment state =
  basisChartToNative (basisChart attachment) (nh3ToMonsterBasis attachment state)

------------------------------------------------------------------------
-- Wrong-type firewalls.
------------------------------------------------------------------------

data FiniteNative369ChartCreatesWholeVOAStateBijection : Set where
data C3PhaseCreatesMonsterModuleIntertwiner : Set where
data BasisRecognitionCreatesHZetaSameObjectRecognition : Set where
data CharacterCompilerCreatesConcreteCharacterTransport : Set where
data PhaseBijectionCreatesPhysicalNH3BasisAttachment : Set where

finiteChartDoesNotCreateWholeVOAStateBijection :
  FiniteNative369ChartCreatesWholeVOAStateBijection → ⊥
finiteChartDoesNotCreateWholeVOAStateBijection ()

phaseDoesNotCreateMonsterModuleIntertwiner :
  C3PhaseCreatesMonsterModuleIntertwiner → ⊥
phaseDoesNotCreateMonsterModuleIntertwiner ()

basisRecognitionDoesNotCreateHZetaSameObjectRecognition :
  BasisRecognitionCreatesHZetaSameObjectRecognition → ⊥
basisRecognitionDoesNotCreateHZetaSameObjectRecognition ()

characterCompilerDoesNotCreateConcreteTransport :
  CharacterCompilerCreatesConcreteCharacterTransport → ⊥
characterCompilerDoesNotCreateConcreteTransport ()

phaseBijectionDoesNotCreatePhysicalAttachment :
  PhaseBijectionCreatesPhysicalNH3BasisAttachment → ⊥
phaseBijectionDoesNotCreatePhysicalAttachment ()

------------------------------------------------------------------------
-- Machine-readable current status.
------------------------------------------------------------------------

record RepresentationNativeCorrectionBoundary : Set where
  constructor representation-native-correction-boundary
  field
    native369FiniteChartIsBasisLabelChart : Bool
    native369FiniteChartIsWholeVOAStateBijection : Bool
    actualBasisRecognitionComposesWithNative369 : Bool
    legacyFiniteActualSectorRecognitionPaysLinearVOARecognition : Bool
    proofRelevantBasisRecognitionWrapperAvailable : Bool
    proofRelevantHZetaRecognitionWrapperAvailable : Bool
    hZetaCharacterTransportCompilerAvailable : Bool
    proofRelevantPhysicalNH3BasisAttachmentTyped : Bool
    actualHZetaSameObjectRecognitionPaid : Bool
    actualLinearHomSpacePaid : Bool
    physicalNH3ToMonsterLinearStatePaid : Bool

open RepresentationNativeCorrectionBoundary public

canonicalRepresentationNativeCorrectionBoundary :
  RepresentationNativeCorrectionBoundary
canonicalRepresentationNativeCorrectionBoundary =
  representation-native-correction-boundary
    true
    false
    true
    false
    true
    true
    true
    true
    false
    false
    false
