module DASHI.Physics.Closure.ExtremalFrobeniusMonsterAuthorityBoundary where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import Ontology.GodelLattice as GL
import DASHI.Physics.Moonshine.DASHIMonsterVOAUniquenessReceipt as Unique
import DASHI.Physics.Moonshine.DongLiMasonOrbifoldReceiptSurface as DLM
import DASHI.Physics.Moonshine.PrimeLaneVOAEquivalenceReceiptSurface as Equiv

------------------------------------------------------------------------
-- Extremal Frobenius / Monster boundary.
--
-- This module records the last honest gap in the orbit-count bridge:
--
--   Vec15 extremal orbit count + a distinguished vacuum target is not the
--   FLM Monster module V^natural unless an external graded module
--   isomorphism authority is supplied.
--
-- Existing FLM and EMS authority receipts are consumed as Monster-VOA and
-- c=24 uniqueness inputs.  They do not construct the missing graded
-- isomorphism from the DASHI Vec15 extremal Frobenius target to V^natural.

data ExtremalFrobeniusMonsterBoundaryStatus : Set where
  orbitCountVacuumToVNaturalBlockedByGradedIsomorphismAuthority :
    ExtremalFrobeniusMonsterBoundaryStatus

data ExtremalFrobeniusMonsterPromotionAuthorityToken : Set where

data ExtremalFrobeniusMonsterActionAuthorityToken : Set where

data ExtremalFrobeniusInternalCountTarget : Set where
  vec15ExtremalOrbitCountPlusVacuumTarget :
    ExtremalFrobeniusInternalCountTarget

data ExtremalFrobeniusVacuumTarget : Set where
  extremalFrobeniusVacuumTarget :
    ExtremalFrobeniusVacuumTarget

data ExtremalFrobeniusGradedIsomorphismAuthorityState : Set where
  missingExternalGradedModuleIsomorphismAuthority :
    ExtremalFrobeniusGradedIsomorphismAuthorityState

data ExtremalFrobeniusMonsterBoundary : Set where
  boundaryOrbitCountPlusVacuumIsInternalTargetOnly :
    ExtremalFrobeniusMonsterBoundary

  boundaryVNaturalTargetComesFromFLMAuthorityReceipt :
    ExtremalFrobeniusMonsterBoundary

  boundaryEMSAuthorityIsC24UniquenessOnly :
    ExtremalFrobeniusMonsterBoundary

  boundaryNoGradedModuleIsomorphismConstructed :
    ExtremalFrobeniusMonsterBoundary

  boundaryNoMonsterActionConstructed :
    ExtremalFrobeniusMonsterBoundary

  boundaryNoVOAConstructionInThisModule :
    ExtremalFrobeniusMonsterBoundary

  boundaryNoPromotionTokenSet :
    ExtremalFrobeniusMonsterBoundary

  boundaryNoTerminalClaimPromotion :
    ExtremalFrobeniusMonsterBoundary

canonicalExtremalFrobeniusMonsterBoundaries :
  List ExtremalFrobeniusMonsterBoundary
canonicalExtremalFrobeniusMonsterBoundaries =
  boundaryOrbitCountPlusVacuumIsInternalTargetOnly
  ∷ boundaryVNaturalTargetComesFromFLMAuthorityReceipt
  ∷ boundaryEMSAuthorityIsC24UniquenessOnly
  ∷ boundaryNoGradedModuleIsomorphismConstructed
  ∷ boundaryNoMonsterActionConstructed
  ∷ boundaryNoVOAConstructionInThisModule
  ∷ boundaryNoPromotionTokenSet
  ∷ boundaryNoTerminalClaimPromotion
  ∷ []

record Vec15ExtremalOrbitCountWithVacuumTarget : Setω where
  field
    countCarrier :
      Set

    countCarrierIsVec15Nat :
      countCarrier ≡ GL.Vec15 Nat

    internalCountTarget :
      ExtremalFrobeniusInternalCountTarget

    vacuumTarget :
      ExtremalFrobeniusVacuumTarget

    vacuumIncluded :
      Bool

    vacuumIncludedIsTrue :
      vacuumIncluded ≡ true

    identifiesVNatural :
      Bool

    identifiesVNaturalIsFalse :
      identifiesVNatural ≡ false

    targetBoundary :
      List String

open Vec15ExtremalOrbitCountWithVacuumTarget public

canonicalVec15ExtremalOrbitCountWithVacuumTarget :
  Vec15ExtremalOrbitCountWithVacuumTarget
canonicalVec15ExtremalOrbitCountWithVacuumTarget =
  record
    { countCarrier =
        GL.Vec15 Nat
    ; countCarrierIsVec15Nat =
        refl
    ; internalCountTarget =
        vec15ExtremalOrbitCountPlusVacuumTarget
    ; vacuumTarget =
        extremalFrobeniusVacuumTarget
    ; vacuumIncluded =
        true
    ; vacuumIncludedIsTrue =
        refl
    ; identifiesVNatural =
        false
    ; identifiesVNaturalIsFalse =
        refl
    ; targetBoundary =
        "The internal target is a Vec15 Nat extremal orbit-count carrier plus a distinguished vacuum target"
        ∷ "This target does not itself carry a graded Monster-module structure"
        ∷ "This target is not identified with V^natural without an external graded module isomorphism authority"
        ∷ []
    }

record ExternalGradedModuleIsomorphismAuthorityBoundary : Setω where
  field
    internalCountTarget :
      Vec15ExtremalOrbitCountWithVacuumTarget

    monsterVOATarget :
      Unique.MonsterVOATarget

    monsterVOATargetIsFLMVNatural :
      monsterVOATarget ≡ Unique.flmMonsterVOAVNatural

    monsterVOAUniquenessReceipt :
      Unique.DASHIMonsterVOAUniquenessReceipt

    flmAuthority :
      Unique.DASHIMonsterVOAUniquenessAuthorityReceipt

    flmAuthorityIsExistingReceipt :
      flmAuthority ≡ Unique.flmMonsterVOAConstructionAuthority

    emsAuthority :
      Unique.DASHIMonsterVOAUniquenessAuthorityReceipt

    emsAuthorityIsExistingReceipt :
      emsAuthority
      ≡
      Unique.vanEkerenMollerScheithauer2017C24HolomorphicVOAOrbifoldUniquenessAuthority

    primeLaneVOAEquivalenceSurface :
      Equiv.DASHIPrimeLaneEquivReceiptSurface

    dlmOrbifoldReceiptSurface :
      DLM.DongLiMasonOrbifoldReceiptSurface

    gradedIsomorphismAuthorityState :
      ExtremalFrobeniusGradedIsomorphismAuthorityState

    gradedIsomorphismAuthorityStateIsMissing :
      gradedIsomorphismAuthorityState
      ≡
      missingExternalGradedModuleIsomorphismAuthority

    noTerminalPromotionBoundary :
      List ExtremalFrobeniusMonsterBoundary

    noTerminalPromotionBoundaryIsCanonical :
      noTerminalPromotionBoundary
      ≡
      canonicalExtremalFrobeniusMonsterBoundaries

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    promotionTokenSet :
      Bool

    promotionTokenSetIsFalse :
      promotionTokenSet ≡ false

    monsterActionConstructed :
      Bool

    monsterActionConstructedIsFalse :
      monsterActionConstructed ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    noPromotionWithoutAuthority :
      ExtremalFrobeniusMonsterPromotionAuthorityToken →
      ⊥

    noMonsterActionWithoutAuthority :
      ExtremalFrobeniusMonsterActionAuthorityToken →
      ⊥

    authorityBoundary :
      List String

open ExternalGradedModuleIsomorphismAuthorityBoundary public

canonicalExternalGradedModuleIsomorphismAuthorityBoundary :
  ExternalGradedModuleIsomorphismAuthorityBoundary
canonicalExternalGradedModuleIsomorphismAuthorityBoundary =
  record
    { internalCountTarget =
        canonicalVec15ExtremalOrbitCountWithVacuumTarget
    ; monsterVOATarget =
        Unique.flmMonsterVOAVNatural
    ; monsterVOATargetIsFLMVNatural =
        refl
    ; monsterVOAUniquenessReceipt =
        Unique.canonicalDASHIMonsterVOAUniquenessReceipt
    ; flmAuthority =
        Unique.flmMonsterVOAConstructionAuthority
    ; flmAuthorityIsExistingReceipt =
        refl
    ; emsAuthority =
        Unique.vanEkerenMollerScheithauer2017C24HolomorphicVOAOrbifoldUniquenessAuthority
    ; emsAuthorityIsExistingReceipt =
        refl
    ; primeLaneVOAEquivalenceSurface =
        Equiv.canonicalDASHIPrimeLaneEquivReceiptSurface
    ; dlmOrbifoldReceiptSurface =
        DLM.canonicalDongLiMasonOrbifoldReceiptSurface
    ; gradedIsomorphismAuthorityState =
        missingExternalGradedModuleIsomorphismAuthority
    ; gradedIsomorphismAuthorityStateIsMissing =
        refl
    ; noTerminalPromotionBoundary =
        canonicalExtremalFrobeniusMonsterBoundaries
    ; noTerminalPromotionBoundaryIsCanonical =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; promotionTokenSet =
        false
    ; promotionTokenSetIsFalse =
        refl
    ; monsterActionConstructed =
        false
    ; monsterActionConstructedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; noMonsterActionWithoutAuthority =
        λ ()
    ; authorityBoundary =
        "FLM authority is consumed only as the external construction receipt for V^natural"
        ∷ "EMS authority is consumed only as the external c=24 holomorphic VOA/orbifold uniqueness receipt"
        ∷ "DLM and prime-lane VOA equivalence receipts are retained as existing Moonshine/VOA bridge surfaces"
        ∷ "Vec15 extremal orbit count plus vacuum is not identified with V^natural here"
        ∷ "The missing ingredient is an external graded module isomorphism from the internal Vec15/vacuum target to the FLM Monster module"
        ∷ "This module does not set a promotion token, construct a Monster action, construct a VOA, or promote a terminal claim"
        ∷ []
    }

ExtremalFrobeniusMonsterAuthorityBoundarySurface :
  Setω
ExtremalFrobeniusMonsterAuthorityBoundarySurface =
  ExternalGradedModuleIsomorphismAuthorityBoundary

canonicalExtremalFrobeniusMonsterAuthorityBoundarySurface :
  ExtremalFrobeniusMonsterAuthorityBoundarySurface
canonicalExtremalFrobeniusMonsterAuthorityBoundarySurface =
  canonicalExternalGradedModuleIsomorphismAuthorityBoundary

extremalFrobeniusMonsterTheoremPromoted :
  Bool
extremalFrobeniusMonsterTheoremPromoted =
  theoremPromoted canonicalExternalGradedModuleIsomorphismAuthorityBoundary

extremalFrobeniusMonsterTheoremPromotedIsFalse :
  extremalFrobeniusMonsterTheoremPromoted ≡ false
extremalFrobeniusMonsterTheoremPromotedIsFalse =
  refl

extremalFrobeniusMonsterActionConstructed :
  Bool
extremalFrobeniusMonsterActionConstructed =
  monsterActionConstructed
    canonicalExternalGradedModuleIsomorphismAuthorityBoundary

extremalFrobeniusMonsterActionConstructedIsFalse :
  extremalFrobeniusMonsterActionConstructed ≡ false
extremalFrobeniusMonsterActionConstructedIsFalse =
  refl

extremalFrobeniusMonsterTerminalClaimPromoted :
  Bool
extremalFrobeniusMonsterTerminalClaimPromoted =
  terminalClaimPromoted
    canonicalExternalGradedModuleIsomorphismAuthorityBoundary

extremalFrobeniusMonsterTerminalClaimPromotedIsFalse :
  extremalFrobeniusMonsterTerminalClaimPromoted ≡ false
extremalFrobeniusMonsterTerminalClaimPromotedIsFalse =
  refl
