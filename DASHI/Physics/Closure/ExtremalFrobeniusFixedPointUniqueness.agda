module DASHI.Physics.Closure.ExtremalFrobeniusFixedPointUniqueness where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import Ontology.GodelLattice as GL
import DASHI.Physics.Closure.ExtremalFrobeniusVacuumFixedPoint as Vacuum

------------------------------------------------------------------------
-- Extremal vacuum uniqueness boundary.
--
-- The +1 in `196883 + 1` is the distinguished zero FactorVec vacuum.
-- `ExtremalFrobeniusVacuumFixedPoint` proves that this zero point is fixed
-- by the three currently modeled extremal actions.  Uniqueness requires an
-- additional finite-field/primitive-root law: every point fixed by all
-- primitive non-identity p47/p59/p71 lane actions is the zero vector.

zeroVacuum15 :
  GL.Vec15 Nat
zeroVacuum15 =
  Vacuum.zeroVec15

zeroVacuum15-is-zero :
  zeroVacuum15 ≡ Vacuum.zeroVec15
zeroVacuum15-is-zero =
  refl

record FixedPointFreeExtremalLaneAction : Set₁ where
  field
    actionSurface :
      Vacuum.ExtremalFrobeniusActionSurface

    fixedByAllExtremalImpliesZero :
      (v : GL.FactorVec) →
      Vacuum.p47Action actionSurface v ≡ v →
      Vacuum.p59Action actionSurface v ≡ v →
      Vacuum.p71Action actionSurface v ≡ v →
      v ≡ Vacuum.zeroFactorVec

    missingIfAbsent :
      List String

VacuumUniqueTarget : Set₁
VacuumUniqueTarget =
  (law : FixedPointFreeExtremalLaneAction) →
  (v : GL.FactorVec) →
  Vacuum.p47Action (FixedPointFreeExtremalLaneAction.actionSurface law) v ≡ v →
  Vacuum.p59Action (FixedPointFreeExtremalLaneAction.actionSurface law) v ≡ v →
  Vacuum.p71Action (FixedPointFreeExtremalLaneAction.actionSurface law) v ≡ v →
  v ≡ Vacuum.zeroFactorVec

vacuumUnique : VacuumUniqueTarget
vacuumUnique law v p47Fixed p59Fixed p71Fixed =
  FixedPointFreeExtremalLaneAction.fixedByAllExtremalImpliesZero
    law
    v
    p47Fixed
    p59Fixed
    p71Fixed

data ExtremalFrobeniusFixedPointUniquenessMissing : Set where
  missingFiniteFieldPrimitiveRootSemantics :
    ExtremalFrobeniusFixedPointUniquenessMissing

  missingPrimitiveNonIdentityFrobeniusLaneAction :
    ExtremalFrobeniusFixedPointUniquenessMissing

  missingFixedPointFreeExtremalLaneLaw :
    ExtremalFrobeniusFixedPointUniquenessMissing

canonicalExtremalFrobeniusFixedPointUniquenessMissing :
  List ExtremalFrobeniusFixedPointUniquenessMissing
canonicalExtremalFrobeniusFixedPointUniquenessMissing =
  missingFiniteFieldPrimitiveRootSemantics
  ∷ missingPrimitiveNonIdentityFrobeniusLaneAction
  ∷ missingFixedPointFreeExtremalLaneLaw
  ∷ []

record ExtremalFrobeniusFixedPointUniquenessReceipt : Set₂ where
  field
    fixedVacuumSlice :
      Vacuum.ExtremalFrobeniusVacuumFixedPointSlice

    fixedVacuumSliceIsCanonical :
      fixedVacuumSlice ≡ Vacuum.canonicalExtremalFrobeniusVacuumFixedPointSlice

    vacuumCarrier :
      GL.Vec15 Nat

    vacuumCarrierIsZero :
      vacuumCarrier ≡ Vacuum.zeroVec15

    requiredActionLaw :
      Set₁

    requiredActionLawIsFixedPointFreeExtremalLaneAction :
      requiredActionLaw ≡ FixedPointFreeExtremalLaneAction

    conditionalVacuumUniqueTarget :
      Set₁

    conditionalVacuumUniqueTargetIsCanonical :
      conditionalVacuumUniqueTarget ≡ VacuumUniqueTarget

    conditionalVacuumUnique :
      conditionalVacuumUniqueTarget

    exactMissingInhabitants :
      List ExtremalFrobeniusFixedPointUniquenessMissing

    exactMissingInhabitantsAreCanonical :
      exactMissingInhabitants
        ≡
      canonicalExtremalFrobeniusFixedPointUniquenessMissing

    firstMissingInhabitant :
      ExtremalFrobeniusFixedPointUniquenessMissing

    firstMissingInhabitantIsFiniteFieldSemantics :
      firstMissingInhabitant
        ≡
      missingFiniteFieldPrimitiveRootSemantics

    fixedPointUniquenessPromoted :
      Bool

    fixedPointUniquenessPromotedIsFalse :
      fixedPointUniquenessPromoted ≡ false

    receiptBoundary :
      List String

canonicalExtremalFrobeniusFixedPointUniquenessReceipt :
  ExtremalFrobeniusFixedPointUniquenessReceipt
canonicalExtremalFrobeniusFixedPointUniquenessReceipt =
  record
    { fixedVacuumSlice =
        Vacuum.canonicalExtremalFrobeniusVacuumFixedPointSlice
    ; fixedVacuumSliceIsCanonical =
        refl
    ; vacuumCarrier =
        Vacuum.zeroVec15
    ; vacuumCarrierIsZero =
        refl
    ; requiredActionLaw =
        FixedPointFreeExtremalLaneAction
    ; requiredActionLawIsFixedPointFreeExtremalLaneAction =
        refl
    ; conditionalVacuumUniqueTarget =
        VacuumUniqueTarget
    ; conditionalVacuumUniqueTargetIsCanonical =
        refl
    ; conditionalVacuumUnique =
        vacuumUnique
    ; exactMissingInhabitants =
        canonicalExtremalFrobeniusFixedPointUniquenessMissing
    ; exactMissingInhabitantsAreCanonical =
        refl
    ; firstMissingInhabitant =
        missingFiniteFieldPrimitiveRootSemantics
    ; firstMissingInhabitantIsFiniteFieldSemantics =
        refl
    ; fixedPointUniquenessPromoted =
        false
    ; fixedPointUniquenessPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The +1 vacuum is the zero FactorVec fixed by the three extremal actions"
        ∷ "vacuumUnique is conditionally proved from FixedPointFreeExtremalLaneAction.fixedByAllExtremalImpliesZero"
        ∷ "The repo does not currently expose finite-field primitive-root semantics or a primitive non-identity Frobenius/lane action on Vec15"
        ∷ "Accepted fail-closed blocker: inhabit FixedPointFreeExtremalLaneAction with a real primitive non-identity Frobenius/lane action and a proof that only zero is fixed by all extremal actions"
        ∷ "No postulate is introduced and no promotion flag is flipped"
        ∷ []
    }

extremalFrobeniusFixedPointUniquenessFirstMissing :
  ExtremalFrobeniusFixedPointUniquenessReceipt.firstMissingInhabitant
    canonicalExtremalFrobeniusFixedPointUniquenessReceipt
  ≡
  missingFiniteFieldPrimitiveRootSemantics
extremalFrobeniusFixedPointUniquenessFirstMissing =
  refl

extremalFrobeniusFixedPointUniquenessNotPromoted :
  ExtremalFrobeniusFixedPointUniquenessReceipt.fixedPointUniquenessPromoted
    canonicalExtremalFrobeniusFixedPointUniquenessReceipt
  ≡
  false
extremalFrobeniusFixedPointUniquenessNotPromoted =
  refl
