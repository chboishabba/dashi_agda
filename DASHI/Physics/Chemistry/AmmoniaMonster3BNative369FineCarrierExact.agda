module DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierExact where

------------------------------------------------------------------------
-- NATIVE-369 CHART OF THE FINITE MONSTER-ZETA BASIS-LABEL MODEL
--
-- This owner proves only the exact finite coordinate theorem
--
--   ZetaModelBasis = X6 x Fin90
--     <-> Kernel6 x (Completed10 x T^2).
--
-- It does NOT identify those 65610 labels with every vector of the literal
-- linear W_zeta eigenspace.  Representation-native inclusion into W_zeta is
-- owned separately by `Monster3BWZetaBasisVectorRecognitionCorrectionExact`
-- and the H_zeta/S_zeta linear same-object route.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Multiplicity369
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact as Completed
import DASHI.Physics.Chemistry.Atomic369Kernel6HeisenbergBridgeExact as Kernel369

MonsterZetaModelBasis : Set
MonsterZetaModelBasis = Model.ZetaModelBasis

Native369ZetaCoordinate : Set
Native369ZetaCoordinate =
  Kernel369.Kernel6 × Completed.CompletedTenTritSquare

native369ToModel : Native369ZetaCoordinate → MonsterZetaModelBasis
native369ToModel (kernel , multiplicity) =
  Model.zetaBasis
    (Kernel369.kernel6ToX6 kernel)
    (Multiplicity369.completedToFin90 multiplicity)

modelToNative369 : MonsterZetaModelBasis → Native369ZetaCoordinate
modelToNative369 basis =
  Kernel369.x6ToKernel6 (Model.weightPosition basis) ,
  Multiplicity369.fin90ToCompleted (Model.multiplicityCoordinate basis)

native369RoundTrip :
  (native : Native369ZetaCoordinate) →
  modelToNative369 (native369ToModel native) ≡ native
native369RoundTrip (kernel , multiplicity)
  rewrite Kernel369.kernel6RoundTrip kernel
        | Multiplicity369.fin90AfterCompleted multiplicity = refl

model369RoundTrip :
  (basis : MonsterZetaModelBasis) →
  native369ToModel (modelToNative369 basis) ≡ basis
model369RoundTrip (Model.zetaBasis position multiplicity)
  rewrite Kernel369.x6RoundTrip position
        | Multiplicity369.completedAfterFin90 multiplicity = refl

record Native369BasisLabelIsomorphism : Set where
  constructor native369BasisLabelIsomorphism
  field
    toModelBasis : Native369ZetaCoordinate → MonsterZetaModelBasis
    fromModelBasis : MonsterZetaModelBasis → Native369ZetaCoordinate
    fromAfterTo :
      (native : Native369ZetaCoordinate) →
      fromModelBasis (toModelBasis native) ≡ native
    toAfterFrom :
      (basis : MonsterZetaModelBasis) →
      toModelBasis (fromModelBasis basis) ≡ basis

open Native369BasisLabelIsomorphism public

canonicalNative369BasisLabelIsomorphism : Native369BasisLabelIsomorphism
canonicalNative369BasisLabelIsomorphism =
  native369BasisLabelIsomorphism
    native369ToModel modelToNative369 native369RoundTrip model369RoundTrip

-- Backwards-compatible type/value names retained for downstream finite-model
-- consumers.  Their semantics are explicitly basis-label only.
Native369FineCarrierIsomorphism : Set
Native369FineCarrierIsomorphism = Native369BasisLabelIsomorphism

canonicalNative369FineCarrierIsomorphism : Native369FineCarrierIsomorphism
canonicalNative369FineCarrierIsomorphism = canonicalNative369BasisLabelIsomorphism

record PhysicalNH3Native369BasisCoordinate (NH3State : Set) : Set₁ where
  constructor physicalNH3Native369BasisCoordinate
  field
    coordinate : NH3State → Native369ZetaCoordinate
    CoordinateAuthority : Set
    coordinateAuthorityWitness : CoordinateAuthority
    SameObjectWithElectronicState : Set
    sameObjectWithElectronicStateWitness : SameObjectWithElectronicState
    interpretation : String

open PhysicalNH3Native369BasisCoordinate public

compilePhysicalCoordinateToMonsterModelBasis :
  ∀ {NH3State : Set} →
  PhysicalNH3Native369BasisCoordinate NH3State →
  NH3State → MonsterZetaModelBasis
compilePhysicalCoordinateToMonsterModelBasis attachment state =
  native369ToModel (coordinate attachment state)

------------------------------------------------------------------------
-- Wrong-type firewalls.
------------------------------------------------------------------------

data FiniteBasisChartCreatesWholeVOAStateBijection : Set where
data FiniteBasisChartCreatesPhysicalMonsterAction : Set where

data FiniteBasisCoordinateCreatesPhysicalAuthority : Set where

finiteBasisChartDoesNotCreateWholeVOAStateBijection :
  FiniteBasisChartCreatesWholeVOAStateBijection → ⊥
finiteBasisChartDoesNotCreateWholeVOAStateBijection ()

finiteBasisChartDoesNotCreatePhysicalMonsterAction :
  FiniteBasisChartCreatesPhysicalMonsterAction → ⊥
finiteBasisChartDoesNotCreatePhysicalMonsterAction ()

finiteBasisCoordinateDoesNotCreatePhysicalAuthority :
  FiniteBasisCoordinateCreatesPhysicalAuthority → ⊥
finiteBasisCoordinateDoesNotCreatePhysicalAuthority ()

record Native369FineCarrierBoundary : Set where
  constructor native369FineCarrierBoundary
  field
    atomicKernel6ToHeisenbergX6Paid : Bool
    atomicKernel6ToHeisenbergX6PaidIsTrue : atomicKernel6ToHeisenbergX6Paid ≡ true
    fin90ToCompletedTenTritSquarePaid : Bool
    fin90ToCompletedTenTritSquarePaidIsTrue : fin90ToCompletedTenTritSquarePaid ≡ true
    fullMonsterZetaModelHasNative369CarrierChart : Bool
    fullMonsterZetaModelHasNative369CarrierChartIsTrue :
      fullMonsterZetaModelHasNative369CarrierChart ≡ true
    native369FiniteChartIsBasisLabelChart : Bool
    native369FiniteChartIsBasisLabelChartIsTrue :
      native369FiniteChartIsBasisLabelChart ≡ true
    native369FiniteChartIsWholeVOAStateBijection : Bool
    native369FiniteChartIsWholeVOAStateBijectionIsFalse :
      native369FiniteChartIsWholeVOAStateBijection ≡ false
    physicalNH3StateToNative369FineCoordinatePaid : Bool
    physicalNH3StateToNative369FineCoordinatePaidIsFalse :
      physicalNH3StateToNative369FineCoordinatePaid ≡ false
    native369CarrierChartCreatesPhysicalMonsterAction : Bool
    native369CarrierChartCreatesPhysicalMonsterActionIsFalse :
      native369CarrierChartCreatesPhysicalMonsterAction ≡ false
    interpretation : String

open Native369FineCarrierBoundary public

canonicalNative369FineCarrierBoundary : Native369FineCarrierBoundary
canonicalNative369FineCarrierBoundary =
  native369FineCarrierBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Kernel6 x (Completed10 x T^2) is exactly the native-369 chart of the finite Monster-zeta model BASIS LABELS X6 x Fin90. It is not a bijection with every vector in the literal linear W_zeta eigenspace. Actual representation-native basis inclusion, H_zeta/S_zeta same-object recognition, physical NH3 assignment and action equivariance remain separate proof-relevant payments."
