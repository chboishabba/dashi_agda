module DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierExact where

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Actual
import DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact as Base369
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Multiplicity369
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact as Completed
import DASHI.Physics.Chemistry.Atomic369Kernel6HeisenbergBridgeExact as Kernel369

------------------------------------------------------------------------
-- FULL MONSTER-ZETA MODEL BASIS ON NATIVE 369 CARRIERS
--
-- Existing owners pay both coordinate charts independently:
--
--   atomic/triadic Kernel 6 <-> F3^6 / Heisenberg X6,
--   Fin 90 <-> Completed10 x T^2.
--
-- Their product therefore gives an exact finite-carrier chart
--
--   ZetaModelBasis
--     = X6 x Fin90
--     <-> Kernel6 x CompletedTenTritSquare.
--
-- This removes a structural-coordinate gap.  It does NOT identify any physical
-- NH3 state with a particular point of the native-369 product.
------------------------------------------------------------------------

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

record Native369FineCarrierIsomorphism : Set where
  constructor native369FineCarrierIsomorphism
  field
    toModel : Native369ZetaCoordinate → MonsterZetaModelBasis
    fromModel : MonsterZetaModelBasis → Native369ZetaCoordinate
    fromAfterTo :
      (native : Native369ZetaCoordinate) → fromModel (toModel native) ≡ native
    toAfterFrom :
      (basis : MonsterZetaModelBasis) → toModel (fromModel basis) ≡ basis

open Native369FineCarrierIsomorphism public

canonicalNative369FineCarrierIsomorphism : Native369FineCarrierIsomorphism
canonicalNative369FineCarrierIsomorphism =
  native369FineCarrierIsomorphism
    native369ToModel
    modelToNative369
    native369RoundTrip
    model369RoundTrip

------------------------------------------------------------------------
-- Any already-owned literal zeta recognition now gives a compiler from the
-- native-369 fine coordinate directly into that literal recognized sector.
------------------------------------------------------------------------

native369ToActualZeta :
  ∀ {ActualSector : Set} →
  Actual.ActualZetaSectorRecognition ActualSector →
  Native369ZetaCoordinate → ActualSector
native369ToActualZeta recognition native =
  Actual.fromModel recognition (native369ToModel native)

actualZetaToNative369 :
  ∀ {ActualSector : Set} →
  Actual.ActualZetaSectorRecognition ActualSector →
  ActualSector → Native369ZetaCoordinate
actualZetaToNative369 recognition state =
  modelToNative369 (Actual.toModel recognition state)

native369ActualRoundTrip :
  ∀ {ActualSector : Set}
    (recognition : Actual.ActualZetaSectorRecognition ActualSector) →
    (native : Native369ZetaCoordinate) →
  actualZetaToNative369 recognition (native369ToActualZeta recognition native)
  ≡ native
native369ActualRoundTrip recognition native =
  let modelEq = Actual.toAfterFrom recognition (native369ToModel native)
  in
  trans
    (cong modelToNative369 modelEq)
    (native369RoundTrip native)

actualNative369RoundTrip :
  ∀ {ActualSector : Set}
    (recognition : Actual.ActualZetaSectorRecognition ActualSector) →
    (state : ActualSector) →
  native369ToActualZeta recognition (actualZetaToNative369 recognition state)
  ≡ state
actualNative369RoundTrip recognition state =
  let modelRound = model369RoundTrip (Actual.toModel recognition state)
  in
  trans
    (cong (Actual.fromModel recognition) modelRound)
    (Actual.fromAfterTo recognition state)

actualRecognitionToBase369 :
  ∀ {ActualSector : Set} →
  Actual.ActualZetaSectorRecognition ActualSector →
  Base369.ActualBase369SectorRecognition ActualSector
actualRecognitionToBase369 = Base369.composeActualRecognitionWithBase369

------------------------------------------------------------------------
-- A physical chemistry attachment, deliberately left proof-relevant.
------------------------------------------------------------------------

record PhysicalNH3Native369FineCoordinate (NH3State : Set) : Set₁ where
  constructor physicalNH3Native369FineCoordinate
  field
    coordinate : NH3State → Native369ZetaCoordinate
    coordinateAuthority : Set
    sameObjectWithElectronicState : Set
    interpretation : String

open PhysicalNH3Native369FineCoordinate public

compilePhysicalCoordinateToMonsterModel :
  ∀ {NH3State : Set} →
  PhysicalNH3Native369FineCoordinate NH3State →
  NH3State → MonsterZetaModelBasis
compilePhysicalCoordinateToMonsterModel attachment state =
  native369ToModel (coordinate attachment state)

compilePhysicalCoordinateToActualZeta :
  ∀ {NH3State ActualSector : Set} →
  Actual.ActualZetaSectorRecognition ActualSector →
  PhysicalNH3Native369FineCoordinate NH3State →
  NH3State → ActualSector
compilePhysicalCoordinateToActualZeta recognition attachment state =
  native369ToActualZeta recognition (coordinate attachment state)

record Native369FineCarrierBoundary : Set where
  constructor native369FineCarrierBoundary
  field
    atomicKernel6ToHeisenbergX6Paid : Bool
    atomicKernel6ToHeisenbergX6PaidIsTrue : atomicKernel6ToHeisenbergX6Paid ≡ true
    fin90ToCompletedTenTritSquarePaid : Bool
    fin90ToCompletedTenTritSquarePaidIsTrue : fin90ToCompletedTenTritSquarePaid ≡ true
    fullMonsterZetaModelHasNative369CarrierChart : Bool
    fullMonsterZetaModelHasNative369CarrierChartIsTrue : fullMonsterZetaModelHasNative369CarrierChart ≡ true
    actualZetaRecognitionComposesWithNative369Chart : Bool
    actualZetaRecognitionComposesWithNative369ChartIsTrue :
      actualZetaRecognitionComposesWithNative369Chart ≡ true
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
    "The full Monster-zeta finite model basis is exactly charted by native 369 carriers Kernel6 x (Completed10 x T^2), and any existing ActualZetaSectorRecognition composes with this chart by exact two-sided round trips. What remains is physical same-object assignment/equivariance, not a missing finite coordinate system."
