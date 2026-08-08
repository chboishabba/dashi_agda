module DASHI.Moonshine.Monster3BModelProjectorResolutionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- Finish the projector calculation on the concrete finite model
--
--     X x Fin 90,       X = F_3^6.
--
-- Every basis vector has one distinguished weight.  Its projector coefficient
-- is one, every explicitly different weight has coefficient zero, projector
-- coefficients are idempotent, and simultaneous translation preserves the
-- coefficient.  This is the complete pointwise direct-sum resolution needed
-- on the model carrier; promotion to the actual Monster zeta-sector still
-- requires an intertwiner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BFiniteWeightProjectorExact as Projector

------------------------------------------------------------------------
-- Pointwise support and orthogonality.
------------------------------------------------------------------------

DifferentWeight : H.X6 → H.X6 → Set
DifferentWeight left right = Projector.x6Equal left right ≡ false

projectorCoefficientOnOwnWeight :
  (basis : Model.ZetaModelBasis) →
  Projector.weightProjectorCoefficient
    (Model.weightPosition basis) basis
  ≡ 1
projectorCoefficientOnOwnWeight
    (Model.zetaBasis position multiplicity) =
  Projector.weightProjectorOwnWeight position multiplicity

explicitlyDifferentWeightAnnihilatesBasis :
  (selected : H.X6) →
  (basis : Model.ZetaModelBasis) →
  DifferentWeight selected (Model.weightPosition basis) →
  Projector.weightProjectorCoefficient selected basis ≡ 0
explicitlyDifferentWeightAnnihilatesBasis selected basis different
  rewrite different = refl

projectorProductCoefficient :
  H.X6 → H.X6 → Model.ZetaModelBasis → Nat
projectorProductCoefficient left right basis =
  Projector.weightProjectorCoefficient left basis
  * Projector.weightProjectorCoefficient right basis

ownAndDifferentProjectorsArePointwiseOrthogonal :
  (selected : H.X6) →
  (basis : Model.ZetaModelBasis) →
  DifferentWeight selected (Model.weightPosition basis) →
  projectorProductCoefficient
    (Model.weightPosition basis) selected basis
  ≡ 0
ownAndDifferentProjectorsArePointwiseOrthogonal selected basis different
  rewrite projectorCoefficientOnOwnWeight basis
        | explicitlyDifferentWeightAnnihilatesBasis selected basis different =
  refl

ownProjectorIsPointwiseIdempotent :
  (basis : Model.ZetaModelBasis) →
  projectorProductCoefficient
    (Model.weightPosition basis)
    (Model.weightPosition basis)
    basis
  ≡ Projector.weightProjectorCoefficient
      (Model.weightPosition basis) basis
ownProjectorIsPointwiseIdempotent basis =
  Projector.weightProjectorCoefficientIdempotent
    (Model.weightPosition basis) basis

------------------------------------------------------------------------
-- Each weight fibre is literally Fin 90.  Encoding and decoding are
-- constructive and do not require a dense matrix.
------------------------------------------------------------------------

ModelWeightFibre : H.X6 → Set
ModelWeightFibre position = Fin 90

includeWeightFibre :
  (position : H.X6) → ModelWeightFibre position → Model.ZetaModelBasis
includeWeightFibre position multiplicity =
  Model.zetaBasis position multiplicity

recoverWeightFibre :
  (position : H.X6) →
  (basis : Model.ZetaModelBasis) →
  Model.weightPosition basis ≡ position →
  ModelWeightFibre position
recoverWeightFibre position basis weightExact =
  Model.multiplicityCoordinate basis

includeThenRecover :
  (position : H.X6) →
  (multiplicity : ModelWeightFibre position) →
  recoverWeightFibre position
    (includeWeightFibre position multiplicity) refl
  ≡ multiplicity
includeThenRecover position multiplicity = refl

modelWeightFibreDimension : Nat
modelWeightFibreDimension = 90

modelWeightFibreDimensionIs90 : modelWeightFibreDimension ≡ 90
modelWeightFibreDimensionIs90 = refl

modelWeightCount : Nat
modelWeightCount = H.schrodingerBasisDimension

modelWeightCountIs729 : modelWeightCount ≡ 729
modelWeightCountIs729 = refl

modelResolutionDimension : Nat
modelResolutionDimension = modelWeightCount * modelWeightFibreDimension

modelResolutionDimensionIs65610 : modelResolutionDimension ≡ 65610
modelResolutionDimensionIs65610 = refl

------------------------------------------------------------------------
-- Translation covariance of the resolved fibres.
------------------------------------------------------------------------

translateFibreBasis :
  H.Axis6 →
  (position : H.X6) →
  ModelWeightFibre position →
  ModelWeightFibre (H.translate H.axis0 position)
translateFibreBasis axis position multiplicity = multiplicity

-- The multiplicity label is untouched by every translation.  The separate
-- position coordinate carries the entire translation action.
translationPreservesMultiplicityCoordinate :
  (axis : H.Axis6) →
  (basis : Model.ZetaModelBasis) →
  Model.multiplicityCoordinate (Model.translatedBasis axis basis)
  ≡ Model.multiplicityCoordinate basis
translationPreservesMultiplicityCoordinate axis
  (Model.zetaBasis position multiplicity) = refl

projectorResolutionTranslationCovariant :
  (axis : H.Axis6) →
  (selected : H.X6) →
  (basis : Model.ZetaModelBasis) →
  Projector.weightProjectorCoefficient
    (H.translate axis selected)
    (Model.translatedBasis axis basis)
  ≡ Projector.weightProjectorCoefficient selected basis
projectorResolutionTranslationCovariant =
  Projector.translatedProjectorCovariant

record ModelProjectorResolution : Set where
  constructor model-projector-resolution
  field
    weightCount : Nat
    fibreDimension : Nat
    totalDimension : Nat
    weightCountExact : weightCount ≡ 729
    fibreDimensionExact : fibreDimension ≡ 90
    totalDimensionExact : totalDimension ≡ 65610
    totalDimensionFactors : totalDimension ≡ weightCount * fibreDimension

    selectedProjectorOwnsBasis :
      (basis : Model.ZetaModelBasis) →
      Projector.weightProjectorCoefficient
        (Model.weightPosition basis) basis
      ≡ 1

    everyDeclaredDifferentProjectorVanishes :
      (selected : H.X6) →
      (basis : Model.ZetaModelBasis) →
      DifferentWeight selected (Model.weightPosition basis) →
      Projector.weightProjectorCoefficient selected basis ≡ 0

open ModelProjectorResolution public

canonicalModelProjectorResolution : ModelProjectorResolution
canonicalModelProjectorResolution =
  model-projector-resolution
    729 90 65610 refl refl refl refl
    projectorCoefficientOnOwnWeight
    explicitlyDifferentWeightAnnihilatesBasis

record ModelToMonsterResolutionBoundary : Set where
  constructor model-to-monster-resolution-boundary
  field
    completeModelPointwiseResolutionConstructed : Bool
    completeModelPointwiseResolutionConstructedIsTrue :
      completeModelPointwiseResolutionConstructed ≡ true

    actualMonsterZetaIntertwinerConstructed : Bool
    actualMonsterZetaIntertwinerConstructedIsFalse :
      actualMonsterZetaIntertwinerConstructed ≡ false

    modelProjectorsTransportedToActualSector : Bool
    modelProjectorsTransportedToActualSectorIsFalse :
      modelProjectorsTransportedToActualSector ≡ false

canonicalModelToMonsterResolutionBoundary :
  ModelToMonsterResolutionBoundary
canonicalModelToMonsterResolutionBoundary =
  model-to-monster-resolution-boundary true refl false refl false refl
