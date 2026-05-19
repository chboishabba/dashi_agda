module DASHI.Physics.Closure.G3GalileiIdentification where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.G3AssociatedGradedQuotientSurface as Gr
import DASHI.Physics.Closure.G3ConcreteOperators as G3Concrete
import DASHI.Physics.Closure.G3WaveFunctionOperatorAlgebra as G3

------------------------------------------------------------------------
-- G3 Galilei generator identification surface.
--
-- This module names the requested φ-P/H/K/M slots against the selected
-- G3 wave-function operators and the selected prequotient filtration
-- pieces already exposed by G3AssociatedGradedQuotientSurface.
--
-- It is deliberately prequotient and non-promoting: there is still no
-- accepted gr(F) quotient carrier F_n / F_{n-1}, no quotient projection,
-- and no selected p2 operator norm/distance primitive here.

data G3GalileiIdentificationStatus : Set where
  selectedPrequotientIdentificationOnlyNoPromotion :
    G3GalileiIdentificationStatus

data G3GalileiIdentificationBlocker : Set where
  missingEquivalenceModuloPreviousFiltration :
    G3GalileiIdentificationBlocker

  missingAcceptedAssociatedGradedQuotientCarrier :
    G3GalileiIdentificationBlocker

  missingAcceptedProjectionIntoAssociatedGradedQuotient :
    G3GalileiIdentificationBlocker

  missingSelectedP2OperatorDistancePrimitive :
    G3GalileiIdentificationBlocker

data PhiGalileiGeneratorName : Set where
  φ-P :
    G3Concrete.G3SpatialDirection →
    PhiGalileiGeneratorName

  φ-H :
    PhiGalileiGeneratorName

  φ-K :
    G3Concrete.G3SpatialDirection →
    PhiGalileiGeneratorName

  φ-M :
    PhiGalileiGeneratorName

phiGenerator :
  PhiGalileiGeneratorName →
  G3.G3SelectedAssociatedGradedGenerator
phiGenerator (φ-P d) =
  G3.selectedSpatialMomentumGenerator d
phiGenerator φ-H =
  G3.selectedHamiltonianGenerator
phiGenerator (φ-K d) =
  G3.selectedBoostGenerator d
phiGenerator φ-M =
  G3.selectedMassCentralSlot

phiOperator :
  PhiGalileiGeneratorName →
  G3.WaveFunctionOperator
phiOperator name =
  G3.selectedGeneratorOperator (phiGenerator name)

phiDegree :
  PhiGalileiGeneratorName →
  Nat
phiDegree name =
  G3.selectedGeneratorDegree (phiGenerator name)

phiHasSelectedP2Degree :
  (name : PhiGalileiGeneratorName) →
  G3.SelectedOperatorP2Degree
    (phiOperator name)
    (phiDegree name)
phiHasSelectedP2Degree name =
  G3.selectedGeneratorHasDegree (phiGenerator name)

phiPrequotientProjection :
  (name : PhiGalileiGeneratorName) →
  Gr.SelectedFiltrationPiece (phiDegree name)
phiPrequotientProjection name =
  Gr.selectedGeneratorFiltrationPiece (phiGenerator name)

φ-P-operator :
  (d : G3Concrete.G3SpatialDirection) →
  phiOperator (φ-P d) ≡ G3.selectedPψ d
φ-P-operator d =
  refl

φ-H-operator :
  phiOperator φ-H ≡ G3.selectedHψ
φ-H-operator =
  refl

φ-K-operator :
  (d : G3Concrete.G3SpatialDirection) →
  phiOperator (φ-K d) ≡ G3.selectedKψ d
φ-K-operator d =
  refl

φ-M-operator :
  phiOperator φ-M ≡ (λ ψ → ψ)
φ-M-operator =
  refl

φ-P-prequotient :
  (d : G3Concrete.G3SpatialDirection) →
  phiPrequotientProjection (φ-P d)
  ≡
  Gr.selectedGeneratorFiltrationPiece
    (G3.selectedSpatialMomentumGenerator d)
φ-P-prequotient d =
  refl

φ-H-prequotient :
  phiPrequotientProjection φ-H
  ≡
  Gr.selectedGeneratorFiltrationPiece
    G3.selectedHamiltonianGenerator
φ-H-prequotient =
  refl

φ-K-prequotient :
  (d : G3Concrete.G3SpatialDirection) →
  phiPrequotientProjection (φ-K d)
  ≡
  Gr.selectedGeneratorFiltrationPiece
    (G3.selectedBoostGenerator d)
φ-K-prequotient d =
  refl

φ-M-prequotient :
  phiPrequotientProjection φ-M
  ≡
  Gr.selectedGeneratorFiltrationPiece
    G3.selectedMassCentralSlot
φ-M-prequotient =
  refl

record G3GalileiIdentificationSurface : Setω where
  field
    status :
      G3GalileiIdentificationStatus

    selectedGeneratorEvidence :
      G3.G3SelectedAssociatedGradedGalileiEvidence

    selectedPrequotientEvidence :
      Gr.G3SelectedAssociatedGradedPrequotientEvidence

    associatedGradedQuotientSurface :
      Gr.G3AssociatedGradedQuotientSurface

    phiName :
      Set

    phiNameIsSelected :
      phiName ≡ PhiGalileiGeneratorName

    phiToSelectedGenerator :
      PhiGalileiGeneratorName →
      G3.G3SelectedAssociatedGradedGenerator

    phiToSelectedGeneratorIsCanonical :
      phiToSelectedGenerator ≡ phiGenerator

    phiToOperator :
      PhiGalileiGeneratorName →
      G3.WaveFunctionOperator

    phiToOperatorIsSelected :
      phiToOperator ≡ phiOperator

    phiToDegree :
      PhiGalileiGeneratorName →
      Nat

    phiToDegreeIsSelected :
      phiToDegree ≡ phiDegree

    phiToPrequotientProjection :
      (name : PhiGalileiGeneratorName) →
      Gr.SelectedFiltrationPiece (phiDegree name)

    phiToPrequotientProjectionIsSelected :
      phiToPrequotientProjection ≡ phiPrequotientProjection

    phiPNamesSelectedMomentum :
      (d : G3Concrete.G3SpatialDirection) →
      phiToOperator (φ-P d) ≡ G3.selectedPψ d

    phiHNamesSelectedHamiltonian :
      phiToOperator φ-H ≡ G3.selectedHψ

    phiKNamesSelectedBoost :
      (d : G3Concrete.G3SpatialDirection) →
      phiToOperator (φ-K d) ≡ G3.selectedKψ d

    phiMNamesSelectedMassCentralSlot :
      phiToOperator φ-M ≡ (λ ψ → ψ)

    prequotientIdentificationConstructed :
      Bool

    acceptedQuotientIdentificationConstructed :
      Bool

    p2OperatorDistancePrimitiveConstructed :
      Bool

    exactRemainingBlockers :
      List G3GalileiIdentificationBlocker

    quotientSurfaceFirstMissing :
      List Gr.G3AssociatedGradedQuotientFirstMissing

    nonPromotionBoundary :
      List String

canonicalG3GalileiIdentificationSurface :
  G3GalileiIdentificationSurface
canonicalG3GalileiIdentificationSurface =
  record
    { status =
        selectedPrequotientIdentificationOnlyNoPromotion
    ; selectedGeneratorEvidence =
        G3.canonicalG3SelectedAssociatedGradedGalileiEvidence
    ; selectedPrequotientEvidence =
        Gr.canonicalG3SelectedAssociatedGradedPrequotientEvidence
    ; associatedGradedQuotientSurface =
        Gr.canonicalG3AssociatedGradedQuotientSurface
    ; phiName =
        PhiGalileiGeneratorName
    ; phiNameIsSelected =
        refl
    ; phiToSelectedGenerator =
        phiGenerator
    ; phiToSelectedGeneratorIsCanonical =
        refl
    ; phiToOperator =
        phiOperator
    ; phiToOperatorIsSelected =
        refl
    ; phiToDegree =
        phiDegree
    ; phiToDegreeIsSelected =
        refl
    ; phiToPrequotientProjection =
        phiPrequotientProjection
    ; phiToPrequotientProjectionIsSelected =
        refl
    ; phiPNamesSelectedMomentum =
        φ-P-operator
    ; phiHNamesSelectedHamiltonian =
        φ-H-operator
    ; phiKNamesSelectedBoost =
        φ-K-operator
    ; phiMNamesSelectedMassCentralSlot =
        φ-M-operator
    ; prequotientIdentificationConstructed =
        true
    ; acceptedQuotientIdentificationConstructed =
        false
    ; p2OperatorDistancePrimitiveConstructed =
        false
    ; exactRemainingBlockers =
        missingEquivalenceModuloPreviousFiltration
        ∷ missingAcceptedAssociatedGradedQuotientCarrier
        ∷ missingAcceptedProjectionIntoAssociatedGradedQuotient
        ∷ missingSelectedP2OperatorDistancePrimitive
        ∷ []
    ; quotientSurfaceFirstMissing =
        Gr.missingEquivalenceModuloPreviousFiltration
        ∷ Gr.missingAcceptedQuotientCarrier
        ∷ Gr.missingProjectionRespectsQuotientEquivalence
        ∷ []
    ; nonPromotionBoundary =
        "φ-P, φ-H, φ-K, and φ-M are identified with selected generator operators and selected prequotient filtration projections"
        ∷ "This is not an associated-graded quotient identification: no gr-1 quotient class or quotient projection is constructed here"
        ∷ "The first quotient blocker is missingEquivalenceModuloPreviousFiltration"
        ∷ "The p2 metric blocker is missingSelectedP2OperatorDistancePrimitive"
        ∷ "No contraction closure, quotient closure, or G3 promotion is claimed by this surface"
        ∷ []
    }
