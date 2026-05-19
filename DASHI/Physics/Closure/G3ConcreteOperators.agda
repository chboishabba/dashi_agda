module DASHI.Physics.Closure.G3ConcreteOperators where

open import Agda.Primitive using (Set; Setω; lzero; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Process.DASHIMarkovCompatibility as DMC
import DASHI.Physics.Closure.G3PoincareGalileiCarrierChain as G3
import DASHI.Physics.Closure.G3SelectedCarrierInstance as G3Selected
open import MonsterOntos using (SSP; p2; p3; p5; p7)
import Ontology.GodelLattice as GL
import Ontology.Hecke.FactorVecInstances as FVI

------------------------------------------------------------------------
-- Concrete selected-state G3 operators.
--
-- Diagnostics locked the global DMC.DASHIState carrier as abstract.  This
-- module therefore works only on the selected witness from
-- G3SelectedCarrierInstance, whose Carrier is definitionally GL.FactorVec.
-- It constructs concrete p2/spatial endomorphisms and their prime-bump
-- commutation laws.  It deliberately does not claim an IW contraction
-- promotion: the Schrodinger obligation record still has no inhabited
-- PoincareToGalileiContractionCarrier.

data G3SelectedConcreteOperatorStatus : Set where
  selectedConcreteOperatorsOnlyNoG3Promotion :
    G3SelectedConcreteOperatorStatus

data G3SelectedConcreteMissingPiece : Set where
  missingSchrodingerPoincareToGalileiContractionCarrier :
    G3SelectedConcreteMissingPiece

  missingWaveFunctionScalarRingAndBracketSemantics :
    G3SelectedConcreteMissingPiece

  missingAssociatedGradedGalileiIdentification :
    G3SelectedConcreteMissingPiece

data G3SpatialDirection : Set where
  xDirection :
    G3SpatialDirection

  yDirection :
    G3SpatialDirection

  zDirection :
    G3SpatialDirection

spatialPrime :
  G3SpatialDirection →
  SSP
spatialPrime xDirection =
  p3
spatialPrime yDirection =
  p5
spatialPrime zDirection =
  p7

SelectedG3State :
  Set
SelectedG3State =
  GL.FactorVec

SelectedG3Operator :
  Set
SelectedG3Operator =
  SelectedG3State →
  SelectedG3State

selectedInitialFactorVec :
  SelectedG3State
selectedInitialFactorVec =
  DMC.DASHIState.carrierValue
    G3Selected.selectedG3FactorVecDASHIState

selectedCarrierIsFactorVec :
  DMC.DASHIState.Carrier
    G3Selected.selectedG3FactorVecDASHIState
  ≡
  GL.FactorVec
selectedCarrierIsFactorVec =
  refl

selectedBumpAt :
  SSP →
  SelectedG3Operator
selectedBumpAt p v =
  FVI.primeBump p v

selectedP2Bump :
  SelectedG3Operator
selectedP2Bump =
  selectedBumpAt p2

selectedSpatialBump :
  G3SpatialDirection →
  SelectedG3Operator
selectedSpatialBump d =
  selectedBumpAt (spatialPrime d)

selectedP :
  G3SpatialDirection →
  SelectedG3Operator
selectedP =
  selectedSpatialBump

selectedH :
  SelectedG3Operator
selectedH =
  selectedP2Bump

selectedK :
  G3SpatialDirection →
  SelectedG3Operator
selectedK d v =
  selectedP2Bump (selectedSpatialBump d v)

selectedBumpCommutes :
  (p q : SSP) →
  (v : SelectedG3State) →
  selectedBumpAt p (selectedBumpAt q v)
  ≡
  selectedBumpAt q (selectedBumpAt p v)
selectedBumpCommutes =
  FVI.primeBumpCommutes

selectedPPCommutes :
  (d e : G3SpatialDirection) →
  (v : SelectedG3State) →
  selectedP d (selectedP e v)
  ≡
  selectedP e (selectedP d v)
selectedPPCommutes d e =
  selectedBumpCommutes (spatialPrime d) (spatialPrime e)

selectedHPCommutes :
  (d : G3SpatialDirection) →
  (v : SelectedG3State) →
  selectedH (selectedP d v)
  ≡
  selectedP d (selectedH v)
selectedHPCommutes d =
  selectedBumpCommutes p2 (spatialPrime d)

selectedKIsHP :
  (d : G3SpatialDirection) →
  (v : SelectedG3State) →
  selectedK d v
  ≡
  selectedH (selectedP d v)
selectedKIsHP d v =
  refl

selectedKIsPH :
  (d : G3SpatialDirection) →
  (v : SelectedG3State) →
  selectedK d v
  ≡
  selectedP d (selectedH v)
selectedKIsPH =
  selectedHPCommutes

selectedP2Filtration :
  SelectedG3State →
  Nat
selectedP2Filtration v =
  GL.Vec15.e2 v

selectedHFiltrationStep :
  (v : SelectedG3State) →
  selectedP2Filtration (selectedH v)
  ≡
  Agda.Builtin.Nat.suc (selectedP2Filtration v)
selectedHFiltrationStep =
  G3.p2ExponentAfterPrimeBump

selectedInitialP2Filtration :
  selectedP2Filtration selectedInitialFactorVec
  ≡
  G3Selected.selectedP2Exponent
selectedInitialP2Filtration =
  refl

selectedInitialHFiltrationStep :
  selectedP2Filtration (selectedH selectedInitialFactorVec)
  ≡
  Agda.Builtin.Nat.suc (selectedP2Filtration selectedInitialFactorVec)
selectedInitialHFiltrationStep =
  selectedHFiltrationStep selectedInitialFactorVec

record G3SelectedConcreteOperatorPackage : Setω where
  field
    status :
      G3SelectedConcreteOperatorStatus

    selectedDASHIState :
      DMC.DASHIState

    selectedDASHIStateCarrierIsFactorVec :
      DMC.DASHIState.Carrier selectedDASHIState
      ≡
      GL.FactorVec

    selectedState :
      Set

    selectedStateIsFactorVec :
      selectedState ≡ GL.FactorVec

    initialState :
      selectedState

    p2Bump :
      selectedState →
      selectedState

    spatialDirection :
      Set

    spatialPrimeOf :
      spatialDirection →
      SSP

    spatialBump :
      spatialDirection →
      selectedState →
      selectedState

    P :
      spatialDirection →
      selectedState →
      selectedState

    H :
      selectedState →
      selectedState

    K :
      spatialDirection →
      selectedState →
      selectedState

    PPCommutes :
      (d e : spatialDirection) →
      (v : selectedState) →
      P d (P e v) ≡ P e (P d v)

    HPCommutes :
      (d : spatialDirection) →
      (v : selectedState) →
      H (P d v) ≡ P d (H v)

    KIsHP :
      (d : spatialDirection) →
      (v : selectedState) →
      K d v ≡ H (P d v)

    KIsPH :
      (d : spatialDirection) →
      (v : selectedState) →
      K d v ≡ P d (H v)

    p2Filtration :
      selectedState →
      Nat

    HFiltrationStep :
      (v : selectedState) →
      p2Filtration (H v) ≡ Agda.Builtin.Nat.suc (p2Filtration v)

    exactFirstMissingPromotionField :
      String

    missingPieces :
      List G3SelectedConcreteMissingPiece

    nonPromotionBoundary :
      List String

canonicalG3SelectedConcreteOperatorPackage :
  G3SelectedConcreteOperatorPackage
canonicalG3SelectedConcreteOperatorPackage =
  record
    { status =
        selectedConcreteOperatorsOnlyNoG3Promotion
    ; selectedDASHIState =
        G3Selected.selectedG3FactorVecDASHIState
    ; selectedDASHIStateCarrierIsFactorVec =
        selectedCarrierIsFactorVec
    ; selectedState =
        SelectedG3State
    ; selectedStateIsFactorVec =
        refl
    ; initialState =
        selectedInitialFactorVec
    ; p2Bump =
        selectedP2Bump
    ; spatialDirection =
        G3SpatialDirection
    ; spatialPrimeOf =
        spatialPrime
    ; spatialBump =
        selectedSpatialBump
    ; P =
        selectedP
    ; H =
        selectedH
    ; K =
        selectedK
    ; PPCommutes =
        selectedPPCommutes
    ; HPCommutes =
        selectedHPCommutes
    ; KIsHP =
        selectedKIsHP
    ; KIsPH =
        selectedKIsPH
    ; p2Filtration =
        selectedP2Filtration
    ; HFiltrationStep =
        selectedHFiltrationStep
    ; exactFirstMissingPromotionField =
        "SES.G3HamiltonianEvolutionObligations.PoincareToGalileiContractionCarrier"
    ; missingPieces =
        missingSchrodingerPoincareToGalileiContractionCarrier
        ∷ missingWaveFunctionScalarRingAndBracketSemantics
        ∷ missingAssociatedGradedGalileiIdentification
        ∷ []
    ; nonPromotionBoundary =
        "Concrete selected-state operator package only: state carrier is GL.FactorVec, not arbitrary DMC.DASHIState"
        ∷ "P, H, and K are selected FactorVec endomorphisms built from primeBump"
        ∷ "PP and HP commute by Ontology.Hecke.FactorVecInstances.primeBumpCommutes"
        ∷ "No wave-function scalar ring, Lie bracket semantics, associated graded carrier, or Galilei identification is inhabited here"
        ∷ "No PoincareToGalileiContractionCarrier or G3 promotion record is constructed"
        ∷ []
    }
