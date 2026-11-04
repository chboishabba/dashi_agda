{-# OPTIONS --safe #-}
module DASHI.Education.DigitalESDSpectralWorldGapSelectionExact where

------------------------------------------------------------------------
-- FINITE SELECTED EIGENBASIS + SOURCE-INDEXED RESEARCH GAP BRIDGE
--
-- Corrects the over-strong "every Vector is selected above the MP edge"
-- contract by quantifying only over a finite named eigenmode family.
-- The numeric operator, its covariance source, the null-model hypothesis,
-- and the ESD study-world anchor remain separate obligations.
--
-- No eigenvalue, statistical significance or semantic source review
-- is fabricated by this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Information.PNFSpectralGeometry as Spectral
import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World
import DASHI.Education.DigitalESDOpenAxisGapTransportExact as Gap

------------------------------------------------------------------------
-- SPW00: A selected family is not the set of all vectors.  Its operator
-- equation refers to the SAME covariance action that the caller supplies.
-- Each named index must occur in the finite selected-index list.
------------------------------------------------------------------------

record FiniteOperatorEigenFamily
    (𝕂 : Spectral.ScalarStructure) : Set₁ where
  constructor finite-operator-eigen-family
  field
    Vector : Set
    Mode : Set
    selectedModes : List Mode
    modeIsListed : (i : Mode) → i ∈ selectedModes

    covarianceAction : Vector → Vector
    numericCovarianceAction : Vector → Vector
    covarianceHasSameOperator :
      (v : Vector) →
      covarianceAction v ≡ numericCovarianceAction v

    vector : Mode → Vector
    eigenvalue : Mode → Spectral.Scalar 𝕂
    scalarMultiply : Spectral.Scalar 𝕂 → Vector → Vector

    eigenEquation :
      (i : Mode) →
      covarianceAction (vector i) ≡
      scalarMultiply (eigenvalue i) (vector i)

    Orthonormal : Vector → Vector → Set
    selectedFamilyOrthonormal :
      (i j : Mode) → Orthonormal (vector i) (vector j)

open FiniteOperatorEigenFamily public

-- SPW01: Numeric ABI/covariance agreement is explicit.  A proof of the
-- operator equation is transported to the numeric covariance action,
-- not asserted for an unrelated matrix or raw-text embedding.
numericEigenEquation :
  {𝕂 : Spectral.ScalarStructure} →
  (family : FiniteOperatorEigenFamily 𝕂) →
  (i : Mode family) →
  numericCovarianceAction family (vector family i) ≡
  scalarMultiply family (eigenvalue family i) (vector family i)
numericEigenEquation family i =
  trans (sym (covarianceHasSameOperator family (vector family i)))
    (eigenEquation family i)

------------------------------------------------------------------------
-- SPW02: The statistical null-model law is NOT obtained from a Jacobi
-- eigendecomposition.  A caller must explicitly supply assumptions,
-- a null-model receipt, and the chosen edge calibration.
-- "edgeFormula" is a selected model's rule; it is not claimed to be the
-- Agda proof of the Marchenko--Pastur limit theorem.
------------------------------------------------------------------------

record MPNullModelSelection
    (𝕂 : Spectral.ScalarStructure)
    (family : FiniteOperatorEigenFamily 𝕂)
    (band : Spectral.SpectralNoiseBand 𝕂)
    (gate : Spectral.NoiseClassifier 𝕂 band) : Set₁ where
  constructor mp-null-model-selection
  field
    NullHypothesis : Set
    nullAssumptionsReceipt : NullHypothesis
    nullModelSource : String
    numericProducerReceipt : String
    sigmaSquared : Spectral.Scalar 𝕂
    gamma : Spectral.Scalar 𝕂
    edgeFormula :
      Spectral.Scalar 𝕂 →
      Spectral.Scalar 𝕂 →
      Spectral.Scalar 𝕂
    selectedUpperEdge :
      Spectral.upper band ≡ edgeFormula sigmaSquared gamma

    selected : Mode family → Set
    selectedAboveUpperEdge :
      (i : Mode family) →
      selected i →
      Spectral._<_ 𝕂 (Spectral.upper band) (eigenvalue family i)

open MPNullModelSelection public

-- SPW03: The actual existing Spectral.NoiseClassifier proves the
-- conditional candidate classification.  Nothing here promotes truth.
selectedModeIsCandidateSignal :
  {𝕂 : Spectral.ScalarStructure} →
  {family : FiniteOperatorEigenFamily 𝕂} →
  {band : Spectral.SpectralNoiseBand 𝕂} →
  {gate : Spectral.NoiseClassifier 𝕂 band} →
  (calibration : MPNullModelSelection 𝕂 family band gate) →
  (i : Mode family) →
  selected calibration i →
  Spectral.classify gate (eigenvalue family i) ≡
  Spectral.candidateSignal
selectedModeIsCandidateSignal {gate = gate} calibration i selectedProof =
  Spectral.above-null-band gate
    (selectedAboveUpperEdge calibration i selectedProof)

------------------------------------------------------------------------
-- SPW04: The chosen candidate is tied to an ACTUAL accounted ESD world
-- and an EXACT source part/axis address.  The status comes from the
-- same world and is not implicitly changed by the eigenvalue.
------------------------------------------------------------------------

record SameWorldSpectralCandidate
    {scope : World.StudyWorldScope}
    {𝕂 : Spectral.ScalarStructure}
    {family : FiniteOperatorEigenFamily 𝕂}
    {band : Spectral.SpectralNoiseBand 𝕂}
    {gate : Spectral.NoiseClassifier 𝕂 band}
    (world : World.AccountedStudyWorld scope)
    (calibration : MPNullModelSelection 𝕂 family band gate) : Set₁ where
  constructor same-world-spectral-candidate
  field
    sourcePart : World.StudyPart scope
    axis : World.Axis scope

    accountedEvidence :
      World.PartAxisAccounting scope
        (World.study sourcePart) (World.part sourcePart) axis
    accountsAsActualWorld :
      accountedEvidence ≡
      World.accounting world
        (World.study sourcePart) (World.part sourcePart) axis

    chosenMode : Mode family
    chosenIsSelected : selected calibration chosenMode

open SameWorldSpectralCandidate public

-- SPW05: The ESD candidate's spectral status is exactly the selected
-- existing classifier result, without replacing its evidence type.
sameWorldModeIsSpectralCandidate :
  {scope : World.StudyWorldScope} →
  {𝕂 : Spectral.ScalarStructure} →
  {family : FiniteOperatorEigenFamily 𝕂} →
  {band : Spectral.SpectralNoiseBand 𝕂} →
  {gate : Spectral.NoiseClassifier 𝕂 band} →
  {world : World.AccountedStudyWorld scope} →
  {calibration : MPNullModelSelection 𝕂 family band gate} →
  (c : SameWorldSpectralCandidate world calibration) →
  Spectral.classify gate (eigenvalue family (chosenMode c)) ≡
  Spectral.candidateSignal
sameWorldModeIsSpectralCandidate {calibration = calibration} c =
  selectedModeIsCandidateSignal calibration
    (chosenMode c) (chosenIsSelected c)

------------------------------------------------------------------------
-- SPW06: A gap is a separate source-typed research question, never an
-- automatic effect of the null-band classifier or spectral prominence.
------------------------------------------------------------------------

record SameWorldSpectralGap
    {scope : World.StudyWorldScope}
    {𝕂 : Spectral.ScalarStructure}
    {family : FiniteOperatorEigenFamily 𝕂}
    {band : Spectral.SpectralNoiseBand 𝕂}
    {gate : Spectral.NoiseClassifier 𝕂 band}
    {world : World.AccountedStudyWorld scope}
    {calibration : MPNullModelSelection 𝕂 family band gate}
    (candidate : SameWorldSpectralCandidate world calibration) : Set₂ where
  constructor same-world-spectral-gap
  field
    donor : World.StudyPart scope
    gap :
      Gap.CandidateGapQuestionRoute scope world
        donor (sourcePart candidate) (axis candidate)

open SameWorldSpectralGap public

sourceIndexedGapStatus :
  {scope : World.StudyWorldScope} →
  {𝕂 : Spectral.ScalarStructure} →
  {family : FiniteOperatorEigenFamily 𝕂} →
  {band : Spectral.SpectralNoiseBand 𝕂} →
  {gate : Spectral.NoiseClassifier 𝕂 band} →
  {world : World.AccountedStudyWorld scope} →
  {calibration : MPNullModelSelection 𝕂 family band gate} →
  {candidate : SameWorldSpectralCandidate world calibration} →
  (joined : SameWorldSpectralGap candidate) →
  Gap.RecipientGapStatus scope world
    (sourcePart candidate) (axis candidate)
sourceIndexedGapStatus joined =
  Gap.targetStatus (gap joined)

------------------------------------------------------------------------
-- SPW07: The structural limit is explicit: MP classifies eigenvalue
-- candidates; only source-specific reviewed evidence may inhabit the
-- existing directReviewed constructor.  No automatic bridge is offered.
------------------------------------------------------------------------
