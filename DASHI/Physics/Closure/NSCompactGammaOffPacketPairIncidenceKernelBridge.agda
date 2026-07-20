module DASHI.Physics.Closure.NSCompactGammaOffPacketPairIncidenceKernelBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Analysis.WeightedKernelSchurTest
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaOffPacketSchurSplit
open import DASHI.Physics.Closure.NSCompactGammaOffPacketWeightedKernelBridge
open import DASHI.Physics.Closure.NSPairIncidenceKernel
open import DASHI.Physics.Closure.NSPairIncidenceSchurBridge

------------------------------------------------------------------------
-- Compact-Gamma adapter for the repository's exact Fourier pair-incidence
-- program.
--
-- `NSPairIncidenceKernel` supplies the exact finite fold of nonnegative pair
-- majorants, and `NSPairIncidenceSchurBridge` transports its finite row and
-- column sums into `WeightedKernelSchurCertificate`.  This module adds the
-- missing response-majorization layer specific to the compact-Gamma
-- off-packet derivative.
--
-- Three separate facts are required:
--
--   1. the concrete Fourier majorant kernel agrees pointwise with the exact
--      pair-incidence fold;
--   2. the abstract Schur action is exactly the action of its declared kernel;
--   3. the concrete near derivative is bounded by the output energy of the
--      concrete majorant-kernel action.
--
-- The third fact is intentionally an inequality, not an equality: the
-- pair-incidence kernel records absolute/vector majorants and does not claim to
-- reproduce the signed compact-Gamma derivative entry by entry.
------------------------------------------------------------------------

record NearPairIncidenceMajorization
    {p r c : Level}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P)) :
    Set (lsuc (p ⊔ r ⊔ c)) where
  field
    exactKernelAction :
      ExactKernelAction (asWeightedKernelData P) L

    exactKernelInput : VectorIn L

    concreteMajorantKernel : Row → Col → Scalar A
    concreteMajorantKernelMatch :
      ConcreteBiotSavartKernelMatch P concreteMajorantKernel

    concreteNearResponse : Scalar A

    concreteNearResponseBelowMajorantAction :
      _≤_ A concreteNearResponse
        (outputEnergy L
          (evaluateEntries exactKernelAction
            concreteMajorantKernel
            exactKernelInput))

open NearPairIncidenceMajorization public

concreteKernelActionEqualsPairAction :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P))
    (R : NearPairIncidenceMajorization A P L) →
  evaluateEntries (exactKernelAction R)
    (concreteMajorantKernel R)
    (exactKernelInput R)
  ≡
  evaluateEntries (exactKernelAction R)
    (pairKernelEntry P)
    (exactKernelInput R)
concreteKernelActionEqualsPairAction A P L R =
  exactKernelActionPointwiseTransport
    (exactKernelAction R)
    (concreteMajorantKernel R)
    (pairKernelEntry P)
    (pointwiseKernelMatch (concreteMajorantKernelMatch R))
    (exactKernelInput R)

pairActionEqualsCertifiedKernelAction :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P))
    (R : NearPairIncidenceMajorization A P L) →
  evaluateEntries (exactKernelAction R)
    (pairKernelEntry P)
    (exactKernelInput R)
  ≡
  applyKernel L (exactKernelInput R)
pairActionEqualsCertifiedKernelAction A P L R =
  sym (applyKernelMatchesEntries
    (exactKernelAction R)
    (exactKernelInput R))

concreteMajorantOutputEqualsCertifiedKernelOutput :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P))
    (R : NearPairIncidenceMajorization A P L) →
  outputEnergy L
    (evaluateEntries (exactKernelAction R)
      (concreteMajorantKernel R)
      (exactKernelInput R))
  ≡
  outputEnergy L (applyKernel L (exactKernelInput R))
concreteMajorantOutputEqualsCertifiedKernelOutput A P L R =
  trans
    (cong
      (outputEnergy L)
      (concreteKernelActionEqualsPairAction A P L R))
    (cong
      (outputEnergy L)
      (pairActionEqualsCertifiedKernelAction A P L R))

concreteNearResponseBelowCertifiedKernelOutput :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P)) →
  (R : NearPairIncidenceMajorization A P L) →
  _≤_ A
    (concreteNearResponse R)
    (outputEnergy L (applyKernel L (exactKernelInput R)))
concreteNearResponseBelowCertifiedKernelOutput A P L R =
  subst
    (λ right → _≤_ A (concreteNearResponse R) right)
    (concreteMajorantOutputEqualsCertifiedKernelOutput A P L R)
    (concreteNearResponseBelowMajorantAction R)

------------------------------------------------------------------------
-- Full adapter: exact pair incidences + finite/uniform Schur realization +
-- concrete near-response majorization feed the existing near/tail chain.
------------------------------------------------------------------------

record OffPacketPairIncidenceEvidence
    {p r c : Level}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P)) :
    Set (lsuc (p ⊔ r ⊔ c)) where
  field
    schurRealization :
      PairIncidenceSchurRealization P L

    pairNearMajorization :
      NearPairIncidenceMajorization A P L

    pairOffPacketResponse : Scalar A
    pairFarShellTail : Scalar A

    pairOffPacketBelowNearPlusTail :
      _≤_ A pairOffPacketResponse
        (_+_ A
          (concreteNearResponse pairNearMajorization)
          pairFarShellTail)

    pairSchurOrderTransport :
      {left right : Scalar A} →
      _≤_ L left right →
      _≤_ A left right

open OffPacketPairIncidenceEvidence public

pairIncidenceEvidenceToWeightedKernelEvidence :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P)) →
  OffPacketPairIncidenceEvidence A P L →
  OffPacketWeightedKernelEvidence A (asWeightedKernelData P) L
pairIncidenceEvidenceToWeightedKernelEvidence A P L E = record
  { certificate =
      pairIncidenceWeightedCertificate (schurRealization E)
  ; kernelInput =
      exactKernelInput (pairNearMajorization E)
  ; offPacketResponse =
      pairOffPacketResponse E
  ; nearShellResponse =
      concreteNearResponse (pairNearMajorization E)
  ; farShellTail =
      pairFarShellTail E
  ; offPacketBelowNearPlusTail =
      pairOffPacketBelowNearPlusTail E
  ; concreteNearResponseRepresentedByKernel =
      concreteNearResponseBelowCertifiedKernelOutput
        A P L (pairNearMajorization E)
  ; schurOrderTransport =
      pairSchurOrderTransport E
  }

pairIncidenceEvidenceToOffPacketSplit :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P)) →
  OffPacketPairIncidenceEvidence A P L →
  OffPacketSchurSplitInputs A
pairIncidenceEvidenceToOffPacketSplit A P L E =
  weightedKernelEvidenceToOffPacketSplit
    A (asWeightedKernelData P) L
    (pairIncidenceEvidenceToWeightedKernelEvidence A P L E)
