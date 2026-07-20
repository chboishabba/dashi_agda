module DASHI.Physics.Closure.NSCompactGammaOffPacketPairIncidenceKernelBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc; Set₁)
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
-- `NSPairIncidenceKernel` already supplies the exact finite fold of pair
-- contributions, and `NSPairIncidenceSchurBridge` transports its finite row and
-- column sums into `WeightedKernelSchurCertificate`.  This module adds the
-- missing response-identification layer specific to the compact-Gamma
-- off-packet derivative.
--
-- Three separate facts are required:
--
--   1. the concrete Fourier kernel agrees pointwise with the pair-incidence
--      fold;
--   2. the abstract Schur action is exactly the action of its declared kernel;
--   3. the concrete near derivative is exactly the output energy of the
--      concrete Fourier-kernel action.
--
-- Only their composition may discharge
-- `concreteNearResponseRepresentedByKernel` in the off-packet weighted-kernel
-- bridge.  A coarse empirical shell matrix cannot inhabit this adapter.
------------------------------------------------------------------------

record ExactNearPairIncidenceRepresentation
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

    concreteKernel : Row → Col → Scalar A
    concreteKernelMatch :
      ConcreteBiotSavartKernelMatch P concreteKernel

    concreteNearResponse : Scalar A

    concreteNearResponseIsConcreteAction :
      concreteNearResponse ≡
      outputEnergy L
        (evaluateEntries exactKernelAction
          concreteKernel
          exactKernelInput)

open ExactNearPairIncidenceRepresentation public

concreteKernelActionEqualsPairAction :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P))
    (R : ExactNearPairIncidenceRepresentation A P L) →
  evaluateEntries (exactKernelAction R)
    (concreteKernel R)
    (exactKernelInput R)
  ≡
  evaluateEntries (exactKernelAction R)
    (pairKernelEntry P)
    (exactKernelInput R)
concreteKernelActionEqualsPairAction A P L R =
  exactKernelActionPointwiseTransport
    (exactKernelAction R)
    (concreteKernel R)
    (pairKernelEntry P)
    (pointwiseKernelMatch (concreteKernelMatch R))
    (exactKernelInput R)

pairActionEqualsCertifiedKernelAction :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P))
    (R : ExactNearPairIncidenceRepresentation A P L) →
  evaluateEntries (exactKernelAction R)
    (pairKernelEntry P)
    (exactKernelInput R)
  ≡
  applyKernel L (exactKernelInput R)
pairActionEqualsCertifiedKernelAction A P L R =
  sym (applyKernelMatchesEntries
    (exactKernelAction R)
    (exactKernelInput R))

concreteNearResponseEqualsCertifiedKernelOutput :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P))
    (R : ExactNearPairIncidenceRepresentation A P L) →
  concreteNearResponse R ≡
  outputEnergy L (applyKernel L (exactKernelInput R))
concreteNearResponseEqualsCertifiedKernelOutput A P L R =
  trans
    (concreteNearResponseIsConcreteAction R)
    (trans
      (cong
        (outputEnergy L)
        (concreteKernelActionEqualsPairAction A P L R))
      (cong
        (outputEnergy L)
        (pairActionEqualsCertifiedKernelAction A P L R)))

------------------------------------------------------------------------
-- The absorption arithmetic used by the off-packet split only assumed
-- transitivity.  Equality-to-order conversion additionally needs reflexivity,
-- kept as an explicit local law rather than silently strengthening the shared
-- arithmetic record.
------------------------------------------------------------------------

record ReflexiveAbsorptionOrder
    (A : AbsorptionArithmetic) : Set₁ where
  field
    ≤-refl :
      ∀ value → _≤_ A value value

open ReflexiveAbsorptionOrder public

concreteNearResponseBelowCertifiedKernelOutput :
  ∀ {p r c}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceData Pair Row Col (Scalar A))
    (L : WeightedSchurLaws (asWeightedKernelData P)) →
  ReflexiveAbsorptionOrder A →
  (R : ExactNearPairIncidenceRepresentation A P L) →
  _≤_ A
    (concreteNearResponse R)
    (outputEnergy L (applyKernel L (exactKernelInput R)))
concreteNearResponseBelowCertifiedKernelOutput A P L O R =
  subst
    (λ left →
      _≤_ A left
        (outputEnergy L (applyKernel L (exactKernelInput R))))
    (sym (concreteNearResponseEqualsCertifiedKernelOutput A P L R))
    (≤-refl O
      (outputEnergy L (applyKernel L (exactKernelInput R))))

------------------------------------------------------------------------
-- Full adapter: exact pair incidences + finite/uniform Schur realization +
-- exact compact-Gamma response identity feed the existing near/tail chain.
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

    pairOrderReflexive :
      ReflexiveAbsorptionOrder A

    pairNearRepresentation :
      ExactNearPairIncidenceRepresentation A P L

    pairOffPacketResponse : Scalar A
    pairFarShellTail : Scalar A

    pairOffPacketBelowNearPlusTail :
      _≤_ A pairOffPacketResponse
        (_+_ A
          (concreteNearResponse pairNearRepresentation)
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
      exactKernelInput (pairNearRepresentation E)
  ; offPacketResponse =
      pairOffPacketResponse E
  ; nearShellResponse =
      concreteNearResponse (pairNearRepresentation E)
  ; farShellTail =
      pairFarShellTail E
  ; offPacketBelowNearPlusTail =
      pairOffPacketBelowNearPlusTail E
  ; concreteNearResponseRepresentedByKernel =
      concreteNearResponseBelowCertifiedKernelOutput
        A P L
        (pairOrderReflexive E)
        (pairNearRepresentation E)
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
