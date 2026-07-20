module DASHI.Physics.Closure.NSCompactGammaOffPacketPairIncidenceKernelBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc; Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Analysis.WeightedKernelSchurTest
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaOffPacketSchurSplit
open import DASHI.Physics.Closure.NSCompactGammaOffPacketWeightedKernelBridge

------------------------------------------------------------------------
-- Exact finite pair-incidence kernel.
--
-- The list `pairs` is the finite Galerkin incidence enumeration.  Each pair is
-- attached to one row and one column, and its entry vanishes away from that
-- incidence.  `incidenceKernel` is not a fitted shell matrix: it is the exact
-- finite sum of the declared pair entries at every row/column coordinate.
------------------------------------------------------------------------

_≢_ : ∀ {a} {X : Set a} → X → X → Set a
x ≢ y = x ≡ y → ⊥

record PairIncidenceKernel
    {r c : Level}
    (A : AbsorptionArithmetic)
    (Row : Set r)
    (Col : Set c) : Set (lsuc (r ⊔ c)) where
  field
    Pair : Set (r ⊔ c)
    pairs : List Pair

    pairRow : Pair → Row
    pairCol : Pair → Col
    pairCoefficient : Pair → Scalar A
    pairEntry : Pair → Row → Col → Scalar A

    entryAtIncidence :
      ∀ pair →
      pairEntry pair (pairRow pair) (pairCol pair) ≡
      pairCoefficient pair

    rowMismatchVanishes :
      ∀ pair row col →
      row ≢ pairRow pair →
      pairEntry pair row col ≡ zero A

    columnMismatchVanishes :
      ∀ pair row col →
      col ≢ pairCol pair →
      pairEntry pair row col ≡ zero A

open PairIncidenceKernel public

sumPairEntries :
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceKernel A Row Col) →
  List (Pair P) →
  Row →
  Col →
  Scalar A
sumPairEntries A P [] row col = zero A
sumPairEntries A P (pair ∷ rest) row col =
  _+_ A
    (pairEntry P pair row col)
    (sumPairEntries A P rest row col)

incidenceKernel :
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic) →
  PairIncidenceKernel A Row Col →
  Row →
  Col →
  Scalar A
incidenceKernel A P =
  sumPairEntries A P (pairs P)

pairIncidenceWeightedKernel :
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceKernel A Row Col)
    (K : WeightedKernelData Row Col (Scalar A)) →
  WeightedKernelData Row Col (Scalar A)
pairIncidenceWeightedKernel A P K = record
  { kernel = incidenceKernel A P
  ; rowWeight = rowWeight K
  ; colWeight = colWeight K
  }

pairIncidenceKernelIdentity :
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (P : PairIncidenceKernel A Row Col)
    (K : WeightedKernelData Row Col (Scalar A)) →
  kernel K ≡ incidenceKernel A P →
  KernelIdentityMatch K (pairIncidenceWeightedKernel A P K)
pairIncidenceKernelIdentity A P K entriesMatch = record
  { kernelMatches = entriesMatch
  ; rowWeightsMatch = refl
  ; colWeightsMatch = refl
  }

------------------------------------------------------------------------
-- Exact concrete-near representation.
--
-- Besides entrywise identity, this record requires exact action semantics for
-- the abstract Schur vector model.  The concrete near derivative must equal the
-- output energy of the pair-incidence action itself.  These two equalities are
-- enough to transport the response to the kernel output used by the certified
-- Schur estimate; no empirical comparison inequality is inserted here.
------------------------------------------------------------------------

record ExactNearPairIncidenceRepresentation
    {r c : Level}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (K : WeightedKernelData Row Col (Scalar A))
    (L : WeightedSchurLaws K) : Set (lsuc (r ⊔ c)) where
  field
    exactPairKernel : PairIncidenceKernel A Row Col
    exactKernelAction : ExactKernelAction K L
    exactKernelInput : VectorIn L
    concreteNearResponse : Scalar A

    exactPairKernelIdentity :
      KernelIdentityMatch K
        (pairIncidenceWeightedKernel A exactPairKernel K)

    concreteNearResponseIsPairAction :
      concreteNearResponse ≡
      outputEnergy L
        (evaluateEntries exactKernelAction
          (kernel (pairIncidenceWeightedKernel A exactPairKernel K))
          exactKernelInput)

open ExactNearPairIncidenceRepresentation public

certifiedKernelActionEqualsPairAction :
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (K : WeightedKernelData Row Col (Scalar A))
    (L : WeightedSchurLaws K)
    (R : ExactNearPairIncidenceRepresentation A K L) →
  applyKernel L (exactKernelInput R) ≡
  evaluateEntries (exactKernelAction R)
    (kernel (pairIncidenceWeightedKernel A (exactPairKernel R) K))
    (exactKernelInput R)
certifiedKernelActionEqualsPairAction A K L R =
  exactKernelActionTransportByIdentity
    (exactKernelAction R)
    (exactPairKernelIdentity R)
    (exactKernelInput R)

concreteNearResponseEqualsCertifiedKernelOutput :
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (K : WeightedKernelData Row Col (Scalar A))
    (L : WeightedSchurLaws K)
    (R : ExactNearPairIncidenceRepresentation A K L) →
  concreteNearResponse R ≡
  outputEnergy L (applyKernel L (exactKernelInput R))
concreteNearResponseEqualsCertifiedKernelOutput A K L R =
  trans
    (concreteNearResponseIsPairAction R)
    (sym
      (cong
        (outputEnergy L)
        (certifiedKernelActionEqualsPairAction A K L R)))

record ReflexiveAbsorptionOrder
    (A : AbsorptionArithmetic) : Set₁ where
  field
    ≤-refl :
      ∀ value → _≤_ A value value

open ReflexiveAbsorptionOrder public

concreteNearResponseBelowCertifiedKernelOutput :
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (K : WeightedKernelData Row Col (Scalar A))
    (L : WeightedSchurLaws K) →
  ReflexiveAbsorptionOrder A →
  (R : ExactNearPairIncidenceRepresentation A K L) →
  _≤_ A
    (concreteNearResponse R)
    (outputEnergy L (applyKernel L (exactKernelInput R)))
concreteNearResponseBelowCertifiedKernelOutput A K L O R =
  subst
    (λ left →
      _≤_ A left
        (outputEnergy L (applyKernel L (exactKernelInput R))))
    (sym (concreteNearResponseEqualsCertifiedKernelOutput A K L R))
    (≤-refl O
      (outputEnergy L (applyKernel L (exactKernelInput R))))

------------------------------------------------------------------------
-- Adapter into the existing Schur-tail chain.
------------------------------------------------------------------------

record OffPacketPairIncidenceEvidence
    {r c : Level}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (K : WeightedKernelData Row Col (Scalar A))
    (L : WeightedSchurLaws K) : Set (lsuc (r ⊔ c)) where
  field
    pairCertificate : WeightedKernelSchurCertificate K L
    pairOrderReflexive : ReflexiveAbsorptionOrder A
    pairNearRepresentation : ExactNearPairIncidenceRepresentation A K L

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
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (K : WeightedKernelData Row Col (Scalar A))
    (L : WeightedSchurLaws K) →
  OffPacketPairIncidenceEvidence A K L →
  OffPacketWeightedKernelEvidence A K L
pairIncidenceEvidenceToWeightedKernelEvidence A K L E = record
  { certificate = pairCertificate E
  ; kernelInput = exactKernelInput (pairNearRepresentation E)
  ; offPacketResponse = pairOffPacketResponse E
  ; nearShellResponse = concreteNearResponse (pairNearRepresentation E)
  ; farShellTail = pairFarShellTail E
  ; offPacketBelowNearPlusTail = pairOffPacketBelowNearPlusTail E
  ; concreteNearResponseRepresentedByKernel =
      concreteNearResponseBelowCertifiedKernelOutput
        A K L
        (pairOrderReflexive E)
        (pairNearRepresentation E)
  ; schurOrderTransport = pairSchurOrderTransport E
  }

pairIncidenceEvidenceToOffPacketSplit :
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (K : WeightedKernelData Row Col (Scalar A))
    (L : WeightedSchurLaws K) →
  OffPacketPairIncidenceEvidence A K L →
  OffPacketSchurSplitInputs A
pairIncidenceEvidenceToOffPacketSplit A K L E =
  weightedKernelEvidenceToOffPacketSplit A K L
    (pairIncidenceEvidenceToWeightedKernelEvidence A K L E)
