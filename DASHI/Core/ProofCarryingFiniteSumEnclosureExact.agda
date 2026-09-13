module DASHI.Core.ProofCarryingFiniteSumEnclosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PROOF-CARRYING FINITE SUM ENCLOSURE
--
-- Domain-neutral extraction of the useful part of the existing certified
-- finite-assembly pattern.  Unlike a status field of type `Set`, every semantic
-- claim below has an inhabitant.  No analytic theorem is manufactured: a
-- producer must provide the finite terms and the enclosure/Within receipts.
------------------------------------------------------------------------

record FiniteAdditiveCarrier : Set₁ where
  field
    Scalar : Set
    zeroS : Scalar
    addS : Scalar → Scalar → Scalar

open FiniteAdditiveCarrier public

foldScalars :
  (C : FiniteAdditiveCarrier) →
  List (Scalar C) →
  Scalar C
foldScalars C [] = zeroS C
foldScalars C (x ∷ xs) = addS C x (foldScalars C xs)

mapValues :
  {A B : Set} →
  (A → B) →
  List A →
  List B
mapValues f [] = []
mapValues f (x ∷ xs) = f x ∷ mapValues f xs

record ProofCarryingFiniteSumEnclosure
    (C : FiniteAdditiveCarrier) : Set₁ where
  constructor proof-carrying-finite-sum-enclosure
  field
    Term : Set
    terms : List Term
    evaluateTerm : Term → Scalar C

    Interval Error : Set
    Contains : Interval → Scalar C → Set
    aggregate : Interval

    aggregateContainsFiniteSum :
      Contains
        aggregate
        (foldScalars C (mapValues evaluateTerm terms))

    approximant : Scalar C
    error : Error
    Within : Scalar C → Scalar C → Error → Set

    finiteSumWithinApproximant :
      Within
        (foldScalars C (mapValues evaluateTerm terms))
        approximant
        error

    certificateReference : String

open ProofCarryingFiniteSumEnclosure public

------------------------------------------------------------------------
-- ORDERED UPPER-ENDPOINT SPECIALIZATION
--
-- Many consumers do not need to reason about the entire interval object.  They
-- need one theorem: the exact finite fold is below a certified upper endpoint.
-- Keep the interval semantics generic, but require a proof-bearing eliminator
-- from aggregate containment to the chosen order.  The resulting finite-sum
-- upper theorem is then compiler output, not a second domain-level assumption.
------------------------------------------------------------------------

record ProofCarryingFiniteSumUpperEnclosure
    (C : FiniteAdditiveCarrier)
    (certificate : ProofCarryingFiniteSumEnclosure C) : Set₁ where
  field
    lessOrEqual : Scalar C → Scalar C → Set
    certifiedUpper : Scalar C

    aggregateContainmentImpliesUpper :
      ∀ {value : Scalar C} →
      Contains certificate (aggregate certificate) value →
      lessOrEqual value certifiedUpper

    upperReference : String

open ProofCarryingFiniteSumUpperEnclosure public

finiteSumBelowCertifiedUpper :
  ∀ {C certificate} →
  (upperCertificate : ProofCarryingFiniteSumUpperEnclosure C certificate) →
  lessOrEqual upperCertificate
    (foldScalars C
      (mapValues
        (evaluateTerm certificate)
        (terms certificate)))
    (certifiedUpper upperCertificate)
finiteSumBelowCertifiedUpper {certificate = certificate} upperCertificate =
  aggregateContainmentImpliesUpper upperCertificate
    (aggregateContainsFiniteSum certificate)

record ProofCarryingFiniteSumBoundary : Set where
  constructor proof-carrying-finite-sum-boundary
  field
    aggregateContainmentRequiresReceipt : Bool
    aggregateContainmentRequiresReceiptIsTrue :
      aggregateContainmentRequiresReceipt ≡ true

    finiteSumApproximationRequiresReceipt : Bool
    finiteSumApproximationRequiresReceiptIsTrue :
      finiteSumApproximationRequiresReceipt ≡ true

    upperEndpointEliminatesSecondFiniteSumUpperAssumption : Bool
    upperEndpointEliminatesSecondFiniteSumUpperAssumptionIsTrue :
      upperEndpointEliminatesSecondFiniteSumUpperAssumption ≡ true

    finiteCertificateImpliesUnstatedInfiniteLimit : Bool
    finiteCertificateImpliesUnstatedInfiniteLimitIsFalse :
      finiteCertificateImpliesUnstatedInfiniteLimit ≡ false

canonicalProofCarryingFiniteSumBoundary : ProofCarryingFiniteSumBoundary
canonicalProofCarryingFiniteSumBoundary =
  proof-carrying-finite-sum-boundary
    true refl
    true refl
    true refl
    false refl
