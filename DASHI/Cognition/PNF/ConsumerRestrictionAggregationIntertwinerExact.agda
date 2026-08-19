module DASHI.Cognition.PNF.ConsumerRestrictionAggregationIntertwinerExact where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Consumer-indexed restriction before quotient/fold.
--
-- Runtime motivation: a parent hierarchy close already consumes bounded child
-- interface fibres.  The optimization question is therefore not whether to
-- replace a global-history scan by child fibres; that locality is already
-- present.  The sharper question is whether a selective parent/consumer
-- admission can be applied to the child rows before an expensive quotient/fold.
--
-- The theorem shape is an exact intertwiner:
--
--   restrictAggregate c p (aggregate xs)
--     = aggregate (restrictFine c p xs)
--
-- This is the same proof-engineering discipline used elsewhere in DASHI for
-- factorized refinement/naturality: "compatible" is not enough; the square must
-- commute exactly for the declared consumer and role.
------------------------------------------------------------------------

record FibreSaturatedRestriction
  (Consumer Parent Fine Key : Set)
  : Set₁ where
  field
    fineKey : Fine → Key
    admitFine : Consumer → Parent → Fine → Bool
    saturated : ∀ consumer parent x y →
      fineKey x ≡ fineKey y →
      admitFine consumer parent x ≡ admitFine consumer parent y

open FibreSaturatedRestriction public

record KeyIndexedRestriction
  (Consumer Parent Fine Key : Set)
  : Set₁ where
  field
    keyOf : Fine → Key
    admitKey : Consumer → Parent → Key → Bool

open KeyIndexedRestriction public

keyIndexedRestrictionIsSaturated :
  ∀ {Consumer Parent Fine Key : Set}
    (restriction : KeyIndexedRestriction Consumer Parent Fine Key) →
  FibreSaturatedRestriction Consumer Parent Fine Key
keyIndexedRestrictionIsSaturated restriction = record
  { fineKey = keyOf restriction
  ; admitFine = λ consumer parent fine →
      admitKey restriction consumer parent (keyOf restriction fine)
  ; saturated = λ consumer parent x y sameKey →
      cong (admitKey restriction consumer parent) sameKey
  }
  where
    cong : ∀ {A B : Set} {x y : A} →
      (f : A → B) → x ≡ y → f x ≡ f y
    cong f refl = refl

------------------------------------------------------------------------
-- A single same-key / different-admission witness refutes saturation.
------------------------------------------------------------------------

record AdmissionFactorizationDefect
  {Consumer Parent Fine Key : Set}
  (restriction : FibreSaturatedRestriction Consumer Parent Fine Key)
  : Set where
  field
    consumer : Consumer
    parent : Parent
    left right : Fine
    sameKey : fineKey restriction left ≡ fineKey restriction right
    admissionDiffers :
      admitFine restriction consumer parent left
      ≡ admitFine restriction consumer parent right → ⊥

open AdmissionFactorizationDefect public

saturatedRestrictionRejectsFactorizationDefect :
  ∀ {Consumer Parent Fine Key : Set}
    (restriction : FibreSaturatedRestriction Consumer Parent Fine Key) →
  AdmissionFactorizationDefect restriction → ⊥
saturatedRestrictionRejectsFactorizationDefect restriction defect =
  admissionDiffers defect
    (saturated restriction
      (consumer defect)
      (parent defect)
      (left defect)
      (right defect)
      (sameKey defect))

------------------------------------------------------------------------
-- Fibre-local fold / quotient boundary.
--
-- This record intentionally does not assert that every aggregation is safe to
-- push through.  The exact commuting equation is a separate obligation.  This
-- blocks the common invalid optimization where admission depends on a hidden
-- member coordinate, fibre cardinality, provenance diversity, or the aggregate
-- result itself.
------------------------------------------------------------------------

record FibreLocalFold
  (Fine Aggregate : Set)
  : Set₁ where
  field
    aggregate : List Fine → Aggregate

open FibreLocalFold public

record ConsumerRestrictionAggregationIntertwiner
  (Consumer Parent Fine Aggregate : Set)
  : Set₁ where
  field
    fold : FibreLocalFold Fine Aggregate
    restrictFine : Consumer → Parent → List Fine → List Fine
    restrictAggregate : Consumer → Parent → Aggregate → Aggregate
    intertwines : ∀ consumer parent xs →
      restrictAggregate consumer parent (aggregate fold xs)
      ≡ aggregate fold (restrictFine consumer parent xs)

open ConsumerRestrictionAggregationIntertwiner public

consumerRestrictionMayMoveBeforeAggregation :
  ∀ {Consumer Parent Fine Aggregate : Set}
    (law : ConsumerRestrictionAggregationIntertwiner
      Consumer Parent Fine Aggregate)
    (consumer : Consumer)
    (parent : Parent)
    (xs : List Fine) →
  restrictAggregate law consumer parent (aggregate (fold law) xs)
  ≡ aggregate (fold law) (restrictFine law consumer parent xs)
consumerRestrictionMayMoveBeforeAggregation law consumer parent xs =
  intertwines law consumer parent xs

------------------------------------------------------------------------
-- Role/query indexing.
--
-- A key may be irrelevant for one publication/router while remaining relevant
-- to another.  Pushdown therefore carries the consumer, parent and role/query
-- index; it never promotes local irrelevance into global semantic erasure.
------------------------------------------------------------------------

record ConsumerRoleIndexedRestriction
  (Consumer Parent Role Fine Key : Set)
  : Set₁ where
  field
    indexedKey : Fine → Key
    indexedAdmission : Consumer → Parent → Role → Key → Bool

open ConsumerRoleIndexedRestriction public

------------------------------------------------------------------------
-- Physical-economy evidence is downstream of semantic legality.
--
-- The formal theorem licenses the transformation.  Empirical receipts decide
-- whether it is worthwhile.  The counts are kept separate so a reduction in
-- rows entering GROUP BY is not falsely promoted into a reduction in rows read
-- from PostgreSQL.
------------------------------------------------------------------------

record PushdownEconomyReceipt : Set where
  field
    rowsScanned : Nat
    rowsAdmitted : Nat
    rowsGrouped : Nat
    rowsOutput : Nat
    rowsAttemptedWrite : Nat
    rowsCommittedWrite : Nat
  where
    open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Concentration / heavy-tail optimization pressure.
------------------------------------------------------------------------

record ConcentrationWitness : Set where
  field
    totalWork : Nat
    hottestWork : Nat
    topKWork : Nat
    k : Nat
  where
    open import Agda.Builtin.Nat using (Nat)
