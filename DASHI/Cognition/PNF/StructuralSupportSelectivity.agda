module DASHI.Cognition.PNF.StructuralSupportSelectivity where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- Structural support is a sparse seam, not a new all-pairs graph.
-- Runtime implementations must measure and bound the support fanout before
-- downstream identity/factor joins are allowed to treat the seam as cheap.
------------------------------------------------------------------------

record StructuralSupportFanoutReceipt : Set where
  constructor structuralSupportFanoutReceipt
  field
    region : RegionId
    factorArgumentCount : Nat
    supportEdgeCount : Nat
    declaredFanoutBudget : Nat
    supportEdgesWithinBudget :
      supportEdgeCount ≤ᶜ (declaredFanoutBudget *ᶜ factorArgumentCount)

open StructuralSupportFanoutReceipt public

record StructuralSupportLookupKey : Set where
  constructor structuralSupportLookupKey
  field
    supportRegion : RegionId
    supportToken : TokenId
    supportObject : ObjectId

open StructuralSupportLookupKey public

record StructuralSupportSelectivityBoundary : Set where
  constructor structuralSupportSelectivityBoundary
  field
    supportMayBeBuiltAsUnboundedTokenObjectCrossProduct : Bool
    supportMayBeBuiltAsUnboundedTokenObjectCrossProductIsFalse :
      supportMayBeBuiltAsUnboundedTokenObjectCrossProduct ≡ false
    regionTokenObjectCompositeKeyAvailable : Bool
    regionTokenObjectCompositeKeyAvailableIsTrue :
      regionTokenObjectCompositeKeyAvailable ≡ true
    supportFanoutMustBeMeasured : Bool
    supportFanoutMustBeMeasuredIsTrue : supportFanoutMustBeMeasured ≡ true

open StructuralSupportSelectivityBoundary public

canonicalStructuralSupportSelectivityBoundary :
  StructuralSupportSelectivityBoundary
canonicalStructuralSupportSelectivityBoundary =
  structuralSupportSelectivityBoundary false refl true refl true refl
