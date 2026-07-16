module DASHI.Physics.YangMills.CMP122RelativeDomainSourceLedger where

-- Literal source-extraction boundary for the relative localization terms in
-- Balaban, CMP 122 II.  This module intentionally contains no proposed
-- lattice carrier, component algorithm, attachment code, or fibre estimate.
-- Its purpose is to make those future choices answer to the source index.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Base renaming (ℕ to Nat)
open import Data.Product using (_×_)

open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  ; paperImport
  )

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- The rows are deliberately metadata rather than theorem witnesses.  They
-- identify what a future concrete model must account for.
data CMP122IndexedSymbol : Set where
  source-Y source-Z-minus source-residual-components source-relative-tree-length source-S-operation
    source-K-activity source-R-activity : CMP122IndexedSymbol

record CMP122SymbolLedgerRow : Set where
  field
    symbol : CMP122IndexedSymbol
    sourceLocator : String
    carrierScale : String
    finiteRepresentationStatus : Bool
    connectivityStatus : Bool
    enlargementStatus : Bool
    componentStatus : Bool
    rootOrIncidenceStatus : Bool
    weightStatus : Bool
    summationStatus : Bool

-- CMP 122 II (1.67)--(1.68), pp. 376--377 in the article pagination.
-- `Y ∩ Z⁻` is a union of components of Z⁻ containing at least one component;
-- it is not source-faithful to impose Z ⊆ Y.  The relative tree is contained
-- in Y and meets every M-cube of each component of Y \ Z.
record CMP122RelativeIndex : Set₁ where
  field
    SourceDomain : Set
    MCube : Set
    SourceComponent : Set
    SourceTreeCode : Set

    scale : Nat
    Y : SourceDomain
    Z-minus : SourceDomain

    isAdmissibleLocalizationDomain : SourceDomain → Set
    isExcludedLargeFieldRegion : SourceDomain → Set

    sourcePairAdmissible :
      isAdmissibleLocalizationDomain Y ×
      isExcludedLargeFieldRegion Z-minus

    residualComponents : List SourceComponent
    sourceComponents : SourceDomain → SourceDomain → List SourceComponent
    componentsExact : residualComponents ≡ sourceComponents Y Z-minus
    componentCubes : SourceComponent → List MCube

    tree : SourceTreeCode
    treeContainedInY : SourceTreeCode → SourceDomain → Set
    treeMeetsMCube : SourceTreeCode → MCube → Set
    relativeTreeWitness :
      treeContainedInY tree Y ×
      (∀ component →
        component ∈ residualComponents →
        ∀ cube → cube ∈ componentCubes component → treeMeetsMCube tree cube)

    relativeTreeLength : Nat
    sourceTreeLength : SourceDomain → SourceDomain → Nat
    relativeTreeLengthExact :
      relativeTreeLength ≡ sourceTreeLength Y Z-minus

    -- This is intentionally a source statement, not a construction of a
    -- least tree.  Finite candidate enumeration must be extracted before a
    -- canonical minimizer is introduced.
    treeIsShortest : Set

    sourceAuthorityId : SourceAuthorityId
    sourceLocator : String
    status : VerificationStatus

open CMP122RelativeIndex public

-- The source still leaves several model details to be extracted from the
-- surrounding definitions and resummations.  These false flags prevent this
-- ledger from being mistaken for an instantiated finite carrier.
record CMP122RelativeExtractionState : Set where
  field
    exactFiniteDomainCarrierExtracted : Bool
    exactComponentOperationExtracted : Bool
    exactPairAdmissibilityExtracted : Bool
    exactTreeCandidateEnumerationExtracted : Bool
    exactWeightMajorantExtracted : Bool
    canonicalFibrePartitionProved : Bool
    weightedFibreBoundProved : Bool

currentCMP122RelativeExtractionState : CMP122RelativeExtractionState
currentCMP122RelativeExtractionState = record
  { exactFiniteDomainCarrierExtracted = false
  ; exactComponentOperationExtracted = false
  ; exactPairAdmissibilityExtracted = false
  ; exactTreeCandidateEnumerationExtracted = false
  ; exactWeightMajorantExtracted = false
  ; canonicalFibrePartitionProved = false
  ; weightedFibreBoundProved = false
  }

-- Source-ledger rows.  `true` means the cited passage explicitly exposes the
-- requested datum; `false` means further extraction is required before a
-- concrete definition may be made in DASHI.
cmp122RelativeLedger : List CMP122SymbolLedgerRow
cmp122RelativeLedger =
  record
    { symbol = source-Y
    ; sourceLocator = "CMP 122 II (1.66)--(1.68), pp. 376--377"
    ; carrierScale = "Y ∈ D_k; scale-k localization domain"
    ; finiteRepresentationStatus = false
    ; connectivityStatus = false
    ; enlargementStatus = false
    ; componentStatus = true
    ; rootOrIncidenceStatus = true
    ; weightStatus = true
    ; summationStatus = true
    }
  ∷ record
    { symbol = source-Z-minus
    ; sourceLocator = "CMP 122 II (1.67)--(1.68), pp. 376--377"
    ; carrierScale = "excluded large-field region used in the relative metric"
    ; finiteRepresentationStatus = false
    ; connectivityStatus = false
    ; enlargementStatus = false
    ; componentStatus = true
    ; rootOrIncidenceStatus = true
    ; weightStatus = true
    ; summationStatus = true
    }
  ∷ record
    { symbol = source-residual-components
    ; sourceLocator = "CMP 122 II (1.67), p. 376"
    ; carrierScale = "components of Y \\ Z; each represented by its M-cubes"
    ; finiteRepresentationStatus = false
    ; connectivityStatus = false
    ; enlargementStatus = false
    ; componentStatus = true
    ; rootOrIncidenceStatus = true
    ; weightStatus = false
    ; summationStatus = true
    }
  ∷ record
    { symbol = source-relative-tree-length
    ; sourceLocator = "CMP 122 II (1.67), p. 376"
    ; carrierScale = "M⁻¹ times shortest tree length"
    ; finiteRepresentationStatus = false
    ; connectivityStatus = false
    ; enlargementStatus = false
    ; componentStatus = true
    ; rootOrIncidenceStatus = true
    ; weightStatus = true
    ; summationStatus = true
    }
  ∷ record
    { symbol = source-S-operation
    ; sourceLocator = "CMP 122 II (1.79)--(1.80), p. 384"
    ; carrierScale = "large-field region across successive RG scales"
    ; finiteRepresentationStatus = false
    ; connectivityStatus = false
    ; enlargementStatus = true
    ; componentStatus = true
    ; rootOrIncidenceStatus = false
    ; weightStatus = true
    ; summationStatus = true
    }
  ∷ record
    { symbol = source-K-activity
    ; sourceLocator = "CMP 122 II (1.68), p. 377"
    ; carrierScale = "localized activity indexed by Y ∈ D_k"
    ; finiteRepresentationStatus = false
    ; connectivityStatus = false
    ; enlargementStatus = false
    ; componentStatus = true
    ; rootOrIncidenceStatus = true
    ; weightStatus = true
    ; summationStatus = true
    }
  ∷ record
    { symbol = source-R-activity
    ; sourceLocator = "CMP 122 II (1.98)--(1.100), pp. 390--391"
    ; carrierScale = "exponentiated R-operation, domains X ∈ D_k"
    ; finiteRepresentationStatus = false
    ; connectivityStatus = true
    ; enlargementStatus = true
    ; componentStatus = true
    ; rootOrIncidenceStatus = false
    ; weightStatus = true
    ; summationStatus = true
    }
  ∷ []
