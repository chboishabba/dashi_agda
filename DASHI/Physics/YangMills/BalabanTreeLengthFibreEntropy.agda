module DASHI.Physics.YangMills.BalabanTreeLengthFibreEntropy where

-- Source boundary for the replacement of the synthetic diameter-shell
-- entropy lane by Bałaban's tree-length entropy lane.
--
-- CMP 109 (1987), p. 257, defines a localization domain as a finite
-- wall-connected family of M-cubes.  After rescaling those M-cubes to unit
-- cubes, d_j(X) is the length of a shortest tree graph contained in X and
-- meeting every cube of X.  The same paragraph says that shortest trees made
-- from cube edges give an equivalent definition.  Thus the base-domain
-- normalization is edgeCount(T) = d_j(X); no diameter comparison is used.
--
-- This module makes that source-backed normalization and the proof-irrelevant
-- code-fibre boundary explicit.  It intentionally does *not* manufacture the
-- source-specific weighted fibre estimate or the KP incompatibility charge.

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_≤_)
open import Relation.Nullary using (Dec)

open import DASHI.Core.Prelude using (_×_; _,_; proj₁; proj₂)
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; balaban-cmp-109
  ; dashi-internal-proof
  ; paperImport
  ; provedConditionalReducer
  ; VerificationStatus
  )

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- Canonical codes, rather than equality of proof-carrying tree records.

record TreeCodeEquality (TreeCode : Set) : Set₁ where
  field
    _≡ᶜ_ : (left right : TreeCode) → Dec (left ≡ right)

record CanonicalTreeCodeFibre
  (Domain TreeCode : Set)
  : Set₁ where
  field
    codeEquality : TreeCodeEquality TreeCode
    canonicalTreeCode : Domain → TreeCode

  fibre : TreeCode → Domain → Set
  fibre code X = canonicalTreeCode X ≡ code

  fibre-dec : ∀ code X → Dec (fibre code X)
  fibre-dec code X =
    TreeCodeEquality._≡ᶜ_ codeEquality (canonicalTreeCode X) code

  assigned : ∀ X → fibre (canonicalTreeCode X) X
  assigned X = refl

  functional : ∀ {left right X} → fibre left X → fibre right X → left ≡ right
  functional {left} {right} left-fibre right-fibre =
    trans (sym left-fibre) right-fibre

  sound : ∀ {code X} → fibre code X → canonicalTreeCode X ≡ code
  sound witness = witness

open CanonicalTreeCodeFibre public

------------------------------------------------------------------------
-- The source-normalised minimizer.  `ConnectsDomainCubes` deliberately
-- remains a parameter: CMP 109 fixes the base M-cube notion, whereas the
-- later R-operation has to supply its own precise marked-component relation.

record CanonicalShortestConnectingTree
  (Domain TreeCode : Set)
  (ConnectsDomainCubes : Domain → TreeCode → Set)
  (edgeCount sourceLength : TreeCode → Nat)
  (treeLength : Domain → Nat)
  : Set₁ where
  field
    codeFibre : CanonicalTreeCodeFibre Domain TreeCode

    admissible : ∀ X → ConnectsDomainCubes X (canonicalTreeCode codeFibre X)

    minimal : ∀ X code →
      ConnectsDomainCubes X code →
      sourceLength (canonicalTreeCode codeFibre X) ≤ sourceLength code

    realises-treeLength : ∀ X →
      sourceLength (canonicalTreeCode codeFibre X) ≡ treeLength X

    sourceLength-is-edgeCount : ∀ code → sourceLength code ≡ edgeCount code

  canonical-edgeCount-is-treeLength : ∀ X →
    edgeCount (canonicalTreeCode codeFibre X) ≡ treeLength X
  canonical-edgeCount-is-treeLength X =
    trans (sym (sourceLength-is-edgeCount (canonicalTreeCode codeFibre X)))
      (realises-treeLength X)

open CanonicalShortestConnectingTree public

------------------------------------------------------------------------
-- CMP 109 provenance.  This record is the exact input still needed to
-- instantiate the generic code construction for the scale-k localization
-- domains.  The edge-count equality is source-backed for base localization
-- domains; it is not an assertion about every later enlarged R-domain.

record BalabanCMP109TreeLengthSource
  (Domain TreeCode : Set)
  (ConnectsDomainCubes : Domain → TreeCode → Set)
  (edgeCount sourceLength : TreeCode → Nat)
  (treeLength : Domain → Nat)
  : Set₁ where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    sourceDefinition : String
    status : VerificationStatus

    canonicalShortestTree :
      CanonicalShortestConnectingTree
        Domain TreeCode ConnectsDomainCubes edgeCount sourceLength treeLength

    sourceAuthorityIsCMP109 : sourceAuthorityId ≡ balaban-cmp-109
    theoremLocatorIsCanonical :
      theoremLocator ≡ "CMP 109 (1987), p. 257, definitions preceding (0.24)-(0.25)"
    sourceDefinitionIsCanonical :
      sourceDefinition ≡
      "After rescaling π_j M-cubes to unit cubes, d_j(X) is the length of a shortest tree graph contained in X and intersecting every cube of X; cube-edge trees give an equivalent definition."
    noClayPromotion : clayYangMillsPromoted ≡ false

------------------------------------------------------------------------
-- Exact remaining analytic inputs.  These are intentionally *not* given
-- current witnesses.  In particular, `weightedFibreBound` and
-- `incompatibilityCharge` are the two Bałaban R/localization obligations
-- which must be extracted from CMP 119 / CMP 122 II before this can replace
-- the present paper-import P06/P07 diameter-shell path.

record TreeLengthWeightedFibreOpenInputs
  (Domain TreeCode Root : Set)
  (edgeCount treeLength : TreeCode → Nat)
  : Set₁ where
  field
    activityWeight : Domain → Set
    residualWeight : Domain → Set

    -- A concrete finite weighted-sum interpretation belongs here once the
    -- localization-domain carrier is extracted.  Keeping it abstract prevents
    -- an accidental replacement of analytic weights by raw cardinalities.
    rootedTree : Root → TreeCode → Set

    activityDecay : Set
    weightedFibreBound : Set
    incompatibilityCharge : Set
    geometricSummation : Set

    sourceBoundary : String
    sourceBoundaryIsCanonical :
      sourceBoundary ≡
      "Open source leaves: finite localization-domain enumeration, weighted fibre estimate over canonical d_k-minimizing tree codes, and the incompatibility charging estimate.  CMP 109 fixes the base d_j normalization only."
    noClayPromotion : clayYangMillsPromoted ≡ false

record TreeLengthWeightedFibreRouteStatus : Set where
  field
    sourceNormalisationExtracted : Bool
    canonicalCodeFibreImplemented : Bool
    weightedFibreEstimateExtracted : Bool
    incompatibilityChargeExtracted : Bool
    kpFeasibilityDerived : Bool
    noClayPromotion : clayYangMillsPromoted ≡ false

currentTreeLengthWeightedFibreRouteStatus : TreeLengthWeightedFibreRouteStatus
currentTreeLengthWeightedFibreRouteStatus = record
  { sourceNormalisationExtracted = true
  ; canonicalCodeFibreImplemented = true
  ; weightedFibreEstimateExtracted = false
  ; incompatibilityChargeExtracted = false
  ; kpFeasibilityDerived = false
  ; noClayPromotion = refl
  }
