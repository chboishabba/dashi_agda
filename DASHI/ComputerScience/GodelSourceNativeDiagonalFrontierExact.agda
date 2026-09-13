module DASHI.ComputerScience.GodelSourceNativeDiagonalFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel
import DASHI.ComputerScience.GodelPrimitiveRecursiveRepresentabilityBridgeExact as PR

------------------------------------------------------------------------
-- SOURCE-NATIVE GÖDEL ROUTE VS EXECUTABLE BASE-12 PRESENTATION
--
-- The standard Gödel construction establishes a source-native substitution
-- function on its own Gödel numbering and proves that relation primitive
-- recursive before applying representability.  Our base-12 codec is an exact
-- executable presentation, but it is not silently identified with that
-- historical numbering.
------------------------------------------------------------------------

record SourceNativeGodelCoding
    (F : Godel.ArithmetisedFormalSystem)
    (S : Godel.ArithmetisedSubstitution F)
    (PRT : PR.PrimitiveRecursiveTheory) : Set₁ where
  constructor sourceNativeGodelCoding
  field
    sourceNativeSelfSubstitutionPR :
      PR.SelfSubstitutionPrimitiveRecursive F S PRT

open SourceNativeGodelCoding public

record SourceNativeDiagonalAuthority
    (F : Godel.ArithmetisedFormalSystem)
    (S : Godel.ArithmetisedSubstitution F)
    (PRT : PR.PrimitiveRecursiveTheory) : Set₁ where
  constructor sourceNativeDiagonalAuthority
  field
    coding : SourceNativeGodelCoding F S PRT
    representability : PR.PrimitiveRecursiveRepresentabilityAuthority F PRT
    precomposition : PR.RepresentedFunctionPrecomposition F

open SourceNativeDiagonalAuthority public

sourceNativeAuthorityCompilesDiagonal :
  (F : Godel.ArithmetisedFormalSystem) →
  (S : Godel.ArithmetisedSubstitution F) →
  (PRT : PR.PrimitiveRecursiveTheory) →
  SourceNativeDiagonalAuthority F S PRT →
  Godel.DiagonalLemmaAuthority F
sourceNativeAuthorityCompilesDiagonal F S PRT authority =
  PR.compileDiagonalLemmaFromPrimitiveRecursiveRepresentation
    F S PRT
    (sourceNativeSelfSubstitutionPR (coding authority))
    (representability authority)
    (precomposition authority)

------------------------------------------------------------------------
-- Proof-debt split: the historical theorem family is source-established, but
-- exact local contract alignment is still required before certification.
------------------------------------------------------------------------

sourceNativeRepresentabilityNeedsAlignment : Debt.ProofDebtRoutingReceipt
sourceNativeRepresentabilityNeedsAlignment =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.sourceEstablished
    Debt.transcribedUnaligned
    Debt.proofDeferred
    Debt.sourceOnly
    Debt.transcriptionDebt
    refl

------------------------------------------------------------------------
-- No transport from source-native numbering to our executable base-12 code
-- without a same-code/isomorphism theorem preserving substitution semantics.
------------------------------------------------------------------------

data SourceNativePRStatusTransfersToBase12 : Set where
data Base12ExactRetractionIdentifiesHistoricalGodelNumbering : Set where

data SourceCitationConstructsDiagonalAuthority : Set where

sourceNativePRDoesNotTransferWithoutWeld :
  SourceNativePRStatusTransfersToBase12 → ⊥
sourceNativePRDoesNotTransferWithoutWeld ()

base12RetractionDoesNotIdentifyHistoricalNumbering :
  Base12ExactRetractionIdentifiesHistoricalGodelNumbering → ⊥
base12RetractionDoesNotIdentifyHistoricalNumbering ()

citationDoesNotConstructAuthority :
  SourceCitationConstructsDiagonalAuthority → ⊥
citationDoesNotConstructAuthority ()

record GodelSourceNativeDiagonalBoundary : Set where
  constructor godelSourceNativeDiagonalBoundary
  field
    sourceNativeRouteTyped : Bool
    base12RouteTypedSeparately : Bool
    sourceNativeRepresentabilityAligned : Bool
    sourceNativeAuthorityCertified : Bool
    base12PromotedToHistoricalNumbering : Bool
    concreteDiagonalLemmaCertified : Bool

canonicalGodelSourceNativeDiagonalBoundary : GodelSourceNativeDiagonalBoundary
canonicalGodelSourceNativeDiagonalBoundary =
  godelSourceNativeDiagonalBoundary
    true true false false false false
