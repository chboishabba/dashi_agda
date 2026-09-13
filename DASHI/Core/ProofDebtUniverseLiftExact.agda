module DASHI.Core.ProofDebtUniverseLiftExact where

open import Agda.Primitive using (Level; _⊔_)

import DASHI.Core.ProofDebtRouterExact as Debt

------------------------------------------------------------------------
-- UNIVERSE-POLYMORPHIC SOURCE-ALIGNED DEFERRED THEOREM
--
-- ProofDebtRouterExact's SourceAlignedDeferredTheorem is intentionally simple
-- and currently takes T : Set.  Some established theorem consumers (including
-- dependent finite-game existence records) naturally live in Set₁.  This is a
-- thin universe lift of the same receipt coordinates, not a second debt router.
------------------------------------------------------------------------

record SourceAlignedDeferredTheoremℓ
    {ℓ : Level}
    (T : Set ℓ) : Set ℓ where
  constructor source-aligned-deferred-theoremℓ
  field
    source : Debt.SourceIdentity
    alignment : Debt.StatementAlignmentReceipt
    alignmentVerified : Debt.FullyAligned alignment
    preferredBackend : Debt.PreferredBackend

open SourceAlignedDeferredTheoremℓ public

ConditionalDevelopmentℓ :
  ∀ {ℓT ℓR : Level} → Set ℓT → Set ℓR → Set (ℓT ⊔ ℓR)
ConditionalDevelopmentℓ T Result = T → Result

runConditionalDevelopmentℓ :
  ∀ {ℓT ℓR : Level}
    {T : Set ℓT}
    {Result : Set ℓR} →
  ConditionalDevelopmentℓ T Result → T → Result
runConditionalDevelopmentℓ downstream theorem = downstream theorem

record CertifiedKnownTheoremℓ
    {ℓ : Level}
    (T : Set ℓ) : Set ℓ where
  constructor certified-known-theoremℓ
  field
    deferredReceipt : SourceAlignedDeferredTheoremℓ T
    theorem : T
    backend : Debt.PreferredBackend
    certification : Debt.CertificationStatus

open CertifiedKnownTheoremℓ public

certifyDeferredℓ :
  ∀ {ℓ : Level} {T : Set ℓ} →
  SourceAlignedDeferredTheoremℓ T →
  T →
  Debt.PreferredBackend →
  Debt.CertificationStatus →
  CertifiedKnownTheoremℓ T
certifyDeferredℓ receipt proof backendUsed status =
  certified-known-theoremℓ receipt proof backendUsed status

------------------------------------------------------------------------
-- Existing Set-level receipts embed without changing semantics.
------------------------------------------------------------------------

liftSetDeferred :
  ∀ {T : Set} →
  Debt.SourceAlignedDeferredTheorem T →
  SourceAlignedDeferredTheoremℓ T
liftSetDeferred receipt =
  source-aligned-deferred-theoremℓ
    (Debt.source receipt)
    (Debt.alignment receipt)
    (Debt.alignmentVerified receipt)
    (Debt.preferredBackend receipt)

------------------------------------------------------------------------
-- Boundary: the lift transports provenance/alignment metadata only.  It still
-- contains no theorem inhabitant and cannot turn a Set₁ proposition into Set.
------------------------------------------------------------------------

record ProofDebtUniverseLiftBoundary : Set where
  constructor proof-debt-universe-lift-boundary
  field
    canonicalSourceIdentityReused : Bool
    canonicalAlignmentReceiptReused : Bool
    canonicalBackendStatusReused : Bool
    theoremInhabitantManufacturedByLift : Bool
    theoremUniverseCollapsedToSet : Bool
    secondDebtRouterIntroduced : Bool

canonicalProofDebtUniverseLiftBoundary : ProofDebtUniverseLiftBoundary
canonicalProofDebtUniverseLiftBoundary =
  proof-debt-universe-lift-boundary
    true true true false false false
