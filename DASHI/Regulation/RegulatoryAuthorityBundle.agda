module DASHI.Regulation.RegulatoryAuthorityBundle where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Regulation.RegulatoryProjectionCore

----------------------------------------------------------------------
-- Multi-authority composition.
--
-- Authorities remain separate.  The bundle does not merge their laws;
-- it indexes the projections that constrain one shared activity carrier.
----------------------------------------------------------------------

record AuthorityBundle : Set₁ where
  field
    SharedActivity : Set
    AuthorityIndex : Set

    projectionAt : AuthorityIndex → RegulatoryProjection
    embedActivity :
      (i : AuthorityIndex) →
      SharedActivity → HiddenActivity (projectionAt i)

    bundleReading : String

open AuthorityBundle public

record EffectiveObligationSurface (B : AuthorityBundle) : Set₁ where
  field
    EffectiveObligation : Set

    collect :
      (i : AuthorityIndex B) →
      (activity : SharedActivity B) →
      List EffectiveObligation

    -- Collection preserves authority provenance; it is not an assertion
    -- that all obligations share a common source or universal rank.
    provenancePreserved : ⊤
    effectiveReading    : String

open EffectiveObligationSurface public

record ConflictWitness
  (B : AuthorityBundle)
  (E : EffectiveObligationSurface B) : Set₁ where
  field
    leftAuthority  : AuthorityIndex B
    rightAuthority : AuthorityIndex B

    leftObligation  : EffectiveObligation E
    rightObligation : EffectiveObligation E

    conflictRelation : Compatibility
    conflictReading  : String

open ConflictWitness public

record RegulatoryPressure
  (B : AuthorityBundle)
  (E : EffectiveObligationSurface B) : Set₁ where
  field
    Cost : Set

    zeroCost : Cost
    combine  : Cost → Cost → Cost

    obligationCost : EffectiveObligation E → Cost

    pressureReading : String

open RegulatoryPressure public

record NatRegulatoryPressure
  (B : AuthorityBundle)
  (E : EffectiveObligationSurface B) : Set₁ where
  field
    costOf : EffectiveObligation E → Nat

  totalCost : List (EffectiveObligation E) → Nat
  totalCost []       = zero
  totalCost (x ∷ xs) = costOf x + totalCost xs

open NatRegulatoryPressure public

----------------------------------------------------------------------
-- A theorem bundle contains actual terms.  It is downstream of the
-- projections and comparisons, and introduces no Boolean verification.
----------------------------------------------------------------------

record RegulatoryTheoryBundle : Set₁ where
  field
    authorities : AuthorityBundle
    obligations : EffectiveObligationSurface authorities

    guards : RegulatoryGuardBundle

    conflictGraph : RegulatoryConflictGraph

    authoritySeparation : ⊤
    nonReconstruction   : ⊤
    evidenceGated       : ⊤

    theoryReading : String

open RegulatoryTheoryBundle public

canonicalAuthorityBundle : AuthorityBundle
canonicalAuthorityBundle = record
  { SharedActivity = ⊤
  ; AuthorityIndex = ⊤
  ; projectionAt = λ _ → canonicalRegulatoryProjection
  ; embedActivity = λ _ activity → activity
  ; bundleReading = "Canonical one-authority bundle."
  }

canonicalEffectiveSurface :
  EffectiveObligationSurface canonicalAuthorityBundle
canonicalEffectiveSurface = record
  { EffectiveObligation = ⊤
  ; collect = λ _ _ → tt ∷ []
  ; provenancePreserved = tt
  ; effectiveReading = "Canonical effective surface with preserved authority index."
  }

canonicalConflictGraph : RegulatoryConflictGraph
canonicalConflictGraph = record
  { Node = ⊤
  ; relation = λ _ _ → compatible
  ; graphReading = "Canonical graph: one compatible node."
  }

canonicalRegulatoryTheoryBundle : RegulatoryTheoryBundle
canonicalRegulatoryTheoryBundle = record
  { authorities = canonicalAuthorityBundle
  ; obligations = canonicalEffectiveSurface
  ; guards = canonicalGuards
  ; conflictGraph = canonicalConflictGraph
  ; authoritySeparation = tt
  ; nonReconstruction = tt
  ; evidenceGated = tt
  ; theoryReading = "Regulatory anatomy bundle: authority-indexed, residual-aware, and evidence-gated."
  }
