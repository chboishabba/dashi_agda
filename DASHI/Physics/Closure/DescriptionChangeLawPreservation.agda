module DASHI.Physics.Closure.DescriptionChangeLawPreservation where

-- A foundations-facing distinction between two questions that are easy to
-- conflate:
--
--   * operation-order invariance asks whether locally available operations may
--     be scheduled differently without changing the causal result;
--   * description-change preservation asks whether a state may be reduced to a
--     canonical description without changing its observable content or losing
--     its lawful continuation.
--
-- This module formalises the second question on the existing normalizeAdd / W9
-- MDL seam.  It does not claim a Wolfram-style causal-invariance theorem, a
-- general coarse-graining theorem, or a derivation of spacetime.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_+_)

import DASHI.Arithmetic.NormalizeAdd as NA
import DASHI.Arithmetic.NormalizeAddState as NAS
import DASHI.Arithmetic.NormalizeAddSumPreservation as Sum
import DASHI.Physics.Closure.W9MDLTerminationSeamRoute as W9

------------------------------------------------------------------------
-- The two foundational axes.


data FoundationsVariationAxis : Set where
  operationOrder : FoundationsVariationAxis
  stateDescription : FoundationsVariationAxis


data FoundationsInvariantTarget : Set where
  causalDependencyShape : FoundationsInvariantTarget
  observableAndLawfulContinuation : FoundationsInvariantTarget

record FoundationsQuestion : Set where
  field
    variedAxis : FoundationsVariationAxis
    invariantTarget : FoundationsInvariantTarget
    plainQuestion : String

operationOrderQuestion : FoundationsQuestion
operationOrderQuestion =
  record
    { variedAxis = operationOrder
    ; invariantTarget = causalDependencyShape
    ; plainQuestion =
        "If locally available operations happen in another order, is the same causal structure obtained?"
    }

descriptionChangeQuestion : FoundationsQuestion
descriptionChangeQuestion =
  record
    { variedAxis = stateDescription
    ; invariantTarget = observableAndLawfulContinuation
    ; plainQuestion =
        "If the same state is rewritten more compactly, is the observable preserved and does a lawful continuation remain?"
    }

------------------------------------------------------------------------
-- Description-change law preservation.
--
-- This is intentionally stronger than merely changing units and narrower than
-- a universal renormalisation theorem.  A description-changing operator must:
--
--   1. preserve a named observable;
--   2. preserve the existence of the admitted continuation;
--   3. reach a named canonical state; and
--   4. be idempotent once that canonicalisation has been applied.

record DescriptionChangeLaw : Setω where
  field
    State : Set
    Observable : Set

    changeDescription : State → State
    observe : State → Observable

    lawfulContinuation : State → Set
    canonical : State → Set

    observablePreserved :
      ∀ s → observe (changeDescription s) ≡ observe s

    lawfulContinuationPreserved :
      ∀ s →
      lawfulContinuation s →
      lawfulContinuation (changeDescription s)

    reachesCanonical :
      ∀ s → canonical (changeDescription s)

    canonicalisationIdempotent :
      ∀ s →
      changeDescription (changeDescription s)
      ≡
      changeDescription s

------------------------------------------------------------------------
-- Existing concrete witness: normalizeAdd.
--
-- normalizeAdd changes residue/carry bookkeeping while leaving lhs and rhs
-- fixed.  Its observable sum is therefore preserved definitionally; the next
-- description is canonical; and a second application is definitionally the
-- same state.  The admitted continuation here is precisely "one more
-- normalization step is canonical", not an unrestricted claim about every
-- physical future.

normalizeAdd-idempotent :
  ∀ s →
  NA.normalizeAdd (NA.normalizeAdd s)
  ≡
  NA.normalizeAdd s
normalizeAdd-idempotent _ = refl

normalizeAddLawfulContinuation :
  NAS.NormalizeAddState → Set
normalizeAddLawfulContinuation s =
  NAS.normalizeAddCanonical (NA.normalizeAdd s)

normalizeAdd-lawfulContinuationPreserved :
  ∀ s →
  normalizeAddLawfulContinuation s →
  normalizeAddLawfulContinuation (NA.normalizeAdd s)
normalizeAdd-lawfulContinuationPreserved s _ =
  NA.normalizeAdd-canonical (NA.normalizeAdd s)

canonicalDescriptionChangeLaw : DescriptionChangeLaw
canonicalDescriptionChangeLaw =
  record
    { State = NAS.NormalizeAddState
    ; Observable = Nat
    ; changeDescription = NA.normalizeAdd
    ; observe = λ s → NAS.lhs s + NAS.rhs s
    ; lawfulContinuation = normalizeAddLawfulContinuation
    ; canonical = NAS.normalizeAddCanonical
    ; observablePreserved = Sum.normalizeAdd-sumPreserved
    ; lawfulContinuationPreserved =
        normalizeAdd-lawfulContinuationPreserved
    ; reachesCanonical = NA.normalizeAdd-canonical
    ; canonicalisationIdempotent = normalizeAdd-idempotent
    }

------------------------------------------------------------------------
-- Link to the existing MDL termination seam and explicit scope boundaries.

record DescriptionChangeLawReceipt : Setω where
  field
    law : DescriptionChangeLaw
    mdlTerminationSeam : W9.MDLTerminationSeamWitness

    question : FoundationsQuestion

    establishedClaims : List String
    nonClaims : List String

canonicalDescriptionChangeLawReceipt : DescriptionChangeLawReceipt
canonicalDescriptionChangeLawReceipt =
  record
    { law = canonicalDescriptionChangeLaw
    ; mdlTerminationSeam = W9.canonicalMDLTerminationSeamWitness
    ; question = descriptionChangeQuestion
    ; establishedClaims =
        "normalizeAdd is a concrete description-changing operator"
        ∷ "the lhs+rhs observable is preserved"
        ∷ "the admitted next continuation remains canonical"
        ∷ "canonicalisation is idempotent"
        ∷ "the operator is connected to the accepted W9 MDL termination seam"
        ∷ []
    ; nonClaims =
        "not a theorem that arbitrary coarse-grainings preserve physics"
        ∷ "not a Nyquist replacement"
        ∷ "not a statistical noise classifier"
        ∷ "not a Wolfram-style causal-invariance or confluence theorem"
        ∷ "not a derivation of spacetime"
        ∷ []
    }

currentDescriptionChangeFoundationsQuestion : FoundationsQuestion
currentDescriptionChangeFoundationsQuestion =
  DescriptionChangeLawReceipt.question
    canonicalDescriptionChangeLawReceipt
