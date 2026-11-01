module DASHI.Core.RecoverableQuotientCompositionExact where

------------------------------------------------------------------------
-- EXACT COMPOSITION OF REOPENABLE PROJECTIONS
--
-- This is a small compositional shell around the existing
-- ProvenanceBearingQuotient.  It makes the residual of a composite quotient
-- explicit:
--
--   delta_21(x) = (delta_1(x), delta_2(pi_1 x))
--
-- and proves exact reopening by construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as PBQ

record ExactRecoverableProjection (X Y : Set) : Set₁ where
  constructor exactRecoverableProjection
  field
    Residual : Set
    project : X → Y
    residual : X → Residual
    reopen : Y → Residual → X
    reopenExact : (x : X) → reopen (project x) (residual x) ≡ x

open ExactRecoverableProjection public

fromProvenanceBearingQuotient :
  (core : Fibre.FibreRestrictionCore) →
  PBQ.ProvenanceBearingQuotient core →
  ExactRecoverableProjection (Fibre.Carrier core) (Fibre.Surface core)
fromProvenanceBearingQuotient core quotient =
  exactRecoverableProjection
    (PBQ.Receipt quotient)
    (Fibre.project core)
    (PBQ.receipt quotient)
    (PBQ.reopen quotient)
    (PBQ.reopenExact quotient)

composeRecoverable :
  ∀ {X Y Z : Set} →
  ExactRecoverableProjection X Y →
  ExactRecoverableProjection Y Z →
  ExactRecoverableProjection X Z
composeRecoverable first second =
  exactRecoverableProjection
    (Residual first × Residual second)
    (λ x → project second (project first x))
    (λ x → residual first x , residual second (project first x))
    (λ z receiptPair →
      reopen first
        (reopen second z (secondResidual receiptPair))
        (firstResidual receiptPair))
    reopenComposite
  where
    firstResidual :
      Residual first × Residual second → Residual first
    firstResidual (left , right) = left

    secondResidual :
      Residual first × Residual second → Residual second
    secondResidual (left , right) = right

    reopenComposite :
      (x : X) →
      reopen first
        (reopen second
          (project second (project first x))
          (residual second (project first x)))
        (residual first x)
      ≡ x
    reopenComposite x
      rewrite reopenExact second (project first x)
            | reopenExact first x = refl

compositeResidualIsProduct :
  ∀ {X Y Z : Set}
    (first : ExactRecoverableProjection X Y)
    (second : ExactRecoverableProjection Y Z) →
  Residual (composeRecoverable first second)
  ≡ (Residual first × Residual second)
compositeResidualIsProduct first second = refl
