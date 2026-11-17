module DASHI.Analysis.CollatzSyracuseEarlyCylinderEliminationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseEarlyCylinderEliminationExact as Early

leaf1100Paid :
  Early.EarlyCylinderEliminationBoundary.prefix1100Paid
    Early.canonicalEarlyCylinderEliminationBoundary
  ≡ 1
leaf1100Paid = refl

leaf11010Paid :
  Early.EarlyCylinderEliminationBoundary.prefix11010Paid
    Early.canonicalEarlyCylinderEliminationBoundary
  ≡ 1
leaf11010Paid = refl

leaf11100Paid :
  Early.EarlyCylinderEliminationBoundary.prefix11100Paid
    Early.canonicalEarlyCylinderEliminationBoundary
  ≡ 1
leaf11100Paid = refl

residualCompilerPaid :
  Early.EarlyCylinderEliminationBoundary.residualThreeCylinderCompilerPaid
    Early.canonicalEarlyCylinderEliminationBoundary
  ≡ 1
residualCompilerPaid = refl

residualProducerOpen :
  Early.EarlyCylinderEliminationBoundary.residualProducerPaid
    Early.canonicalEarlyCylinderEliminationBoundary
  ≡ 0
residualProducerOpen = refl
