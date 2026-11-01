{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRDiscreteToSmoothMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.GRHolonomyTaylorRicciEvidenceExact as E
import DASHI.Physics.Foundations.GRDiscreteToSmoothMaxCutExact as M

requestDoesNotCloseGR :
  E.requestSurfaceAloneClosesCurvatureConvergence ≡ false
requestDoesNotCloseGR = refl

evidenceStillRequired :
  E.theoremBearingBundleStillRequired ≡ true
evidenceStillRequired = refl

canonicalEvidenceNotConstructed :
  M.theoremBearingEvidenceConstructed M.canonicalGRDiscreteToSmoothMaxCut
  ≡ false
canonicalEvidenceNotConstructed = refl
