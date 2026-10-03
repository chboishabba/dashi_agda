{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayProjectiveCompactnessMaxCut20261003Test where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.BalabanClayProjectiveCompactnessMaxCut20261003Exact as Cut

projectiveMarginalsRemainLive :
  Cut.routeDisposition Cut.projectiveFiniteMarginals
    ≡ Cut.viablePhysicalProducer
projectiveMarginalsRemainLive = refl

boundedPlaquetteStillInsufficient :
  Cut.routeDisposition Cut.boundedPlaquetteMoment
    ≡ Cut.insufficientForContinuumContainment
boundedPlaquetteStillInsufficient = refl
