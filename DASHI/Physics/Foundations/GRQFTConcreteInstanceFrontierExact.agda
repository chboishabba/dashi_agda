{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTConcreteInstanceFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- FIRST GENUINELY OPEN LOCAL GR/QFT INSTANCE FRONTIER
--
-- Transport/normalization compilers are paid.  The remaining internal work is
-- concrete-instance work, not another abstract theorem wrapper.
------------------------------------------------------------------------

data GRQFTConcreteInstanceLeaf : Set where
  attachPinnedLiteralYMToRecoveredQFT :
    GRQFTConcreteInstanceLeaf
  attachLiteralNonflatGRToRecoveredGR :
    GRQFTConcreteInstanceLeaf
  instantiateCommonEinsteinMetricVariation :
    GRQFTConcreteInstanceLeaf
  instantiateCommonBalabanAllSectorProducer :
    GRQFTConcreteInstanceLeaf
  instantiateSharedMetricProducerLanguage :
    GRQFTConcreteInstanceLeaf
  evaluateSameCarrierStressResidual :
    GRQFTConcreteInstanceLeaf
  replaceRejectedW4CalibrationCandidate :
    GRQFTConcreteInstanceLeaf

canonicalConcreteInstanceLeaves :
  List GRQFTConcreteInstanceLeaf
canonicalConcreteInstanceLeaves =
  attachPinnedLiteralYMToRecoveredQFT
  ∷ attachLiteralNonflatGRToRecoveredGR
  ∷ instantiateCommonEinsteinMetricVariation
  ∷ instantiateCommonBalabanAllSectorProducer
  ∷ instantiateSharedMetricProducerLanguage
  ∷ evaluateSameCarrierStressResidual
  ∷ replaceRejectedW4CalibrationCandidate
  ∷ []

record GRQFTConcreteInstanceFrontier : Set where
  constructor grqftConcreteInstanceFrontier
  field
    directQFTTargetEqualityStillPrimitive : Bool
    directQFTTargetEqualityStillPrimitiveIsFalse :
      directQFTTargetEqualityStillPrimitive ≡ false
    directGRTargetEqualityStillPrimitive : Bool
    directGRTargetEqualityStillPrimitiveIsFalse :
      directGRTargetEqualityStillPrimitive ≡ false
    finiteEinsteinEquationStillOpen : Bool
    finiteEinsteinEquationStillOpenIsFalse :
      finiteEinsteinEquationStillOpen ≡ false
    finiteNormalizedCouplingUniquenessStillOpen : Bool
    finiteNormalizedCouplingUniquenessStillOpenIsFalse :
      finiteNormalizedCouplingUniquenessStillOpen ≡ false
    currentW4CandidateStillUnknown : Bool
    currentW4CandidateStillUnknownIsFalse :
      currentW4CandidateStillUnknown ≡ false
    remainingLeaves : List GRQFTConcreteInstanceLeaf
    frontierStatement : String

open GRQFTConcreteInstanceFrontier public

canonicalGRQFTConcreteInstanceFrontier :
  GRQFTConcreteInstanceFrontier
canonicalGRQFTConcreteInstanceFrontier =
  grqftConcreteInstanceFrontier
    false refl
    false refl
    false refl
    false refl
    false refl
    canonicalConcreteInstanceLeaves
    "Pinned YM stress is definitionally literal YM stress; one pinned-literal=recovered-QFT seam transports it to the selected target. Remaining local work is that same-object attachment, GR analytic realization, total-sector aggregation/shared stress, and replacement of the rejected W4 calibration candidate."
