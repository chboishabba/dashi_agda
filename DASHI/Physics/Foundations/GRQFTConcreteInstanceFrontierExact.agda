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
  attachLiteralRound131YMToRecoveredQFT :
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
  attachLiteralRound131YMToRecoveredQFT
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
    "All currently identified transport/normalization debt is paid. Remaining local GR/QFT work is same-object and shared-metric concrete instantiation plus replacement of the numerically rejected W4 calibration candidate."
