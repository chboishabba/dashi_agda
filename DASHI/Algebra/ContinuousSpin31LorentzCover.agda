module DASHI.Algebra.ContinuousSpin31LorentzCover where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Unified.GRQuantumStrictProofTerms as Strict

------------------------------------------------------------------------
-- Continuous Spin(3,1) -> SO+(3,1) double cover.
--
-- Finite Q8 -> V4 is a useful exact model, but it is not the connected Lie-group
-- theorem.  This authority requires topology, smooth structure, the identity
-- component, a continuous/smooth homomorphism, exact kernel, local triviality,
-- and two-sheeted fibres.

record TopologicalGroup : Set₁ where
  field
    Carrier : Set
    identity : Carrier
    product : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier

    OpenSet : Set
    isOpen : OpenSet → Set
    contains : OpenSet → Carrier → Set

    groupLaws : Set
    groupLawsProof : groupLaws
    topologyLaws : Set
    topologyLawsProof : topologyLaws
    multiplicationContinuous : Set
    multiplicationContinuousProof : multiplicationContinuous
    inverseContinuous : Set
    inverseContinuousProof : inverseContinuous
open TopologicalGroup public

record SmoothGroupMap
  (domain codomain : TopologicalGroup) : Set₁ where
  field
    map : Carrier domain → Carrier codomain
    homomorphism :
      (left right : Carrier domain) →
      map (product domain left right)
      ≡ product codomain (map left) (map right)
    identityPreserved : map (identity domain) ≡ identity codomain
    continuous : Set
    continuousProof : continuous
    smooth : Set
    smoothProof : smooth
open SmoothGroupMap public

record TwoSheetedCover
  (domain codomain : TopologicalGroup)
  (rho : SmoothGroupMap domain codomain) : Set₁ where
  field
    Preimage : Carrier codomain → Set
    exactPreimage : (target : Carrier codomain) → Preimage target

    plusOne minusOne : Carrier domain
    plusAndMinusDistinct : Set
    plusAndMinusDistinctProof : plusAndMinusDistinct

    kernelExactlyPlusMinusOne :
      (element : Carrier domain) →
      Set

    Fiber : Carrier codomain → Set
    fiberHasExactlyTwoPoints :
      (target : Carrier codomain) → Set

    evenlyCoveredNeighborhood :
      (target : Carrier codomain) → Set
    localHomeomorphism : Set
    localHomeomorphismProof : localHomeomorphism
    coveringMap : Set
    coveringMapProof : coveringMap
open TwoSheetedCover public

record ContinuousSpin31LorentzCover : Set₁ where
  field
    Spin31 : TopologicalGroup
    SOPlus31 : TopologicalGroup
    rho : SmoothGroupMap Spin31 SOPlus31
    cover : TwoSheetedCover Spin31 SOPlus31 rho

    spin31IsConnectedDoubleCover : Set
    spin31IsConnectedDoubleCoverProof : spin31IsConnectedDoubleCover
    targetIsProperOrthochronousLorentzGroup : Set
    targetIsProperOrthochronousLorentzGroupProof :
      targetIsProperOrthochronousLorentzGroup
    lieAlgebraMapIsIsomorphism : Set
    lieAlgebraMapIsIsomorphismProof : lieAlgebraMapIsIsomorphism
    actionPreservesMinkowskiQuadraticForm : Set
    actionPreservesMinkowskiQuadraticFormProof :
      actionPreservesMinkowskiQuadraticForm
    orientationAndTimeOrientationPreserved : Set
    orientationAndTimeOrientationPreservedProof :
      orientationAndTimeOrientationPreserved

    algebraicSurface : Strict.StrictSpinDoubleCoverProof
    spinCarrierAgreement :
      Strict.SpinDoubleCoverProof.Spin
        (Strict.StrictSpinDoubleCoverProof.base algebraicSurface)
      ≡ Carrier Spin31
    lorentzCarrierAgreement :
      Strict.SpinDoubleCoverProof.SO
        (Strict.StrictSpinDoubleCoverProof.base algebraicSurface)
      ≡ Carrier SOPlus31
    algebraicAndContinuousMapsAgree : Set
    algebraicAndContinuousMapsAgreeProof :
      algebraicAndContinuousMapsAgree
open ContinuousSpin31LorentzCover public

continuousSpinAlgebraicSurface :
  ContinuousSpin31LorentzCover → Strict.StrictSpinDoubleCoverProof
continuousSpinAlgebraicSurface = algebraicSurface
