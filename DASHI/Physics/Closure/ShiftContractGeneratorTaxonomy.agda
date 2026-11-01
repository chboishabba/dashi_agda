module DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy where

open import DASHI.Physics.Closure.ShiftContractGeneratorFourthStepBoundary as GFB
  using
    ( CertifiedFourthStepExit
    ; CertifiedFourthStepExitOnCycle
    ; CertifiedFourthStepStay
    ; anchoredExplicitFourthStepBoundary
    ; anchoredTrajectoryFourthStepBoundary
    ; balancedComposedFourthStepBoundary
    ; balancedCycleFourthStepBoundary
    ; denseComposedFourthStepBoundary
    ; denseExplicitFourthStepBoundary
    ; oneHotExplicitFourthStepBoundary
    )
open import DASHI.Physics.Closure.ShiftContractMixedScaleTrajectoryFamily as MTF
  using
    ( MixedScaleGeneratorClass
    ; MixedScaleTrajectoryFamily
    ; familyAt
    ; fullSupportCascade
    ; supportCascade
    )
open import DASHI.Physics.Closure.ShiftContractParametricTrajectoryCompositionFamily as PTF
  using
    ( GeneratorClass
    ; anchoredTrajectory
    ; balancedComposed
    ; balancedCycle
    ; denseComposed
    ; explicitWidth1
    ; explicitWidth2
    ; explicitWidth3
    ; familyAt
    )
open import DASHI.Physics.Closure.ShiftContractStateFamily as SCSF
  using (ShiftContractStateFamily)
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (TriadicIndex)

------------------------------------------------------------------------
-- Higher-level taxonomy over the normalized generator surfaces.
--
-- The noncanonical seam now has two normalized branches:
-- - same-fibre 3-state prefixes, some of which already have certified
--   fourth-step behavior;
-- - mixed-scale trajectory families with typed fibre transitions.
--
-- This module connects those surfaces without pretending every prefix class
-- already has the same amount of dynamic certification.

data PrefixBoundaryShape : Set where
  boundaryUnknown : PrefixBoundaryShape
  boundaryExit : PrefixBoundaryShape
  boundaryExitToAnchored : PrefixBoundaryShape
  boundaryStay : PrefixBoundaryShape

prefixBoundaryShape : GeneratorClass → PrefixBoundaryShape
prefixBoundaryShape explicitWidth1 = boundaryStay
prefixBoundaryShape explicitWidth2 = boundaryExit
prefixBoundaryShape explicitWidth3 = boundaryStay
prefixBoundaryShape balancedCycle = boundaryExitToAnchored
prefixBoundaryShape denseComposed = boundaryStay
prefixBoundaryShape balancedComposed = boundaryExitToAnchored
prefixBoundaryShape anchoredTrajectory = boundaryExit

data CertifiedExitClass : Set where
  certifiedExplicitWidth2 : CertifiedExitClass
  certifiedAnchoredTrajectory : CertifiedExitClass

exitClassToGeneratorClass : CertifiedExitClass → GeneratorClass
exitClassToGeneratorClass certifiedExplicitWidth2 = explicitWidth2
exitClassToGeneratorClass certifiedAnchoredTrajectory = anchoredTrajectory

exitBoundaryAt : (c : CertifiedExitClass) → CertifiedFourthStepExit
exitBoundaryAt certifiedExplicitWidth2 = anchoredExplicitFourthStepBoundary
exitBoundaryAt certifiedAnchoredTrajectory = anchoredTrajectoryFourthStepBoundary

data CertifiedExitToAnchoredClass : Set where
  certifiedBalancedCycle : CertifiedExitToAnchoredClass
  certifiedBalancedComposed : CertifiedExitToAnchoredClass

exitToAnchoredClassToGeneratorClass :
  CertifiedExitToAnchoredClass → GeneratorClass
exitToAnchoredClassToGeneratorClass certifiedBalancedCycle = balancedCycle
exitToAnchoredClassToGeneratorClass certifiedBalancedComposed = balancedComposed

exitToAnchoredBoundaryAt :
  (c : CertifiedExitToAnchoredClass) → CertifiedFourthStepExitOnCycle
exitToAnchoredBoundaryAt certifiedBalancedCycle = balancedCycleFourthStepBoundary
exitToAnchoredBoundaryAt certifiedBalancedComposed = balancedComposedFourthStepBoundary

data CertifiedStayClass : Set where
  certifiedExplicitWidth1 : CertifiedStayClass
  certifiedExplicitWidth3 : CertifiedStayClass
  certifiedDenseComposed : CertifiedStayClass

stayClassToGeneratorClass : CertifiedStayClass → GeneratorClass
stayClassToGeneratorClass certifiedExplicitWidth1 = explicitWidth1
stayClassToGeneratorClass certifiedExplicitWidth3 = explicitWidth3
stayClassToGeneratorClass certifiedDenseComposed = denseComposed

stayBoundaryAt : (c : CertifiedStayClass) → CertifiedFourthStepStay
stayBoundaryAt certifiedExplicitWidth1 = oneHotExplicitFourthStepBoundary
stayBoundaryAt certifiedExplicitWidth3 = denseExplicitFourthStepBoundary
stayBoundaryAt certifiedDenseComposed = denseComposedFourthStepBoundary

record ShiftContractGeneratorTaxonomy : Set₂ where
  field
    prefixFamily :
      GeneratorClass → ShiftContractStateFamily TriadicIndex
    prefixFourthStepShape :
      GeneratorClass → PrefixBoundaryShape
    mixedScaleFamily :
      MixedScaleGeneratorClass → MixedScaleTrajectoryFamily

canonicalShiftContractGeneratorTaxonomy :
  ShiftContractGeneratorTaxonomy
canonicalShiftContractGeneratorTaxonomy =
  record
    { prefixFamily = PTF.familyAt
    ; prefixFourthStepShape = prefixBoundaryShape
    ; mixedScaleFamily = MTF.familyAt
    }

open ShiftContractGeneratorTaxonomy public
