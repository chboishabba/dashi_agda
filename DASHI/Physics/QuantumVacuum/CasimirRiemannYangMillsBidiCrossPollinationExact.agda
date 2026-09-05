module DASHI.Physics.QuantumVacuum.CasimirRiemannYangMillsBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.PoissonSummationKernelBidiExact as PS
import DASHI.Analysis.RenormalisedDifferenceLimitExact as RDL
import DASHI.Analysis.SumIntegralDefectExact as SID

------------------------------------------------------------------------
-- BIDI CROSS-POLLINATION MAP
--
-- We extract reusable theorem SHAPES from neighboring lanes while refusing to
-- transport their application receipts sideways into Casimir.
------------------------------------------------------------------------

data Lane : Set where
  riemannLane yangMillsLane casimirLane : Lane

data ReusableShape : Set where
  poissonSummationShape
  cutoffRemovalShape
  sumIntegralDefectShape
  renormalisedDifferenceShape
  sameObjectWeldShape
  nonFactorabilityShape : ReusableShape

record CrossPollinationEdge : Set where
  field
    source target : Lane
    shape : ReusableShape
    theoremShapeReusable : Bool
    applicationReceiptReusable : Bool
    reading : String

open CrossPollinationEdge public

riemannToCasimirPoisson : CrossPollinationEdge
riemannToCasimirPoisson = record
  { source = riemannLane
  ; target = casimirLane
  ; shape = poissonSummationShape
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "Reuse Poisson theorem architecture; Casimir must prove its own function/lattice/convergence hypotheses."
  }

yangMillsToCasimirCutoff : CrossPollinationEdge
yangMillsToCasimirCutoff = record
  { source = yangMillsLane
  ; target = casimirLane
  ; shape = cutoffRemovalShape
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "Reuse cutoff-obligation discipline; eventual exact stabilization is not Casimir difference convergence."
  }

casimirToGenericDifference : CrossPollinationEdge
casimirToGenericDifference = record
  { source = casimirLane
  ; target = casimirLane
  ; shape = renormalisedDifferenceShape
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = true
  ; reading = "Casimir contributes the generic matched-difference theorem shape back to DASHI once proved generically."
  }

------------------------------------------------------------------------
-- The reverse direction is equally important: once the generic kernels exist,
-- neighboring lanes may instantiate them on their OWN objects.  This is BIDI
-- cross-pollination without same-object collapse.
------------------------------------------------------------------------

record GenericKernelConsumer : Set₁ where
  field
    lane : Lane
    PoissonProblem : Set
    DifferenceProblem : Set
    DefectProblem : Set
    localHypothesesRequired : Set
    consumerReading : String

open GenericKernelConsumer public

record SameObjectFirewall : Set where
  field
    sharedTheoremShapeDoesNotIdentifyApplications : Bool
    equalOutputDimensionDoesNotIdentifyApplications : Bool
    equalNumericalCoefficientDoesNotIdentifyApplications : Bool

    sharedShapeFalsePromotionBlocked :
      sharedTheoremShapeDoesNotIdentifyApplications ≡ true
    equalDimensionFalsePromotionBlocked :
      equalOutputDimensionDoesNotIdentifyApplications ≡ true
    equalCoefficientFalsePromotionBlocked :
      equalNumericalCoefficientDoesNotIdentifyApplications ≡ true

canonicalSameObjectFirewall : SameObjectFirewall
canonicalSameObjectFirewall = record
  { sharedTheoremShapeDoesNotIdentifyApplications = true
  ; equalOutputDimensionDoesNotIdentifyApplications = true
  ; equalNumericalCoefficientDoesNotIdentifyApplications = true
  ; sharedShapeFalsePromotionBlocked = refl
  ; equalDimensionFalsePromotionBlocked = refl
  ; equalCoefficientFalsePromotionBlocked = refl
  }

------------------------------------------------------------------------
-- Machine-readable status.
------------------------------------------------------------------------

record BidiCrossPollinationStatus : Set where
  field
    genericPoissonKernelOwned : Bool
    genericDifferenceKernelOwned : Bool
    genericDefectKernelOwned : Bool
    casimirInstantiationInterfaceOwned : Bool
    riemannReceiptImportedIntoCasimir : Bool
    yangMillsReceiptImportedIntoCasimir : Bool

    genericPoissonKernelOwnedIsTrue : genericPoissonKernelOwned ≡ true
    genericDifferenceKernelOwnedIsTrue : genericDifferenceKernelOwned ≡ true
    genericDefectKernelOwnedIsTrue : genericDefectKernelOwned ≡ true
    casimirInstantiationInterfaceOwnedIsTrue : casimirInstantiationInterfaceOwned ≡ true
    riemannReceiptImportedIntoCasimirIsFalse : riemannReceiptImportedIntoCasimir ≡ false
    yangMillsReceiptImportedIntoCasimirIsFalse : yangMillsReceiptImportedIntoCasimir ≡ false

canonicalBidiCrossPollinationStatus : BidiCrossPollinationStatus
canonicalBidiCrossPollinationStatus = record
  { genericPoissonKernelOwned = true
  ; genericDifferenceKernelOwned = true
  ; genericDefectKernelOwned = true
  ; casimirInstantiationInterfaceOwned = true
  ; riemannReceiptImportedIntoCasimir = false
  ; yangMillsReceiptImportedIntoCasimir = false
  ; genericPoissonKernelOwnedIsTrue = refl
  ; genericDifferenceKernelOwnedIsTrue = refl
  ; genericDefectKernelOwnedIsTrue = refl
  ; casimirInstantiationInterfaceOwnedIsTrue = refl
  ; riemannReceiptImportedIntoCasimirIsFalse = refl
  ; yangMillsReceiptImportedIntoCasimirIsFalse = refl
  }
