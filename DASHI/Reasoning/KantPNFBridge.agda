module DASHI.Reasoning.KantPNFBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Reasoning.KantCriticalCompiler as Kant

------------------------------------------------------------------------
-- PNF comparison outcomes routed into a Kantian critical audit without
-- collapsing contradiction, residual difference, no typed meet or scope.
------------------------------------------------------------------------

data PNFCriticalClass : Set where
  exactClass compatibleClass contradictionClass residualClass noMeetClass :
    PNFCriticalClass

classifyComparison : PNF.ComparisonResult → PNFCriticalClass
classifyComparison PNF.equivalent = exactClass
classifyComparison PNF.compatible = compatibleClass
classifyComparison PNF.contradictory = contradictionClass
classifyComparison PNF.residuallyDifferent = residualClass
classifyComparison PNF.noTypedMeet = noMeetClass

candidateCriticalResult : PNFCriticalClass → Kant.CriticalResult
candidateCriticalResult exactClass = Kant.constitutiveResult
candidateCriticalResult compatibleClass = Kant.regulativeResult
candidateCriticalResult contradictionClass = Kant.contradictionResult
candidateCriticalResult residualClass = Kant.regulativeResult
candidateCriticalResult noMeetClass = Kant.noTypedMeetResult

record PNFCategoryApplication : Set₁ where
  field
    event : PNF.EventPNF
    category : Kant.KantCategory
    schemaReference : String
    schemaWitnessAvailable : Bool
    result : Kant.CriticalResult
    constitutivePromotionClaimed : Bool
    criticalReceipt : String

record KantPNFBridgeBoundary : Set where
  field
    comparisonClassesPreserved : Bool
    contradictionEqualsNoMeet : Bool
    residualEqualsAntinomy : Bool
    schemaReferenceEqualsSchemaWitness : Bool
    compatibleAutomaticallyConstitutive : Bool
    pnfEventEqualsNoumenalObject : Bool
    boundaryNote : String

canonicalKantPNFBridgeBoundary : KantPNFBridgeBoundary
canonicalKantPNFBridgeBoundary = record
  { comparisonClassesPreserved = true
  ; contradictionEqualsNoMeet = false
  ; residualEqualsAntinomy = false
  ; schemaReferenceEqualsSchemaWitness = false
  ; compatibleAutomaticallyConstitutive = false
  ; pnfEventEqualsNoumenalObject = false
  ; boundaryNote =
      "PNF outcomes seed critical classification, but category application still requires a schema witness and scope receipt."
  }
