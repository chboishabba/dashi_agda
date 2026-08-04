module DASHI.Reasoning.RSITypedDependencyHyperfabric where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Reasoning.LacanRegisterSinthomeHyperfabric as Legacy
import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric

------------------------------------------------------------------------
-- Upgrade the legacy three-Boolean RSI presence test to an indexed ternary
-- support object and a typed hyperedge.  The old Boolean theorems remain
-- available as a lossy projection and regression surface.
------------------------------------------------------------------------

data RegisterWitness : Lacan.LacanianRegister → Set where
  imaginaryWitness : RegisterWitness Lacan.imaginaryRegister
  symbolicWitness : RegisterWitness Lacan.symbolicRegister
  realWitness : RegisterWitness Lacan.realRegister

data RSIJointSupport : Set where
  rsiJointSupport : RSIJointSupport

noPairSupport : ¬ ⊥
noPairSupport impossible = impossible

canonicalIrreducibleRSIDependency :
  Dependency.IrreducibleTernaryDependency
    (RegisterWitness Lacan.imaginaryRegister)
    (RegisterWitness Lacan.symbolicRegister)
    (RegisterWitness Lacan.realRegister)
    RSIJointSupport
    ⊥ ⊥ ⊥
canonicalIrreducibleRSIDependency = record
  { leftWitness = imaginaryWitness
  ; middleWitness = symbolicWitness
  ; rightWitness = realWitness
  ; jointSupport = rsiJointSupport
  ; noLeftMiddleSupport = noPairSupport
  ; noLeftRightSupport = noPairSupport
  ; noMiddleRightSupport = noPairSupport
  ; dependencyReceipt =
      "RSI coherence is carried by one declared ternary support witness; no pair-support constructor exists in this model."
  }

------------------------------------------------------------------------
-- Finite typed hyperedge realisation.
------------------------------------------------------------------------

data RSIVertex : Set where
  imaginaryVertex symbolicVertex realVertex : RSIVertex

data RSIEdge : Set where
  rsiJointEdge : RSIEdge

data RSIIncidence : RSIVertex → RSIEdge → Set where
  imaginaryIncident : RSIIncidence imaginaryVertex rsiJointEdge
  symbolicIncident : RSIIncidence symbolicVertex rsiJointEdge
  realIncident : RSIIncidence realVertex rsiJointEdge

rsiVertexStalk : RSIVertex → Set
rsiVertexStalk imaginaryVertex = ⊤
rsiVertexStalk symbolicVertex = ⊤
rsiVertexStalk realVertex = ⊤

rsiEdgeStalk : RSIEdge → Set
rsiEdgeStalk rsiJointEdge = ⊤

rsiRestrict :
  ∀ {vertex edge} →
  RSIIncidence vertex edge →
  rsiVertexStalk vertex →
  rsiEdgeStalk edge
rsiRestrict imaginaryIncident tt = tt
rsiRestrict symbolicIncident tt = tt
rsiRestrict realIncident tt = tt

rsiEdgeProvenance : RSIEdge → List String
rsiEdgeProvenance rsiJointEdge =
  "Imaginary register witness"
  ∷ "Symbolic register witness"
  ∷ "Real register witness"
  ∷ "ternary dependency receipt"
  ∷ []

rsiEdgeSalience : RSIEdge → Nat
rsiEdgeSalience rsiJointEdge = 3

canonicalRSITypedHyperfabric :
  Hyperfabric.TypedHyperfabric RSIVertex RSIEdge
canonicalRSITypedHyperfabric = record
  { vertexStalk = rsiVertexStalk
  ; edgeStalk = rsiEdgeStalk
  ; incidence = RSIIncidence
  ; restrict = rsiRestrict
  ; edgeProvenance = rsiEdgeProvenance
  ; edgeSalience = rsiEdgeSalience
  ; fabricLabel = "RSI irreducible ternary dependency hyperedge"
  }

canonicalRSIGlobalSection :
  Hyperfabric.GlobalSection canonicalRSITypedHyperfabric
canonicalRSIGlobalSection = record
  { vertexValue = λ
      { imaginaryVertex → tt
      ; symbolicVertex → tt
      ; realVertex → tt
      }
  ; edgeValue = λ { rsiJointEdge → tt }
  ; compatible = λ
      { imaginaryIncident → refl
      ; symbolicIncident → refl
      ; realIncident → refl
      }
  ; sectionReceipt =
      "All three register stalks restrict to the single ternary edge value."
  }

------------------------------------------------------------------------
-- Three non-collapsed Borromean levels.
------------------------------------------------------------------------

record BorromeanDependencyLevels : Set where
  field
    logicalDeletionSensitivity :
      Legacy.rsiDependencyCoherent Legacy.allRSIPresent ≡ true
    imaginaryDeletionBreaks :
      Legacy.rsiDependencyCoherent Legacy.withoutImaginary ≡ false
    symbolicDeletionBreaks :
      Legacy.rsiDependencyCoherent Legacy.withoutSymbolic ≡ false
    realDeletionBreaks :
      Legacy.rsiDependencyCoherent Legacy.withoutReal ≡ false
    relationalTernaryWitness :
      Dependency.IrreducibleTernaryDependency
        (RegisterWitness Lacan.imaginaryRegister)
        (RegisterWitness Lacan.symbolicRegister)
        (RegisterWitness Lacan.realRegister)
        RSIJointSupport ⊥ ⊥ ⊥
    topologicalLinkDiagramProvided : Bool
    pairwiseTopologicalUnlinkingProved : Bool
    globalTopologicalLinkingProved : Bool
    borromeanTopologicalLinkProved : Bool

canonicalBorromeanDependencyLevels : BorromeanDependencyLevels
canonicalBorromeanDependencyLevels = record
  { logicalDeletionSensitivity = Legacy.allThreeDependencyCoherent
  ; imaginaryDeletionBreaks = Legacy.removeImaginaryBreaksDependency
  ; symbolicDeletionBreaks = Legacy.removeSymbolicBreaksDependency
  ; realDeletionBreaks = Legacy.removeRealBreaksDependency
  ; relationalTernaryWitness = canonicalIrreducibleRSIDependency
  ; topologicalLinkDiagramProvided = false
  ; pairwiseTopologicalUnlinkingProved = false
  ; globalTopologicalLinkingProved = false
  ; borromeanTopologicalLinkProved = false
  }

record RSITypedDependencyAuthorityBoundary : Set where
  field
    booleanPresenceUpgraded : Bool
    irreducibleTernarySupportProvedForDeclaredModel : Bool
    globalTypedSectionConstructed : Bool
    relationalBorromeanityEqualsTopologicalBorromeanity : Bool
    topologicalBorromeanLinkProved : Bool
    registerWitnessDiagnosesPerson : Bool
    boundaryNote : String

canonicalRSITypedDependencyAuthorityBoundary :
  RSITypedDependencyAuthorityBoundary
canonicalRSITypedDependencyAuthorityBoundary = record
  { booleanPresenceUpgraded = true
  ; irreducibleTernarySupportProvedForDeclaredModel = true
  ; globalTypedSectionConstructed = true
  ; relationalBorromeanityEqualsTopologicalBorromeanity = false
  ; topologicalBorromeanLinkProved = false
  ; registerWitnessDiagnosesPerson = false
  ; boundaryNote =
      "RSI now has an indexed ternary hyperedge and compatible section. This proves relational dependence only; knot diagrams, isotopy and link invariants remain open."
  }
