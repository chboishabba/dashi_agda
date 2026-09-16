module DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants

------------------------------------------------------------------------
-- TYPED HYPERFABRIC -> PANTS INTERFACE GLUING CERTIFICATE
--
-- Arbitrary hyperfabric edge stalks are not assumed to be branch channels.
-- A domain supplies an interpretation of the two selected edge-stalk values
-- into Pants.BranchChannel.  Gluing is admissible only when the canonical
-- Pants.InterfaceMatch is provided on those realized channels.
--
-- This is a seam certificate.  It does not itself rewrite incidence, merge
-- edges, or construct a new TypedHyperfabric; such topology change belongs to
-- an explicit reorganisation layer.
------------------------------------------------------------------------

record HyperfabricPantsGluing
    {Vertex Edge : Set}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    (section : Hyperfabric.GlobalSection fabric) : Set₁ where
  constructor hyperfabric-pants-gluing
  field
    leftEdge : Edge
    rightEdge : Edge
    realizeChannel :
      (edge : Edge) →
      Hyperfabric.edgeStalk fabric edge →
      Pants.BranchChannel
    seamInterface :
      Pants.InterfaceMatch
        (realizeChannel leftEdge (Hyperfabric.edgeValue section leftEdge))
        (realizeChannel rightEdge (Hyperfabric.edgeValue section rightEdge))
    gluingReceipt : String

open HyperfabricPantsGluing public

seamPropositionMatch :
  ∀ {Vertex Edge}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    {section : Hyperfabric.GlobalSection fabric} →
  (gluing : HyperfabricPantsGluing section) →
  Pants.propositionType
    (Pants.channelBoundary
      (realizeChannel gluing (leftEdge gluing)
        (Hyperfabric.edgeValue section (leftEdge gluing))))
  ≡
  Pants.propositionType
    (Pants.channelBoundary
      (realizeChannel gluing (rightEdge gluing)
        (Hyperfabric.edgeValue section (rightEdge gluing))))
seamPropositionMatch gluing =
  Pants.propositionMatches (seamInterface gluing)

seamCapacityMatch :
  ∀ {Vertex Edge}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    {section : Hyperfabric.GlobalSection fabric} →
  (gluing : HyperfabricPantsGluing section) →
  Pants.boundaryCapacity
    (Pants.channelBoundary
      (realizeChannel gluing (leftEdge gluing)
        (Hyperfabric.edgeValue section (leftEdge gluing))))
  ≡
  Pants.boundaryCapacity
    (Pants.channelBoundary
      (realizeChannel gluing (rightEdge gluing)
        (Hyperfabric.edgeValue section (rightEdge gluing))))
seamCapacityMatch gluing =
  Pants.capacityMatches (seamInterface gluing)

seamPhaseMatch :
  ∀ {Vertex Edge}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    {section : Hyperfabric.GlobalSection fabric} →
  (gluing : HyperfabricPantsGluing section) →
  Pants.boundaryPhase
    (Pants.channelBoundary
      (realizeChannel gluing (leftEdge gluing)
        (Hyperfabric.edgeValue section (leftEdge gluing))))
  ≡
  Pants.boundaryPhase
    (Pants.channelBoundary
      (realizeChannel gluing (rightEdge gluing)
        (Hyperfabric.edgeValue section (rightEdge gluing))))
seamPhaseMatch gluing =
  Pants.phaseMatches (seamInterface gluing)

------------------------------------------------------------------------
-- Finite witness: reuse the repository's exact selected-leg/inner-waist match.
------------------------------------------------------------------------

data SeamVertex : Set where
  seamVertex : SeamVertex

data SeamEdge : Set where
  outerSelectedEdge : SeamEdge
  innerInputEdge : SeamEdge

data SeamIncidence : SeamVertex → SeamEdge → Set where

seamFabric : Hyperfabric.TypedHyperfabric SeamVertex SeamEdge
seamFabric = record
  { vertexStalk = λ _ → ⊤
  ; edgeStalk = λ _ → Pants.BranchChannel
  ; incidence = SeamIncidence
  ; restrict = λ ()
  ; edgeProvenance = λ
      { outerSelectedEdge → "outer selected pants leg" ∷ []
      ; innerInputEdge → "inner pants waist" ∷ []
      }
  ; edgeSalience = λ _ → 1
  ; fabricLabel = "finite pants seam hyperfabric specimen"
  }

seamSection : Hyperfabric.GlobalSection seamFabric
seamSection = record
  { vertexValue = λ _ → tt
  ; edgeValue = λ
      { outerSelectedEdge → Pants.selectedChannel2
      ; innerInputEdge → Pants.innerInputChannel2
      }
  ; compatible = λ ()
  ; sectionReceipt = "two selected pants channels retained as hyperfabric edge values"
  }

canonicalPantsGluing : HyperfabricPantsGluing seamSection
canonicalPantsGluing = hyperfabric-pants-gluing
  outerSelectedEdge
  innerInputEdge
  (λ _ channel → channel)
  Pants.outerInnerMatch
  "canonical outer selected leg / inner waist InterfaceMatch lifted as a hyperfabric seam certificate"

canonicalPantsGluingReusesExactInterfaceMatch :
  seamInterface canonicalPantsGluing ≡ Pants.outerInnerMatch
canonicalPantsGluingReusesExactInterfaceMatch = refl

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data SeamCertificateAutomaticallyConstructsNewHyperfabric : Set where

seamDoesNotAutomaticallyConstructNewHyperfabric :
  SeamCertificateAutomaticallyConstructsNewHyperfabric → ⊥
seamDoesNotAutomaticallyConstructNewHyperfabric ()

record TypedHyperfabricPantsGluingBoundary : Set where
  constructor typed-hyperfabric-pants-gluing-boundary
  field
    domainInterpretationFromEdgeStalkRequired : Bool
    canonicalInterfaceMatchRequired : Bool
    propositionCapacityPhaseWaveOpennessRetained : Bool
    interfaceMatchAuthorizesTypedSeam : Bool
    interfaceMatchAutomaticallyRewritesIncidence : Bool
    interfaceMatchAutomaticallyRewritesIncidenceIsFalse :
      interfaceMatchAutomaticallyRewritesIncidence ≡ false
    seamAutomaticallyErasesPathMemory : Bool
    seamAutomaticallyErasesPathMemoryIsFalse :
      seamAutomaticallyErasesPathMemory ≡ false
    capacityAgreementAloneMeansFullInterfaceAgreement : Bool
    capacityAgreementAloneMeansFullInterfaceAgreementIsFalse :
      capacityAgreementAloneMeansFullInterfaceAgreement ≡ false
    seamCreatesParallelHyperfabricKernel : Bool
    seamCreatesParallelHyperfabricKernelIsFalse :
      seamCreatesParallelHyperfabricKernel ≡ false
    boundaryNote : String

open TypedHyperfabricPantsGluingBoundary public

canonicalTypedHyperfabricPantsGluingBoundary :
  TypedHyperfabricPantsGluingBoundary
canonicalTypedHyperfabricPantsGluingBoundary =
  typed-hyperfabric-pants-gluing-boundary
    true
    true
    true
    true
    false refl
    false refl
    false refl
    false refl
    "A hyperfabric pants seam is admissible only after the selected edge-stalk values are interpreted as branch channels and the existing five-coordinate InterfaceMatch is paid. The seam certificate does not itself rewrite hyperfabric topology or erase path memory."
