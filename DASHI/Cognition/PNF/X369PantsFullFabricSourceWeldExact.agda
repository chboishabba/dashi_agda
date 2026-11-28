module DASHI.Cognition.PNF.X369PantsFullFabricSourceWeldExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Geometry-forward source weld to EXISTING heterogeneous pants quotient.
-- No parallel hyperfabric/seam ontology; no false equality of channels.
-- Kernel intentionally deferred until requested.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as Geometry
import DASHI.Reasoning.TypedHyperfabricPantsSignatureCompletenessExact as Complete
import DASHI.Reasoning.TypedHyperfabricPantsSourceHeterogeneousTransportExact as Existing
import DASHI.Reasoning.TypedHyperfabricCore as Fabric
open import Data.List.Base using (_++_)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

-- Each source carries its own OWNED stalk, projection to the five
-- fields licensed by the selected pants boundary, and ordered provenance.
-- The left and right stalk types may differ (e.g. boundary vs channel).
module MatchedSource
  (Left Right : Set)
  (left : Left)
  (right : Right)
  (asLeft : Left → Pants.BranchChannel)
  (asRight : Right → Pants.BranchChannel)
  (signatureAgreement :
    Geometry.boundarySignature (asLeft left) ≡
    Geometry.boundarySignature (asRight right))
  (leftProvenance rightProvenance : List String) where

  module Seam =
    Existing.HeterogeneousMatchedSource
      Left Right left right asLeft asRight
      signatureAgreement leftProvenance rightProvenance

  licensedInterface : Pants.InterfaceMatch (asLeft left) (asRight right)
  licensedInterface = Complete.signatureMatchComplete signatureAgreement

  mergedSignature : Geometry.SeamSignature
  mergedSignature = Geometry.boundarySignature (asLeft left)

  -- Two genuinely different incidences become one merged edge; this is
  -- the existing donor's actual topology change, not just a match flag.
  actualMergedIncidences :
    Geometry.mergeEdge Geometry.outerEdge ≡
    Geometry.mergeEdge Geometry.innerEdge
  actualMergedIncidences = Seam.bothSourceEdgesReallyMerge

  originalProvenanceRetained :
    Fabric.edgeProvenance Seam.afterFabric Geometry.mergedSeam ≡
    Fabric.edgeProvenance Seam.beforeFabric Geometry.outerEdge
    ++ Fabric.edgeProvenance Seam.beforeFabric Geometry.innerEdge
  originalProvenanceRetained = Seam.entireSourceProvenanceRetained

  -- Source BIDI: signature quotient does NOT reconstruct the two
  -- heterogeneous original stalks. Keep both independent source values.
  record RetainedSeamPacket : Set where
    constructor retainedSeamPacket
    field
      interface : Geometry.SeamSignature
      leftResidual : Left
      rightResidual : Right
  open RetainedSeamPacket

  pack : RetainedSeamPacket
  pack = retainedSeamPacket mergedSignature left right

  reopenLeft : RetainedSeamPacket → Left
  reopenLeft = leftResidual

  reopenRight : RetainedSeamPacket → Right
  reopenRight = rightResidual

  reopenLeftExact : reopenLeft pack ≡ left
  reopenLeftExact = refl

  reopenRightExact : reopenRight pack ≡ right
  reopenRightExact = refl

  mergedSignatureExact : interface pack ≡
    Geometry.boundarySignature (asLeft left)
  mergedSignatureExact = refl

  originalRightSignatureReopens :
    interface pack ≡ Geometry.boundarySignature (asRight right)
  originalRightSignatureReopens = signatureAgreement

  -- Back-solve exactly which additional consumer observations may use
  -- the five-field quotient: a source-supplied readout compatibility
  -- equation is NECESSARY; a common signature reader is SUFFICIENT.
  module Consumer {Output : Set}
    (leftRead : Left → Output)
    (rightRead : Right → Output) where

    noSignatureOnlyReaderWhenDistinguished :
      (leftRead left ≡ rightRead right → ⊥) →
      (reader : Geometry.SeamSignature → Output) →
      ((x : Left) → reader (Geometry.boundarySignature (asLeft x))
        ≡ leftRead x) →
      ((y : Right) → reader (Geometry.boundarySignature (asRight y))
        ≡ rightRead y) → ⊥
    noSignatureOnlyReaderWhenDistinguished distinct reader exactLeft exactRight =
      distinct
        (trans (sym (exactLeft left))
          (trans (Future.cong reader signatureAgreement)
            (exactRight right)))

    factorThroughSignatureAtSource :
      (reader : Geometry.SeamSignature → Output) →
      ((x : Left) → leftRead x ≡
        reader (Geometry.boundarySignature (asLeft x))) →
      ((y : Right) → rightRead y ≡
        reader (Geometry.boundarySignature (asRight y))) →
      leftRead left ≡ rightRead right
    factorThroughSignatureAtSource reader leftFactors rightFactors =
      trans (leftFactors left)
        (trans (Future.cong reader signatureAgreement)
          (sym (rightFactors right)))

-- The exact ORIGINAL selected heterogeneous specimen is already
-- owned by TypedHyperfabricOriginalHeterogeneousPantsSeamExact.
-- The new construction above consumes rather than reconstructs it.
-- For source byte histories and original neural consumers, supply
-- actual source stalk interpreters/observations or a separating pair.
