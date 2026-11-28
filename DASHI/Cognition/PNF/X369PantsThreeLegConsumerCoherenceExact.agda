module DASHI.Cognition.PNF.X369PantsThreeLegConsumerCoherenceExact where

-- Geometry-forward triple/pants gluing; reuse actual five-field donor.
-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Three heterogeneous source legs share ONE licensed interface only
-- when the original signatures agree. Both original histories/provenance
-- remain independent after the edge-address quotient.
-- Agda kernel intentionally deferred.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.TypedHyperfabricCore as Fabric
open import Data.List.Base using (_++_)
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as Seam
import DASHI.Reasoning.TypedHyperfabricPantsSignatureCompletenessExact as Complete
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl p = p

module ThreeSourceLegs
  (A B C : Set)
  (a : A) (b : B) (c : C)
  (toA : A → Pants.BranchChannel)
  (toB : B → Pants.BranchChannel)
  (toC : C → Pants.BranchChannel)
  (ab : Seam.boundarySignature (toA a) ≡
        Seam.boundarySignature (toB b))
  (bc : Seam.boundarySignature (toB b) ≡
        Seam.boundarySignature (toC c))
  (sourceA sourceB sourceC : List String) where

  ac : Seam.boundarySignature (toA a) ≡
       Seam.boundarySignature (toC c)
  ac = trans ab bc

  -- These are the ACTUAL source five-field InterfaceMatch constructors.
  abInterface : Pants.InterfaceMatch (toA a) (toB b)
  abInterface = Complete.signatureMatchComplete ab

  bcInterface : Pants.InterfaceMatch (toB b) (toC c)
  bcInterface = Complete.signatureMatchComplete bc

  acInterface : Pants.InterfaceMatch (toA a) (toC c)
  acInterface = Complete.signatureMatchComplete ac

  -- Both binary parenthesizations construct the same seam signature.
  -- We deliberately do not identify full BranchChannels or their basins.
  leftAssociate : Seam.SeamSignature
  leftAssociate = Seam.boundarySignature (toA a)

  rightAssociate : Seam.SeamSignature
  rightAssociate = Seam.boundarySignature (toC c)

  associationCoherence : leftAssociate ≡ rightAssociate
  associationCoherence = ac

  -- Actual nonvacuous THREE-INCIDENCE source typed hyperfabric:
  -- before: three distinct heterogeneous edge stalks;
  -- after: one signature edge incident at all three original vertices.
  -- This strengthens the existing original binary pants seam rather
  -- than merely counting three proposed edges in a receipt.
  data Side : Set where
    sideA sideB sideC : Side

  data BeforeEdge : Set where
    legA legB legC : BeforeEdge

  data AfterEdge : Set where
    commonWaist : AfterEdge

  data BeforeIncidence : Side → BeforeEdge → Set where
    aIncidence : BeforeIncidence sideA legA
    bIncidence : BeforeIncidence sideB legB
    cIncidence : BeforeIncidence sideC legC

  data AfterIncidence : Side → AfterEdge → Set where
    aMerged : AfterIncidence sideA commonWaist
    bMerged : AfterIncidence sideB commonWaist
    cMerged : AfterIncidence sideC commonWaist

  SourceStalk : Side → Set
  SourceStalk sideA = A
  SourceStalk sideB = B
  SourceStalk sideC = C

  EdgeStalk : BeforeEdge → Set
  EdgeStalk legA = A
  EdgeStalk legB = B
  EdgeStalk legC = C

  originalVertices : (s : Side) → SourceStalk s
  originalVertices sideA = a
  originalVertices sideB = b
  originalVertices sideC = c

  originalEdges : (e : BeforeEdge) → EdgeStalk e
  originalEdges legA = a
  originalEdges legB = b
  originalEdges legC = c

  beforeFabric : Fabric.TypedHyperfabric Side BeforeEdge
  beforeFabric = record
    { vertexStalk = SourceStalk
    ; edgeStalk = EdgeStalk
    ; incidence = BeforeIncidence
    ; restrict = λ
        { aIncidence value → value
        ; bIncidence value → value
        ; cIncidence value → value
        }
    ; edgeProvenance = λ
        { legA → sourceA
        ; legB → sourceB
        ; legC → sourceC
        }
    ; edgeSalience = λ _ → 1
    ; fabricLabel = "three heterogeneous source pants legs"
    }

  beforeSection : Fabric.GlobalSection beforeFabric
  beforeSection = record
    { vertexValue = originalVertices
    ; edgeValue = originalEdges
    ; compatible = λ
        { aIncidence → refl
        ; bIncidence → refl
        ; cIncidence → refl
        }
    ; sectionReceipt = "real three-leg original source values"
    }

  afterFabric : Fabric.TypedHyperfabric Side AfterEdge
  afterFabric = record
    { vertexStalk = SourceStalk
    ; edgeStalk = λ _ → Seam.SeamSignature
    ; incidence = AfterIncidence
    ; restrict = λ
        { aMerged value → Seam.boundarySignature (toA value)
        ; bMerged value → Seam.boundarySignature (toB value)
        ; cMerged value → Seam.boundarySignature (toC value)
        }
    ; edgeProvenance = λ _ → sourceA ++ sourceB ++ sourceC
    ; edgeSalience = λ _ → 1
    ; fabricLabel = "source-licensed trivalent merged signature waist"
    }

  afterSection : Fabric.GlobalSection afterFabric
  afterSection = record
    { vertexValue = originalVertices
    ; edgeValue = λ _ → Seam.boundarySignature (toA a)
    ; compatible = λ
        { aMerged → refl
        ; bMerged → sym ab
        ; cMerged → sym ac
        }
    ; sectionReceipt = "three source incidences restrict to matched waist"
    }

  mergeEdge : BeforeEdge → AfterEdge
  mergeEdge legA = commonWaist
  mergeEdge legB = commonWaist
  mergeEdge legC = commonWaist

  mergeIncidence : {side : Side} {edge : BeforeEdge} →
    BeforeIncidence side edge → AfterIncidence side (mergeEdge edge)
  mergeIncidence aIncidence = aMerged
  mergeIncidence bIncidence = bMerged
  mergeIncidence cIncidence = cMerged

  interpretBefore : (edge : BeforeEdge) →
    EdgeStalk edge → Pants.BranchChannel
  interpretBefore legA = toA
  interpretBefore legB = toB
  interpretBefore legC = toC

  everySourceIncidencePreserved :
    {side : Side} {edge : BeforeEdge} →
    (incident : BeforeIncidence side edge) →
    Seam.boundarySignature
      (interpretBefore edge
        (Fabric.restrict beforeFabric incident
          (Fabric.vertexValue beforeSection side)))
    ≡
    Fabric.restrict afterFabric (mergeIncidence incident)
      (Fabric.vertexValue afterSection side)
  everySourceIncidencePreserved aIncidence = refl
  everySourceIncidencePreserved bIncidence = refl
  everySourceIncidencePreserved cIncidence = refl

  sourceEdgeValuesPreserved :
    (edge : BeforeEdge) →
    Seam.boundarySignature
      (interpretBefore edge (Fabric.edgeValue beforeSection edge))
    ≡
    Fabric.edgeValue afterSection (mergeEdge edge)
  sourceEdgeValuesPreserved legA = refl
  sourceEdgeValuesPreserved legB = sym ab
  sourceEdgeValuesPreserved legC = sym ac

  allThreeOriginalProvenancesRetained :
    Fabric.edgeProvenance afterFabric commonWaist ≡
      sourceA ++ sourceB ++ sourceC
  allThreeOriginalProvenancesRetained = refl

  allThreeOriginalEdgesIdentify :
    (mergeEdge legA ≡ mergeEdge legB) ×
    (mergeEdge legB ≡ mergeEdge legC)
  allThreeOriginalEdgesIdentify = refl , refl

  allThreeMergedIncidences :
    AfterIncidence sideA commonWaist ×
    (AfterIncidence sideB commonWaist ×
     AfterIncidence sideC commonWaist)
  allThreeMergedIncidences = aMerged , (bMerged , cMerged)

  record OriginalLegs : Set where
    constructor retainedOriginalLegs
    field
      firstSource : A
      secondSource : B
      thirdSource : C
      firstProvenance : List String
      secondProvenance : List String
      thirdProvenance : List String
      licensedSignature : Seam.SeamSignature
  open OriginalLegs

  packet : OriginalLegs
  packet = retainedOriginalLegs
    a b c sourceA sourceB sourceC (Seam.boundarySignature (toA a))

  reopenAll : OriginalLegs → A × (B × C)
  reopenAll t = firstSource t , (secondSource t , thirdSource t)

  tripleBidi : reopenAll packet ≡ (a , (b , c))
  tripleBidi = refl

  leftProvenanceBidi : firstProvenance packet ≡ sourceA
  leftProvenanceBidi = refl
  middleProvenanceBidi : secondProvenance packet ≡ sourceB
  middleProvenanceBidi = refl
  rightProvenanceBidi : thirdProvenance packet ≡ sourceC
  rightProvenanceBidi = refl

  -- Inverting two source packets is stronger than the seam-signature
  -- quotient: a 5-field matched interface never licenses deleting an
  -- original recurrent history, consumer version, or face datum.
  module TrivalentConsumer {Output : Set}
    (readA : A → Output) (readB : B → Output)
    (readC : C → Output) where

    -- The failure of even ONE source consumer means the common seam
    -- signature alone is insufficient for an all-leg reader.
    noSingleSignatureReaderAB :
      (readA a ≡ readB b → ⊥) →
      (reader : Seam.SeamSignature → Output) →
      ((x : A) → reader (Seam.boundarySignature (toA x))
        ≡ readA x) →
      ((y : B) → reader (Seam.boundarySignature (toB y))
        ≡ readB y) → ⊥
    noSingleSignatureReaderAB distinct reader ra rb =
      distinct (trans (sym (ra a))
        (trans (Future.cong reader ab) (rb b)))

    noSingleSignatureReaderBC :
      (readB b ≡ readC c → ⊥) →
      (reader : Seam.SeamSignature → Output) →
      ((x : B) → reader (Seam.boundarySignature (toB x))
        ≡ readB x) →
      ((y : C) → reader (Seam.boundarySignature (toC y))
        ≡ readC y) → ⊥
    noSingleSignatureReaderBC distinct reader rb rc =
      distinct (trans (sym (rb b))
        (trans (Future.cong reader bc) (rc c)))

-- Original relational-pants donor specialization for the nonempty
-- selected/waist/selected triple. This is a finite three-leg seam,
-- NOT an arbitrary smooth cobordism or a Leech lattice coset glue.
module OriginalSelectedTriple =
  ThreeSourceLegs
    Pants.BranchChannel Pants.BranchChannel Pants.BranchChannel
    Pants.selectedChannel2 Pants.innerInputChannel2 Pants.selectedChannel2
    (λ x → x) (λ x → x) (λ x → x)
    (Seam.interfaceMatchImpliesSignatureEquality Pants.outerInnerMatch)
    (sym (Seam.interfaceMatchImpliesSignatureEquality Pants.outerInnerMatch))
    [] [] []
