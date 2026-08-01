module DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredBlockEndpointCertificateExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embedding
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredEndpointCertificateExact as Endpoint

------------------------------------------------------------------------
-- One decidable certificate for every point of the centred CMP109 block.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The centred block and every contour family are finite.  The pointwise
-- certificate decision is therefore nested over the literal `(2r+1)^4`
-- enumeration.  An accepted block certificate proves endpoint equality for
-- every centred site and every generated coordinate ordering, not merely for a
-- selected witness used by a downstream theorem.
------------------------------------------------------------------------

allCarrierMembership :
  ∀ {A : Set} {Predicate : A → Set} {value values} →
  Endpoint.All Predicate values →
  Carrier._∈_ value values →
  Predicate value
allCarrierMembership (Endpoint.allCons proof rest) Carrier.here = proof
allCarrierMembership
    (Endpoint.allCons proof rest) (Carrier.there membership) =
  allCarrierMembership rest membership

record CenteredBlockEndpointCertificate
    (n radius : Nat)
    (start : Blocks.PeriodicBlock n) : Set where
  field
    everyCenteredPointCertified :
      Endpoint.All
        (λ point → Endpoint.CenteredEndpointCertificate
          n radius start point)
        (Carrier.elements (Centered.centeredBlockFinite radius))

open CenteredBlockEndpointCertificate public

centeredBlockEndpointCertificateDecision :
  ∀ {n} radius (start : Blocks.PeriodicBlock n) →
  Carrier.Dec (CenteredBlockEndpointCertificate n radius start)
centeredBlockEndpointCertificateDecision {n} radius start
  with Endpoint.decideAll
    (Endpoint.centeredEndpointCertificateDecision start)
    (Carrier.elements (Centered.centeredBlockFinite radius))
... | Carrier.yes proof = Carrier.yes record
  { everyCenteredPointCertified = proof }
... | Carrier.no notProof = Carrier.no λ certificate →
  notProof (everyCenteredPointCertified certificate)

centeredPointCertificateFromBlock :
  ∀ {n radius} {start : Blocks.PeriodicBlock n} →
  CenteredBlockEndpointCertificate n radius start →
  ∀ point → Endpoint.CenteredEndpointCertificate n radius start point
centeredPointCertificateFromBlock {radius = radius} certificate point =
  allCarrierMembership
    (everyCenteredPointCertified certificate)
    (Carrier.complete (Centered.centeredBlockFinite radius) point)

blockCertifiedCenteredContourEndpointExact :
  ∀ {n radius} {start : Blocks.PeriodicBlock n} →
  CenteredBlockEndpointCertificate n radius start →
  ∀ point order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (Embedding.centeredDisplacement4 point)) →
  Bond.walk start (Periodic.contourWord order)
  ≡ Embedding.centeredTargetSite start point
blockCertifiedCenteredContourEndpointExact certificate point order membership =
  Endpoint.certifiedCenteredContourEndpointExact
    (centeredPointCertificateFromBlock certificate point)
    order membership

record EmbeddedCenteredBlockEndpointCertificate
    (n radius : Nat)
    (embedding : Embedding.CenteredPeriodicNoWrapEmbedding n radius) : Set where
  field
    blockCertificate : CenteredBlockEndpointCertificate n radius
      (Embedding.embeddingCentre embedding)

open EmbeddedCenteredBlockEndpointCertificate public

blockCertifiedEmbeddedPrintedEndpointExact :
  ∀ {n radius}
    {embedding : Embedding.CenteredPeriodicNoWrapEmbedding n radius} →
  EmbeddedCenteredBlockEndpointCertificate n radius embedding →
  ∀ point order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (Embedding.centeredDisplacement4 point)) →
  Bond.walk
    (Embedding.embeddingCentre embedding)
    (Periodic.contourWord order)
  ≡ Embedding.embed embedding point
blockCertifiedEmbeddedPrintedEndpointExact
    {embedding = embedding} certificate point order membership =
  trans
    (blockCertifiedCenteredContourEndpointExact
      (blockCertificate certificate) point order membership)
    (sym (Embedding.embedMeaning embedding point))

cmp109CenteredBlockEndpointDecisionLevel : ProofLevel
cmp109CenteredBlockEndpointDecisionLevel = computed

cmp109CenteredBlockCompleteEndpointCertificateLevel : ProofLevel
cmp109CenteredBlockCompleteEndpointCertificateLevel = machineChecked

cmp109CenteredBlockCertificateTransportLevel : ProofLevel
cmp109CenteredBlockCertificateTransportLevel = machineChecked

physicalCMP109CenteredBlockEndpointCertificateInputsLevel : ProofLevel
physicalCMP109CenteredBlockEndpointCertificateInputsLevel = conditional
