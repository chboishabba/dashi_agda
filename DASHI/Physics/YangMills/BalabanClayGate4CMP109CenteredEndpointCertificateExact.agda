module DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredEndpointCertificateExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embedding

------------------------------------------------------------------------
-- Decidable endpoint certificate for the complete finite CMP109 contour family.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Immediately before equation (0.4), the source ranges over every permutation
-- of the nonzero coordinate segments.  The sibling modules enumerate exactly
-- that finite family and compute the canonical centred target.  For a concrete
-- finite torus, start site and centred offset, equality of every enumerated
-- endpoint is decidable.  An accepted certificate therefore replaces a
-- separately supplied symbolic coordinate-commutation theorem in executable
-- physical instances.
--
-- This is deliberately stronger than testing one selected contour: membership
-- in the complete generated list transports the certificate to every printed
-- ordering.
------------------------------------------------------------------------

data All {A : Set} (Predicate : A → Set) : List A → Set where
  allNil : All Predicate []
  allCons : ∀ {value values} →
    Predicate value → All Predicate values →
    All Predicate (value ∷ values)

allMembership :
  ∀ {A : Set} {Predicate : A → Set} {value values} →
  All Predicate values →
  Contours._∈_ value values →
  Predicate value
allMembership (allCons proof rest) Contours.here = proof
allMembership (allCons proof rest) (Contours.there membership) =
  allMembership rest membership

decideAll :
  ∀ {A : Set} {Predicate : A → Set} →
  ((value : A) → Carrier.Dec (Predicate value)) →
  (values : List A) →
  Carrier.Dec (All Predicate values)
decideAll decision [] = Carrier.yes allNil
decideAll decision (value ∷ values)
  with decision value | decideAll decision values
... | Carrier.yes proof | Carrier.yes rest =
  Carrier.yes (allCons proof rest)
... | Carrier.no notProof | restDecision =
  Carrier.no λ where
    (allCons proof rest) → notProof proof
... | Carrier.yes proof | Carrier.no notRest =
  Carrier.no λ where
    (allCons selected rest) → notRest rest

centeredEndpointPredicate :
  ∀ {n radius} →
  Blocks.PeriodicBlock n →
  Centered.CenteredBlockPoint4 radius →
  List Contours.AxisSegment → Set
centeredEndpointPredicate start point order =
  Bond.walk start (Periodic.contourWord order)
  ≡ Embedding.centeredTargetSite start point

centeredOrderEndpointDecision :
  ∀ {n radius}
    (start : Blocks.PeriodicBlock n)
    (point : Centered.CenteredBlockPoint4 radius)
    order →
  Carrier.Dec (centeredEndpointPredicate start point order)
centeredOrderEndpointDecision {n} start point order =
  Carrier.periodicTorus4DecidableEquality (suc n)
    (Bond.walk start (Periodic.contourWord order))
    (Embedding.centeredTargetSite start point)

record CenteredEndpointCertificate
    (n radius : Nat)
    (start : Blocks.PeriodicBlock n)
    (point : Centered.CenteredBlockPoint4 radius) : Set where
  field
    allEnumeratedEndpointsExact :
      All (centeredEndpointPredicate start point)
        (Contours.cmp109ShortestContourOrders
          (Embedding.centeredDisplacement4 point))

open CenteredEndpointCertificate public

centeredEndpointCertificateDecision :
  ∀ {n radius}
    (start : Blocks.PeriodicBlock n)
    (point : Centered.CenteredBlockPoint4 radius) →
  Carrier.Dec (CenteredEndpointCertificate n radius start point)
centeredEndpointCertificateDecision {n} {radius} start point
  with decideAll
    (centeredOrderEndpointDecision start point)
    (Contours.cmp109ShortestContourOrders
      (Embedding.centeredDisplacement4 point))
... | Carrier.yes proof = Carrier.yes record
  { allEnumeratedEndpointsExact = proof }
... | Carrier.no notProof = Carrier.no λ certificate →
  notProof (allEnumeratedEndpointsExact certificate)

certifiedCenteredContourEndpointExact :
  ∀ {n radius}
    {start : Blocks.PeriodicBlock n}
    {point : Centered.CenteredBlockPoint4 radius} →
  CenteredEndpointCertificate n radius start point →
  ∀ order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (Embedding.centeredDisplacement4 point)) →
  Bond.walk start (Periodic.contourWord order)
  ≡ Embedding.centeredTargetSite start point
certifiedCenteredContourEndpointExact certificate order membership =
  allMembership
    (allEnumeratedEndpointsExact certificate)
    membership

record EmbeddedCenteredEndpointCertificate
    (n radius : Nat)
    (embedding : Embedding.CenteredPeriodicNoWrapEmbedding n radius)
    (point : Centered.CenteredBlockPoint4 radius) : Set where
  field
    computed : CenteredEndpointCertificate n radius
      (Embedding.embeddingCentre embedding) point

open EmbeddedCenteredEndpointCertificate public

certifiedEmbeddedPrintedEndpointExact :
  ∀ {n radius}
    {embedding : Embedding.CenteredPeriodicNoWrapEmbedding n radius}
    {point : Centered.CenteredBlockPoint4 radius} →
  EmbeddedCenteredEndpointCertificate n radius embedding point →
  ∀ order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (Embedding.centeredDisplacement4 point)) →
  Bond.walk
    (Embedding.embeddingCentre embedding)
    (Periodic.contourWord order)
  ≡ Embedding.embed embedding point
certifiedEmbeddedPrintedEndpointExact
    {embedding = embedding} {point = point}
    certificate order membership =
  trans
    (certifiedCenteredContourEndpointExact
      (computed certificate) order membership)
    (sym (Embedding.embedMeaning embedding point))

cmp109CenteredEndpointDecisionLevel : ProofLevel
cmp109CenteredEndpointDecisionLevel = computed

cmp109CenteredCompleteFamilyCertificateLevel : ProofLevel
cmp109CenteredCompleteFamilyCertificateLevel = machineChecked

cmp109CenteredCertificateMembershipTransportLevel : ProofLevel
cmp109CenteredCertificateMembershipTransportLevel = machineChecked

physicalCMP109ConcreteEndpointCertificateInputsLevel : ProofLevel
physicalCMP109ConcreteEndpointCertificateInputsLevel = conditional
