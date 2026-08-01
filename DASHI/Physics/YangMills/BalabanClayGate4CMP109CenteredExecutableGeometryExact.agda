module DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredExecutableGeometryExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embedding
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredBlockEndpointCertificateExact as BlockCertificate
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredTorusBijectionExact as Bijection

------------------------------------------------------------------------
-- One executable decision for the complete literal centred geometry.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- For a chosen radius r, both remaining finite geometry questions are
-- decidable:
--
-- 1. does the direct centred-offset bijection agree with the repository walk?
-- 2. do all printed coordinate orderings reach the canonical target for every
--    one of the `(2r+1)^4` points?
--
-- An accepted value below constructs the literal no-wrap embedding and proves
-- the endpoint theorem for the entire block.  No symbolic commutation theorem,
-- cardinality coincidence or selected-path witness remains in the consumer.
------------------------------------------------------------------------

record CenteredExecutableGeometry (radius : Nat) : Set where
  field
    walkAgreement : Bijection.CenteredTorusWalkAgreementCertificate radius

    allEndpoints :
      BlockCertificate.CenteredBlockEndpointCertificate
        (Bijection.centeredTorusParameter radius)
        radius
        (Bijection.directCenteredOrigin {radius})

  embedding : Embedding.CenteredPeriodicNoWrapEmbedding
    (Bijection.centeredTorusParameter radius) radius
  embedding = Bijection.canonicalCenteredNoWrapEmbedding walkAgreement

  embeddedEndpointCertificate :
    BlockCertificate.EmbeddedCenteredBlockEndpointCertificate
      (Bijection.centeredTorusParameter radius) radius embedding
  embeddedEndpointCertificate = record
    { BlockCertificate.EmbeddedCenteredBlockEndpointCertificate.blockCertificate =
        allEndpoints
    }

open CenteredExecutableGeometry public

centeredExecutableGeometryDecision :
  ∀ radius → Carrier.Dec (CenteredExecutableGeometry radius)
centeredExecutableGeometryDecision radius
  with Bijection.centeredTorusWalkAgreementCertificateDecision radius
     | BlockCertificate.centeredBlockEndpointCertificateDecision
         radius (Bijection.directCenteredOrigin {radius})
... | Carrier.yes walk | Carrier.yes endpoints = Carrier.yes record
  { walkAgreement = walk
  ; allEndpoints = endpoints
  }
... | Carrier.no notWalk | endpointDecision = Carrier.no λ geometry →
  notWalk (walkAgreement geometry)
... | Carrier.yes walk | Carrier.no notEndpoints = Carrier.no λ geometry →
  notEndpoints (allEndpoints geometry)

executableCenteredGeometryEndpointExact :
  ∀ {radius} →
  CenteredExecutableGeometry radius →
  ∀ point order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (Embedding.centeredDisplacement4 point)) →
  Bond.walk
    (Embedding.embeddingCentre (embedding geometry))
    (Periodic.contourWord order)
  ≡ Embedding.embed (embedding geometry) point
executableCenteredGeometryEndpointExact geometry =
  BlockCertificate.blockCertifiedEmbeddedPrintedEndpointExact
    (embeddedEndpointCertificate geometry)

executableCenteredGeometryInjective :
  ∀ {radius}
    (geometry : CenteredExecutableGeometry radius)
    {left right : Centered.CenteredBlockPoint4 radius} →
  Embedding.embed (embedding geometry) left
  ≡ Embedding.embed (embedding geometry) right →
  left ≡ right
executableCenteredGeometryInjective geometry =
  Embedding.embedInjective (embedding geometry)

cmp109CenteredExecutableGeometryDecisionLevel : ProofLevel
cmp109CenteredExecutableGeometryDecisionLevel = computed

cmp109CenteredExecutableWholeBlockEndpointLevel : ProofLevel
cmp109CenteredExecutableWholeBlockEndpointLevel = machineChecked

cmp109CenteredExecutableNoWrapInjectionLevel : ProofLevel
cmp109CenteredExecutableNoWrapInjectionLevel = machineChecked

physicalCMP109ChosenRadiusGeometryDecisionInputsLevel : ProofLevel
physicalCMP109ChosenRadiusGeometryDecisionInputsLevel = conditional
