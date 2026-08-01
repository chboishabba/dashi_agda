module DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredTorusBijectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embedding
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredEndpointCertificateExact as Endpoint
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredBlockEndpointCertificateExact as BlockCertificate

------------------------------------------------------------------------
-- Explicit centred-offset/odd-periodic-torus bijection.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - I. Small Fields",
-- arXiv:1108.1335v2 [math-ph]. No DOI recorded.
--
-- A centred coordinate with radius r has one origin, r positive offsets and r
-- negative offsets.  This module maps it bijectively to CyclicIndex(1+r+r),
-- hence maps the full centred block bijectively to the repository's periodic
-- four-torus of the same odd width.  Positive k maps to cyclic index k, while
-- negative k maps to cyclic index 1+2r-k, exactly matching repeated successor
-- and predecessor steps from the origin.  Injectivity and decode round trips
-- are proved structurally; no cardinality-only argument remains.
--
-- Agreement between this direct bijection and the repository's concrete
-- signed-step walk is a finite decidable certificate over the whole block.
------------------------------------------------------------------------

data IndexSplit (leftSize rightSize : Nat) : Set where
  fromLeft : Carrier.CyclicIndex leftSize → IndexSplit leftSize rightSize
  fromRight : Carrier.CyclicIndex rightSize → IndexSplit leftSize rightSize

injectLeftIndex :
  ∀ {leftSize rightSize} →
  Carrier.CyclicIndex leftSize →
  Carrier.CyclicIndex (leftSize + rightSize)
injectLeftIndex {zero} ()
injectLeftIndex {suc leftSize} Carrier.zeroᵢ = Carrier.zeroᵢ
injectLeftIndex {suc leftSize} (Carrier.sucᵢ index) =
  Carrier.sucᵢ (injectLeftIndex index)

injectRightIndex :
  ∀ {leftSize rightSize} →
  Carrier.CyclicIndex rightSize →
  Carrier.CyclicIndex (leftSize + rightSize)
injectRightIndex {zero} index = index
injectRightIndex {suc leftSize} index =
  Carrier.sucᵢ (injectRightIndex {leftSize} index)

splitIndex :
  ∀ {leftSize rightSize} →
  Carrier.CyclicIndex (leftSize + rightSize) →
  IndexSplit leftSize rightSize
splitIndex {zero} index = fromRight index
splitIndex {suc leftSize} Carrier.zeroᵢ = fromLeft Carrier.zeroᵢ
splitIndex {suc leftSize} (Carrier.sucᵢ index)
  with splitIndex {leftSize} index
... | fromLeft left = fromLeft (Carrier.sucᵢ left)
... | fromRight right = fromRight right

splitInjectedLeft :
  ∀ {leftSize rightSize}
    (index : Carrier.CyclicIndex leftSize) →
  splitIndex (injectLeftIndex {leftSize} {rightSize} index)
  ≡ fromLeft index
splitInjectedLeft {zero} ()
splitInjectedLeft {suc leftSize} Carrier.zeroᵢ = refl
splitInjectedLeft {suc leftSize} (Carrier.sucᵢ index)
  rewrite splitInjectedLeft {leftSize} {rightSize} index = refl

splitInjectedRight :
  ∀ {leftSize rightSize}
    (index : Carrier.CyclicIndex rightSize) →
  splitIndex (injectRightIndex {leftSize} {rightSize} index)
  ≡ fromRight index
splitInjectedRight {zero} index = refl
splitInjectedRight {suc leftSize} index
  rewrite splitInjectedRight {leftSize} {rightSize} index = refl

weakenFiniteIndex :
  ∀ {size} → Carrier.CyclicIndex size → Carrier.CyclicIndex (suc size)
weakenFiniteIndex {zero} ()
weakenFiniteIndex {suc size} Carrier.zeroᵢ = Carrier.zeroᵢ
weakenFiniteIndex {suc size} (Carrier.sucᵢ index) =
  Carrier.sucᵢ (weakenFiniteIndex index)

reverseFiniteIndex :
  ∀ {size} → Carrier.CyclicIndex size → Carrier.CyclicIndex size
reverseFiniteIndex {zero} ()
reverseFiniteIndex {suc size} Carrier.zeroᵢ = Adjacency.lastCyclic
reverseFiniteIndex {suc size} (Carrier.sucᵢ index) =
  weakenFiniteIndex (reverseFiniteIndex index)

reverseLastFiniteIndex : ∀ size →
  reverseFiniteIndex (Adjacency.lastCyclic {size}) ≡ Carrier.zeroᵢ
reverseLastFiniteIndex zero = refl
reverseLastFiniteIndex (suc size)
  rewrite reverseLastFiniteIndex size = refl

reverseWeakenFiniteIndex :
  ∀ {size} (index : Carrier.CyclicIndex size) →
  reverseFiniteIndex (weakenFiniteIndex index)
  ≡ Carrier.sucᵢ (reverseFiniteIndex index)
reverseWeakenFiniteIndex {zero} ()
reverseWeakenFiniteIndex {suc size} Carrier.zeroᵢ = refl
reverseWeakenFiniteIndex {suc size} (Carrier.sucᵢ index)
  rewrite reverseWeakenFiniteIndex index = refl

reverseFiniteIndexInvolutive :
  ∀ {size} (index : Carrier.CyclicIndex size) →
  reverseFiniteIndex (reverseFiniteIndex index) ≡ index
reverseFiniteIndexInvolutive {zero} ()
reverseFiniteIndexInvolutive {suc size} Carrier.zeroᵢ =
  reverseLastFiniteIndex size
reverseFiniteIndexInvolutive {suc size} (Carrier.sucᵢ index)
  rewrite reverseWeakenFiniteIndex (reverseFiniteIndex index)
        | reverseFiniteIndexInvolutive index = refl

centeredOffsetIndex :
  ∀ {radius} →
  Centered.CenteredOffset radius →
  Carrier.CyclicIndex (suc (radius + radius))
centeredOffsetIndex Centered.centre = Carrier.zeroᵢ
centeredOffsetIndex (Centered.positive index) =
  Carrier.sucᵢ (injectLeftIndex index)
centeredOffsetIndex (Centered.negative index) =
  Carrier.sucᵢ (injectRightIndex (reverseFiniteIndex index))

centeredOffsetFromIndex :
  ∀ {radius} →
  Carrier.CyclicIndex (suc (radius + radius)) →
  Centered.CenteredOffset radius
centeredOffsetFromIndex Carrier.zeroᵢ = Centered.centre
centeredOffsetFromIndex (Carrier.sucᵢ index)
  with splitIndex index
... | fromLeft left = Centered.positive left
... | fromRight right = Centered.negative (reverseFiniteIndex right)

centeredOffsetDecodeEncode :
  ∀ {radius} (offset : Centered.CenteredOffset radius) →
  centeredOffsetFromIndex (centeredOffsetIndex offset) ≡ offset
centeredOffsetDecodeEncode Centered.centre = refl
centeredOffsetDecodeEncode (Centered.positive index)
  rewrite splitInjectedLeft index = refl
centeredOffsetDecodeEncode (Centered.negative index)
  rewrite splitInjectedRight (reverseFiniteIndex index)
        | reverseFiniteIndexInvolutive index = refl

centeredOffsetIndexInjective :
  ∀ {radius} {left right : Centered.CenteredOffset radius} →
  centeredOffsetIndex left ≡ centeredOffsetIndex right →
  left ≡ right
centeredOffsetIndexInjective {left = left} {right = right} equality =
  trans
    (sym (centeredOffsetDecodeEncode left))
    (trans
      (cong centeredOffsetFromIndex equality)
      (centeredOffsetDecodeEncode right))

pairCong :
  ∀ {A B : Set} {leftA rightA : A} {leftB rightB : B} →
  leftA ≡ rightA → leftB ≡ rightB →
  Carrier.pair leftA leftB ≡ Carrier.pair rightA rightB
pairCong refl refl = refl

centeredTorusParameter : Nat → Nat
centeredTorusParameter radius = radius + radius

centeredTorusWidth : Nat → Nat
centeredTorusWidth radius = suc (centeredTorusParameter radius)

centeredTorusWidthIsDisplayedOddSide : ∀ radius →
  centeredTorusWidth radius ≡ Centered.oddSide radius
centeredTorusWidthIsDisplayedOddSide radius =
  cong suc (Centered.selfAddEqualsTwice radius)

directCenteredEmbed :
  ∀ {radius} →
  Centered.CenteredBlockPoint4 radius →
  Blocks.PeriodicBlock (centeredTorusParameter radius)
directCenteredEmbed
    (Carrier.pair (Carrier.pair offset0 offset1)
      (Carrier.pair offset2 offset3)) =
  Carrier.pair
    (Carrier.pair
      (centeredOffsetIndex offset0)
      (centeredOffsetIndex offset1))
    (Carrier.pair
      (centeredOffsetIndex offset2)
      (centeredOffsetIndex offset3))

directCenteredDecode :
  ∀ {radius} →
  Blocks.PeriodicBlock (centeredTorusParameter radius) →
  Centered.CenteredBlockPoint4 radius
directCenteredDecode
    (Carrier.pair (Carrier.pair index0 index1)
      (Carrier.pair index2 index3)) =
  Carrier.pair
    (Carrier.pair
      (centeredOffsetFromIndex index0)
      (centeredOffsetFromIndex index1))
    (Carrier.pair
      (centeredOffsetFromIndex index2)
      (centeredOffsetFromIndex index3))

directCenteredDecodeEncode :
  ∀ {radius} (point : Centered.CenteredBlockPoint4 radius) →
  directCenteredDecode (directCenteredEmbed point) ≡ point
directCenteredDecodeEncode
    (Carrier.pair (Carrier.pair offset0 offset1)
      (Carrier.pair offset2 offset3)) =
  pairCong
    (pairCong
      (centeredOffsetDecodeEncode offset0)
      (centeredOffsetDecodeEncode offset1))
    (pairCong
      (centeredOffsetDecodeEncode offset2)
      (centeredOffsetDecodeEncode offset3))

directCenteredEmbedInjective :
  ∀ {radius}
    {left right : Centered.CenteredBlockPoint4 radius} →
  directCenteredEmbed left ≡ directCenteredEmbed right →
  left ≡ right
directCenteredEmbedInjective {left = left} {right = right} equality =
  trans
    (sym (directCenteredDecodeEncode left))
    (trans
      (cong directCenteredDecode equality)
      (directCenteredDecodeEncode right))

directCenteredOrigin :
  ∀ {radius} → Blocks.PeriodicBlock (centeredTorusParameter radius)
directCenteredOrigin =
  Carrier.pair
    (Carrier.pair Carrier.zeroᵢ Carrier.zeroᵢ)
    (Carrier.pair Carrier.zeroᵢ Carrier.zeroᵢ)

directCenteredOriginExact : ∀ {radius} →
  directCenteredEmbed (Centered.centeredOrigin4 {radius})
  ≡ directCenteredOrigin
directCenteredOriginExact = refl

directWalkAgreementPredicate :
  ∀ {radius} → Centered.CenteredBlockPoint4 radius → Set
directWalkAgreementPredicate {radius} point =
  directCenteredEmbed point
  ≡ Embedding.centeredTargetSite directCenteredOrigin point

record CenteredTorusWalkAgreementCertificate (radius : Nat) : Set where
  field
    everyDirectEmbeddingAgreesWithWalk :
      Endpoint.All directWalkAgreementPredicate
        (Carrier.elements (Centered.centeredBlockFinite radius))

open CenteredTorusWalkAgreementCertificate public

directWalkAgreementDecision :
  ∀ {radius} (point : Centered.CenteredBlockPoint4 radius) →
  Carrier.Dec (directWalkAgreementPredicate point)
directWalkAgreementDecision {radius} point =
  Carrier.periodicTorus4DecidableEquality
    (centeredTorusWidth radius)
    (directCenteredEmbed point)
    (Embedding.centeredTargetSite directCenteredOrigin point)

centeredTorusWalkAgreementCertificateDecision :
  ∀ radius → Carrier.Dec (CenteredTorusWalkAgreementCertificate radius)
centeredTorusWalkAgreementCertificateDecision radius
  with Endpoint.decideAll directWalkAgreementDecision
    (Carrier.elements (Centered.centeredBlockFinite radius))
... | Carrier.yes proof = Carrier.yes record
  { everyDirectEmbeddingAgreesWithWalk = proof }
... | Carrier.no notProof = Carrier.no λ certificate →
  notProof (everyDirectEmbeddingAgreesWithWalk certificate)

directEmbeddingAgreesWithWalk :
  ∀ {radius} →
  CenteredTorusWalkAgreementCertificate radius →
  ∀ point → directWalkAgreementPredicate point
directEmbeddingAgreesWithWalk {radius} certificate point =
  BlockCertificate.allCarrierMembership
    (everyDirectEmbeddingAgreesWithWalk certificate)
    (Carrier.complete (Centered.centeredBlockFinite radius) point)

canonicalCenteredNoWrapEmbedding :
  ∀ {radius} →
  CenteredTorusWalkAgreementCertificate radius →
  Embedding.CenteredPeriodicNoWrapEmbedding
    (centeredTorusParameter radius) radius
canonicalCenteredNoWrapEmbedding certificate = record
  { Embedding.CenteredPeriodicNoWrapEmbedding.embeddingCentre =
      directCenteredOrigin
  ; Embedding.CenteredPeriodicNoWrapEmbedding.embed = directCenteredEmbed
  ; Embedding.CenteredPeriodicNoWrapEmbedding.embedMeaning =
      directEmbeddingAgreesWithWalk certificate
  ; Embedding.CenteredPeriodicNoWrapEmbedding.embedInjective =
      directCenteredEmbedInjective
  ; Embedding.CenteredPeriodicNoWrapEmbedding.originMeaning =
      directCenteredOriginExact
  }

cmp109CenteredFiniteIndexReversalLevel : ProofLevel
cmp109CenteredFiniteIndexReversalLevel = machineChecked

cmp109CenteredOffsetPeriodicBijectionLevel : ProofLevel
cmp109CenteredOffsetPeriodicBijectionLevel = machineChecked

cmp109CenteredBlockPeriodicInjectionLevel : ProofLevel
cmp109CenteredBlockPeriodicInjectionLevel = machineChecked

cmp109CenteredDirectWalkAgreementDecisionLevel : ProofLevel
cmp109CenteredDirectWalkAgreementDecisionLevel = computed

cmp109CenteredCanonicalNoWrapEmbeddingLevel : ProofLevel
cmp109CenteredCanonicalNoWrapEmbeddingLevel = machineChecked

physicalCMP109CenteredWalkAgreementCertificateInputsLevel : ProofLevel
physicalCMP109CenteredWalkAgreementCertificateInputsLevel = conditional
