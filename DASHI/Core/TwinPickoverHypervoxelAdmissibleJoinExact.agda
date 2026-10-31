{-# OPTIONS --safe #-}
module DASHI.Core.TwinPickoverHypervoxelAdmissibleJoinExact where

-- An actual join theorem over the ORIGINAL RecursiveRadixHypervoxel owner.
-- No new gluing carrier, no Boolean receipts, no analytic postulates.
open import DASHI.Core.Prelude
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Residual

-- If two histories have the same exact parent+suffix, they have
-- the same refined address. Neither chart alone is assumed sufficient.
fineAgreement :
  ∀ {rank coarseDepth fineDepth}
  (parentA parentB : Hyper.TernaryAddress rank coarseDepth)
  (suffixA suffixB : Hyper.AddressSuffix rank fineDepth) →
  parentA ≡ parentB → suffixA ≡ suffixB →
  Hyper.joinAddress parentA suffixA ≡ Hyper.joinAddress parentB suffixB
fineAgreement parentA parentB suffixA suffixB refl refl = refl

-- A consumer factoring through the exact joined address is invariant
-- under equality of the fully retained parent and suffix pair.
addressConsumerDescent :
  ∀ {rank coarseDepth fineDepth} {Outcome : Set}
  (query : Hyper.TernaryAddress rank (Hyper._⊕_ coarseDepth fineDepth) → Outcome)
  (parentA parentB : Hyper.TernaryAddress rank coarseDepth)
  (suffixA suffixB : Hyper.AddressSuffix rank fineDepth) →
  parentA ≡ parentB → suffixA ≡ suffixB →
  query (Hyper.joinAddress parentA suffixA)
    ≡ query (Hyper.joinAddress parentB suffixB)
addressConsumerDescent query parentA parentB suffixA suffixB pa su =
  cong query (fineAgreement parentA parentB suffixA suffixB pa su)

-- Every original cross-object join already carries interface compatibility.
-- Transport that *actual* seam equality to arbitrary observable consumers.
seamConsumerAgreement :
  ∀ {Left Interface Right Outcome : Set}
  (join : Hyper.CrossObjectJoin Left Interface Right)
  (query : Hyper.CrossObjectJoin.Joined join → Outcome)
  (interface : Interface) →
  query (Hyper.CrossObjectJoin.injectLeft join
           (Hyper.CrossObjectJoin.leftInterface join interface))
  ≡ query (Hyper.CrossObjectJoin.injectRight join
           (Hyper.CrossObjectJoin.rightInterface join interface))
seamConsumerAgreement join query interface =
  cong query (Hyper.CrossObjectJoin.interfaceCompatible join interface)


-- The first NONTRIVIAL descent contract. A domain must supply the actual
-- original history's fine address and a proof its consumer factors there.
-- Only then may an address quotient replace the retained full history.

record FineAddressFactorisation
    {History Outcome : Set}
    (rank coarseDepth fineDepth : Nat)
    (coarse : History → Hyper.TernaryAddress rank coarseDepth)
    (suffix : History → Hyper.AddressSuffix rank fineDepth)
    (consumer : History → Outcome) : Set₁ where
  field
    decodeFine :
      Hyper.TernaryAddress rank (Hyper._⊕_ coarseDepth fineDepth) → Outcome
    factorLaw : (h : History) →
      consumer h ≡ decodeFine (Hyper.joinAddress (coarse h) (suffix h))

open FineAddressFactorisation public

-- A retained (coarse, suffix) pair is sufficient for the actual consumer,
-- PROVIDED the fine factorisation was established by the domain.
retainedPairSufficient :
  ∀ {History Outcome : Set} {rank coarseDepth fineDepth}
  {coarse : History → Hyper.TernaryAddress rank coarseDepth}
  {suffix : History → Hyper.AddressSuffix rank fineDepth}
  {consumer : History → Outcome} →
  FineAddressFactorisation rank coarseDepth fineDepth coarse suffix consumer →
  Residual.ConsumerSufficient (λ h → coarse h , suffix h) consumer
retainedPairSufficient witness x y same =
  trans (factorLaw witness x)
    (trans
      (cong
        (λ pair → decodeFine witness
          (Hyper.joinAddress (proj₁ pair) (proj₂ pair)))
        same)
      (sym (factorLaw witness y)))

-- Construct an explicit original-repository residual repair certificate
-- rather than inventing a competing observer/quotient proof ontology.
canonicalResidualRepair :
  ∀ {History Outcome : Set} {rank coarseDepth fineDepth}
  {coarse : History → Hyper.TernaryAddress rank coarseDepth}
  {suffix : History → Hyper.AddressSuffix rank fineDepth}
  {consumer : History → Outcome} →
  (witness : FineAddressFactorisation rank coarseDepth fineDepth
                   coarse suffix consumer) →
  Residual.ResidualRepair coarse suffix consumer
canonicalResidualRepair witness = record
  { jointSufficient = retainedPairSufficient witness }

-- Under a witnessed consumer-relevant coarse collision, a successful
-- retained suffix MUST differ. This discharges the admissible-refinement
-- necessity theorem using the original repository's existing proof.
retainedSuffixSeparatesConsumerCollision :
  ∀ {History Outcome : Set} {rank coarseDepth fineDepth}
  {coarse : History → Hyper.TernaryAddress rank coarseDepth}
  {suffix : History → Hyper.AddressSuffix rank fineDepth}
  {consumer : History → Outcome} →
  (collision : Residual.ConsumerRelevantCollision coarse consumer) →
  (witness : FineAddressFactorisation rank coarseDepth fineDepth
                    coarse suffix consumer) →
  suffix (Residual.left collision) ≡
  suffix (Residual.right collision) → ⊥
retainedSuffixSeparatesConsumerCollision collision witness =
  Residual.residualMustSeparateRelevantCollision
    collision (canonicalResidualRepair witness)
