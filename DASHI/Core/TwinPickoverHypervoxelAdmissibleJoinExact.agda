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

