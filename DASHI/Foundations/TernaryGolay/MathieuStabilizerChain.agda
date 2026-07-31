module DASHI.Foundations.TernaryGolay.MathieuStabilizerChain where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_*_)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.MathieuSourceAtlas as Sources
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.PuncturedPerfectCode as Puncture
import DASHI.Foundations.TernaryGolay.SourceAtlas as BaseSources

------------------------------------------------------------------------
-- Stabilizer-chain disambiguation.
--
-- The order 660 subgroup is real, but it is not the ordered two-point
-- stabilizer of the sharply five-transitive degree-12 action:
--
--   |M12| / 12       = 7920,
--   |M12| / (12*11)  = 720,
--   |M11| / 12       = 660.
--
-- L2(11) is a distinct maximal subgroup of M11 of index 12.
------------------------------------------------------------------------

m12Order : Nat
m12Order = 95040

m11PointStabilizerOrder : Nat
m11PointStabilizerOrder = 7920

orderedTwoPointStabilizerOrder : Nat
orderedTwoPointStabilizerOrder = 720

psl211Order : Nat
psl211Order = 660

pointOrbitArithmetic :
  12 * m11PointStabilizerOrder ≡ m12Order
pointOrbitArithmetic = refl

orderedPairOrbitArithmetic :
  11 * orderedTwoPointStabilizerOrder
  ≡ m11PointStabilizerOrder
orderedPairOrbitArithmetic = refl

pslIndexTwelveArithmetic :
  12 * psl211Order ≡ m11PointStabilizerOrder
pslIndexTwelveArithmetic = refl

record StabilizerRoleSeparation : Set where
  constructor stabilizerRoleSeparation
  field
    atlasAuthor : String
    atlasTitle : String
    atlasURL : String
    fullGroupOrder : Nat
    fullGroupOrderIs95040 : fullGroupOrder ≡ 95040
    oncePuncturedCoordinateStabilizerOrder : Nat
    oncePuncturedOrderIs7920 :
      oncePuncturedCoordinateStabilizerOrder ≡ 7920
    orderedTwoPointStabilizerOrderField : Nat
    orderedTwoPointOrderIs720 :
      orderedTwoPointStabilizerOrderField ≡ 720
    psl211MaximalSubgroupOrder : Nat
    psl211OrderIs660 :
      psl211MaximalSubgroupOrder ≡ 660
    psl211IsOrderedTwoPointStabilizer : Bool
    psl211IsOrderedTwoPointStabilizerIsFalse :
      psl211IsOrderedTwoPointStabilizer ≡ false
    psl211IsIndexTwelveSubgroupOfM11 : Bool
    psl211IsIndexTwelveSubgroupOfM11IsTrue :
      psl211IsIndexTwelveSubgroupOfM11 ≡ true
    derivedS4511BlockCount :
      Explicit.listCount Puncture.derivedBlocks ≡ 66
    derivedS4511Incidence :
      Puncture.derivedSteinerCheck ≡ true

canonicalStabilizerRoleSeparation : StabilizerRoleSeparation
canonicalStabilizerRoleSeparation =
  stabilizerRoleSeparation
    (BaseSources.author Sources.atlasM11Entry)
    (BaseSources.title Sources.atlasM11Entry)
    (BaseSources.canonicalURL Sources.atlasM11Entry)
    95040 refl
    7920 refl
    720 refl
    660 refl
    false refl
    true refl
    Puncture.derivedBlockCountIs66
    Puncture.derivedSteinerS4511

stabilizerChainReceipt : GenericReceipt.GenericReceipt
stabilizerChainReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Mathieu stabilizer-chain role separation"
    "DASHI.Foundations.TernaryGolay.MathieuStabilizerChain"
    "canonicalStabilizerRoleSeparation"
    "the orders 95040, 7920, 720 and 660 are assigned to distinct roles; the once-punctured derived design is the locally computed S(4,5,11), while L2(11) is recorded as an index-12 M11 subgroup rather than a two-point stabilizer"
    "the ATLAS identification of the order-660 subgroup remains an external group theorem; no puncturing operation is conflated with subgroup index arithmetic"
    "agda -i . DASHI/Foundations/TernaryGolay/MathieuStabilizerChain.agda"

stabilizerChainReceiptNonPromoting :
  GenericReceipt.promotesClaim stabilizerChainReceipt ≡ false
stabilizerChainReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse stabilizerChainReceipt
