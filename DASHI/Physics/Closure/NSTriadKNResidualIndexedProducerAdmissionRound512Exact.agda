module DASHI.Physics.Closure.NSTriadKNResidualIndexedProducerAdmissionRound512Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNClayResidualIntrospectionRound509Exact as R509
import DASHI.Physics.Closure.NSTriadKNSignedNetworkBudgetCompilerRound511Exact as R511

------------------------------------------------------------------------
-- ROUND512 / RESIDUAL-INDEXED PRODUCER ADMISSION
--
-- The introspective diagram exposes one remaining observer collision in R510/511:
-- "signed phase/network/time geometry" is a useful producer family, but it is
-- useful for the sharpened physical part of leaf B.  No theorem currently
-- identifies that carrier with leaf A's literal nonseparable R406 resolvent
-- signed cross.  Producer relevance must therefore be indexed by the exact live
-- residual, rather than recorded as a global label.
------------------------------------------------------------------------

data ProducerRoute512 : Set where
  directR406SignedSpacetimeEstimate : ProducerRoute512
  signedNetworkNormalFormBudget : ProducerRoute512
  literalR406RemainderWeld : ProducerRoute512

data RouteAdmission512 : Set where
  attacksExactResidual : RouteAdmission512
  adjacentButDoesNotPayResidual : RouteAdmission512

routeAdmission : R509.ClayResidual509 → ProducerRoute512 → RouteAdmission512
routeAdmission R509.signedCrossUniformBoundResidual directR406SignedSpacetimeEstimate =
  attacksExactResidual
routeAdmission R509.signedCrossUniformBoundResidual signedNetworkNormalFormBudget =
  adjacentButDoesNotPayResidual
routeAdmission R509.signedCrossUniformBoundResidual literalR406RemainderWeld =
  adjacentButDoesNotPayResidual

routeAdmission R509.externalCrossTriadCriticalPaymentResidual directR406SignedSpacetimeEstimate =
  adjacentButDoesNotPayResidual
routeAdmission R509.externalCrossTriadCriticalPaymentResidual signedNetworkNormalFormBudget =
  attacksExactResidual
routeAdmission R509.externalCrossTriadCriticalPaymentResidual literalR406RemainderWeld =
  adjacentButDoesNotPayResidual

routeAdmission R509.literalR406RemainderWeldResidual directR406SignedSpacetimeEstimate =
  adjacentButDoesNotPayResidual
routeAdmission R509.literalR406RemainderWeldResidual signedNetworkNormalFormBudget =
  adjacentButDoesNotPayResidual
routeAdmission R509.literalR406RemainderWeldResidual literalR406RemainderWeld =
  attacksExactResidual

routeAdmission R509.clayCutsetClosed _ = adjacentButDoesNotPayResidual

currentLeafAProducer : ProducerRoute512
currentLeafAProducer = directR406SignedSpacetimeEstimate

currentLeafAProducerIsAdmitted :
  routeAdmission R509.signedCrossUniformBoundResidual currentLeafAProducer
  ≡ attacksExactResidual
currentLeafAProducerIsAdmitted = refl

signedNetworkBudgetDoesNotAttackLeafA :
  routeAdmission R509.signedCrossUniformBoundResidual signedNetworkNormalFormBudget
  ≡ adjacentButDoesNotPayResidual
signedNetworkBudgetDoesNotAttackLeafA = refl

signedNetworkBudgetAttacksLeafBPhysicalResidual :
  routeAdmission R509.externalCrossTriadCriticalPaymentResidual signedNetworkNormalFormBudget
  ≡ attacksExactResidual
signedNetworkBudgetAttacksLeafBPhysicalResidual = refl

------------------------------------------------------------------------
-- R511 remains a real theorem compiler, but its existence is not leaf-A payment.
------------------------------------------------------------------------

round511CompilerClosed : R511.round511ExactSignedBudgetCompilerClosed ≡ true
round511CompilerClosed = R511.round511ExactSignedBudgetCompilerClosedIsTrue

data SignedNetworkCompilerPaysLeafA : Set where
signedNetworkCompilerDoesNotPayLeafA : SignedNetworkCompilerPaysLeafA → ⊥
signedNetworkCompilerDoesNotPayLeafA ()

round512LeafAStillOpen : Bool
round512LeafAStillOpen = true

round512LeafBProducerBetterSpecified : Bool
round512LeafBProducerBetterSpecified = true

round512ClayPromotion : Bool
round512ClayPromotion = false

round512LeafAStillOpenIsTrue : round512LeafAStillOpen ≡ true
round512LeafAStillOpenIsTrue = refl

round512LeafBProducerBetterSpecifiedIsTrue :
  round512LeafBProducerBetterSpecified ≡ true
round512LeafBProducerBetterSpecifiedIsTrue = refl

round512ClayPromotionIsFalse : round512ClayPromotion ≡ false
round512ClayPromotionIsFalse = refl
