module DASHI.Physics.Closure.NSTriadKNFiniteIncidenceSubspaceAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import Base369 using (TriTruth)
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Foundations.FiniteLinear.AntiDiagonalKernel as AntiDiagonal
import DASHI.Foundations.FiniteLinear.F3Subspace as Linear
import DASHI.Physics.Closure.NSTriadKNExactPairIncidenceGramAssembly as Gram

------------------------------------------------------------------------
-- Finite orientation carrier for the NS pair-incidence Gram seam.
--
-- NSTriadKNExactPairIncidenceGramAssembly identifies the missing concrete
-- rank-one edge vector as
--
--               b_r = e_(source r) - e_(target r).
--
-- Over F3, the two-coordinate coefficient carrier is exactly the
-- anti-diagonal image t |-> (t,-t), equivalently ker(x+y).  This module
-- instantiates that finite-linear orientation object and nothing stronger:
-- the physical scalar coefficient, shell vector space, rank-one operator and
-- equality with the PDE auxiliary Gram fold remain the existing obligations.
------------------------------------------------------------------------

PairEdge : Set
PairEdge = AntiDiagonal.Vec2

orientedPairEdge : TriTruth → PairEdge
orientedPairEdge = AntiDiagonal.antiDiagonal

orientedPairEdgeInImage :
  (coefficient : TriTruth) →
  Linear.Member AntiDiagonal.antiDiagonalLine
    (orientedPairEdge coefficient)
orientedPairEdgeInImage coefficient =
  Linear.imageMember coefficient refl

orientedPairEdgeHasZeroSum :
  (coefficient : TriTruth) →
  Linear.Member AntiDiagonal.sumZeroLine
    (orientedPairEdge coefficient)
orientedPairEdgeHasZeroSum coefficient =
  AntiDiagonal.antiDiagonalToSumZero
    (orientedPairEdgeInImage coefficient)

finitePairEdgeKernelImageEquality :
  AntiDiagonal.sumZeroLine Linear.≈ₛ AntiDiagonal.antiDiagonalLine
finitePairEdgeKernelImageEquality =
  AntiDiagonal.sumZeroIsAntiDiagonal

record FiniteIncidenceGramAdapterStatus : Set where
  constructor finiteIncidenceGramAdapterStatus
  field
    sourceModule : String
    sourcePendingRecord : String
    finiteOrientedPairCarrierInstantiated : Bool
    finiteOrientedPairCarrierInstantiatedIsTrue :
      finiteOrientedPairCarrierInstantiated ≡ true
    sourceMinusTargetEncodedAsAntiDiagonal : Bool
    sourceMinusTargetEncodedAsAntiDiagonalIsTrue :
      sourceMinusTargetEncodedAsAntiDiagonal ≡ true
    sumZeroKernelEqualsEdgeImage : Bool
    sumZeroKernelEqualsEdgeImageIsTrue :
      sumZeroKernelEqualsEdgeImage ≡ true
    physicalExactScalarCarrierInstantiatedHere : Bool
    physicalExactScalarCarrierInstantiatedHereIsFalse :
      physicalExactScalarCarrierInstantiatedHere ≡ false
    pairIncidenceFoldEqualsPDEGramProvedHere : Bool
    pairIncidenceFoldEqualsPDEGramProvedHereIsFalse :
      pairIncidenceFoldEqualsPDEGramProvedHere ≡ false
    reading : String

open FiniteIncidenceGramAdapterStatus public

canonicalFiniteIncidenceGramAdapterStatus :
  FiniteIncidenceGramAdapterStatus
canonicalFiniteIncidenceGramAdapterStatus =
  finiteIncidenceGramAdapterStatus
    "DASHI.Physics.Closure.NSTriadKNExactPairIncidenceGramAssembly"
    "ExactPairIncidenceFoldEqualsAuxiliaryTriadGram"
    true refl
    true refl
    true refl
    false refl
    false refl
    "the reusable finite-subspace API now owns the oriented source-minus-target coefficient skeleton; the exact ordered-scalar Fourier shell vector and PDE Gram operator equality remain in the NS closure lane"

sourceGramClosureStillOpen :
  Gram.exactPairIncidenceFoldEqualsAuxiliaryTriadGramClosed ≡ false
sourceGramClosureStillOpen = refl

finiteIncidenceGramAdapterReceipt : GenericReceipt.GenericReceipt
finiteIncidenceGramAdapterReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "finite pair-incidence subspace adapter"
    "DASHI.Physics.Closure.NSTriadKNFiniteIncidenceSubspaceAdapter"
    "canonicalFiniteIncidenceGramAdapterStatus"
    "the source-minus-target two-coordinate F3 edge carrier is instantiated as the anti-diagonal image and proved equal to the sum-zero kernel"
    "the physical exact scalar carrier, Fourier shell basis, rank-one operator fold and literal PDE Gram equality remain explicit NS obligations"
    "agda -i . DASHI/Physics/Closure/NSTriadKNFiniteIncidenceSubspaceAdapter.agda"

finiteIncidenceGramAdapterReceiptNonPromoting :
  GenericReceipt.promotesClaim finiteIncidenceGramAdapterReceipt ≡ false
finiteIncidenceGramAdapterReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse finiteIncidenceGramAdapterReceipt
