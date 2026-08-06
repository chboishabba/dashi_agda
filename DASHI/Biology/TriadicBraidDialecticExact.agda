module DASHI.Biology.TriadicBraidDialecticExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Three dialectical strands.  The endpoint action below factors through the
-- symmetric group; the separate history carrier retains braid-word order.

record TritTriple : Set where
  constructor tritTriple
  field
    first : Triadic.KernelTrit
    second : Triadic.KernelTrit
    third : Triadic.KernelTrit

open TritTriple public

data BraidGenerator : Set where
  sigma1 : BraidGenerator
  sigma2 : BraidGenerator

applyGenerator : BraidGenerator → TritTriple → TritTriple
applyGenerator sigma1 (tritTriple a b c) = tritTriple b a c
applyGenerator sigma2 (tritTriple a b c) = tritTriple a c b

leftYangBaxter : TritTriple → TritTriple
leftYangBaxter x =
  applyGenerator sigma1
    (applyGenerator sigma2
      (applyGenerator sigma1 x))

rightYangBaxter : TritTriple → TritTriple
rightYangBaxter x =
  applyGenerator sigma2
    (applyGenerator sigma1
      (applyGenerator sigma2 x))

yangBaxterEndpointEquality :
  (x : TritTriple) → leftYangBaxter x ≡ rightYangBaxter x
yangBaxterEndpointEquality (tritTriple a b c) = refl

sigma1EndpointInvolutive :
  (x : TritTriple) →
  applyGenerator sigma1 (applyGenerator sigma1 x) ≡ x
sigma1EndpointInvolutive (tritTriple a b c) = refl

sigma2EndpointInvolutive :
  (x : TritTriple) →
  applyGenerator sigma2 (applyGenerator sigma2 x) ≡ x
sigma2EndpointInvolutive (tritTriple a b c) = refl

------------------------------------------------------------------------
-- Braid history is not collapsed merely because the endpoint action agrees.

data BraidWordKind : Set where
  sigma1Sigma2Sigma1 : BraidWordKind
  sigma2Sigma1Sigma2 : BraidWordKind
  directEndpointPermutation : BraidWordKind

data CrossingOrientation : Set where
  positiveCrossing : CrossingOrientation
  negativeCrossing : CrossingOrientation

record BraidResidual : Set where
  constructor braidResidual
  field
    wordKind : BraidWordKind
    crossingCount : Nat
    orientation : CrossingOrientation
    historicalLevel : Nat

open BraidResidual public

leftBraidResidual : BraidResidual
leftBraidResidual =
  braidResidual sigma1Sigma2Sigma1 3 positiveCrossing 1

rightBraidResidual : BraidResidual
rightBraidResidual =
  braidResidual sigma2Sigma1Sigma2 3 negativeCrossing 1

leftAndRightCrossingCountsAgree :
  crossingCount leftBraidResidual ≡ crossingCount rightBraidResidual
leftAndRightCrossingCountsAgree = refl

leftAndRightWordKindsDiffer :
  ¬ (wordKind leftBraidResidual ≡ wordKind rightBraidResidual)
leftAndRightWordKindsDiffer ()

record BraidedTransition : Set where
  constructor braidedTransition
  field
    source : TritTriple
    endpoint : TritTriple
    residual : BraidResidual

open BraidedTransition public

canonicalSource : TritTriple
canonicalSource =
  tritTriple
    Triadic.negativeTrit
    Triadic.zeroTrit
    Triadic.positiveTrit

leftTransition : BraidedTransition
leftTransition =
  braidedTransition canonicalSource
    (leftYangBaxter canonicalSource)
    leftBraidResidual

rightTransition : BraidedTransition
rightTransition =
  braidedTransition canonicalSource
    (rightYangBaxter canonicalSource)
    rightBraidResidual

braidRelationSharesEndpoint :
  endpoint leftTransition ≡ endpoint rightTransition
braidRelationSharesEndpoint = refl

braidRelationRetainsDistinctWordResidual :
  ¬ (wordKind (residual leftTransition)
     ≡ wordKind (residual rightTransition))
braidRelationRetainsDistinctWordResidual ()

------------------------------------------------------------------------
-- Triadic semantics are typed independently from the braid topology.

data DialecticalStrandRole : Set where
  thesisStrand : DialecticalStrandRole
  mediatingStrand : DialecticalStrandRole
  antithesisStrand : DialecticalStrandRole

roleTrit : DialecticalStrandRole → Triadic.KernelTrit
roleTrit thesisStrand = Triadic.positiveTrit
roleTrit mediatingStrand = Triadic.zeroTrit
roleTrit antithesisStrand = Triadic.negativeTrit

canonicalDialecticalTriple : TritTriple
canonicalDialecticalTriple =
  tritTriple
    (roleTrit antithesisStrand)
    (roleTrit mediatingStrand)
    (roleTrit thesisStrand)

record TriadicBraidBoundary : Set where
  constructor triadicBraidBoundary
  field
    endpointEqualityErasesBraidHistory : Bool
    endpointEqualityErasesBraidHistoryIsFalse :
      endpointEqualityErasesBraidHistory ≡ false

    permutationRepresentationIsFaithfulBraidGroupAction : Bool
    permutationRepresentationIsFaithfulBraidGroupActionIsFalse :
      permutationRepresentationIsFaithfulBraidGroupAction ≡ false

    mediatingStrandAlwaysResolvesOpposition : Bool
    mediatingStrandAlwaysResolvesOppositionIsFalse :
      mediatingStrandAlwaysResolvesOpposition ≡ false

    braidWordDiagnosesPerson : Bool
    braidWordDiagnosesPersonIsFalse :
      braidWordDiagnosesPerson ≡ false

open TriadicBraidBoundary public

canonicalTriadicBraidBoundary : TriadicBraidBoundary
canonicalTriadicBraidBoundary =
  triadicBraidBoundary false refl false refl false refl false refl
