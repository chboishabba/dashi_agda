module DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalGramFactorizationRound65Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- DOI: no DOI assigned to the cited historical conference article.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 65 / SAME-CARRIER B1-B3 CONSUMER
--
-- The historical GramInterferenceCell is Q-valued.  This module reconstructs
-- the factorization directly in Carrier(realField model).  The only extra
-- structure beyond OrderedRealExtension is the standard monotonicity of
-- multiplication on nonnegative elements.
--
-- For a physical factorized cell
--
--   pairProduct <= leftOuter * overlap * rightOuter,
--   0 <= leftOuter,rightOuter,overlap,
--   leftOuter,rightOuter <= 1,
--
-- we derive pairProduct <= overlap on the SAME carrier.  If the internal
-- overlap is then bounded by the embedded six-three gap, the physical pair
-- product inherits that bound without identifying physical energy with Q.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Ordered
import DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalMajorantRound62Exact as Embed
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree

record NonnegativeMultiplicativeOrder
    {r : Level}
    {F : C3.RealField r}
    (O : Ordered.OrderedRealExtension F) : Set (lsuc r) where
  field
    multiplyNonnegative : ∀ {a b} →
      Ordered._≤_ O (C3.zero F) a →
      Ordered._≤_ O (C3.zero F) b →
      Ordered._≤_ O (C3.zero F) (C3.multiply F a b)

    multiplyMonotoneNonnegative : ∀ {a a' b b'} →
      Ordered._≤_ O (C3.zero F) a →
      Ordered._≤_ O (C3.zero F) b →
      Ordered._≤_ O (C3.zero F) a' →
      Ordered._≤_ O (C3.zero F) b' →
      Ordered._≤_ O a a' →
      Ordered._≤_ O b b' →
      Ordered._≤_ O (C3.multiply F a b) (C3.multiply F a' b')

open NonnegativeMultiplicativeOrder public

oneNonnegative :
  ∀ {r} {F : C3.RealField r}
    (O : Ordered.OrderedRealExtension F) →
  Ordered._≤_ O (C3.zero F) (C3.one F)
oneNonnegative {F = F} O =
  subst
    (λ target → Ordered._≤_ O (C3.zero F) target)
    (C3.multiplyOneLeft F (C3.one F))
    (Ordered.zeroBelowSquare O (C3.one F))

multiplyOneRight :
  ∀ {r} {F : C3.RealField r} (value : C3.Carrier F) →
  C3.multiply F value (C3.one F) ≡ value
multiplyOneRight {F = F} value =
  trans
    (C3.multiplyCommutative F value (C3.one F))
    (C3.multiplyOneLeft F value)

record PhysicalFactorizedGramCell
    {r : Level}
    {F : C3.RealField r}
    (O : Ordered.OrderedRealExtension F)
    (M : NonnegativeMultiplicativeOrder O)
    (gap : Nat) : Set r where
  field
    leftOuter overlap rightOuter pairProduct : C3.Carrier F

    leftOuterNonnegative : Ordered._≤_ O (C3.zero F) leftOuter
    overlapNonnegative : Ordered._≤_ O (C3.zero F) overlap
    rightOuterNonnegative : Ordered._≤_ O (C3.zero F) rightOuter
    pairProductNonnegative : Ordered._≤_ O (C3.zero F) pairProduct

    leftOuterContraction : Ordered._≤_ O leftOuter (C3.one F)
    rightOuterContraction : Ordered._≤_ O rightOuter (C3.one F)

    pairProductFactorizationBound :
      Ordered._≤_ O pairProduct
        (C3.multiply F
          (C3.multiply F leftOuter overlap)
          rightOuter)

open PhysicalFactorizedGramCell public

physicalOuterContractionsRemove :
  ∀ {r} {F : C3.RealField r}
    {O : Ordered.OrderedRealExtension F}
    {M : NonnegativeMultiplicativeOrder O}
    {gap}
    (cell : PhysicalFactorizedGramCell O M gap) →
  Ordered._≤_ O (pairProduct cell) (overlap cell)
physicalOuterContractionsRemove {F = F} {O = O} {M = M} cell =
  let
    leftTimesOverlapBelow :
      Ordered._≤_ O
        (C3.multiply F (leftOuter cell) (overlap cell))
        (overlap cell)
    leftTimesOverlapBelow =
      subst
        (λ target →
          Ordered._≤_ O
            (C3.multiply F (leftOuter cell) (overlap cell))
            target)
        (C3.multiplyOneLeft F (overlap cell))
        (multiplyMonotoneNonnegative M
          (leftOuterNonnegative cell)
          (overlapNonnegative cell)
          (oneNonnegative O)
          (overlapNonnegative cell)
          (leftOuterContraction cell)
          (Ordered.leqReflexive O (overlap cell)))

    leftTimesOverlapNN :
      Ordered._≤_ O (C3.zero F)
        (C3.multiply F (leftOuter cell) (overlap cell))
    leftTimesOverlapNN =
      multiplyNonnegative M
        (leftOuterNonnegative cell)
        (overlapNonnegative cell)

    withRight :
      Ordered._≤_ O
        (C3.multiply F
          (C3.multiply F (leftOuter cell) (overlap cell))
          (rightOuter cell))
        (C3.multiply F (overlap cell) (C3.one F))
    withRight =
      multiplyMonotoneNonnegative M
        leftTimesOverlapNN
        (rightOuterNonnegative cell)
        (overlapNonnegative cell)
        (oneNonnegative O)
        leftTimesOverlapBelow
        (rightOuterContraction cell)

    withRightMeaning :
      C3.multiply F (overlap cell) (C3.one F) ≡ overlap cell
    withRightMeaning = multiplyOneRight (overlap cell)
  in
  Ordered.leqTransitive O
    (pairProductFactorizationBound cell)
    (subst
      (λ target →
        Ordered._≤_ O
          (C3.multiply F
            (C3.multiply F (leftOuter cell) (overlap cell))
            (rightOuter cell))
          target)
      withRightMeaning
      withRight)

record PhysicalSixThreeGramCell
    {r : Level}
    {F : C3.RealField r}
    (O : Ordered.OrderedRealExtension F)
    (M : NonnegativeMultiplicativeOrder O)
    (R : Embed.OrderedRationalEmbedding O)
    (gap : Nat) : Set r where
  field
    factorized : PhysicalFactorizedGramCell O M gap
    overlapSixThree :
      Ordered._≤_ O
        (overlap factorized)
        (Embed.embed R (SixThree.twoBranchSquaredGap gap))

open PhysicalSixThreeGramCell public

physicalPairProductBelowSixThree :
  ∀ {r} {F : C3.RealField r}
    {O : Ordered.OrderedRealExtension F}
    {M : NonnegativeMultiplicativeOrder O}
    {R : Embed.OrderedRationalEmbedding O}
    {gap}
    (cell : PhysicalSixThreeGramCell O M R gap) →
  Ordered._≤_ O
    (pairProduct (factorized cell))
    (Embed.embed R (SixThree.twoBranchSquaredGap gap))
physicalPairProductBelowSixThree {O = O} cell =
  Ordered.leqTransitive O
    (physicalOuterContractionsRemove (factorized cell))
    (overlapSixThree cell)

round65SameCarrierPhysicalGramFactorizationConstructed : Bool
round65SameCarrierPhysicalGramFactorizationConstructed = true

round65SameCarrierSixThreeConsumerConstructed : Bool
round65SameCarrierSixThreeConsumerConstructed = true

round65SameCarrierPhysicalGramFactorizationConstructedIsTrue :
  round65SameCarrierPhysicalGramFactorizationConstructed ≡ true
round65SameCarrierPhysicalGramFactorizationConstructedIsTrue = refl

round65SameCarrierSixThreeConsumerConstructedIsTrue :
  round65SameCarrierSixThreeConsumerConstructed ≡ true
round65SameCarrierSixThreeConsumerConstructedIsTrue = refl
