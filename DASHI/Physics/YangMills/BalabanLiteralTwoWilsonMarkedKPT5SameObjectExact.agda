{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedKPT5SameObjectExact where

------------------------------------------------------------------------
-- MARKED KP LOG-PARTITION = LITERAL FINITE-T5 GENERATING FUNCTION, AT THE
-- MIXED-SECOND-DERIVATIVE STRENGTH ACTUALLY NEEDED BY H1.
--
-- Generic normalized source calculus already proves
--
--   D_L D_R log Z_T5 = Cov_T5(L,R).
--
-- The marked-polymer route already proves
--
--   D_L D_R log Z_KP = sum_{Y touches L,R} D_L D_R Phi_Y.
--
-- Therefore the remaining response same-object payment is only that these two
-- mixed derivatives are evaluations of the SAME literal finite generating
-- functional.  Once supplied, the signed Wilson covariance identity consumed
-- by R494 is compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (_∈_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedPolymerExpansionExact as Marked
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterDifferentiationExact as Diff
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonCMP116ConnectingTailExact as Tail
open import DASHI.Physics.YangMills.CompactLieProofLevel

record MarkedKPT5MixedLogSameObject
    {Measure Observable Source Polymer Cluster Volume : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    {family :
      Marked.TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume}
    (differentiable : Marked.DifferentiableTwoWilsonKP family)
    : Set₁ where
  field
    markedMixedDerivativeIsLiteralT5MixedLog :
      ∀ cutoff left right →
      Diff.mixedDerivative
        (Marked.derivativeCalculus differentiable cutoff left right)
        (Marked.markedLogPartition family cutoff left right)
      ≡
      Cumulant.literalMixedSecondLogDerivative
        (R318.meaning base)
        (Cumulant.sourceDirectionOf (R318.meaning base) left)
        (Cumulant.sourceDirectionOf (R318.meaning base) right)
        cutoff

open MarkedKPT5MixedLogSameObject public

markedKPMixedDerivativeIsFiniteT5ConnectedCovariance :
  ∀ {Measure Observable Source Polymer Cluster Volume dataSet extension}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {family :
      Marked.TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume}
    {differentiable : Marked.DifferentiableTwoWilsonKP family} →
  MarkedKPT5MixedLogSameObject base differentiable →
  ∀ cutoff left right →
  Diff.mixedDerivative
    (Marked.derivativeCalculus differentiable cutoff left right)
    (Marked.markedLogPartition family cutoff left right)
  ≡
  R278.connectedCovarianceValue extension
    (Gram.measureSequence dataSet cutoff)
    left right
markedKPMixedDerivativeIsFiniteT5ConnectedCovariance
    {dataSet = dataSet} {extension = extension} {base = base}
    sameObject cutoff left right =
  trans
    (markedMixedDerivativeIsLiteralT5MixedLog
      sameObject cutoff left right)
    (trans
      (cong
        (λ response → response cutoff)
        (Cumulant.literalMixedLogDerivativeIsConnectedCovariance
          (R318.meaning base) left right))
      (R295.sourceConnectedCovarianceIsExactFiniteT5
        dataSet extension left right cutoff))

asSignedCovarianceIdentification :
  ∀ {Measure Observable Source Polymer Cluster Volume Scale Root
      dataSet extension base family differentiable charge payment}
    (sameObject :
      MarkedKPT5MixedLogSameObject
        {Measure = Measure} {Observable = Observable}
        {Source = Source} {Polymer = Polymer} {Cluster = Cluster}
        {Volume = Volume}
        {dataSet = dataSet} {extension = extension}
        base {family = family} differentiable) →
  Tail.TwoWilsonSignedCovarianceIdentification
    {Scale = Scale} {Root = Root}
    {family = family}
    {differentiable = differentiable}
    {charge = charge}
    payment
asSignedCovarianceIdentification
    {dataSet = dataSet} {extension = extension}
    {family = family} {differentiable = differentiable}
    {payment = payment} sameObject = record
  { Tail.TwoWilsonSignedCovarianceIdentification.connectedCovariance =
      λ cutoff left right →
        R278.connectedCovarianceValue extension
          (Gram.measureSequence dataSet cutoff)
          left right
  ; Tail.TwoWilsonSignedCovarianceIdentification.mixedDerivativeIsConnectedCovariance =
      markedKPMixedDerivativeIsFiniteT5ConnectedCovariance sameObject
  ; Tail.TwoWilsonSignedCovarianceIdentification.connectingClusterMeetsBothWilsonSupports =
      λ cutoff left right →
        ∀ cluster
          (membership : cluster ∈ Tail.connectingClusters family cutoff left right) →
        Tail.contributingClusterConnectsBothSupports
          payment cutoff left right cluster membership
  }

markedKPT5MixedLogSameObjectCompilerLevel : ProofLevel
markedKPT5MixedLogSameObjectCompilerLevel = machineChecked

literalMarkedKPGeneratingFunctionalSameObjectLevel : ProofLevel
literalMarkedKPGeneratingFunctionalSameObjectLevel = conditional

finiteT5ConnectedCovarianceAlgebraLevel : ProofLevel
finiteT5ConnectedCovarianceAlgebraLevel =
  R295.round295ExactT5SourceAlgebraCompilerLevel
