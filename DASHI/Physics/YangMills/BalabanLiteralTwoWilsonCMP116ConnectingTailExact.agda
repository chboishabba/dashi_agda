{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonCMP116ConnectingTailExact where

------------------------------------------------------------------------
-- H1-A -> H1-B JOIN:
-- SOURCE-FIRST/KP MARKED EXPANSION + CMP116 POINTWISE CHARGE
--   -> TWO-MARK CONNECTING TAIL.
--
-- The existing marked-polymer compiler already proves
--
--   D_L D_R log Z
--     = sum_{clusters touching both supports} D_L D_R Phi_Y.
--
-- Hence neither the connected-response expansion nor finite triangle
-- inequality is a new physical theorem.  Given the existing CMP116 pointwise
-- cluster charge, the sole quantitative input here is the FINITE SUM of those
-- charges over the two-support family:
--
--   sum_{Y touches L,R} shellCharge(Y)
--     <= configured rooted tail(distance(L,R)).
--
-- Everything else is compiler algebra / same-object packaging.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (_∈_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedPolymerExpansionExact as Marked
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterDifferentiationExact as Diff
open import DASHI.Physics.YangMills.CompactLieProofLevel

finiteAbsTriangle :
  ∀ {A : Set}
    (items : List A)
    (value : A → ℚ) →
  ∣ TwoMark.sumℚ (TwoMark.map value items) ∣
  ≤
  TwoMark.sumℚ
    (TwoMark.map (λ item → ∣ value item ∣) items)
finiteAbsTriangle [] value = ℚP.≤-refl
finiteAbsTriangle (item ∷ items) value =
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      (value item)
      (TwoMark.sumℚ (TwoMark.map value items)))
    (ℚP.+-mono-≤
      ℚP.≤-refl
      (finiteAbsTriangle items value))

finiteSumMonotone :
  ∀ {A : Set}
    (items : List A)
    (lower upper : A → ℚ) →
  (∀ item → lower item ≤ upper item) →
  TwoMark.sumℚ (TwoMark.map lower items)
  ≤
  TwoMark.sumℚ (TwoMark.map upper items)
finiteSumMonotone [] lower upper pointwise = ℚP.≤-refl
finiteSumMonotone (item ∷ items) lower upper pointwise =
  ℚP.+-mono-≤
    (pointwise item)
    (finiteSumMonotone items lower upper pointwise)

connectingClusters :
  ∀ {Observable Source Polymer Cluster Volume}
    (family :
      Marked.TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume) →
  Nat → Observable → Observable → List Cluster
connectingClusters family cutoff left right =
  Diff.filterTwoSupport
    (Marked.touchesLeft family cutoff left right)
    (Marked.touchesRight family cutoff left right)
    (Marked.commonClusters family cutoff left right)

clusterDerivative :
  ∀ {Observable Source Polymer Cluster Volume}
    {family :
      Marked.TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume}
    (differentiable : Marked.DifferentiableTwoWilsonKP family) →
  Nat → Observable → Observable → Cluster → ℚ
clusterDerivative {family = family} differentiable cutoff left right cluster =
  Diff.mixedDerivative
    (Marked.derivativeCalculus differentiable cutoff left right)
    (Marked.markedClusterTerm family cutoff left right cluster)

record TwoWilsonCMP116ConnectingTailPayment
    {Observable Source Polymer Cluster Volume : Set}
    {family :
      Marked.TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume}
    (differentiable : Marked.DifferentiableTwoWilsonKP family)
    (charge : Marked.TwoWilsonCMP116ClusterCharge differentiable)
    : Set₁ where
  field
    supportSeparation : Observable → Observable → Nat
    clusterDiameter : Cluster → Nat

    contributingClusterConnectsBothSupports :
      ∀ cutoff left right cluster →
      cluster ∈ connectingClusters family cutoff left right → Set

    connectingClusterDiameterAtLeastSeparation :
      ∀ cutoff left right cluster →
      cluster ∈ connectingClusters family cutoff left right → Set

    connectingClusterRootedShellInjection :
      ∀ cutoff left right cluster →
      cluster ∈ connectingClusters family cutoff left right → Set

    chargeSumBelowRootedTail :
      ∀ cutoff left right →
      TwoMark.sumℚ
        (TwoMark.map
          (Marked.shellCharge charge cutoff left right)
          (connectingClusters family cutoff left right))
      ≤
      Tail.rootedShellTail (supportSeparation left right)

open TwoWilsonCMP116ConnectingTailPayment public

absoluteDerivativeSumBelowChargeSum :
  ∀ {Observable Source Polymer Cluster Volume family}
    {differentiable : Marked.DifferentiableTwoWilsonKP family}
    (charge : Marked.TwoWilsonCMP116ClusterCharge differentiable)
    cutoff left right →
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster →
        ∣ clusterDerivative differentiable cutoff left right cluster ∣)
      (connectingClusters family cutoff left right))
  ≤
  TwoMark.sumℚ
    (TwoMark.map
      (Marked.shellCharge charge cutoff left right)
      (connectingClusters family cutoff left right))
absoluteDerivativeSumBelowChargeSum
    {family = family} {differentiable = differentiable}
    charge cutoff left right =
  finiteSumMonotone
    (connectingClusters family cutoff left right)
    (λ cluster →
      ∣ clusterDerivative differentiable cutoff left right cluster ∣)
    (Marked.shellCharge charge cutoff left right)
    (Marked.pointwiseDifferentiatedClusterBelowCharge
      charge cutoff left right)

asTwoMarkedConnectedClusterTail :
  ∀ {Observable Source Polymer Cluster Volume family}
    {differentiable : Marked.DifferentiableTwoWilsonKP family}
    {charge : Marked.TwoWilsonCMP116ClusterCharge differentiable} →
  TwoWilsonCMP116ConnectingTailPayment differentiable charge →
  TwoMark.TwoMarkedConnectedClusterTail Nat Observable Cluster
asTwoMarkedConnectedClusterTail
    {family = family} {differentiable = differentiable} {charge = charge}
    payment = record
  { TwoMark.TwoMarkedConnectedClusterTail.supportSeparation =
      supportSeparation payment
  ; TwoMark.TwoMarkedConnectedClusterTail.clusterDiameter =
      clusterDiameter payment
  ; TwoMark.TwoMarkedConnectedClusterTail.contributingClusters =
      connectingClusters family
  ; TwoMark.TwoMarkedConnectedClusterTail.clusterWeight =
      clusterDerivative differentiable
  ; TwoMark.TwoMarkedConnectedClusterTail.connectedResponse =
      λ cutoff left right →
        Diff.mixedDerivative
          (Marked.derivativeCalculus differentiable cutoff left right)
          (Marked.markedLogPartition family cutoff left right)
  ; TwoMark.TwoMarkedConnectedClusterTail.absoluteValue = ∣_∣
  ; TwoMark.TwoMarkedConnectedClusterTail.connectedResponseExpansionExact =
      Marked.twoWilsonMixedDerivativeIsTwoSupportClusterSum differentiable
  ; TwoMark.TwoMarkedConnectedClusterTail.finiteTriangleForConnectingSum =
      λ cutoff left right →
        finiteAbsTriangle
          (connectingClusters family cutoff left right)
          (clusterDerivative differentiable cutoff left right)
  ; TwoMark.TwoMarkedConnectedClusterTail.contributingClusterConnectsBothSupports =
      contributingClusterConnectsBothSupports payment
  ; TwoMark.TwoMarkedConnectedClusterTail.connectingClusterDiameterAtLeastSeparation =
      connectingClusterDiameterAtLeastSeparation payment
  ; TwoMark.TwoMarkedConnectedClusterTail.connectingClusterRootedShellInjection =
      connectingClusterRootedShellInjection payment
  ; TwoMark.TwoMarkedConnectedClusterTail.absoluteConnectingWeightSumBelowRootedTail =
      λ cutoff left right →
        ℚP.≤-trans
          (absoluteDerivativeSumBelowChargeSum charge cutoff left right)
          (chargeSumBelowRootedTail payment cutoff left right)
  }

twoWilsonMixedLogBelowConfiguredRootedTail :
  ∀ {Observable Source Polymer Cluster Volume family}
    {differentiable : Marked.DifferentiableTwoWilsonKP family}
    {charge : Marked.TwoWilsonCMP116ClusterCharge differentiable}
    (payment : TwoWilsonCMP116ConnectingTailPayment differentiable charge)
    cutoff left right →
  ∣
    Diff.mixedDerivative
      (Marked.derivativeCalculus differentiable cutoff left right)
      (Marked.markedLogPartition family cutoff left right)
  ∣
  ≤
  Tail.rootedShellTail (supportSeparation payment left right)
twoWilsonMixedLogBelowConfiguredRootedTail payment =
  TwoMark.connectedResponseHasConfiguredSeparationTail
    (asTwoMarkedConnectedClusterTail payment)


------------------------------------------------------------------------
-- Strong physical-shell form.
--
-- This is the preferred H1 quantitative payment.  It lands on the actual
-- TraversalShellData used by R274/R491, rather than first weakening to the
-- universal dyadic tail.
------------------------------------------------------------------------

record TwoWilsonCMP116PhysicalShellPayment
    {Observable Source Polymer Cluster Volume Scale Root : Set}
    {family :
      Marked.TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume}
    (differentiable : Marked.DifferentiableTwoWilsonKP family)
    (charge : Marked.TwoWilsonCMP116ClusterCharge differentiable)
    : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root

    scaleOfCutoff : Nat → Scale
    connectingRoot : Nat → Observable → Observable → Root
    supportSeparation : Observable → Observable → Nat

    clusterDiameter : Cluster → Nat

    contributingClusterConnectsBothSupports :
      ∀ cutoff left right cluster →
      cluster ∈ connectingClusters family cutoff left right → Set

    connectingClusterDiameterAtLeastSeparation :
      ∀ cutoff left right cluster →
      cluster ∈ connectingClusters family cutoff left right → Set

    connectingClusterRootedShellInjection :
      ∀ cutoff left right cluster →
      cluster ∈ connectingClusters family cutoff left right → Set

    chargeSumBelowPhysicalRootedShell :
      ∀ cutoff left right →
      TwoMark.sumℚ
        (TwoMark.map
          (Marked.shellCharge charge cutoff left right)
          (connectingClusters family cutoff left right))
      ≤
      Shell.rootedShell shellData
        (scaleOfCutoff cutoff)
        (Marked.volumeOfCutoff family cutoff)
        (connectingRoot cutoff left right)
        (supportSeparation left right)

open TwoWilsonCMP116PhysicalShellPayment public

twoWilsonMixedLogBelowPhysicalRootedShell :
  ∀ {Observable Source Polymer Cluster Volume Scale Root family}
    {differentiable : Marked.DifferentiableTwoWilsonKP family}
    {charge : Marked.TwoWilsonCMP116ClusterCharge differentiable}
    (payment :
      TwoWilsonCMP116PhysicalShellPayment
        {Scale = Scale} {Root = Root}
        differentiable charge)
    cutoff left right →
  ∣
    Diff.mixedDerivative
      (Marked.derivativeCalculus differentiable cutoff left right)
      (Marked.markedLogPartition family cutoff left right)
  ∣
  ≤
  Shell.rootedShell (shellData payment)
    (scaleOfCutoff payment cutoff)
    (Marked.volumeOfCutoff family cutoff)
    (connectingRoot payment cutoff left right)
    (TwoWilsonCMP116PhysicalShellPayment.supportSeparation payment left right)
twoWilsonMixedLogBelowPhysicalRootedShell
    {family = family} {differentiable = differentiable} {charge = charge}
    payment cutoff left right =
  ℚP.≤-trans
    (finiteAbsTriangle
      (connectingClusters family cutoff left right)
      (clusterDerivative differentiable cutoff left right))
    (ℚP.≤-trans
      (absoluteDerivativeSumBelowChargeSum charge cutoff left right)
      (chargeSumBelowPhysicalRootedShell payment cutoff left right))

asConfiguredTailPayment :
  ∀ {Observable Source Polymer Cluster Volume Scale Root family}
    {differentiable : Marked.DifferentiableTwoWilsonKP family}
    {charge : Marked.TwoWilsonCMP116ClusterCharge differentiable} →
  TwoWilsonCMP116PhysicalShellPayment
    {Scale = Scale} {Root = Root}
    differentiable charge →
  TwoWilsonCMP116ConnectingTailPayment differentiable charge
asConfiguredTailPayment
    {family = family} {differentiable = differentiable} {charge = charge}
    payment = record
  { TwoWilsonCMP116ConnectingTailPayment.supportSeparation =
      TwoWilsonCMP116PhysicalShellPayment.supportSeparation payment
  ; TwoWilsonCMP116ConnectingTailPayment.clusterDiameter =
      TwoWilsonCMP116PhysicalShellPayment.clusterDiameter payment
  ; TwoWilsonCMP116ConnectingTailPayment.contributingClusterConnectsBothSupports =
      TwoWilsonCMP116PhysicalShellPayment.contributingClusterConnectsBothSupports payment
  ; TwoWilsonCMP116ConnectingTailPayment.connectingClusterDiameterAtLeastSeparation =
      TwoWilsonCMP116PhysicalShellPayment.connectingClusterDiameterAtLeastSeparation payment
  ; TwoWilsonCMP116ConnectingTailPayment.connectingClusterRootedShellInjection =
      TwoWilsonCMP116PhysicalShellPayment.connectingClusterRootedShellInjection payment
  ; TwoWilsonCMP116ConnectingTailPayment.chargeSumBelowRootedTail =
      λ cutoff left right →
        ℚP.≤-trans
          (chargeSumBelowPhysicalRootedShell payment cutoff left right)
          (Shell.rootedShellBelowQuarterHalfPower
            (shellData payment)
            (scaleOfCutoff payment cutoff)
            (Marked.volumeOfCutoff family cutoff)
            (connectingRoot payment cutoff left right)
            (TwoWilsonCMP116PhysicalShellPayment.supportSeparation payment left right))
  }

twoWilsonConnectingTailCompilerLevel : ProofLevel
twoWilsonConnectingTailCompilerLevel = machineChecked

twoWilsonPointwiseCMP116ChargeLevel : ProofLevel
twoWilsonPointwiseCMP116ChargeLevel = conditional

twoWilsonChargeSumBelowRootedTailLevel : ProofLevel
twoWilsonChargeSumBelowRootedTailLevel = conditional
