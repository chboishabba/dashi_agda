{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonBivariateMarkedJetExact where

------------------------------------------------------------------------
-- Concrete two-source rational jet for the literal Wilson marked expansion.
--
-- Only the two-source germ through order st is required by W1/W3:
--
--   a + b s + c t + d s t.
--
-- The mixed coefficient d is extracted by the exact four-point finite
-- difference on this polynomial jet.  This is NOT a claim that a general
-- analytic function is determined by four values.  The physical/source theorem
-- must identify the actual Wilson-Gibbs marked partition/log-partition germ
-- with the jet supplied here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterDifferentiationExact as Diff

record TwoSourceJet : Set where
  constructor jet
  field
    baseCoefficient : ℚ
    leftCoefficient : ℚ
    rightCoefficient : ℚ
    mixedCoefficient : ℚ

open TwoSourceJet public

evaluateJet : TwoSourceJet → ℚ → ℚ → ℚ
evaluateJet j left right =
  baseCoefficient j
  + leftCoefficient j * left
  + rightCoefficient j * right
  + mixedCoefficient j * (left * right)



zeroJet : TwoSourceJet
zeroJet = jet 0ℚ 0ℚ 0ℚ 0ℚ

oneJet : TwoSourceJet
oneJet = jet 1ℚ 0ℚ 0ℚ 0ℚ

addJet : TwoSourceJet → TwoSourceJet → TwoSourceJet
addJet (jet a b c d) (jet e f g h) =
  jet (a + e) (b + f) (c + g) (d + h)

multiplyJet : TwoSourceJet → TwoSourceJet → TwoSourceJet
multiplyJet (jet a b c d) (jet e f g h) =
  jet
    (a * e)
    (a * f + b * e)
    (a * g + c * e)
    (a * h + b * g + c * f + d * e)

scaleJet : ℚ → TwoSourceJet → TwoSourceJet
scaleJet scalar (jet a b c d) =
  jet (scalar * a) (scalar * b) (scalar * c) (scalar * d)

multiplyJetMixedCoefficientExact :
  ∀ left right →
  mixedCoefficient (multiplyJet left right)
  ≡
  baseCoefficient left * mixedCoefficient right
  + leftCoefficient left * rightCoefficient right
  + rightCoefficient left * leftCoefficient right
  + mixedCoefficient left * baseCoefficient right
multiplyJetMixedCoefficientExact (jet a b c d) (jet e f g h) = refl

evaluateAddJet :
  ∀ left right sourceLeft sourceRight →
  evaluateJet (addJet left right) sourceLeft sourceRight
  ≡
  evaluateJet left sourceLeft sourceRight
  + evaluateJet right sourceLeft sourceRight
evaluateAddJet (jet a b c d) (jet e f g h) sourceLeft sourceRight =
  ℚRing.solve-∀ a b c d e f g h sourceLeft sourceRight

-- Product equality is understood in the square-zero two-source jet algebra:
-- terms of degree s² or t² are discarded.  At the level of the mixed source
-- coefficient this is exactly the ordinary product rule.
mixedCoefficientProductRule :
  ∀ left right →
  mixedCoefficient (multiplyJet left right)
  ≡
  baseCoefficient left * mixedCoefficient right
  + leftCoefficient left * rightCoefficient right
  + rightCoefficient left * leftCoefficient right
  + mixedCoefficient left * baseCoefficient right
mixedCoefficientProductRule = multiplyJetMixedCoefficientExact

productJets : List TwoSourceJet → TwoSourceJet
productJets [] = oneJet
productJets (value ∷ values) =
  multiplyJet value (productJets values)

mapJets :
  ∀ {A : Set} →
  (A → TwoSourceJet) →
  List A →
  List TwoSourceJet
mapJets f [] = []
mapJets f (item ∷ items) = f item ∷ mapJets f items

clusterJetFromPolymers :
  ∀ {Polymer : Set} →
  ℚ →
  List Polymer →
  (Polymer → TwoSourceJet) →
  TwoSourceJet
clusterJetFromPolymers coefficient polymers polymerJet =
  scaleJet coefficient (productJets (mapJets polymerJet polymers))




record PolymerJetSupport {Polymer : Set}
    (polymerJet : Polymer → TwoSourceJet) : Set₁ where
  field
    polymerTouchesLeft polymerTouchesRight : Polymer → Bool

    missingLeftKillsPolymerLeft :
      ∀ polymer →
      polymerTouchesLeft polymer ≡ false →
      leftCoefficient (polymerJet polymer) ≡ 0ℚ

    missingLeftKillsPolymerMixed :
      ∀ polymer →
      polymerTouchesLeft polymer ≡ false →
      mixedCoefficient (polymerJet polymer) ≡ 0ℚ

    missingRightKillsPolymerRight :
      ∀ polymer →
      polymerTouchesRight polymer ≡ false →
      rightCoefficient (polymerJet polymer) ≡ 0ℚ

    missingRightKillsPolymerMixed :
      ∀ polymer →
      polymerTouchesRight polymer ≡ false →
      mixedCoefficient (polymerJet polymer) ≡ 0ℚ

open PolymerJetSupport public

anyTouch : ∀ {Polymer : Set} → (Polymer → Bool) → List Polymer → Bool
anyTouch touches [] = false
anyTouch touches (polymer ∷ polymers) with touches polymer
... | true = true
... | false = anyTouch touches polymers

productJetsMissingLeftCoefficientsZero :
  ∀ {Polymer}
    (polymerJet : Polymer → TwoSourceJet)
    (support : PolymerJetSupport polymerJet)
    (polymers : List Polymer) →
  anyTouch (polymerTouchesLeft support) polymers ≡ false →
  leftCoefficient (productJets (mapJets polymerJet polymers)) ≡ 0ℚ
  ×
  mixedCoefficient (productJets (mapJets polymerJet polymers)) ≡ 0ℚ
productJetsMissingLeftCoefficientsZero polymerJet support [] missing =
  refl , refl
productJetsMissingLeftCoefficientsZero
    polymerJet support (polymer ∷ polymers) missing
  with polymerTouchesLeft support polymer
... | true with missing
...   | ()
... | false
  with productJetsMissingLeftCoefficientsZero
    polymerJet support polymers missing
... | restLeftZero , restMixedZero
  rewrite missingLeftKillsPolymerLeft support polymer refl
        | missingLeftKillsPolymerMixed support polymer refl
        | restLeftZero
        | restMixedZero =
  ℚRing.solve-∀
    (baseCoefficient (polymerJet polymer))
    (rightCoefficient (polymerJet polymer))
    (baseCoefficient (productJets (mapJets polymerJet polymers)))
    (rightCoefficient (productJets (mapJets polymerJet polymers)))
  ,
  ℚRing.solve-∀
    (baseCoefficient (polymerJet polymer))
    (rightCoefficient (polymerJet polymer))
    (baseCoefficient (productJets (mapJets polymerJet polymers)))
    (rightCoefficient (productJets (mapJets polymerJet polymers)))

productJetsMissingRightCoefficientsZero :
  ∀ {Polymer}
    (polymerJet : Polymer → TwoSourceJet)
    (support : PolymerJetSupport polymerJet)
    (polymers : List Polymer) →
  anyTouch (polymerTouchesRight support) polymers ≡ false →
  rightCoefficient (productJets (mapJets polymerJet polymers)) ≡ 0ℚ
  ×
  mixedCoefficient (productJets (mapJets polymerJet polymers)) ≡ 0ℚ
productJetsMissingRightCoefficientsZero polymerJet support [] missing =
  refl , refl
productJetsMissingRightCoefficientsZero
    polymerJet support (polymer ∷ polymers) missing
  with polymerTouchesRight support polymer
... | true with missing
...   | ()
... | false
  with productJetsMissingRightCoefficientsZero
    polymerJet support polymers missing
... | restRightZero , restMixedZero
  rewrite missingRightKillsPolymerRight support polymer refl
        | missingRightKillsPolymerMixed support polymer refl
        | restRightZero
        | restMixedZero =
  ℚRing.solve-∀
    (baseCoefficient (polymerJet polymer))
    (leftCoefficient (polymerJet polymer))
    (baseCoefficient (productJets (mapJets polymerJet polymers)))
    (leftCoefficient (productJets (mapJets polymerJet polymers)))
  ,
  ℚRing.solve-∀
    (baseCoefficient (polymerJet polymer))
    (leftCoefficient (polymerJet polymer))
    (baseCoefficient (productJets (mapJets polymerJet polymers)))
    (leftCoefficient (productJets (mapJets polymerJet polymers)))

scaleJetLeftZero :
  ∀ scalar j →
  leftCoefficient j ≡ 0ℚ →
  leftCoefficient (scaleJet scalar j) ≡ 0ℚ
scaleJetLeftZero scalar (jet a b c d) leftZero
  rewrite leftZero =
  ℚRing.solve-∀ scalar

scaleJetRightZero :
  ∀ scalar j →
  rightCoefficient j ≡ 0ℚ →
  rightCoefficient (scaleJet scalar j) ≡ 0ℚ
scaleJetRightZero scalar (jet a b c d) rightZero
  rewrite rightZero =
  ℚRing.solve-∀ scalar

scaleJetMixedZero :
  ∀ scalar j →
  mixedCoefficient j ≡ 0ℚ →
  mixedCoefficient (scaleJet scalar j) ≡ 0ℚ
scaleJetMixedZero scalar (jet a b c d) mixedZero
  rewrite mixedZero =
  ℚRing.solve-∀ scalar

clusterJetSupportFromPolymerSupport :
  ∀ {Polymer Cluster}
    (clusterPolymers : Cluster → List Polymer)
    (clusterCoefficient : Cluster → ℚ)
    (polymerJet : Polymer → TwoSourceJet)
    (support : PolymerJetSupport polymerJet) →
  ClusterJetSupport
    (λ cluster →
      clusterJetFromPolymers
        (clusterCoefficient cluster)
        (clusterPolymers cluster)
        polymerJet)
clusterJetSupportFromPolymerSupport
    clusterPolymers clusterCoefficient polymerJet support = record
  { ClusterJetSupport.touchesLeft =
      λ cluster →
        anyTouch (polymerTouchesLeft support) (clusterPolymers cluster)
  ; ClusterJetSupport.touchesRight =
      λ cluster →
        anyTouch (polymerTouchesRight support) (clusterPolymers cluster)
  ; ClusterJetSupport.missingLeftKillsLeftCoefficient =
      λ cluster missing →
        let zeros =
              productJetsMissingLeftCoefficientsZero
                polymerJet support (clusterPolymers cluster) missing
        in
        scaleJetLeftZero
          (clusterCoefficient cluster)
          (productJets (mapJets polymerJet (clusterPolymers cluster)))
          (proj₁ zeros)
  ; ClusterJetSupport.missingLeftKillsMixedCoefficient =
      λ cluster missing →
        let zeros =
              productJetsMissingLeftCoefficientsZero
                polymerJet support (clusterPolymers cluster) missing
        in
        scaleJetMixedZero
          (clusterCoefficient cluster)
          (productJets (mapJets polymerJet (clusterPolymers cluster)))
          (proj₂ zeros)
  ; ClusterJetSupport.missingRightKillsRightCoefficient =
      λ cluster missing →
        let zeros =
              productJetsMissingRightCoefficientsZero
                polymerJet support (clusterPolymers cluster) missing
        in
        scaleJetRightZero
          (clusterCoefficient cluster)
          (productJets (mapJets polymerJet (clusterPolymers cluster)))
          (proj₁ zeros)
  ; ClusterJetSupport.missingRightKillsMixedCoefficient =
      λ cluster missing →
        let zeros =
              productJetsMissingRightCoefficientsZero
                polymerJet support (clusterPolymers cluster) missing
        in
        scaleJetMixedZero
          (clusterCoefficient cluster)
          (productJets (mapJets polymerJet (clusterPolymers cluster)))
          (proj₂ zeros)
  }


mixedFiniteDifference :
  (ℚ → ℚ → ℚ) → ℚ
mixedFiniteDifference f =
  f 1ℚ 1ℚ - f 1ℚ 0ℚ - f 0ℚ 1ℚ + f 0ℚ 0ℚ

mixedFiniteDifferenceJet :
  ∀ j →
  mixedFiniteDifference (evaluateJet j)
  ≡ mixedCoefficient j
mixedFiniteDifferenceJet (jet a b c d) =
  ℚRing.solve-∀ a b c d

mixedFiniteDifferenceCongruent :
  ∀ left right →
  (∀ sourceLeft sourceRight →
    left sourceLeft sourceRight ≡ right sourceLeft sourceRight) →
  mixedFiniteDifference left ≡ mixedFiniteDifference right
mixedFiniteDifferenceCongruent left right pointwise
  rewrite pointwise 1ℚ 1ℚ
        | pointwise 1ℚ 0ℚ
        | pointwise 0ℚ 1ℚ
        | pointwise 0ℚ 0ℚ = refl

mixedFiniteDifferenceAdd :
  ∀ f g →
  mixedFiniteDifference (λ left right → f left right + g left right)
  ≡ mixedFiniteDifference f + mixedFiniteDifference g
mixedFiniteDifferenceAdd f g =
  ℚRing.solve-∀
    (f 1ℚ 1ℚ) (f 1ℚ 0ℚ) (f 0ℚ 1ℚ) (f 0ℚ 0ℚ)
    (g 1ℚ 1ℚ) (g 1ℚ 0ℚ) (g 0ℚ 1ℚ) (g 0ℚ 0ℚ)

mixedFiniteDifferenceFiniteSum :
  ∀ {Term : Set}
    (terms : List Term)
    (termValue : Term → ℚ → ℚ → ℚ) →
  mixedFiniteDifference
    (λ sourceLeft sourceRight →
      TwoMark.sumℚ
        (TwoMark.map
          (λ term → termValue term sourceLeft sourceRight)
          terms))
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ term → mixedFiniteDifference (termValue term))
      terms)
mixedFiniteDifferenceFiniteSum [] termValue =
  ℚRing.solve-∀
mixedFiniteDifferenceFiniteSum (term ∷ terms) termValue =
  trans
    (mixedFiniteDifferenceAdd
      (termValue term)
      (λ sourceLeft sourceRight →
        TwoMark.sumℚ
          (TwoMark.map
            (λ item → termValue item sourceLeft sourceRight)
            terms)))
    (cong
      (λ rest → mixedFiniteDifference (termValue term) + rest)
      (mixedFiniteDifferenceFiniteSum terms termValue))

rationalJetDerivativeCalculus :
  Diff.MixedSourceDerivativeCalculus ℚ
rationalJetDerivativeCalculus = record
  { Diff.MixedSourceDerivativeCalculus.mixedDerivative =
      mixedFiniteDifference
  ; Diff.MixedSourceDerivativeCalculus.mixedDerivativeCongruent =
      mixedFiniteDifferenceCongruent
  ; Diff.MixedSourceDerivativeCalculus.mixedDerivativeFiniteSum =
      mixedFiniteDifferenceFiniteSum
  }

mixedFiniteDifferenceLeftIndependentZero :
  ∀ term →
  (∀ left₁ left₂ right → term left₁ right ≡ term left₂ right) →
  mixedFiniteDifference term ≡ 0ℚ
mixedFiniteDifferenceLeftIndependentZero term independent
  rewrite independent 1ℚ 0ℚ 1ℚ
        | independent 1ℚ 0ℚ 0ℚ =
  ℚRing.solve-∀ (term 0ℚ 1ℚ) (term 0ℚ 0ℚ)

mixedFiniteDifferenceRightIndependentZero :
  ∀ term →
  (∀ left right₁ right₂ → term left right₁ ≡ term left right₂) →
  mixedFiniteDifference term ≡ 0ℚ
mixedFiniteDifferenceRightIndependentZero term independent
  rewrite independent 1ℚ 1ℚ 0ℚ
        | independent 0ℚ 1ℚ 0ℚ =
  ℚRing.solve-∀ (term 1ℚ 0ℚ) (term 0ℚ 0ℚ)

rationalJetDerivativeVanishing :
  Diff.MixedSourceDerivativeVanishing rationalJetDerivativeCalculus
rationalJetDerivativeVanishing = record
  { Diff.MixedSourceDerivativeVanishing.leftIndependentDerivativeZero =
      mixedFiniteDifferenceLeftIndependentZero
  ; Diff.MixedSourceDerivativeVanishing.rightIndependentDerivativeZero =
      mixedFiniteDifferenceRightIndependentZero
  }

record ClusterJetSupport {Cluster : Set}
    (clusterJet : Cluster → TwoSourceJet) : Set₁ where
  field
    touchesLeft touchesRight : Cluster → Bool

    missingLeftKillsLeftCoefficient :
      ∀ cluster →
      touchesLeft cluster ≡ false →
      leftCoefficient (clusterJet cluster) ≡ 0ℚ

    missingLeftKillsMixedCoefficient :
      ∀ cluster →
      touchesLeft cluster ≡ false →
      mixedCoefficient (clusterJet cluster) ≡ 0ℚ

    missingRightKillsRightCoefficient :
      ∀ cluster →
      touchesRight cluster ≡ false →
      rightCoefficient (clusterJet cluster) ≡ 0ℚ

    missingRightKillsMixedCoefficient :
      ∀ cluster →
      touchesRight cluster ≡ false →
      mixedCoefficient (clusterJet cluster) ≡ 0ℚ

open ClusterJetSupport public

missingLeftJetIndependent :
  ∀ {Cluster}
    {clusterJet : Cluster → TwoSourceJet}
    (support : ClusterJetSupport clusterJet)
    cluster →
  touchesLeft support cluster ≡ false →
  ∀ left₁ left₂ right →
  evaluateJet (clusterJet cluster) left₁ right
  ≡
  evaluateJet (clusterJet cluster) left₂ right
missingLeftJetIndependent support cluster leftMissing left₁ left₂ right
  rewrite missingLeftKillsLeftCoefficient support cluster leftMissing
        | missingLeftKillsMixedCoefficient support cluster leftMissing =
  ℚRing.solve-∀
    (baseCoefficient (clusterJet cluster))
    (rightCoefficient (clusterJet cluster))
    left₁ left₂ right

missingRightJetIndependent :
  ∀ {Cluster}
    {clusterJet : Cluster → TwoSourceJet}
    (support : ClusterJetSupport clusterJet)
    cluster →
  touchesRight support cluster ≡ false →
  ∀ left right₁ right₂ →
  evaluateJet (clusterJet cluster) left right₁
  ≡
  evaluateJet (clusterJet cluster) left right₂
missingRightJetIndependent support cluster rightMissing left right₁ right₂
  rewrite missingRightKillsRightCoefficient support cluster rightMissing
        | missingRightKillsMixedCoefficient support cluster rightMissing =
  ℚRing.solve-∀
    (baseCoefficient (clusterJet cluster))
    (leftCoefficient (clusterJet cluster))
    left right₁ right₂

jetSupportLocality :
  ∀ {Cluster}
    {clusterJet : Cluster → TwoSourceJet} →
  ClusterJetSupport clusterJet →
  Diff.MarkedClusterSupportLocality
    (λ cluster → evaluateJet (clusterJet cluster))
jetSupportLocality support = record
  { Diff.MarkedClusterSupportLocality.touchesLeft =
      touchesLeft support
  ; Diff.MarkedClusterSupportLocality.touchesRight =
      touchesRight support
  ; Diff.MarkedClusterSupportLocality.missingLeftMakesTermIndependent =
      missingLeftJetIndependent support
  ; Diff.MarkedClusterSupportLocality.missingRightMakesTermIndependent =
      missingRightJetIndependent support
  }

jetClusterLogPartition :
  ∀ {Cluster} →
  List Cluster →
  (Cluster → TwoSourceJet) →
  ℚ → ℚ → ℚ
jetClusterLogPartition clusters clusterJet left right =
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster → evaluateJet (clusterJet cluster) left right)
      clusters)

supportIndexedJetExpansion :
  ∀ {Cluster}
    (clusters : List Cluster)
    (clusterJet : Cluster → TwoSourceJet)
    (support : ClusterJetSupport clusterJet) →
  Diff.SupportIndexedMarkedClusterExpansion
    ℚ Cluster rationalJetDerivativeCalculus
supportIndexedJetExpansion clusters clusterJet support = record
  { Diff.SupportIndexedMarkedClusterExpansion.clusters = clusters
  ; Diff.SupportIndexedMarkedClusterExpansion.logPartition =
      jetClusterLogPartition clusters clusterJet
  ; Diff.SupportIndexedMarkedClusterExpansion.clusterTerm =
      λ cluster → evaluateJet (clusterJet cluster)
  ; Diff.SupportIndexedMarkedClusterExpansion.logPartitionExpansionExact =
      λ sourceLeft sourceRight → refl
  ; Diff.SupportIndexedMarkedClusterExpansion.supportLocality =
      jetSupportLocality support
  }

mixedDerivativeOfJetClusterTerm :
  ∀ {Cluster}
    (clusterJet : Cluster → TwoSourceJet)
    cluster →
  Diff.mixedDerivative rationalJetDerivativeCalculus
    (λ left right → evaluateJet (clusterJet cluster) left right)
  ≡ mixedCoefficient (clusterJet cluster)
mixedDerivativeOfJetClusterTerm clusterJet cluster =
  mixedFiniteDifferenceJet (clusterJet cluster)

mixedDerivativeJetExpansionIsTwoSupportMixedCoefficientSum :
  ∀ {Cluster}
    (clusters : List Cluster)
    (clusterJet : Cluster → TwoSourceJet)
    (support : ClusterJetSupport clusterJet) →
  Diff.mixedDerivative rationalJetDerivativeCalculus
    (Diff.logPartition
      (supportIndexedJetExpansion clusters clusterJet support))
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster → mixedCoefficient (clusterJet cluster))
      (Diff.filterTwoSupport
        (touchesLeft support)
        (touchesRight support)
        clusters))
mixedDerivativeJetExpansionIsTwoSupportMixedCoefficientSum
    clusters clusterJet support =
  trans
    (Diff.mixedDerivativeSupportIndexedExpansionIsConnectingSum
      rationalJetDerivativeVanishing
      (supportIndexedJetExpansion clusters clusterJet support))
    (sumMixedJetCoefficients
      (Diff.filterTwoSupport
        (touchesLeft support)
        (touchesRight support)
        clusters))
  where
  sumMixedJetCoefficients :
    (items : List Cluster) →
    TwoMark.sumℚ
      (TwoMark.map
        (λ cluster →
          Diff.mixedDerivative rationalJetDerivativeCalculus
            (λ left right → evaluateJet (clusterJet cluster) left right))
        items)
    ≡
    TwoMark.sumℚ
      (TwoMark.map
        (λ cluster → mixedCoefficient (clusterJet cluster))
        items)
  sumMixedJetCoefficients [] = refl
  sumMixedJetCoefficients (cluster ∷ items)
    rewrite mixedFiniteDifferenceJet (clusterJet cluster)
          | sumMixedJetCoefficients items = refl
