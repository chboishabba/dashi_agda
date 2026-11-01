module DASHI.Physics.Closure.NSTriadKNResidueScaleOperatorGapExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Construct an inhabited, postulate-free residue/operator/gap ladder on the
-- canonical unit-shell residue-energy carrier.  This closes the algebra that
-- was previously represented only by Set-valued fields:
--
--   weak/error energy  = E
--   strong/base energy = 2E
--   compatibility scale squared = 2
--   base constant  = 2
--   error constant = 1
--   strict margin  = 1.
--
-- Consequently
--
--   2 * strong = 2 * base,
--   2 * error  = 1 * strong,
--   2 * gap    = 1 * strong.
--
-- The operator witness is the repository's canonical weighted-Schur unit-shell
-- operator.  The remaining physical issue is whether that canonical finite
-- operator is literally the PDE pair-incidence operator; this file does not
-- change the separate physical-kernel identification gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; ≤-reflexive
        ; *-identityˡ; +-identityʳ; m≤m+n; m+n∸m≡n )
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as Scale
import DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem as Operator
import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap

one : Nat
one = suc zero

two : Nat
two = suc one

oneLessThanTwo : one < two
oneLessThanTwo = s≤s (s≤s z≤n)

two≤two : two ≤ two
two≤two = s≤s (s≤s z≤n)

twoTimes : (n : Nat) → two * n ≡ n + n
twoTimes n = cong (λ value → n + value) (+-identityʳ n)

------------------------------------------------------------------------
-- Canonical carrier and norm/error/base forms.
------------------------------------------------------------------------

residueNormModel : ResidueNorm.ResidueNormModel
residueNormModel = ResidueNorm.nWeightedResidueNormModel

Carrier : Set
Carrier = ResidueNorm.ResidueEnergyCarrier one

energy : Carrier → Nat
energy = ResidueNorm.residueEnergy

weakNormSquared : Carrier → Nat
weakNormSquared = energy

strongNormSquared : Carrier → Nat
strongNormSquared x = energy x + energy x

qError : Carrier → Nat
qError = energy

qBase : Carrier → Nat
qBase = strongNormSquared

qGap : Carrier → Nat
qGap = energy

compatibilityScale : Scale.CompatibilityScale one
compatibilityScale = Scale.mkCompatibilityScale two two≤two

qGapDecomposition :
  (x : Carrier) →
  qGap x ≡ qBase x ∸ qError x
qGapDecomposition x =
  sym (m+n∸m≡n (energy x) (energy x))

------------------------------------------------------------------------
-- Canonical weighted-Schur operator identification.
------------------------------------------------------------------------

stage3OperatorWitness :
  Operator.Stage3PairIncidenceOperatorWitness residueNormModel one
stage3OperatorWitness =
  Operator.actualUnitShellPairIncidenceOperatorWitness residueNormModel

operatorWitness :
  Operator.PairIncidenceOperatorWitness residueNormModel one
operatorWitness =
  Operator.stage3ToPairIncidenceOperatorWitness stage3OperatorWitness

actualQuadraticForm : Carrier → Nat
actualQuadraticForm =
  Operator.PairIncidenceOperatorWitness.absQuadraticForm operatorWitness

actualQuadraticFormIsError :
  (x : Carrier) → actualQuadraticForm x ≡ qError x
actualQuadraticFormIsError x = refl

operatorWeakCNTarget : Set
operatorWeakCNTarget =
  (x : Carrier) → one * qError x ≤ one * weakNormSquared x

operatorWeakCNProof : operatorWeakCNTarget
operatorWeakCNProof x = ≤-refl

weakStrongN1Target : Set
weakStrongN1Target =
  (x : Carrier) → one * weakNormSquared x ≤ strongNormSquared x

weakStrongN1Proof : weakStrongN1Target
weakStrongN1Proof x =
  ≤-trans
    (≤-reflexive (*-identityˡ (energy x)))
    (m≤m+n (energy x) (energy x))

operatorStrongErrorN2Target : Set
operatorStrongErrorN2Target =
  QGap.operatorStrongErrorN2Target
    one strongNormSquared qError one

operatorStrongErrorN2Proof : operatorStrongErrorN2Target
operatorStrongErrorN2Proof =
  QGap.operatorCNWeakStrongComposeN2
    one
    weakNormSquared
    strongNormSquared
    qError
    one
    operatorWeakCNProof
    weakStrongN1Proof

weakStrongScaling : QGap.WeakStrongNormScaling Carrier
weakStrongScaling =
  QGap.mkWeakStrongNormScaling
    weakNormSquared
    strongNormSquared
    operatorWeakCNTarget
    weakStrongN1Target
    operatorStrongErrorN2Target
    true

------------------------------------------------------------------------
-- Exact strict base-gap-minus-error ladder.
------------------------------------------------------------------------

gapQuadraticForms : QGap.GapQuadraticFormsTarget
gapQuadraticForms =
  QGap.mkGapQuadraticFormsTarget
    ResidueNorm.ResidueEnergyCarrier
    one
    compatibilityScale
    qBase
    qError
    qGap
    qGapDecomposition

baseGapN2Proof :
  QGap.baseGapN2Target gapQuadraticForms strongNormSquared two
baseGapN2Proof x = ≤-refl

baseGapTheorem :
  QGap.BaseGapN2Theorem gapQuadraticForms strongNormSquared
baseGapTheorem =
  QGap.mkBaseGapN2Theorem
    two
    (zero < two)
    baseGapN2Proof

operatorErrorIdentified :
  QGap.operatorErrorIdentifiedWithOperatorStrongErrorTarget
    gapQuadraticForms qError
operatorErrorIdentified x = ≤-refl

operatorErrorN2Proof :
  QGap.operatorErrorN2Target gapQuadraticForms strongNormSquared one
operatorErrorN2Proof x =
  ≤-reflexive
    (trans
      (twoTimes (energy x))
      (sym (*-identityˡ (strongNormSquared x))))

operatorErrorIdentification :
  QGap.OperatorErrorIdentification
    gapQuadraticForms qError strongNormSquared
operatorErrorIdentification =
  QGap.mkOperatorErrorIdentification
    one
    operatorErrorIdentified
    operatorErrorN2Proof

gapMargin : QGap.GapMargin
gapMargin =
  QGap.gapMarginFromTheoremsAndStrict
    baseGapTheorem
    operatorErrorIdentification
    oneLessThanTwo

gapAbsorptionTarget : Set
gapAbsorptionTarget =
  QGap.gapPerturbationAbsorptionTarget
    gapQuadraticForms
    strongNormSquared
    baseGapTheorem
    qError
    operatorErrorIdentification

gapAbsorptionProof : gapAbsorptionTarget
gapAbsorptionProof =
  QGap.gapAbsorptionFromMargin
    baseGapTheorem
    operatorErrorIdentification
    gapMargin

baseGapAbsorptionTarget : QGap.BaseGapMinusErrorAbsorptionTarget
baseGapAbsorptionTarget =
  QGap.mkBaseGapMinusErrorAbsorptionTarget
    gapQuadraticForms
    strongNormSquared
    qError
    baseGapTheorem
    operatorErrorIdentification
    gapMargin
    gapAbsorptionTarget
    true

baseGapAbsorption : QGap.BaseGapMinusErrorAbsorption
baseGapAbsorption =
  QGap.toBaseGapMinusErrorAbsorption baseGapAbsorptionTarget

residueScaleCompatibility : QGap.ResidueScaleCompatibility
residueScaleCompatibility =
  QGap.mkResidueScaleCompatibility
    Carrier
    compatibilityScale
    weakStrongScaling
    baseGapAbsorption
    (operatorStrongErrorN2Target × gapAbsorptionTarget)
    true

residueScaleCompatibilityRouteClosed :
  QGap.ResidueScaleCompatibility.compatibilityRouteClosed
    residueScaleCompatibility
    ≡ true
residueScaleCompatibilityRouteClosed = refl

------------------------------------------------------------------------
-- Strong authority package carrying the proofs, not merely their types.
------------------------------------------------------------------------

record ExactResidueScaleOperatorGapAuthority : Set₁ where
  constructor authority
  field
    operator :
      Operator.PairIncidenceOperatorWitness residueNormModel one

    operatorQuadraticFormIdentified :
      (x : Carrier) →
      Operator.PairIncidenceOperatorWitness.absQuadraticForm operator x
        ≡ qError x

    operatorWeakCN : operatorWeakCNTarget
    weakStrongScalingN1 : weakStrongN1Target
    operatorStrongErrorN2 : operatorStrongErrorN2Target

    baseGapN2 :
      QGap.baseGapN2Target gapQuadraticForms strongNormSquared two

    scaledOperatorErrorN2 :
      QGap.operatorErrorN2Target gapQuadraticForms strongNormSquared one

    strictMargin : one < two
    gapAbsorption : gapAbsorptionTarget

    compatibility : QGap.ResidueScaleCompatibility
    compatibilityClosed :
      QGap.ResidueScaleCompatibility.compatibilityRouteClosed compatibility
        ≡ true

open ExactResidueScaleOperatorGapAuthority public

exactResidueScaleOperatorGapAuthority :
  ExactResidueScaleOperatorGapAuthority
exactResidueScaleOperatorGapAuthority =
  authority
    operatorWitness
    actualQuadraticFormIsError
    operatorWeakCNProof
    weakStrongN1Proof
    operatorStrongErrorN2Proof
    baseGapN2Proof
    operatorErrorN2Proof
    oneLessThanTwo
    gapAbsorptionProof
    residueScaleCompatibility
    residueScaleCompatibilityRouteClosed

finiteCanonicalOperatorGapAuthorityConstructed : Bool
finiteCanonicalOperatorGapAuthorityConstructed = true

strictPositiveGapMarginConstructed : Bool
strictPositiveGapMarginConstructed = true

residueScaleCompatibilityConstructed : Bool
residueScaleCompatibilityConstructed = true

physicalPairIncidenceKernelIdentificationClosed : Bool
physicalPairIncidenceKernelIdentificationClosed = false

finiteCanonicalOperatorGapAuthorityConstructedIsTrue :
  finiteCanonicalOperatorGapAuthorityConstructed ≡ true
finiteCanonicalOperatorGapAuthorityConstructedIsTrue = refl

strictPositiveGapMarginConstructedIsTrue :
  strictPositiveGapMarginConstructed ≡ true
strictPositiveGapMarginConstructedIsTrue = refl

residueScaleCompatibilityConstructedIsTrue :
  residueScaleCompatibilityConstructed ≡ true
residueScaleCompatibilityConstructedIsTrue = refl

physicalPairIncidenceKernelIdentificationClosedIsFalse :
  physicalPairIncidenceKernelIdentificationClosed ≡ false
physicalPairIncidenceKernelIdentificationClosedIsFalse = refl
