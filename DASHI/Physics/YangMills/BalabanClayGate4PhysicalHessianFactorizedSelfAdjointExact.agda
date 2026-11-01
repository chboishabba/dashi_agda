module DASHI.Physics.YangMills.BalabanClayGate4PhysicalHessianFactorizedSelfAdjointExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Structural self-adjointness for D* C D and Q* R Q channels.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- The physical channel proofs should expose factorisations rather than prove
-- five unrelated coordinate identities.  Curvature-type terms are represented
-- as D* C D and constraint terms as Q* R Q.  Once the middle operators are
-- self-adjoint, the complete sandwiches are self-adjoint by star algebra alone.
------------------------------------------------------------------------

record StarOperatorAlgebra (Operator : Set) : Set₁ where
  field
    compose : Operator → Operator → Operator
    adjoint : Operator → Operator

    composeAssociative : ∀ outer middle inner →
      compose (compose outer middle) inner
      ≡ compose outer (compose middle inner)

    adjointCompose : ∀ outer inner →
      adjoint (compose outer inner)
      ≡ compose (adjoint inner) (adjoint outer)

    adjointInvolutive : ∀ operator →
      adjoint (adjoint operator) ≡ operator

open StarOperatorAlgebra public

SelfAdjoint :
  ∀ {Operator} → StarOperatorAlgebra Operator → Operator → Set
SelfAdjoint algebra operator = adjoint algebra operator ≡ operator

sandwich :
  ∀ {Operator} → StarOperatorAlgebra Operator →
  Operator → Operator → Operator
sandwich algebra leg middle =
  compose algebra (adjoint algebra leg)
    (compose algebra middle leg)

sandwichSelfAdjoint :
  ∀ {Operator}
    (algebra : StarOperatorAlgebra Operator)
    leg middle →
  SelfAdjoint algebra middle →
  SelfAdjoint algebra (sandwich algebra leg middle)
sandwichSelfAdjoint algebra leg middle middleSelfAdjoint
  rewrite adjointCompose algebra
    (adjoint algebra leg) (compose algebra middle leg)
  | adjointCompose algebra middle leg
  | adjointInvolutive algebra leg
  | middleSelfAdjoint
  | composeAssociative algebra (adjoint algebra leg) middle leg =
  refl

record FiveChannelFactorizations (Operator : Set) : Set₁ where
  field
    algebra : StarOperatorAlgebra Operator

    curvature transport chart gauge constraint : Operator

    curvatureLeg curvatureMiddle : Operator
    transportLeg transportMiddle : Operator
    chartLeg chartMiddle : Operator
    gaugeLeg gaugeMiddle : Operator
    constraintLeg constraintMiddle : Operator

    curvatureMeaning :
      curvature ≡ sandwich algebra curvatureLeg curvatureMiddle
    transportMeaning :
      transport ≡ sandwich algebra transportLeg transportMiddle
    chartMeaning :
      chart ≡ sandwich algebra chartLeg chartMiddle
    gaugeMeaning :
      gauge ≡ sandwich algebra gaugeLeg gaugeMiddle
    constraintMeaning :
      constraint ≡ sandwich algebra constraintLeg constraintMiddle

    curvatureMiddleSelfAdjoint : SelfAdjoint algebra curvatureMiddle
    transportMiddleSelfAdjoint : SelfAdjoint algebra transportMiddle
    chartMiddleSelfAdjoint : SelfAdjoint algebra chartMiddle
    gaugeMiddleSelfAdjoint : SelfAdjoint algebra gaugeMiddle
    constraintMiddleSelfAdjoint : SelfAdjoint algebra constraintMiddle

open FiveChannelFactorizations public

curvatureSelfAdjointFromFactorization :
  ∀ {Operator} (dataSet : FiveChannelFactorizations Operator) →
  SelfAdjoint (algebra dataSet) (curvature dataSet)
curvatureSelfAdjointFromFactorization dataSet =
  subst
    (SelfAdjoint (algebra dataSet))
    (sym (curvatureMeaning dataSet))
    (sandwichSelfAdjoint (algebra dataSet)
      (curvatureLeg dataSet) (curvatureMiddle dataSet)
      (curvatureMiddleSelfAdjoint dataSet))

transportSelfAdjointFromFactorization :
  ∀ {Operator} (dataSet : FiveChannelFactorizations Operator) →
  SelfAdjoint (algebra dataSet) (transport dataSet)
transportSelfAdjointFromFactorization dataSet =
  subst
    (SelfAdjoint (algebra dataSet))
    (sym (transportMeaning dataSet))
    (sandwichSelfAdjoint (algebra dataSet)
      (transportLeg dataSet) (transportMiddle dataSet)
      (transportMiddleSelfAdjoint dataSet))

chartSelfAdjointFromFactorization :
  ∀ {Operator} (dataSet : FiveChannelFactorizations Operator) →
  SelfAdjoint (algebra dataSet) (chart dataSet)
chartSelfAdjointFromFactorization dataSet =
  subst
    (SelfAdjoint (algebra dataSet))
    (sym (chartMeaning dataSet))
    (sandwichSelfAdjoint (algebra dataSet)
      (chartLeg dataSet) (chartMiddle dataSet)
      (chartMiddleSelfAdjoint dataSet))

gaugeSelfAdjointFromFactorization :
  ∀ {Operator} (dataSet : FiveChannelFactorizations Operator) →
  SelfAdjoint (algebra dataSet) (gauge dataSet)
gaugeSelfAdjointFromFactorization dataSet =
  subst
    (SelfAdjoint (algebra dataSet))
    (sym (gaugeMeaning dataSet))
    (sandwichSelfAdjoint (algebra dataSet)
      (gaugeLeg dataSet) (gaugeMiddle dataSet)
      (gaugeMiddleSelfAdjoint dataSet))

constraintSelfAdjointFromFactorization :
  ∀ {Operator} (dataSet : FiveChannelFactorizations Operator) →
  SelfAdjoint (algebra dataSet) (constraint dataSet)
constraintSelfAdjointFromFactorization dataSet =
  subst
    (SelfAdjoint (algebra dataSet))
    (sym (constraintMeaning dataSet))
    (sandwichSelfAdjoint (algebra dataSet)
      (constraintLeg dataSet) (constraintMiddle dataSet)
      (constraintMiddleSelfAdjoint dataSet))

physicalSandwichSelfAdjointLevel : ProofLevel
physicalSandwichSelfAdjointLevel = machineChecked

physicalFiveChannelFactorizationReuseLevel : ProofLevel
physicalFiveChannelFactorizationReuseLevel = machineChecked

physicalCurvatureTransportChartFactorizationInputsLevel : ProofLevel
physicalCurvatureTransportChartFactorizationInputsLevel = conditional

physicalGaugeConstraintFactorizationInputsLevel : ProofLevel
physicalGaugeConstraintFactorizationInputsLevel = conditional
