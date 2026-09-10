module DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact where

------------------------------------------------------------------------
-- ROUND72/R265: COMPACT-LIE LANGEVIN CONNECTION IS BASIS-FREE SKEW ENERGY ZERO
--               + TYPED DIFFERENTIATED-COMMUTATOR SOURCE SURFACE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieBiInvariantSkewLangevinExact as Skew

connectionPairedEnergyCancels = Skew.connectionPairedEnergyCancels
connectionQuadraticEnergyCancels = Skew.connectionQuadraticEnergyCancels
finiteLatticeConnectionEnergyCancels = Skew.finiteLatticeConnectionEnergyCancels

compactLieSkewQuadraticCancellationLevel : ProofLevel
compactLieSkewQuadraticCancellationLevel = machineChecked

record CompactLieLangevinFrameData : Set₁ where
  field
    Site Field Function : Set
    metric : Skew.BiInvariantLieMetricData
    frameDerivative : Site → Skew.Lie metric → Function → Function
    laplacian : Function → Function
    connectionDirection : Site → Field → Skew.Lie metric
    derivativeVector : Site → Field → Skew.Lie metric
    laplacianCommutesWithFrame : Set

    -- Legacy source sockets retained for backwards compatibility only.
    LangevinCommutatorIdentity : Set
    connectionIsOnsiteAdTerm : Set

open CompactLieLangevinFrameData public

literalConnectionQuadraticEnergyCancels :
  (D : CompactLieLangevinFrameData) →
  (field : Field D) →
  ∀ sites →
  Skew.sumConnectionQuadratic
    (metric D)
    (λ site → connectionDirection D site field)
    (λ site → derivativeVector D site field)
    sites
  ≡ Skew.zero (metric D)
literalConnectionQuadraticEnergyCancels D field =
  Skew.finiteLatticeConnectionEnergyCancels
    (metric D)
    (λ site → connectionDirection D site field)
    (λ site → derivativeVector D site field)

------------------------------------------------------------------------
-- R265: typed replacement for the opaque commutator producer socket.
--
-- The coefficient carrier is an INDEX, not an existential field.  Downstream
-- source owners can therefore require the exact scalar carrier (for Row C,
-- physical real coefficients) rather than accepting a neighbouring type.
------------------------------------------------------------------------

record TypedLangevinCommutatorData (Coefficient : Set) : Set₁ where
  field
    frame : CompactLieLangevinFrameData
    add : Coefficient → Coefficient → Coefficient

    commutatorEntry : Site frame → Site frame → Coefficient
    symmetricNonlocalEntry : Site frame → Site frame → Coefficient
    connectionEntry : Site frame → Site frame → Coefficient
    actionHessianEntry : Site frame → Site frame → Coefficient

    commutatorDecomposition : ∀ x y →
      commutatorEntry x y
      ≡ add (symmetricNonlocalEntry x y) (connectionEntry x y)

    symmetricNonlocalIsActionHessian : ∀ x y →
      symmetricNonlocalEntry x y ≡ actionHessianEntry x y

    connectionEntryIsOnsiteAd : connectionIsOnsiteAdTerm frame

open TypedLangevinCommutatorData public

commutatorEntryIsHessianPlusConnection :
  ∀ {Coefficient}
    (dataSet : TypedLangevinCommutatorData Coefficient) →
  ∀ x y →
  commutatorEntry dataSet x y
  ≡ add dataSet
      (actionHessianEntry dataSet x y)
      (connectionEntry dataSet x y)
commutatorEntryIsHessianPlusConnection dataSet x y
  rewrite symmetricNonlocalIsActionHessian dataSet x y =
  commutatorDecomposition dataSet x y

typedLangevinCommutatorCompilerLevel : ProofLevel
typedLangevinCommutatorCompilerLevel = machineChecked

compactLieCasimirFrameCommutationLevel : ProofLevel
compactLieCasimirFrameCommutationLevel = standardImported

compactLieAdSkewConnectionLevel : ProofLevel
compactLieAdSkewConnectionLevel = standardImported

physicalLiteralLangevinCommutatorIdentificationLevel : ProofLevel
physicalLiteralLangevinCommutatorIdentificationLevel = conditional

typedPhysicalLiteralLangevinCommutatorInstantiationLevel : ProofLevel
typedPhysicalLiteralLangevinCommutatorInstantiationLevel = conditional
