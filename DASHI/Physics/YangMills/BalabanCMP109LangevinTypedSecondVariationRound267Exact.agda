{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109LangevinTypedSecondVariationRound267Exact where

------------------------------------------------------------------------
-- ROUND267 / C4b LITERAL CMP109 <-> TYPED LANGEVIN HESSIAN WELD
--
-- Round103 already proves that the CMP116 physical marked Hessian is the second
-- variation of the SAME CMP109 effective potential.  Round265 exposes the
-- differentiated Langevin commutator as a typed matrix decomposition.
--
-- This module forces those two lanes onto ONE object: the action-Hessian entry
-- in the typed Langevin commutator is definitionally chosen to be the literal
-- CMP116 physical Hessian evaluated on site-indexed physical tangents.  The
-- existing Round103 theorem then also identifies it with CMP109 E^(2)/Pi.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier

record LiteralCMP109LangevinSecondVariationWeld : Set₁ where
  field
    carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier
    frame : Langevin.CompactLieLangevinFrameData

    background : Source.Background (Carrier.source carrier)
    siteTangent :
      Langevin.Site frame → Source.Tangent (Carrier.source carrier)

    commutatorEntry : Langevin.Site frame → Langevin.Site frame → ℝ
    symmetricNonlocalEntry : Langevin.Site frame → Langevin.Site frame → ℝ
    connectionEntry : Langevin.Site frame → Langevin.Site frame → ℝ

    commutatorDecomposition : ∀ x y →
      commutatorEntry x y
      ≡ symmetricNonlocalEntry x y +ℝ connectionEntry x y

    symmetricNonlocalIsCMP116PhysicalHessian : ∀ x y →
      symmetricNonlocalEntry x y
      ≡ Carrier.cmp116PhysicalMarkedHessian carrier background
          (siteTangent x) (siteTangent y)

    connectionEntryIsOnsiteAd : Langevin.connectionIsOnsiteAdTerm frame

open LiteralCMP109LangevinSecondVariationWeld public

asTypedLangevinCommutator :
  LiteralCMP109LangevinSecondVariationWeld →
  Langevin.TypedLangevinCommutatorData ℝ
asTypedLangevinCommutator dataSet = record
  { Langevin.TypedLangevinCommutatorData.frame = frame dataSet
  ; Langevin.TypedLangevinCommutatorData.add = _+ℝ_
  ; Langevin.TypedLangevinCommutatorData.commutatorEntry =
      commutatorEntry dataSet
  ; Langevin.TypedLangevinCommutatorData.symmetricNonlocalEntry =
      symmetricNonlocalEntry dataSet
  ; Langevin.TypedLangevinCommutatorData.connectionEntry =
      connectionEntry dataSet
  ; Langevin.TypedLangevinCommutatorData.actionHessianEntry =
      λ x y → Carrier.cmp116PhysicalMarkedHessian
        (carrier dataSet) (background dataSet)
        (siteTangent dataSet x) (siteTangent dataSet y)
  ; Langevin.TypedLangevinCommutatorData.commutatorDecomposition =
      commutatorDecomposition dataSet
  ; Langevin.TypedLangevinCommutatorData.symmetricNonlocalIsActionHessian =
      symmetricNonlocalIsCMP116PhysicalHessian dataSet
  ; Langevin.TypedLangevinCommutatorData.connectionEntryIsOnsiteAd =
      connectionEntryIsOnsiteAd dataSet
  }

typedActionHessianIsCMP116 :
  (dataSet : LiteralCMP109LangevinSecondVariationWeld) →
  ∀ x y →
  Langevin.actionHessianEntry (asTypedLangevinCommutator dataSet) x y
  ≡ Carrier.cmp116PhysicalMarkedHessian
      (carrier dataSet) (background dataSet)
      (siteTangent dataSet x) (siteTangent dataSet y)
typedActionHessianIsCMP116 dataSet x y = refl

typedActionHessianIsCMP109Polarization :
  (dataSet : LiteralCMP109LangevinSecondVariationWeld) →
  ∀ x y →
  Langevin.actionHessianEntry (asTypedLangevinCommutator dataSet) x y
  ≡ Carrier.cmp109Polarization
      (carrier dataSet) (background dataSet)
      (siteTangent dataSet x) (siteTangent dataSet y)
typedActionHessianIsCMP109Polarization dataSet x y =
  trans
    (typedActionHessianIsCMP116 dataSet x y)
    (sym
      (Carrier.cmp109PolarizationIsCMP116PhysicalMarkedHessian
        (carrier dataSet) (background dataSet)
        (siteTangent dataSet x) (siteTangent dataSet y)))

round267TypedCMP109LangevinCompilerLevel : ProofLevel
round267TypedCMP109LangevinCompilerLevel = machineChecked

round267CMP109CMP116IdentityLevel : ProofLevel
round267CMP109CMP116IdentityLevel = Carrier.cmp109CMP116PhysicalHessianIdentityLevel

round267LiteralLangevinDifferentiationInstantiationLevel : ProofLevel
round267LiteralLangevinDifferentiationInstantiationLevel = conditional
