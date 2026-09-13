{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayDirectTerminalConsumerCutRound308Exact where

------------------------------------------------------------------------
-- ROUND308 / TERMINAL CONSUMERS, NOT FAVOURED PRODUCER TACTICS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound306Exact as B306
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact as Kato
import DASHI.Physics.YangMills.BalabanCMP98Path13CurrentPreferredSourceFrontierExact as Eq119
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery
import DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact as Dense

record DirectTerminalClayConsumers
    (Hilbert Scalar Hamiltonian Mass ContinuumTheory : Set) : Set₁ where
  field
    continuumTheory : ContinuumTheory
    PhysicalYangMillsContinuumTheory : ContinuumTheory → Set
    physicalContinuumTheory : PhysicalYangMillsContinuumTheory continuumTheory
    NontrivialContinuumTheory : ContinuumTheory → Set
    continuumNontrivial : NontrivialContinuumTheory continuumTheory

    physicalKatoPackage : Kato.KatoM7OperatorPackage Hilbert Scalar
    massGap : OSGap.PhysicalMassGapCertificate Hamiltonian Mass

    PhysicalHamiltonianMeaning : Hamiltonian → Set
    reconstructedGapHamiltonianIsPhysicalYM :
      PhysicalHamiltonianMeaning (OSGap.hamiltonian massGap)

    KatoHamiltonianMeaning :
      Kato.AssociatedSelfAdjointOperator
        (Kato.physicalForm (Kato.physical physicalKatoPackage)) → Set
    katoAssociatedHamiltonianIsPhysicalYM :
      KatoHamiltonianMeaning (Kato.hamiltonian physicalKatoPackage)

    SameHamiltonianDynamics :
      Hamiltonian →
      Kato.AssociatedSelfAdjointOperator
        (Kato.physicalForm (Kato.physical physicalKatoPackage)) → Set
    sameHamiltonianDynamics :
      SameHamiltonianDynamics
        (OSGap.hamiltonian massGap)
        (Kato.hamiltonian physicalKatoPackage)

open DirectTerminalClayConsumers public

data TerminalSearchObject308 : Set where
  continuumPhysicalConstruction : TerminalSearchObject308
  continuumNontriviality : TerminalSearchObject308
  directContinuumMassGap : TerminalSearchObject308
  physicalYMClosedForm : TerminalSearchObject308
  reconstructedGapHamiltonianSameAsPhysicalYM : TerminalSearchObject308
  cmp98Eq119Path13 : TerminalSearchObject308
  commonInvariantCore : TerminalSearchObject308
  denseCoreGapProducer : TerminalSearchObject308
  vacuumRecoveryGapProducer : TerminalSearchObject308
  rowCClusteringProducer : TerminalSearchObject308

terminalRole308 : TerminalSearchObject308 → Introspective.ProofSearchTargetRole
terminalRole308 continuumPhysicalConstruction = Introspective.canonicalConsumerResidual
terminalRole308 continuumNontriviality = Introspective.canonicalConsumerResidual
terminalRole308 directContinuumMassGap = Introspective.canonicalConsumerResidual
terminalRole308 physicalYMClosedForm = Introspective.canonicalConsumerResidual
terminalRole308 reconstructedGapHamiltonianSameAsPhysicalYM =
  Introspective.canonicalConsumerResidual
terminalRole308 cmp98Eq119Path13 = Introspective.optionalProducerTactic
terminalRole308 commonInvariantCore = Introspective.optionalProducerTactic
terminalRole308 denseCoreGapProducer = Introspective.optionalProducerTactic
terminalRole308 vacuumRecoveryGapProducer = Introspective.optionalProducerTactic
terminalRole308 rowCClusteringProducer = Introspective.optionalProducerTactic

record Round308Boundary : Set where
  constructor round308-boundary
  field
    eq119MandatoryIfPhysicalClosedFormSuppliedDirectly : Bool
    eq119MandatoryIfPhysicalClosedFormSuppliedDirectlyIsFalse :
      eq119MandatoryIfPhysicalClosedFormSuppliedDirectly ≡ false
    commonCoreMandatoryIfHamiltonianEqualitySuppliedDirectly : Bool
    commonCoreMandatoryIfHamiltonianEqualitySuppliedDirectlyIsFalse :
      commonCoreMandatoryIfHamiltonianEqualitySuppliedDirectly ≡ false
    denseCoreAndRecoveryBothMandatoryAfterDirectContinuumGap : Bool
    denseCoreAndRecoveryBothMandatoryAfterDirectContinuumGapIsFalse :
      denseCoreAndRecoveryBothMandatoryAfterDirectContinuumGap ≡ false
    katoDomainAndSelfAdjointnessCompilerOwned : Bool
    katoDomainAndSelfAdjointnessCompilerOwnedIsTrue :
      katoDomainAndSelfAdjointnessCompilerOwned ≡ true

canonicalRound308Boundary : Round308Boundary
canonicalRound308Boundary = round308-boundary false refl false refl false refl true refl

round308DirectBGapCompilerLevel : ProofLevel
round308DirectBGapCompilerLevel = B306.round306MassGapAssemblyLevel

round308DirectBG1Level : ProofLevel
round308DirectBG1Level = B306.round306G1LiteralAbsoluteTwoJLocalizationLevel

round308DirectBG2Level : ProofLevel
round308DirectBG2Level = B306.round306G2PhysicalPairwiseTimeMeaningLevel

round308DirectBG3Level : ProofLevel
round308DirectBG3Level = B306.round306G3PhysicalMassRateNormalizationLevel

round308KatoCompilerLevel : ProofLevel
round308KatoCompilerLevel = Kato.katoClosedFormHamiltonianCompilerLevel

round308PhysicalClosedFormLevel : ProofLevel
round308PhysicalClosedFormLevel = Kato.literalPhysicalYMClosedSemiboundedFormLevel

round308Eq119ProducerLevel : ProofLevel
round308Eq119ProducerLevel = Eq119.cmp98Path13CurrentPreferredSourceFrontierLevel

round308CommonCoreProducerLevel : ProofLevel
round308CommonCoreProducerLevel = Kato.literalPhysicalYMCommonInvariantOperatorCoreLevel

round308RecoveryProducerLevel : ProofLevel
round308RecoveryProducerLevel = Recovery.physicalVacuumRecoveryProducerLevel

round308DenseCoreProducerLevel : ProofLevel
round308DenseCoreProducerLevel = Dense.physicalDenseCoreAndContinuityInputsLevel

round308TerminalConsumerInhabitationLevel : ProofLevel
round308TerminalConsumerInhabitationLevel = conditional
