{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayDirectTerminalConsumerCutRound308Exact where

------------------------------------------------------------------------
-- ROUND308 / TERMINAL CONSUMERS, NOT FAVOURED PRODUCER TACTICS
--
-- Apply the introspective mandatory-route test one final time.
--
-- A Clay-facing direct route consumes:
--
--   C1  one constructed, nontrivial continuum Yang--Mills/OS family;
--   C2  the direct continuum mass-gap certificate (R306: G1+G2+G3 + standard
--       clustering->spectrum authority);
--   C3  one literal physical YM closed semibounded form on the selected
--       gauge-invariant Hilbert carrier (Kato then constructs domain+self-adjoint
--       associated Hamiltonian);
--   C4  the Hamiltonian carrying C2 is the SAME operator/dynamics as the Kato
--       physical YM Hamiltonian reconstructed from C1.
--
-- The following remain valuable producers but are not definitionally mandatory
-- once the corresponding consumer is supplied directly:
--
--   * CMP98 Eq.119 / Path13 realization: producer for physical action/form data;
--   * common invariant core: producer for generator-equality proofs;
--   * dense-core spectral exclusion: alternative gap producer;
--   * Mosco/vacuum recovery: alternative finite->continuum gap producer;
--   * Heat/Doob/Langevin/Row-C: alternative clustering producer.
--
-- This module does not claim C1-C4 are inhabited.  It prevents proof-search
-- architecture from being mistaken for the Clay statement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound306Exact as B306
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact as Kato
import DASHI.Physics.YangMills.BalabanClayLocalNoncollapseExact as Noncollapse
import DASHI.Physics.YangMills.BalabanCMP98Path13CurrentPreferredSourceFrontierExact as Eq119
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery
import DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact as Dense

record DirectTerminalClayConsumers
    (Hilbert Scalar Hamiltonian Mass ContinuumTheory : Set) : Set₁ where
  field
    -- C1: completed nontrivial continuum construction.  The internal OS/RG
    -- producer may vary; the terminal contract only needs the exact constructed
    -- theory and its physical/nontrivial meaning.
    continuumTheory : ContinuumTheory
    PhysicalYangMillsContinuumTheory : ContinuumTheory → Set
    physicalContinuumTheory : PhysicalYangMillsContinuumTheory continuumTheory

    NontrivialContinuumTheory : ContinuumTheory → Set
    continuumNontrivial : NontrivialContinuumTheory continuumTheory

    -- C3: Kato input.  Domain+self-adjointness are compiler outputs.
    physicalKatoPackage : Kato.KatoM7OperatorPackage Hilbert Scalar

    -- C2: direct B result on the reconstructed Hamiltonian carrier.
    massGap : OSGap.PhysicalMassGapCertificate Hamiltonian Mass

    -- C4: exact same-object/evolution weld.  This is intentionally consumer-
    -- local: proving it may use a common core + generator uniqueness, but the
    -- common core is not itself part of the final equality statement.
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

-- Retained producer statuses, deliberately not promoted to terminal necessity.
round308Eq119ProducerLevel : ProofLevel
round308Eq119ProducerLevel = Eq119.currentPreferredEq119CompilerLevel

round308CommonCoreProducerLevel : ProofLevel
round308CommonCoreProducerLevel = Kato.literalPhysicalYMCommonInvariantOperatorCoreLevel

round308RecoveryProducerLevel : ProofLevel
round308RecoveryProducerLevel = Recovery.physicalVacuumRecoveryProducerLevel

round308DenseCoreProducerLevel : ProofLevel
round308DenseCoreProducerLevel = Dense.physicalDenseCoreAndContinuityInputsLevel

round308TerminalConsumerInhabitationLevel : ProofLevel
round308TerminalConsumerInhabitationLevel = conditional
