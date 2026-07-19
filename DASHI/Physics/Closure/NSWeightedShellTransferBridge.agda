module DASHI.Physics.Closure.NSWeightedShellTransferBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Analysis.BlockSchurCoercivity
open import DASHI.Analysis.WeightedKernelSchurTest
open import DASHI.Physics.Closure.NSShellSchurInstance
open import DASHI.Physics.Closure.NSFactorizedCrossShellBound

------------------------------------------------------------------------
-- Concrete weighted-kernel bridge for the two off-diagonal NS transfers.
--
-- The certificate objects below are indexed by their actual kernels.  The
-- `representsK01` / `representsK10` fields are deliberately proof-relevant:
-- coarse shell-angle telemetry is not enough unless it is identified with the
-- pair-incidence operator used by the shell decomposition.
------------------------------------------------------------------------

record NSWeightedTransferEvidence
    {v s r01 c01r r10 c10r : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    {Row01 : Set r01}
    {Col01 : Set c01r}
    {Row10 : Set r10}
    {Col10 : Set c10r}
    {O : SchurOrderLaws Scalar}
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O)
    (K01 : WeightedKernelData Row01 Col01 Scalar)
    (L01 : WeightedSchurLaws K01)
    (K10 : WeightedKernelData Row10 Col10 Scalar)
    (L10 : WeightedSchurLaws K10) :
    Set (lsuc (v ⊔ s ⊔ r01 ⊔ c01r ⊔ r10 ⊔ c10r)) where
  field
    k01Certificate : WeightedKernelSchurCertificate K01 L01
    k10Certificate : WeightedKernelSchurCertificate K10 L10

    representsK01 : Set (v ⊔ s ⊔ r01 ⊔ c01r)
    representsK10 : Set (v ⊔ s ⊔ r10 ⊔ c10r)
    k01Representation : representsK01
    k10Representation : representsK10

    afterK01 : ShellVector → Scalar
    afterLowResolvent : ShellVector → Scalar
    afterK10 : ShellVector → Scalar

    c01 : Scalar
    r0 : Scalar
    c10 : Scalar

    certificateGivesK01Bound :
      WeightedKernelSchurCertificate K01 L01 →
      representsK01 →
      ∀ x → _≤_ O (afterK01 x) c01

    lowResolventBound :
      ∀ x →
      _≤_ O
        (afterLowResolvent x)
        (schurMultiply M r0 (afterK01 x))

    certificateGivesK10Bound :
      WeightedKernelSchurCertificate K10 L10 →
      representsK10 →
      ∀ x →
      _≤_ O
        (afterK10 x)
        (schurMultiply M c10 (afterLowResolvent x))

    correctionControlledByReturn :
      ∀ x →
      _≤_ O
        (inner I x (crossCorrection I x))
        (afterK10 x)

open NSWeightedTransferEvidence public

weightedTransferToFactorizedEvidence :
  ∀ {v s r01 c01r r10 c10r}
    {ShellVector : Set v}
    {Scalar : Set s}
    {Row01 : Set r01}
    {Col01 : Set c01r}
    {Row10 : Set r10}
    {Col10 : Set c10r}
    {O : SchurOrderLaws Scalar}
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O)
    (K01 : WeightedKernelData Row01 Col01 Scalar)
    (L01 : WeightedSchurLaws K01)
    (K10 : WeightedKernelData Row10 Col10 Scalar)
    (L10 : WeightedSchurLaws K10) →
  NSWeightedTransferEvidence M I K01 L01 K10 L10 →
  NSFactorizedCrossShellEvidence M I
weightedTransferToFactorizedEvidence M I K01 L01 K10 L10 E = record
  { afterK01 = afterK01 E
  ; afterLowResolvent = afterLowResolvent E
  ; afterK10 = afterK10 E
  ; c01 = c01 E
  ; r0 = r0 E
  ; c10 = c10 E
  ; correctionControlledByReturn = correctionControlledByReturn E
  ; k10Bound =
      certificateGivesK10Bound E
        (k10Certificate E)
        (k10Representation E)
  ; lowResolventBound = lowResolventBound E
  ; k01Bound =
      certificateGivesK01Bound E
        (k01Certificate E)
        (k01Representation E)
  }