{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119GRQFTStressExportExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact as Common
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C

record PinnedCMP119GRQFTStressEndpoint
    (StressTensor Hamiltonian : Set) : Set₁ where
  constructor pinnedCMP119GRQFTStressEndpoint
  field
    qftStressTensor : StressTensor
    qftHamiltonian : Hamiltonian
    StressCharge : StressTensor → Hamiltonian
    qftStressChargeGeneratesSameHamiltonian :
      StressCharge qftStressTensor ≡ qftHamiltonian

open PinnedCMP119GRQFTStressEndpoint public

exportPinnedCMP119StressEndpoint :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) →
  PinnedCMP119GRQFTStressEndpoint StressTensor Hamiltonian
exportPinnedCMP119StressEndpoint
    {reconstruction = reconstruction} {group = group} inputs =
  pinnedCMP119GRQFTStressEndpoint
    (C.stressTensor inputs)
    (OSR.reconstructedHamiltonian reconstruction group)
    (Common.stressCharge (C.stressCommonCore inputs))
    (C.stressChargeGeneratesPinnedHamiltonian inputs)

exportedStressIsLiteralPinnedStress :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) →
  qftStressTensor (exportPinnedCMP119StressEndpoint inputs)
  ≡ C.stressTensor inputs
exportedStressIsLiteralPinnedStress inputs = refl

exportedHamiltonianIsSamePinnedOSHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) →
  qftHamiltonian (exportPinnedCMP119StressEndpoint inputs)
  ≡ OSR.reconstructedHamiltonian reconstruction group
exportedHamiltonianIsSamePinnedOSHamiltonian inputs = refl

pinnedCMP119GRQFTStressExportLevel : ProofLevel
pinnedCMP119GRQFTStressExportLevel = machineChecked

importsGRQFTSharedCarrier : Bool
importsGRQFTSharedCarrier = false

importsGRQFTSharedCarrierIsFalse :
  importsGRQFTSharedCarrier ≡ false
importsGRQFTSharedCarrierIsFalse = refl

grqftStressWeldPromoted : Bool
grqftStressWeldPromoted = false

grqftStressWeldPromotedIsFalse :
  grqftStressWeldPromoted ≡ false
grqftStressWeldPromotedIsFalse = refl
