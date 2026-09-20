{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact where

------------------------------------------------------------------------
-- C / ROUND109 COMPLETED MARKED STRESS -> CONCRETE PINNED LOCAL-C STRESS
--
-- The concrete Local-C package already carries a stress tensor equal to its
-- pinned common-core stress. Round109 already identifies its completed marked
-- stress with the literal Clay stress tensor. Therefore only one same-object
-- equality is required:
--
--   literal Clay stress tensor = concrete Local-C stress tensor.
--
-- Everything after that, including equality with the common-core stress and
-- the pinned OS Hamiltonian, is compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact as Common
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR

record Round109ConcreteLocalCStressWeld
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    : Set₂ where
  field
    completion : R109.LiteralSchwingerStressMarkedCompletion Y group

    literalClayStressIsConcreteLocalCStress :
      Top.stressTensor Y group ≡ LocalC.stressTensor localC

open Round109ConcreteLocalCStressWeld public

completedMarkedStressIsConcreteLocalCStress :
  ∀ {C S Y group G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (weld :
      Round109ConcreteLocalCStressWeld
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector} {Hamiltonian = Hamiltonian}
        {Algebra = Algebra} {Scale = Scale} {Volume = Volume}
        {Root = Root} {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {osS = osS}
        {osInputs = osInputs} {reconstruction = reconstruction}
        localC) →
  Marked.continuumComposite
    (StressMarked.stressField
      (StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields
        (R109.completedSources (completion weld))))
  ≡ LocalC.stressTensor localC
completedMarkedStressIsConcreteLocalCStress weld =
  trans
    (R109.literalStressIsCompletedMarkedStress (completion weld))
    (literalClayStressIsConcreteLocalCStress weld)

literalClayStressIsPinnedCommonCoreStress :
  ∀ {C S Y group G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (weld :
      Round109ConcreteLocalCStressWeld
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector} {Hamiltonian = Hamiltonian}
        {Algebra = Algebra} {Scale = Scale} {Volume = Volume}
        {Root = Root} {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {osS = osS}
        {osInputs = osInputs} {reconstruction = reconstruction}
        localC) →
  Top.stressTensor Y group
  ≡ Common.stressTensor (LocalC.stressCommonCore localC)
literalClayStressIsPinnedCommonCoreStress {localC = localC} weld =
  trans
    (literalClayStressIsConcreteLocalCStress weld)
    (LocalC.stressTensorIsCommonCoreStress localC)

completedMarkedStressChargeUsesPinnedHamiltonian :
  ∀ {C S Y group G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (weld :
      Round109ConcreteLocalCStressWeld
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector} {Hamiltonian = Hamiltonian}
        {Algebra = Algebra} {Scale = Scale} {Volume = Volume}
        {Root = Root} {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {osS = osS}
        {osInputs = osInputs} {reconstruction = reconstruction}
        localC) →
  Common.stressCharge (LocalC.stressCommonCore localC)
    (LocalC.stressTensor localC)
  ≡ OSR.reconstructedHamiltonian reconstruction group
completedMarkedStressChargeUsesPinnedHamiltonian {localC = localC} weld =
  LocalC.stressChargeGeneratesPinnedHamiltonian localC

round109ConcreteLocalCSameStressCompilerLevel : ProofLevel
round109ConcreteLocalCSameStressCompilerLevel = machineChecked

literalRound109ConcreteLocalCSameStressLevel : ProofLevel
literalRound109ConcreteLocalCSameStressLevel = conditional
