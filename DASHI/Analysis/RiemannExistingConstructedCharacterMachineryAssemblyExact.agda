module DASHI.Analysis.RiemannExistingConstructedCharacterMachineryAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Analysis.MarxConstructiveRealRingNormalisation
import DASHI.Analysis.RiemannConstructedComplexCharacterCoreExact as Core
import DASHI.Analysis.RiemannConstructedRealPhaseCoherenceExact as Phase
import DASHI.Analysis.RiemannConstructedComplexExpAddReductionExact as ExpAdd

------------------------------------------------------------------------
-- ASSUMED-IN-REPO ORDINARY MACHINERY -> ONE CONSTRUCTED H_X CORE
--
-- This owner follows the BIDI instruction that ordinary ring / quotient /
-- transcendental machinery is already available in-repo.  It does not reopen
-- those generic implementations.  Instead it packages the exact receipts the
-- RH character consumer needs and composes the already-proved reduction maps.
------------------------------------------------------------------------

record ExistingConstructedCharacterMachinery
    (C : ConstructedComplexPackage) : Set₁ where
  constructor existing-constructed-character-machinery
  field
    ringNormalisation :
      ConstructedRealRingNormalisationLaws (real (realPackage C))

    negationMultiplication :
      Phase.ConstructedRealNegationMultiplicationLaw (real (realPackage C))

    cartesianExpProductNormalisation :
      ExpAdd.CartesianComplexExpProductNormalisation C

    machineryReference : String

open ExistingConstructedCharacterMachinery public

assembledRealPhaseCoherence :
  (C : ConstructedComplexPackage) →
  ExistingConstructedCharacterMachinery C →
  Core.RealPhaseCoherence C
assembledRealPhaseCoherence C M =
  Phase.realPhaseCoherenceFromRingNormalisation
    C
    (ringNormalisation M)
    (negationMultiplication M)

assembledComplexExponentialHomomorphism :
  (C : ConstructedComplexPackage) →
  ExistingConstructedCharacterMachinery C →
  Core.ComplexExponentialHomomorphism C
assembledComplexExponentialHomomorphism C M =
  ExpAdd.complexExponentialHomomorphismFromCartesianNormalisation
    C
    (cartesianExpProductNormalisation M)

assembledConstructedComplexCharacterCore :
  (C : ConstructedComplexPackage) →
  ExistingConstructedCharacterMachinery C →
  Core.ConstructedComplexCharacterCore C
assembledConstructedComplexCharacterCore C M =
  Core.constructed-complex-character-core
    (assembledRealPhaseCoherence C M)
    (assembledComplexExponentialHomomorphism C M)

------------------------------------------------------------------------
-- The two target theorems are therefore direct projections of one assembled
-- donor.  Neither is an independent RH premise once the ordinary machinery
-- receipt has been supplied.
------------------------------------------------------------------------

assembledTargetCharacterProduct :
  (C : ConstructedComplexPackage) →
  (M : ExistingConstructedCharacterMachinery C) →
  (b t u : Real (real (realPackage C))) →
  _*C_
    (expC (complexExponential C) (Core.minusPhase C t u))
    (expC (complexExponential C) (Core.plusPhase C b u))
  ≡ expC
      (complexExponential C)
      (Core.plusPhase C (_-_ (real (realPackage C)) b t) u)
assembledTargetCharacterProduct C M =
  Core.targetTimesSource (assembledConstructedComplexCharacterCore C M)

assembledEvenProjection :
  (C : ConstructedComplexPackage) →
  (M : ExistingConstructedCharacterMachinery C) →
  (delta u : Real (real (realPackage C))) →
  re
    (expC
      (complexExponential C)
      (Core.plusPhase C delta u))
  ≡ cos
      (complexExponential C)
      (_*_ (real (realPackage C)) delta u)
assembledEvenProjection C M =
  Core.evenProjection (assembledConstructedComplexCharacterCore C M)
