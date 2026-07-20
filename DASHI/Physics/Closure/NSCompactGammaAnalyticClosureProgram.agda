module DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaOffPacketTriadMajorization
open import DASHI.Physics.Closure.NSCompactGammaOffPacketTailDecayBridge
open import DASHI.Physics.Closure.NSCompactGammaGalerkinLimitBridge
open import DASHI.Physics.Closure.NSCompactGammaTimeIntegrabilityBridge

------------------------------------------------------------------------
-- Final analytic closure surface for the compact-Gamma lane.
--
-- This module deliberately does not replace any analytic theorem by a Boolean
-- receipt.  It names the five concrete witnesses required by the program and
-- proves that, once they are supplied for one carrier, every downstream result
-- is obtained without another hidden seam.
------------------------------------------------------------------------

record FullShellUniformMajorization
    {m : Level}
    (Mode : Set m)
    (A : AbsorptionArithmetic) : Set (lsuc m) where
  field
    shell : Nat → Mode → Set
    incidence : Nat → Mode → Mode → Set

    localFourierResponse : Nat → Mode → Mode → Scalar A
    localFourierMajorant : Nat → Mode → Mode → Scalar A

    everyLocalFourierMajorization :
      (cutoff : Nat) →
      (target source : Mode) →
      incidence cutoff target source →
      _≤_ A
        (localFourierResponse cutoff target source)
        (localFourierMajorant cutoff target source)

    rowBudget columnBudget : Scalar A

    fullShellRowBound :
      (cutoff : Nat) →
      (target : Mode) →
      shell cutoff target →
      Scalar A

    fullShellColumnBound :
      (cutoff : Nat) →
      (source : Mode) →
      shell cutoff source →
      Scalar A

    rowBoundUniform :
      (cutoff : Nat) →
      (target : Mode) →
      (inside : shell cutoff target) →
      _≤_ A (fullShellRowBound cutoff target inside) rowBudget

    columnBoundUniform :
      (cutoff : Nat) →
      (source : Mode) →
      (inside : shell cutoff source) →
      _≤_ A (fullShellColumnBound cutoff source inside) columnBudget

open FullShellUniformMajorization public

record AnalyticTailDecay
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (F : RadiusIndexedOffPacketSplit Radius A) : Set (lsuc r) where
  field
    vanishingTail : OrderVanishingTail A F

open AnalyticTailDecay public

record GalerkinCompactnessWitnesses
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A) : Set₁ where
  field
    compactnessAndIdentification : UniformLogModulusGalerkinFamily A C

open GalerkinCompactnessWitnesses public

record AdmissibleSolutionPath
    {t s : Level}
    (Time : Set t)
    (State : Set s) : Set (lsuc (t ⊔ s)) where
  field
    stateAt : Time → State
    CompactGammaAdmissible : State → Set

    initialTime : Time
    initialAdmissible : CompactGammaAdmissible (stateAt initialTime)

    admissibilityPreserved :
      (time : Time) →
      CompactGammaAdmissible (stateAt time)

open AdmissibleSolutionPath public

record CompactGammaAnalyticClosure
    {p m r t s : Level}
    (PairAtom : Set p)
    (Mode : Set m)
    (Radius : Set r)
    (Time : Set t)
    (State : Set s)
    (A : AbsorptionArithmetic)
    (M : FiniteMajorantArithmetic A)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (C : SequentialOrderClosure A)
    (J : MonotoneTimeIntegral Time A) :
    Set (lsuc (p ⊔ m ⊔ r ⊔ t ⊔ s)) where
  field
    differentiatedTriads : TriadMajorizationInputs PairAtom A M
    fullShell : FullShellUniformMajorization Mode A
    tailDecay : AnalyticTailDecay A F
    galerkinLimit : GalerkinCompactnessWitnesses A C
    solutionPath : AdmissibleSolutionPath Time State
    timeIntegrability : BKMEnvelopeInputs A J

open CompactGammaAnalyticClosure public

------------------------------------------------------------------------
-- Exported consequences.
------------------------------------------------------------------------

closureNearResponseMajorized :
  ∀ {p m r t s}
    {PairAtom : Set p}
    {Mode : Set m}
    {Radius : Set r}
    {Time : Set t}
    {State : Set s}
    (A : AbsorptionArithmetic)
    (M : FiniteMajorantArithmetic A)
    {F : RadiusIndexedOffPacketSplit Radius A}
    {C : SequentialOrderClosure A}
    {J : MonotoneTimeIntegral Time A} →
  (P : CompactGammaAnalyticClosure
    PairAtom Mode Radius Time State A M F C J) →
  _≤_ A
    (concreteNearResponse (differentiatedTriads P))
    (majorantActionOutput (differentiatedTriads P))
closureNearResponseMajorized A M P =
  triadMajorization A M (differentiatedTriads P)

closureTailEventuallyAbsorbable :
  ∀ {p m r t s}
    {PairAtom : Set p}
    {Mode : Set m}
    {Radius : Set r}
    {Time : Set t}
    {State : Set s}
    (A : AbsorptionArithmetic)
    (M : FiniteMajorantArithmetic A)
    (F : RadiusIndexedOffPacketSplit Radius A)
    {C : SequentialOrderClosure A}
    {J : MonotoneTimeIntegral Time A} →
  (P : CompactGammaAnalyticClosure
    PairAtom Mode Radius Time State A M F C J) →
  (budget : Scalar A) →
  AdmissibleTailBudget (vanishingTail (tailDecay P)) budget →
  Σ Radius
    (λ radius →
      _≤_ A
        (farShellTail (splitAt F radius))
        budget)
closureTailEventuallyAbsorbable A M F P =
  tailEventuallyBelow (vanishingTail (tailDecay P))

closureLogModulusPassesToContinuum :
  ∀ {p m r t s}
    {PairAtom : Set p}
    {Mode : Set m}
    {Radius : Set r}
    {Time : Set t}
    {State : Set s}
    (A : AbsorptionArithmetic)
    (M : FiniteMajorantArithmetic A)
    {F : RadiusIndexedOffPacketSplit Radius A}
    (C : SequentialOrderClosure A)
    {J : MonotoneTimeIntegral Time A} →
  (P : CompactGammaAnalyticClosure
    PairAtom Mode Radius Time State A M F C J) →
  _≤_ A
    (continuumAbsoluteLogDerivative
      (compactnessAndIdentification (galerkinLimit P)))
    (continuumLogModulusBudget
      (compactnessAndIdentification (galerkinLimit P)))
closureLogModulusPassesToContinuum A M C P =
  uniformLogModulusPassesToContinuum A C
    (compactnessAndIdentification (galerkinLimit P))

closureAdmissibilityPreserved :
  ∀ {p m r t s}
    {PairAtom : Set p}
    {Mode : Set m}
    {Radius : Set r}
    {Time : Set t}
    {State : Set s}
    {A : AbsorptionArithmetic}
    {M : FiniteMajorantArithmetic A}
    {F : RadiusIndexedOffPacketSplit Radius A}
    {C : SequentialOrderClosure A}
    {J : MonotoneTimeIntegral Time A} →
  (P : CompactGammaAnalyticClosure
    PairAtom Mode Radius Time State A M F C J) →
  (time : Time) →
  CompactGammaAdmissible (solutionPath P)
    (stateAt (solutionPath P) time)
closureAdmissibilityPreserved P =
  admissibilityPreserved (solutionPath P)

closureBKMTimeIntegralFinite :
  ∀ {p m r t s}
    {PairAtom : Set p}
    {Mode : Set m}
    {Radius : Set r}
    {Time : Set t}
    {State : Set s}
    (A : AbsorptionArithmetic)
    (M : FiniteMajorantArithmetic A)
    {F : RadiusIndexedOffPacketSplit Radius A}
    {C : SequentialOrderClosure A}
    (J : MonotoneTimeIntegral Time A) →
  (P : CompactGammaAnalyticClosure
    PairAtom Mode Radius Time State A M F C J) →
  _≤_ A
    (integrate J (vorticityNorm (timeIntegrability P)))
    (bkmBudget (timeIntegrability P))
closureBKMTimeIntegralFinite A M J P =
  compactGammaEnvelopeBoundsBKMIntegral A J (timeIntegrability P)
