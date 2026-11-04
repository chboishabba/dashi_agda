{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOSRealTimeDifferenceQuotientGeneratorWeldExact where

------------------------------------------------------------------------
-- P03/P07: STRONG GENERATOR WELD FOR THE ORIGINAL TSVF / R331 OS CLOCK.
--
-- OriginalTSVFToOSClock.oneStepIntertwines is only a discrete algebraic
-- statement. It must NOT identify the Euclidean OS contraction
-- e^{-tau H/hbar} with real-time observer unitaries e^{-itH/hbar}.
--
-- On the SAME ORIGINAL observer and reconstructed OS state carrier,
-- if a physically supplied real-time unitary intertwinement and linear
-- embedding are available, then ALL sampled strong difference
-- quotients commute with that embedding. If the actual observer and
-- original reconstructed OS H strong derivatives converge in one
-- selected topology and that topology has unique limits, the physical
-- generators intertwine. That last equality is a DERIVED theorem, not
-- supplied as an independent field or a second Hamiltonian.
--
-- The missing physical sources are explicit: real Time, Hilbert
-- topology/completion, real-time unitary and Stone continuity, common
-- dense self-adjoint domains, the meaning of the original OS H as
-- a physical operator, Wick analytic continuation, and the correct
-- conversion from -iH/hbar derivative to energy H on both carriers.
-- No unrelated finite clock fixture or arbitrary physical promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Quantum.TSVF as TSVF
import DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact as Bidi
import DASHI.Physics.Foundations.TSVFOSSameSelectedClockIterateExact as Clock
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

module _
  {F : Bidi.BidirectionallyAdmissibleHistoryFibre}
  {Q : TSVF.QuantumSurface}
  (E : TSVF.TSVFEnsemble Q)
  {Observable Point Scalar : Set}
  {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
  (reconstruction :
    OS.OSReconstructionAuthority Observable Point Scalar system)
  (Energy : Set)
  (clock : Clock.OriginalTSVFToOSClock {F} {Q} E
    {Observable} {Point} {Scalar} {system} reconstruction Energy)
  where

  ObserverState : Set
  ObserverState = TSVF.QuantumSurface.Ket Q

  ReconstructedState : Set
  ReconstructedState = Clock.OSState clock

  -- Reuse the existing two-sided selected state identification.
  J : ObserverState → ReconstructedState
  J = Clock.embedObserver clock

  record RealTimeDerivativeBridge : Set₁ where
    field
      Time : Set
      RealStep : Set
      samplesToZero : Nat → Time
      inverseRealStep : Nat → RealStep

      -- PHYSICAL real-time groups, separate from osStep and Euclidean T.
      observerUnitary : Time → ObserverState → ObserverState
      osUnitary : Time → ReconstructedState → ReconstructedState

      observerSubtract :
        ObserverState → ObserverState → ObserverState
      osSubtract :
        ReconstructedState → ReconstructedState → ReconstructedState
      observerScale : RealStep → ObserverState → ObserverState
      osScale : RealStep → ReconstructedState → ReconstructedState

      linearSubtract :
        ∀ a b →
        J (observerSubtract a b)
        ≡ osSubtract (J a) (J b)
      linearScale :
        ∀ scalar a →
        J (observerScale scalar a)
        ≡ osScale scalar (J a)

      realTimeGroupIntertwines :
        ∀ t a → J (observerUnitary t a)
                ≡ osUnitary t (J a)

      -- Physical selected operator meaning consumes the ORIGINAL OS
      -- H, not a second independently chosen Hamiltonian.
      observerGenerator : ObserverState → ObserverState
      osGeneratorFromOriginalHamiltonian :
        OS.Hamiltonian reconstruction →
        ReconstructedState → ReconstructedState

      ObserverConverges :
        (Nat → ObserverState) → ObserverState → Set
      OSConverges :
        (Nat → ReconstructedState) → ReconstructedState → Set

      -- True Hilbert unitaries are continuous, but physical Hilbert
      -- completion remains OPEN and hence these are inputs here.
      embeddingPreservesLimit :
        ∀ {sequence limit} →
        ObserverConverges sequence limit →
        OSConverges (λ n → J (sequence n)) (J limit)

      osConvergesRespectPointwise :
        ∀ {sequence other limit} →
        (∀ n → sequence n ≡ other n) →
        OSConverges sequence limit →
        OSConverges other limit

      osLimitUnique :
        ∀ {sequence x y} →
        OSConverges sequence x →
        OSConverges sequence y → x ≡ y

      ObserverGeneratorDomain : ObserverState → Set
      OSDomain : ReconstructedState → Set
      mappedDomain :
        ∀ a → ObserverGeneratorDomain a → OSDomain (J a)

      observerDerivativeExists :
        ∀ a → ObserverGeneratorDomain a →
        ObserverConverges
          (λ n →
            observerScale (inverseRealStep n)
              (observerSubtract
                (observerUnitary (samplesToZero n) a) a))
          (observerGenerator a)

      originalOSDerivativeExists :
        ∀ a → OSDomain a →
        OSConverges
          (λ n →
            osScale (inverseRealStep n)
              (osSubtract
                (osUnitary (samplesToZero n) a) a))
          (osGeneratorFromOriginalHamiltonian
            (OS.hamiltonian reconstruction) a)

  open RealTimeDerivativeBridge public

  observerDifferenceQuotient :
    (source : RealTimeDerivativeBridge) →
    Nat → ObserverState → ObserverState
  observerDifferenceQuotient source n a =
    observerScale source (inverseRealStep source n)
      (observerSubtract source
        (observerUnitary source (samplesToZero source n) a) a)

  osDifferenceQuotient :
    (source : RealTimeDerivativeBridge) →
    Nat → ReconstructedState → ReconstructedState
  osDifferenceQuotient source n a =
    osScale source (inverseRealStep source n)
      (osSubtract source
        (osUnitary source (samplesToZero source n) a) a)

  -- Derived for all n from the original J and real-time group equality.
  originalSelectedDifferenceQuotientsIntertwine :
    (source : RealTimeDerivativeBridge)
    (n : Nat) (a : ObserverState) →
    J (observerDifferenceQuotient source n a)
    ≡ osDifferenceQuotient source n (J a)
  originalSelectedDifferenceQuotientsIntertwine source n a =
    trans
      (linearScale source (inverseRealStep source n)
        (observerSubtract source
          (observerUnitary source (samplesToZero source n) a) a))
      (cong
        (osScale source (inverseRealStep source n))
        (trans
          (linearSubtract source
            (observerUnitary source (samplesToZero source n) a) a)
          (cong
            (λ v → osSubtract source v (J a))
            (realTimeGroupIntertwines source
              (samplesToZero source n) a))))

  -- Actual selected reconstructed Hamiltonian, not an H label:
  -- uniqueness of the OS strong limit proves equality of generators.
  originalSelectedStrongGeneratorIntertwines :
    (source : RealTimeDerivativeBridge)
    (a : ObserverState)
    (domain : ObserverGeneratorDomain source a) →
    J (observerGenerator source a)
    ≡
    osGeneratorFromOriginalHamiltonian source
      (OS.hamiltonian reconstruction) (J a)
  originalSelectedStrongGeneratorIntertwines source a domain =
    osLimitUnique source
      {sequence = λ n → osDifferenceQuotient source n (J a)}
      (osConvergesRespectPointwise source
        (λ n →
          originalSelectedDifferenceQuotientsIntertwine source n a)
        (embeddingPreservesLimit source
          (observerDerivativeExists source a domain)))
      (originalOSDerivativeExists source
        (J a) (mappedDomain source a domain))

  ------------------------------------------------------------------------
  -- Selected physical ENERGY H = i*hbar*dU/dt (Schrodinger convention).
  -- The previous theorem identifies the strong derivative generator
  -- K=-iH/hbar. Energy H requires the COMPLEX LINEAR, physically
  -- calibrated action factor i*hbar to commute with the SAME J.
  --
  -- This is not an automatic equivalence of the abstract original OS
  -- Hamiltonian carrier with a self-adjoint energy operator. The
  -- conversion laws below must come from the real physical Hilbert.
  ------------------------------------------------------------------------

  record PhysicalHbarEnergyConversion
      (source : RealTimeDerivativeBridge) : Set₁ where
    field
      ComplexActionScalar : Set
      iHbar : ComplexActionScalar

      observerComplexScale :
        ComplexActionScalar → ObserverState → ObserverState
      osComplexScale :
        ComplexActionScalar → ReconstructedState → ReconstructedState

      -- The ORIGINAL selected observer-state isometry must be
      -- complex-linear for H=i*hbar K to transport.
      selectedJComplexLinearAtIHbar :
        ∀ a →
        J (observerComplexScale iHbar a)
        ≡ osComplexScale iHbar (J a)

      observerPhysicalEnergyOperator :
        ObserverState → ObserverState
      observerEnergyIsSchrodingerGenerator :
        ∀ a →
        observerPhysicalEnergyOperator a
        ≡ observerComplexScale iHbar
             (observerGenerator source a)

      -- Meaning of the *same original* OS.hamiltonian, not a
      -- manufactured independent operator called H_OS.
      originalOSPhysicalEnergyOperator :
        OS.Hamiltonian reconstruction →
        ReconstructedState → ReconstructedState

      originalOSEnergyIsSchrodingerGenerator :
        ∀ a →
        originalOSPhysicalEnergyOperator
          (OS.hamiltonian reconstruction) a
        ≡
        osComplexScale iHbar
          (osGeneratorFromOriginalHamiltonian source
            (OS.hamiltonian reconstruction) a)

  open PhysicalHbarEnergyConversion public

  -- On the ACTUAL mapped strong-derivative domain, the same physical
  -- energy Hamiltonian is now derived using the source's complex
  -- linearity and the independently calibrated i*hbar conversion.
  originalSelectedPhysicalEnergyIntertwines :
    (source : RealTimeDerivativeBridge)
    (conversion : PhysicalHbarEnergyConversion source)
    (a : ObserverState)
    (domain : ObserverGeneratorDomain source a) →
    J (observerPhysicalEnergyOperator conversion a)
    ≡
    originalOSPhysicalEnergyOperator conversion
      (OS.hamiltonian reconstruction) (J a)
  originalSelectedPhysicalEnergyIntertwines
      source conversion a domain =
    trans
      (cong J
        (observerEnergyIsSchrodingerGenerator conversion a))
      (trans
        (selectedJComplexLinearAtIHbar conversion
          (observerGenerator source a))
        (trans
          (cong
            (osComplexScale conversion (iHbar conversion))
            (originalSelectedStrongGeneratorIntertwines
              source a domain))
          (sym
            (originalOSEnergyIsSchrodingerGenerator
              conversion (J a)))))

-- SOURCE conditional, KERNEL PENDING. In particular the original
-- OSReconstructionAuthority.Hamiltonian is presently just an abstract
-- carrier and its value: the genuinely physical Hilbert generator
-- interpretation is a substantial missing mathematical producer.
