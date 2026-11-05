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
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

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
      zeroTime : Time
      addTime : Time → Time → Time
      negateTime : Time → Time

      -- A physically nontrivial real one-parameter group rather
      -- than arbitrary names for two independently selected flows.
      RealStep : Set

      TimeConvergesToZero : (Nat → Time) → Set
      samplesToZero : Nat → Time
      selectedTimeSamplesConverge :
        TimeConvergesToZero samplesToZero
      inverseRealStep : Nat → RealStep

      -- PHYSICAL real-time groups, separate from osStep and Euclidean T.
      observerUnitary : Time → ObserverState → ObserverState
      osUnitary : Time → ReconstructedState → ReconstructedState

      observerZeroIsIdentity :
        ∀ a → observerUnitary zeroTime a ≡ a
      osZeroIsIdentity :
        ∀ a → osUnitary zeroTime a ≡ a
      observerAdditiveGroupLaw :
        ∀ t u a →
          observerUnitary (addTime t u) a
          ≡ observerUnitary t (observerUnitary u a)
      osAdditiveGroupLaw :
        ∀ t u a →
          osUnitary (addTime t u) a
          ≡ osUnitary t (osUnitary u a)
      observerTimeInverse :
        ∀ t a →
          observerUnitary (negateTime t) (observerUnitary t a)
          ≡ a
      osTimeInverse :
        ∀ t a →
          osUnitary (negateTime t) (osUnitary t a)
          ≡ a

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

      -- A non-vacuous source-specific selected ket: at minimum the
      -- ORIGINAL preselected forward state belongs to the domain.
      -- Empty-domain "proofs" are not accepted as a P07 population.
      originalSelectedForwardKetInDomain :
        ObserverGeneratorDomain (TSVF.forwardState E)

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

  -- This is the source-specialized ORIGINAL TSVF selected forward ket,
  -- not an arbitrary or empty observer domain.
  originalForwardKetStrongGeneratorIntertwines :
    (source : RealTimeDerivativeBridge) →
    J (observerGenerator source (TSVF.forwardState E))
    ≡
    osGeneratorFromOriginalHamiltonian source
      (OS.hamiltonian reconstruction) (J (TSVF.forwardState E))
  originalForwardKetStrongGeneratorIntertwines source =
    originalSelectedStrongGeneratorIntertwines
      source (TSVF.forwardState E)
      (originalSelectedForwardKetInDomain source)

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

  originalForwardKetPhysicalEnergyIntertwines :
    (source : RealTimeDerivativeBridge)
    (conversion : PhysicalHbarEnergyConversion source) →
    J (observerPhysicalEnergyOperator conversion
        (TSVF.forwardState E))
    ≡
    originalOSPhysicalEnergyOperator conversion
      (OS.hamiltonian reconstruction)
      (J (TSVF.forwardState E))
  originalForwardKetPhysicalEnergyIntertwines source conversion =
    originalSelectedPhysicalEnergyIntertwines
      source conversion (TSVF.forwardState E)
      (originalSelectedForwardKetInDomain source)

  ------------------------------------------------------------------------
  -- P07.L05--L07 / P11: BIDIRECTIONAL STRONG DERIVATIVE DOMAIN WELD.
  --
  -- The ORIGINAL clock contains a two-sided state isomorphism:
  --   J = embedObserver; decodeObserver (J x) = x;
  --   J (decodeObserver y) = y.
  -- This lets us pull the SAME real-time finite difference quotients
  -- back from OS to the selected observer, with no second embedding
  -- or inverse-H assumption.
  --
  -- Actual limits, physical topology, completeness, analytic Stone
  -- reconstruction and dense self-adjoint domains remain sourced
  -- physical premises. We DO derive the two-way differentiability
  -- equivalence and uniqueness of the observer strong derivative.
  ------------------------------------------------------------------------

  ObserverHasStrongDerivative :
    (source : RealTimeDerivativeBridge) →
    ObserverState → Set
  ObserverHasStrongDerivative source a =
    Σ ObserverState
      (λ derivative →
        ObserverConverges source
          (λ n → observerDifferenceQuotient source n a)
          derivative)

  OSHasStrongDerivative :
    (source : RealTimeDerivativeBridge) →
    ReconstructedState → Set
  OSHasStrongDerivative source y =
    Σ ReconstructedState
      (λ derivative →
        OSConverges source
          (λ n → osDifferenceQuotient source n y)
          derivative)

  -- Forward differentiability transport is a NEW theorem: it does
  -- not assume observer-generator equality or OS-generator equality.
  originalObserverStrongDifferentiabilityImpliesOS :
    (source : RealTimeDerivativeBridge)
    (a : ObserverState) →
    ObserverHasStrongDerivative source a →
    OSHasStrongDerivative source (J a)
  originalObserverStrongDifferentiabilityImpliesOS
      source a (derivative , convergence) =
    J derivative ,
    osConvergesRespectPointwise source
      (λ n → originalSelectedDifferenceQuotientsIntertwine source n a)
      (embeddingPreservesLimit source convergence)

  -- The ORIGINAL embedding is also INJECTIVE by decodeEmbed.
  -- Consequently uniqueness of the original OS strong limit
  -- implies uniqueness of the observer strong limit without
  -- postulating a second, independent observer uniqueness theorem.
  originalObserverStrongLimitUniqueFromOS :
    (source : RealTimeDerivativeBridge)
    {sequence : Nat → ObserverState}
    {x y : ObserverState} →
    ObserverConverges source sequence x →
    ObserverConverges source sequence y →
    x ≡ y
  originalObserverStrongLimitUniqueFromOS
      source {x = x} {y = y} first second =
    trans
      (sym (Clock.decodeEmbed clock x))
      (trans
        (cong (Clock.decodeObserver clock)
          (osLimitUnique source
            (embeddingPreservesLimit source first)
            (embeddingPreservesLimit source second)))
        (Clock.decodeEmbed clock y))

  -- Unlike an arbitrary 'backwards time' axiom, this is ONLY
  -- continuity of the ORIGINAL physical inverse identification.
  -- It must follow from a genuinely unitary onto J on a completed
  -- Hilbert topology, not merely from the old Set-level decode.
  record OriginalInverseHilbertContinuity
      (source : RealTimeDerivativeBridge) : Set₁ where
    field
      decodePreservesStrongLimit :
        ∀ {sequence limit} →
        OSConverges source sequence limit →
        ObserverConverges source
          (λ n → Clock.decodeObserver clock (sequence n))
          (Clock.decodeObserver clock limit)

      observerLimitRespectsPointwise :
        ∀ {sequence other limit} →
        (∀ n → sequence n ≡ other n) →
        ObserverConverges source sequence limit →
        ObserverConverges source other limit

      -- The true generator DOMAIN is defined by differentiability,
      -- not a freely chosen subset containing only the forward ket.
      observerDerivativeDomainComplete :
        ∀ a →
        ObserverHasStrongDerivative source a →
        ObserverGeneratorDomain source a

  open OriginalInverseHilbertContinuity public

  -- Converse finite-difference quotient transport follows entirely
  -- from the SAME original two-sided state isomorphism and earlier
  -- J-intertwiner. No extra inverse group intertwinement assumption.
  originalOSDifferenceQuotientsDecodeToObserver :
    (source : RealTimeDerivativeBridge)
    (n : Nat) (a : ObserverState) →
    Clock.decodeObserver clock
      (osDifferenceQuotient source n (J a))
    ≡
    observerDifferenceQuotient source n a
  originalOSDifferenceQuotientsDecodeToObserver source n a =
    trans
      (cong (Clock.decodeObserver clock)
        (sym (originalSelectedDifferenceQuotientsIntertwine source n a)))
      (Clock.decodeEmbed clock
        (observerDifferenceQuotient source n a))

  -- This is the core BIDI comparison for the ORIGINAL selected
  -- observer/OS state: a strong OS derivative determines an observer
  -- strong derivative using original decodeObserver and its topology.
  originalOSStrongDifferentiabilityImpliesObserver :
    (source : RealTimeDerivativeBridge)
    (inverse : OriginalInverseHilbertContinuity source)
    (a : ObserverState) →
    OSHasStrongDerivative source (J a) →
    ObserverHasStrongDerivative source a
  originalOSStrongDifferentiabilityImpliesObserver
      source inverse a (derivative , convergence) =
    Clock.decodeObserver clock derivative ,
    observerLimitRespectsPointwise inverse
      (λ n →
        originalOSDifferenceQuotientsDecodeToObserver source n a)
      (decodePreservesStrongLimit inverse convergence)

  -- Derive actual two-way DOMAIN equivalence; it is NOT asserted
  -- as an independent one-field same-H source identity.
  -- Domain-completeness and continuity of J-inverse remain the
  -- exact physical sublemmas the complete Hilbert must provide.
  originalObserverOSStrongGeneratorDomainsIff :
    (source : RealTimeDerivativeBridge)
    (inverse : OriginalInverseHilbertContinuity source)
    (a : ObserverState) →
    (ObserverGeneratorDomain source a →
      OSDomain source (J a))
    ×
    (OSDomain source (J a) →
      ObserverGeneratorDomain source a)
  originalObserverOSStrongGeneratorDomainsIff
      source inverse a =
    mappedDomain source a ,
    (λ osDomain →
      observerDerivativeDomainComplete inverse a
        (originalOSStrongDifferentiabilityImpliesObserver
          source inverse a
          (osGeneratorFromOriginalHamiltonian source
              (OS.hamiltonian reconstruction) (J a) ,
           originalOSDerivativeExists source
             (J a) osDomain)))

  -- Matching strong derivatives now holds ON THE ENTIRE selected
  -- generator domain (not only the original forward ket) in both
  -- directions. Combined with the earlier i*hbar theorem, this is
  -- the analytic part of the common H domain identification.
  -- It still requires genuine physical H, real time and topology.
  originalOSDomainGivesOriginalPhysicalEnergyEquality :
    (source : RealTimeDerivativeBridge)
    (inverse : OriginalInverseHilbertContinuity source)
    (conversion : PhysicalHbarEnergyConversion source)
    (a : ObserverState)
    (osDomain : OSDomain source (J a)) →
    J (observerPhysicalEnergyOperator conversion a)
    ≡
    originalOSPhysicalEnergyOperator conversion
      (OS.hamiltonian reconstruction) (J a)
  originalOSDomainGivesOriginalPhysicalEnergyEquality
      source inverse conversion a osDomain =
    originalSelectedPhysicalEnergyIntertwines
      source conversion a
      (observerDerivativeDomainComplete inverse a
        (originalOSStrongDifferentiabilityImpliesObserver
          source inverse a
          (osGeneratorFromOriginalHamiltonian source
              (OS.hamiltonian reconstruction) (J a) ,
           originalOSDerivativeExists source
             (J a) osDomain)))

  ------------------------------------------------------------------------
  -- P03/P07 strongest topology-compatible Pareto cut:
  -- DERIVE inverse strong-limit continuity from a genuinely matched
  -- distance/convergence source on the ORIGINAL J, rather than
  -- postulate decode continuity as an unrelated physical witness.
  --
  -- This is a SOURCE-level isometric topology specification. The
  -- proof of the comparison is independent of the numerical distance
  -- backend; constructing a real noncollapsed Hilbert norm with
  -- metric axioms, Cauchy completion, and the proper strong operator
  -- topology is STILL a separate physical/analytic requirement.
  ------------------------------------------------------------------------

  record OriginalIsometricStrongLimitSource
      (source : RealTimeDerivativeBridge) : Set₁ where
    field
      Distance : Set
      observerDistance : ObserverState → ObserverState → Distance
      osDistance : ReconstructedState → ReconstructedState → Distance

      -- ACTUAL same observer/OS isometry, not just pointwise equality
      -- of the two clock labels or one selected spectral value.
      selectedJPreservesDistances :
        ∀ a b →
        osDistance (J a) (J b) ≡ observerDistance a b

      DistanceConverges : (Nat → Distance) → Set

      distanceConvergenceRespectsPointwise :
        ∀ {seq other} →
        (∀ n → seq n ≡ other n) →
        DistanceConverges seq → DistanceConverges other

      -- Characterise convergence by distance-to-target on BOTH
      -- original physical carriers, not independent arbitrary
      -- boolean continuity tags. The actual norm/metric topology
      -- must be physically constructed outside this conditional file.
      observerConvergenceIntoDistance :
        ∀ {seq limit} →
        ObserverConverges source seq limit →
        DistanceConverges
          (λ n → observerDistance (seq n) limit)
      observerDistanceIntoConvergence :
        ∀ {seq limit} →
        DistanceConverges
          (λ n → observerDistance (seq n) limit) →
        ObserverConverges source seq limit

      osConvergenceIntoDistance :
        ∀ {seq limit} →
        OSConverges source seq limit →
        DistanceConverges
          (λ n → osDistance (seq n) limit)
      osDistanceIntoConvergence :
        ∀ {seq limit} →
        DistanceConverges
          (λ n → osDistance (seq n) limit) →
        OSConverges source seq limit

      -- The ORIGINAL physical operator domain must contain ALL
      -- strong derivatives, not merely the selected original ket.
      metricObserverDerivativeDomainComplete :
        ∀ a →
        ObserverHasStrongDerivative source a →
        ObserverGeneratorDomain source a

  open OriginalIsometricStrongLimitSource public

  -- On the ORIGINAL onto state identification, OS distances are
  -- *definitionally reducible* to observer distances by decoding.
  -- This is the same original J and its same-source decodeEmbed/
  -- embedDecode, not a second chosen isometric Hilbert equivalence.
  originalOSDistanceTransportedByDecoder :
    (source : RealTimeDerivativeBridge)
    (metric : OriginalIsometricStrongLimitSource source)
    (x y : ReconstructedState) →
    osDistance metric x y ≡
    observerDistance metric
      (Clock.decodeObserver clock x)
      (Clock.decodeObserver clock y)
  originalOSDistanceTransportedByDecoder source metric x y =
    trans
      (cong₂ (osDistance metric)
        (sym (Clock.embedDecode clock x))
        (sym (Clock.embedDecode clock y)))
      (selectedJPreservesDistances metric
        (Clock.decodeObserver clock x)
        (Clock.decodeObserver clock y))

  -- Matched J-isometry already makes the OBSERVER->OS strong
  -- continuity hypothesis follow from the declared distance law.
  originalMatchedDistancesForceForwardLimitContinuity :
    (source : RealTimeDerivativeBridge)
    (metric : OriginalIsometricStrongLimitSource source)
    {sequence : Nat → ObserverState}
    {limit : ObserverState} →
    ObserverConverges source sequence limit →
    OSConverges source
      (λ n → J (sequence n)) (J limit)
  originalMatchedDistancesForceForwardLimitContinuity
      source metric {sequence} {limit} convergence =
    osDistanceIntoConvergence metric
      (distanceConvergenceRespectsPointwise metric
        (λ n →
          sym (selectedJPreservesDistances metric
            (sequence n) limit))
        (observerConvergenceIntoDistance metric convergence))

  -- Actual original inverse continuity is NOT supplied directly:
  -- it is DERIVED from the same norm/distance and J's original
  -- two-sided inverse. Convergence predicates are both controlled
  -- by ONE DistanceConverges source.
  originalMatchedDistancesForceInverseLimitContinuity :
    (source : RealTimeDerivativeBridge)
    (metric : OriginalIsometricStrongLimitSource source)
    {sequence : Nat → ReconstructedState}
    {limit : ReconstructedState} →
    OSConverges source sequence limit →
    ObserverConverges source
      (λ n → Clock.decodeObserver clock (sequence n))
      (Clock.decodeObserver clock limit)
  originalMatchedDistancesForceInverseLimitContinuity
      source metric {sequence} {limit} convergence =
    observerDistanceIntoConvergence metric
      (distanceConvergenceRespectsPointwise metric
        (λ n →
          originalOSDistanceTransportedByDecoder
            source metric (sequence n) limit)
        (osConvergenceIntoDistance metric convergence))

  -- Every occurrence of observer pointwise sequence transport also
  -- follows from this SAME metric-convergence authority.
  originalMetricObserverLimitPointwiseTransport :
    (source : RealTimeDerivativeBridge)
    (metric : OriginalIsometricStrongLimitSource source)
    {sequence other : Nat → ObserverState}
    {limit : ObserverState} →
    (∀ n → sequence n ≡ other n) →
    ObserverConverges source sequence limit →
    ObserverConverges source other limit
  originalMetricObserverLimitPointwiseTransport
      source metric {sequence} {other} {limit}
      equal convergence =
    observerDistanceIntoConvergence metric
      (distanceConvergenceRespectsPointwise metric
        (λ n → cong
          (λ x → observerDistance metric x limit)
          (equal n))
        (observerConvergenceIntoDistance metric convergence))

  -- The previously required two-sided continuity/domain record is
  -- now an ACTUAL construction from the original J isometry and
  -- the single source's metric/distance-to-target topology.
  originalMetricSourceProducesInverseHilbertContinuity :
    (source : RealTimeDerivativeBridge)
    (metric : OriginalIsometricStrongLimitSource source) →
    OriginalInverseHilbertContinuity source
  originalMetricSourceProducesInverseHilbertContinuity
      source metric =
    record
      { OriginalInverseHilbertContinuity.decodePreservesStrongLimit =
          originalMatchedDistancesForceInverseLimitContinuity
            source metric
      ; OriginalInverseHilbertContinuity.observerLimitRespectsPointwise =
          originalMetricObserverLimitPointwiseTransport
            source metric
      ; OriginalInverseHilbertContinuity.observerDerivativeDomainComplete =
          metricObserverDerivativeDomainComplete metric
      }

  -- Final SOURCE theorem: matched actual selected distance topology
  -- yields the two-way ORIGINAL observer/OS physical generator
  -- DOMAIN identification without separately postulating decode
  -- continuity (even though physical metric/hilbert is missing).
  originalMatchedMetricSourceForcesTwoSidedGeneratorDomains :
    (source : RealTimeDerivativeBridge)
    (metric : OriginalIsometricStrongLimitSource source)
    (a : ObserverState) →
    (ObserverGeneratorDomain source a →
      OSDomain source (J a))
    ×
    (OSDomain source (J a) →
      ObserverGeneratorDomain source a)
  originalMatchedMetricSourceForcesTwoSidedGeneratorDomains
      source metric a =
    originalObserverOSStrongGeneratorDomainsIff
      source (originalMetricSourceProducesInverseHilbertContinuity
        source metric) a

-- SOURCE conditional, KERNEL PENDING. In particular the original
-- OSReconstructionAuthority.Hamiltonian is presently just an abstract
-- carrier and its value: the genuinely physical Hilbert generator
-- interpretation is a substantial missing mathematical producer.
