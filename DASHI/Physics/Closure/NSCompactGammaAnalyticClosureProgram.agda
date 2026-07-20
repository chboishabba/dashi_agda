module DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram where

open import Agda.Primitive using (Level; lzero; Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaOffPacketTriadMajorization as Major
import DASHI.Physics.Closure.NSCompactGammaDifferentiatedTriadInstantiation as Triads
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSCompactGammaOffPacketTailDecayBridge as Tail
import DASHI.Physics.Closure.NSCompactGammaGalerkinLimitBridge as Galerkin
import DASHI.Physics.Closure.NSCompactGammaAdmissiblePreservation as Admissible
import DASHI.Physics.Closure.NSCompactGammaBKMTimeIntegrability as BKM

------------------------------------------------------------------------
-- Cross-pollinated compact-Gamma analytic closure.
--
-- The earlier version of this module carried five opaque records, including an
-- arbitrary scalar-valued "full shell row bound", an undifferentiated Galerkin
-- convergence premise, wholesale path admissibility, and a free integrability
-- envelope.  The repository now has stronger owners for every one of those
-- seams.  This module composes those owners without weakening them.
------------------------------------------------------------------------

record AdmissibleInvariantRegionCertificate
    (Time State Shell : Set)
    (O : Admissible.OrderedScalar lzero)
    (S : Admissible.CompactGammaSystem O State Shell)
    (B : Admissible.CompactGammaThresholds O)
    (selection : Admissible.ShellSelection Shell)
    (path : Admissible.Path Time State)
    (continuityStructure : Admissible.ContinuityStructure Time O) : Setω where
  field
    continuity :
      ∀ K → Admissible.UsedShell selection K →
      Admissible.CompactGammaPathContinuity
        continuityStructure S path K

    boundaryEstimate :
      ∀ K → Admissible.UsedShell selection K →
      Admissible.BoundaryDerivativeEstimate {O = O} Time

    logarithmicEnergyControl :
      ∀ K → Admissible.UsedShell selection K →
      Admissible.LogarithmicModulusIntegration {O = O} Time

    packetEnergyPositivity :
      ∀ K → Admissible.UsedShell selection K →
      Admissible.PacketEnergyPositivity S path K

    -- The no-first-exit input is produced from the four analytic leaves above;
    -- it is not accepted independently.
    deriveNoFirstExit :
      ∀ K (used : Admissible.UsedShell selection K) →
      Admissible.CompactGammaPathContinuity
        continuityStructure S path K →
      Admissible.BoundaryDerivativeEstimate {O = O} Time →
      Admissible.LogarithmicModulusIntegration {O = O} Time →
      Admissible.PacketEnergyPositivity S path K →
      Admissible.NoFirstExitInputs {S = S} {B = B} path K

    firstExitCompleteness :
      ∀ K → Admissible.UsedShell selection K →
      Admissible.FirstExitCompleteness S B path K

open AdmissibleInvariantRegionCertificate public

noFirstExitInputsFromAnalyticLeaves :
  ∀ {Time State Shell : Set}
    {O : Admissible.OrderedScalar lzero}
    {S : Admissible.CompactGammaSystem O State Shell}
    {B : Admissible.CompactGammaThresholds O}
    {selection : Admissible.ShellSelection Shell}
    {path : Admissible.Path Time State}
    {continuityStructure : Admissible.ContinuityStructure Time O} →
  (I : AdmissibleInvariantRegionCertificate
    Time State Shell O S B selection path continuityStructure) →
  ∀ K (used : Admissible.UsedShell selection K) →
  Admissible.NoFirstExitInputs {S = S} {B = B} path K
noFirstExitInputsFromAnalyticLeaves I K used =
  deriveNoFirstExit I K used
    (continuity I K used)
    (boundaryEstimate I K used)
    (logarithmicEnergyControl I K used)
    (packetEnergyPositivity I K used)

admissibilityPreservedAtEveryUsedShell :
  ∀ {Time State Shell : Set}
    {O : Admissible.OrderedScalar lzero}
    {S : Admissible.CompactGammaSystem O State Shell}
    {B : Admissible.CompactGammaThresholds O}
    {selection : Admissible.ShellSelection Shell}
    {path : Admissible.Path Time State}
    {continuityStructure : Admissible.ContinuityStructure Time O} →
  (I : AdmissibleInvariantRegionCertificate
    Time State Shell O S B selection path continuityStructure) →
  ∀ time →
  Admissible.ShellFamilyAdmissible S B selection
    (Admissible.at path time)
admissibilityPreservedAtEveryUsedShell I =
  Admissible.simultaneousShellPreservation
    (firstExitCompleteness I)
    (noFirstExitInputsFromAnalyticLeaves I)

------------------------------------------------------------------------
-- Uniform Galerkin preservation and closed compactness-limit passage.
------------------------------------------------------------------------

record GalerkinAdmissibilityLimitCertificate
    (Cutoff Time State Shell : Set)
    (O : Admissible.OrderedScalar lzero)
    (S : Admissible.CompactGammaSystem O State Shell)
    (B : Admissible.CompactGammaThresholds O)
    (selection : Admissible.ShellSelection Shell)
    (family : Admissible.GalerkinFamily Cutoff Time State)
    (limitPath : Admissible.Path Time State) : Setω where
  field
    uniformPreservation :
      Admissible.UniformGalerkinPreservation S B selection family

    compactnessLimit :
      Admissible.GalerkinCompactnessLimit family limitPath

    closedAdmissibleLimit :
      Admissible.ClosedAdmissibleInequalities
        S B selection family limitPath compactnessLimit

open GalerkinAdmissibilityLimitCertificate public

galerkinAdmissibilityPassesToContinuum :
  ∀ {Cutoff Time State Shell : Set}
    {O : Admissible.OrderedScalar lzero}
    {S : Admissible.CompactGammaSystem O State Shell}
    {B : Admissible.CompactGammaThresholds O}
    {selection : Admissible.ShellSelection Shell}
    {family : Admissible.GalerkinFamily Cutoff Time State}
    {limitPath : Admissible.Path Time State} →
  GalerkinAdmissibilityLimitCertificate
    Cutoff Time State Shell O S B selection family limitPath →
  ∀ time →
  Admissible.ShellFamilyAdmissible S B selection
    (Admissible.at limitPath time)
galerkinAdmissibilityPassesToContinuum I =
  Admissible.galerkinPreservationPassesToLimit
    (uniformPreservation I)
    (closedAdmissibleLimit I)

------------------------------------------------------------------------
-- Coherence of the BKM path with the invariant-region path.  The BKM module is
-- intentionally self-contained, so the adapter records the exact carrier map
-- and path commuting square rather than identifying the two paths by prose.
------------------------------------------------------------------------

record CompactGammaBKMCoherence
    (Time State : Set)
    (path : Admissible.Path Time State)
    (A : AbsorptionArithmetic) : Setω where
  field
    bkmData :
      BKM.CompactGammaBKMData
        {lzero} {lzero} {lzero} {lzero} {lzero}

    mapTime : BKM.Time bkmData → Time
    mapState : BKM.State bkmData → State

    pathCommutes :
      ∀ time →
      mapState (BKM.path bkmData time) ≡
      Admissible.at path (mapTime time)

    ValueCoherent : BKM.Value bkmData → Scalar A → Set
    envelopeCoherent : Set
    envelopeCoherence : envelopeCoherent

open CompactGammaBKMCoherence public

------------------------------------------------------------------------
-- Final proof-relevant package.  Every field is now owned by the strongest
-- repository module available for that lane.
------------------------------------------------------------------------

record CompactGammaAnalyticClosure : Setω where
  field
    PairAtom Mode Vector Radius : Set

    arithmetic : AbsorptionArithmetic
    finiteMajorantArithmetic :
      Major.FiniteMajorantArithmetic arithmetic

    differentiatedTriads :
      Triads.DifferentiatedTriadAtomFamily
        PairAtom Mode Vector arithmetic finiteMajorantArithmetic

    fullShellFamily :
      FullShell.FullShellFourierFamily
        {i = lzero} Mode (Scalar arithmetic)

    fullShellProgram :
      FullShell.FullShellSchurProgram fullShellFamily

    tailProductArithmetic : Tail.TailProductArithmetic arithmetic
    radiusSplits : Tail.RadiusIndexedOffPacketSplit Radius arithmetic

    quantitativeTailDecay :
      Tail.UniformAnalyticTailDecay
        arithmetic tailProductArithmetic radiusSplits

    sequentialOrderClosure :
      Galerkin.SequentialOrderClosure arithmetic

    galerkinCompactnessAndIdentification :
      Galerkin.ActualGalerkinCompactGammaFamily
        arithmetic sequentialOrderClosure

    Time State Shell Cutoff : Set
    orderedScalar : Admissible.OrderedScalar lzero
    gammaSystem :
      Admissible.CompactGammaSystem orderedScalar State Shell
    thresholds : Admissible.CompactGammaThresholds orderedScalar
    shellSelection : Admissible.ShellSelection Shell
    solutionPath : Admissible.Path Time State
    continuityStructure :
      Admissible.ContinuityStructure Time orderedScalar

    invariantRegion :
      AdmissibleInvariantRegionCertificate
        Time State Shell orderedScalar gammaSystem thresholds
        shellSelection solutionPath continuityStructure

    galerkinPaths : Admissible.GalerkinFamily Cutoff Time State
    limitPath : Admissible.Path Time State

    admissibleGalerkinLimit :
      GalerkinAdmissibilityLimitCertificate
        Cutoff Time State Shell orderedScalar gammaSystem thresholds
        shellSelection galerkinPaths limitPath

    limitPathMatchesSolutionPath :
      ∀ time →
      Admissible.at limitPath time ≡ Admissible.at solutionPath time

    bkmCoherence :
      CompactGammaBKMCoherence Time State solutionPath arithmetic

open CompactGammaAnalyticClosure public

------------------------------------------------------------------------
-- Exported consequences: local majorization, exact full-shell Schur sums,
-- quantitative tail decay, actual Galerkin passage, invariant-region closure,
-- and final BKM continuation.
------------------------------------------------------------------------

closureNearResponseMajorized :
  (P : CompactGammaAnalyticClosure) →
  _≤_ (arithmetic P)
    (Triads.concreteNearResponse (differentiatedTriads P))
    (Triads.majorantActionOutput (differentiatedTriads P))
closureNearResponseMajorized P =
  Triads.analyticTriadsMajorizeNearResponse
    (arithmetic P)
    (finiteMajorantArithmetic P)
    (differentiatedTriads P)

closureFullShellRowEstimate :
  (P : CompactGammaAnalyticClosure) →
  (K N : Nat) →
  (target : Mode P) →
  _≤_ (FullShell.fullShellKernelAt (fullShellFamily P) K N)
    (FullShell.rowWeightedSum
      (FullShell.fullShellKernelAt (fullShellFamily P) K N)
      target)
    (FullShell.multiply
      (FullShell.fullShellKernelAt (fullShellFamily P) K N)
      (FullShell.rowConstant
        (FullShell.certificateAt
          (FullShell.uniformSchur (fullShellProgram P)) K N))
      (FullShell.rowWeight
        (FullShell.fullShellKernelAt (fullShellFamily P) K N)
        target))
closureFullShellRowEstimate P =
  FullShell.fullShellRowEstimate
    (FullShell.uniformSchur (fullShellProgram P))

closureFullShellColumnEstimate :
  (P : CompactGammaAnalyticClosure) →
  (K N : Nat) →
  (source : Mode P) →
  _≤_ (FullShell.fullShellKernelAt (fullShellFamily P) K N)
    (FullShell.columnWeightedSum
      (FullShell.fullShellKernelAt (fullShellFamily P) K N)
      source)
    (FullShell.multiply
      (FullShell.fullShellKernelAt (fullShellFamily P) K N)
      (FullShell.columnConstant
        (FullShell.certificateAt
          (FullShell.uniformSchur (fullShellProgram P)) K N))
      (FullShell.colWeight
        (FullShell.fullShellKernelAt (fullShellFamily P) K N)
        source))
closureFullShellColumnEstimate P =
  FullShell.fullShellColumnEstimate
    (FullShell.uniformSchur (fullShellProgram P))

closureQuantitativeTailBound :
  (P : CompactGammaAnalyticClosure) →
  (radius : Radius P) →
  _≤_ (arithmetic P)
    (Tail.farShellTail
      (Tail.splitAt (radiusSplits P) radius))
    (Tail._·_ (tailProductArithmetic P)
      (Tail.epsilon
        (Tail.rate (Tail.scale (quantitativeTailDecay P))) radius)
      (Tail._·_ (tailProductArithmetic P)
        (Tail.shellEnergy
          (Tail.scale (quantitativeTailDecay P)))
        (Tail.tangentNorm
          (Tail.scale (quantitativeTailDecay P)))))
closureQuantitativeTailBound P =
  Tail.quantitativeTailBound (quantitativeTailDecay P)

closureTailVanishesInOrder :
  (P : CompactGammaAnalyticClosure) →
  Tail.OrderVanishingTail (arithmetic P) (radiusSplits P)
closureTailVanishesInOrder P =
  Tail.quantitativeDecayToOrderVanishingTail
    (arithmetic P)
    (tailProductArithmetic P)
    (radiusSplits P)
    (quantitativeTailDecay P)

closureLogModulusPassesToContinuum :
  (P : CompactGammaAnalyticClosure) →
  _≤_ (arithmetic P)
    (Galerkin.absoluteLogDerivative
      (Galerkin.setting (galerkinCompactnessAndIdentification P))
      (Galerkin.continuumSolution
        (Galerkin.setting (galerkinCompactnessAndIdentification P))
        (Galerkin.evaluationTime
          (Galerkin.compactGammaLimit
            (galerkinCompactnessAndIdentification P))))
      (Galerkin.tangent
        (Galerkin.compactGammaLimit
          (galerkinCompactnessAndIdentification P))))
    (Galerkin.modulusBudget
      (Galerkin.setting (galerkinCompactnessAndIdentification P))
      (Galerkin.continuumSolution
        (Galerkin.setting (galerkinCompactnessAndIdentification P))
        (Galerkin.evaluationTime
          (Galerkin.compactGammaLimit
            (galerkinCompactnessAndIdentification P))))
      (Galerkin.tangent
        (Galerkin.compactGammaLimit
          (galerkinCompactnessAndIdentification P))))
closureLogModulusPassesToContinuum P =
  Galerkin.actualGalerkinLogModulusPassesToContinuum
    (arithmetic P)
    (sequentialOrderClosure P)
    (galerkinCompactnessAndIdentification P)

closureAdmissibilityPreserved :
  (P : CompactGammaAnalyticClosure) →
  ∀ time →
  Admissible.ShellFamilyAdmissible
    (gammaSystem P)
    (thresholds P)
    (shellSelection P)
    (Admissible.at (solutionPath P) time)
closureAdmissibilityPreserved P =
  admissibilityPreservedAtEveryUsedShell (invariantRegion P)

closureGalerkinAdmissibilityPassesToLimit :
  (P : CompactGammaAnalyticClosure) →
  ∀ time →
  Admissible.ShellFamilyAdmissible
    (gammaSystem P)
    (thresholds P)
    (shellSelection P)
    (Admissible.at (limitPath P) time)
closureGalerkinAdmissibilityPassesToLimit P =
  galerkinAdmissibilityPassesToContinuum (admissibleGalerkinLimit P)

closureBKMContinuation :
  (P : CompactGammaAnalyticClosure) →
  BKM.Continuation (bkmData (bkmCoherence P))
closureBKMContinuation P =
  BKM.compactGammaBKMContinuation (bkmData (bkmCoherence P))
