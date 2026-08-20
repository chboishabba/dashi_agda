module DASHI.Physics.Closure.NSTriadKNPressureDirectionHermitianOrthogonalityRound84Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND84 / PRESSURE-DIRECTION ORTHOGONALITY, RETAINED PACKET CLOSED
--
-- The Round84 advective/pressure split exposes the literal pressure RHS as a
-- longitudinal Leray term.  On every retained physical mode the velocity is
-- transverse.  Hence the pressure direction is Hermitian-orthogonal to both
-- the packet velocity and its |k|^2-weighted copy.
--
-- The key exact consequence is
--
--   Ddot_P = 0,
--
-- on any selected packet whose listed modes are proved to be retained by the
-- same finite Galerkin system.  Therefore the pressure contribution to the
-- compact-transfer relative-growth core simplifies from
--
--   R_P = qdot_P D - q Ddot_P
--
-- to
--
--   R_P = qdot_P D.
--
-- The explicit packet-membership witness is necessary: Round82's raw datum
-- stores an arbitrary packet-mode list, while physical transversality is only
-- available on retained modes.  No membership is silently reconstructed.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Literal
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift
import DASHI.Physics.Closure.NSTriadKNLiteralRHSRelativeGrowthSplitRound83Exact as R83
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP
import DASHI.Physics.Closure.NSTriadKNNonlinearRelativeGrowthAdvectivePressureSplitRound84Exact as Split

------------------------------------------------------------------------
-- Generic exact zero-pairing and transverse/longitudinal laws.
------------------------------------------------------------------------

hermitianZeroLeft :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.complex3Zero F) value ≡ C3.complexZero F
hermitianZeroLeft {F = F} value =
  trans
    (cong (λ first → C3.hermitianPairing3 first value)
      (sym (Hermitian.complex3ScaleZero (C3.complex3Zero F))))
    (trans
      (Scaling.hermitianPairingScaleLeft
        (C3.complexZero F) (C3.complex3Zero F) value)
      (trans
        (cong
          (λ scalar → C3.complexMultiply scalar
            (C3.hermitianPairing3 (C3.complex3Zero F) value))
          (Hermitian.complexConjugateZero F))
        (Hermitian.complexMultiplyZeroLeft
          (C3.hermitianPairing3 (C3.complex3Zero F) value))))

hermitianZeroRight :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex3 F) →
  C3.hermitianPairing3 value (C3.complex3Zero F) ≡ C3.complexZero F
hermitianZeroRight {F = F} value =
  trans
    (cong (C3.hermitianPairing3 value)
      (sym (Hermitian.complex3ScaleZero (C3.complex3Zero F))))
    (trans
      (Scaling.hermitianPairingScaleRight
        (C3.complexZero F) value (C3.complex3Zero F))
      (Hermitian.complexMultiplyZeroLeft
        (C3.hermitianPairing3 value (C3.complex3Zero F))))

hermitianTransverseLongitudinalRightZero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (mode : Z3.FourierMode)
    (value : C3.Complex3 F)
    (scalar : C3.Complex F) →
  C3.bilinearDot3 (C3.modeVector E mode) value ≡ C3.complexZero F →
  C3.hermitianPairing3 value
    (C3.complex3Scale scalar (C3.modeVector E mode))
  ≡ C3.complexZero F
hermitianTransverseLongitudinalRightZero {F = F}
    E mode value scalar transverse =
  trans
    (Scaling.hermitianPairingScaleRight
      scalar value (C3.modeVector E mode))
    (trans
      (cong (C3.complexMultiply scalar)
        (trans
          (Algebra.bilinearDot3Commutative
            (C3.complex3Conjugate value) (C3.modeVector E mode))
          (trans
            (Phase.modeDotConjugateValueIsConjugate E mode value)
            (trans
              (cong C3.complexConjugate transverse)
              (Hermitian.complexConjugateZero F)))))
      (Hermitian.complexMultiplyZeroRight scalar))

hermitianLongitudinalTransverseRightZero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (mode : Z3.FourierMode)
    (value : C3.Complex3 F)
    (scalar : C3.Complex F) →
  C3.bilinearDot3 (C3.modeVector E mode) value ≡ C3.complexZero F →
  C3.hermitianPairing3
    (C3.complex3Scale scalar (C3.modeVector E mode)) value
  ≡ C3.complexZero F
hermitianLongitudinalTransverseRightZero {F = F}
    E mode value scalar transverse =
  trans
    (Scaling.hermitianPairingScaleLeft
      scalar (C3.modeVector E mode) value)
    (trans
      (cong
        (C3.complexMultiply (C3.complexConjugate scalar))
        (trans
          (Hermitian.realModePairingIsBilinear E mode value)
          transverse))
      (Hermitian.complexMultiplyZeroRight (C3.complexConjugate scalar)))

------------------------------------------------------------------------
-- Each literal pressure ordered term is longitudinal in its output mode.
------------------------------------------------------------------------

lerayRankOneScalar :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
lerayRankOneScalar {F = F} {E = E} {I = I} system incidence =
  C3.complexMultiply
    (C3.realEmbed F (C3.inverseNormSquared I (Physical.k incidence)))
    (C3.bilinearDot3
      (C3.modeVector E (Physical.k incidence))
      (AP.rawOrderedValue system incidence))

pressureOrderedTermHermitianRightZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (value : C3.Complex3 F) →
  C3.bilinearDot3 (C3.modeVector E (Physical.k incidence)) value
    ≡ C3.complexZero F →
  C3.hermitianPairing3 value (AP.pressureOrderedTerm system incidence)
    ≡ C3.complexZero F
pressureOrderedTermHermitianRightZero {F = F} {E = E}
    system incidence value transverse =
  trans
    (cong (C3.hermitianPairing3 value)
      (AP.pressureOrderedTermIsPlusImaginaryRankOne system incidence))
    (trans
      (Scaling.hermitianPairingScaleRight
        (C3.complexI F) value (AP.lerayRankOneCorrection system incidence))
      (trans
        (cong (C3.complexMultiply (C3.complexI F))
          (hermitianTransverseLongitudinalRightZero
            E (Physical.k incidence) value
            (lerayRankOneScalar system incidence) transverse))
        (Hermitian.complexMultiplyZeroRight (C3.complexI F))))

pressureOrderedTermHermitianLeftZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (value : C3.Complex3 F) →
  C3.bilinearDot3 (C3.modeVector E (Physical.k incidence)) value
    ≡ C3.complexZero F →
  C3.hermitianPairing3 (AP.pressureOrderedTerm system incidence) value
    ≡ C3.complexZero F
pressureOrderedTermHermitianLeftZero {F = F} {E = E}
    system incidence value transverse =
  trans
    (cong (λ first → C3.hermitianPairing3 first value)
      (AP.pressureOrderedTermIsPlusImaginaryRankOne system incidence))
    (trans
      (Scaling.hermitianPairingScaleLeft
        (C3.complexI F) (AP.lerayRankOneCorrection system incidence) value)
      (trans
        (cong
          (λ pair → C3.complexMultiply
            (C3.complexConjugate (C3.complexI F)) pair)
          (hermitianLongitudinalTransverseRightZero
            E (Physical.k incidence) value
            (lerayRankOneScalar system incidence) transverse))
        (Hermitian.complexMultiplyZeroRight
          (C3.complexConjugate (C3.complexI F)))))

pressureListHermitianRightZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (incidences : List Physical.PhysicalTriadIncidence)
    (value : C3.Complex3 F) →
  C3.bilinearDot3 (C3.modeVector E output) value ≡ C3.complexZero F →
  (∀ incidence → incidence Cube.∈ incidences → Physical.k incidence ≡ output) →
  C3.hermitianPairing3 value
    (Audit.sumVectors (AP.mapPressureTerms system incidences))
  ≡ C3.complexZero F
pressureListHermitianRightZero system output [] value transverse outputs =
  hermitianZeroRight value
pressureListHermitianRightZero {F = F} {E = E}
    system output (incidence ∷ rest) value transverse outputs =
  let
    outputEq = outputs incidence (Cube.here refl)
    headTransverse = subst
      (λ selected →
        C3.bilinearDot3 (C3.modeVector E selected) value ≡ C3.complexZero F)
      (sym outputEq) transverse
  in
  trans
    (Additive.hermitianPairingAddRight value
      (AP.pressureOrderedTerm system incidence)
      (Audit.sumVectors (AP.mapPressureTerms system rest)))
    (trans
      (cong₂ C3.complexAdd
        (pressureOrderedTermHermitianRightZero
          system incidence value headTransverse)
        (pressureListHermitianRightZero system output rest value transverse
          (λ selected member → outputs selected (Cube.there member))))
      (Field.complexAddZeroLeft (C3.complexZero F)))

pressureListHermitianLeftZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (incidences : List Physical.PhysicalTriadIncidence)
    (value : C3.Complex3 F) →
  C3.bilinearDot3 (C3.modeVector E output) value ≡ C3.complexZero F →
  (∀ incidence → incidence Cube.∈ incidences → Physical.k incidence ≡ output) →
  C3.hermitianPairing3
    (Audit.sumVectors (AP.mapPressureTerms system incidences)) value
  ≡ C3.complexZero F
pressureListHermitianLeftZero system output [] value transverse outputs =
  hermitianZeroLeft value
pressureListHermitianLeftZero {F = F} {E = E}
    system output (incidence ∷ rest) value transverse outputs =
  let
    outputEq = outputs incidence (Cube.here refl)
    headTransverse = subst
      (λ selected →
        C3.bilinearDot3 (C3.modeVector E selected) value ≡ C3.complexZero F)
      (sym outputEq) transverse
  in
  trans
    (Additive.hermitianPairingAddLeft
      (AP.pressureOrderedTerm system incidence)
      (Audit.sumVectors (AP.mapPressureTerms system rest)) value)
    (trans
      (cong₂ C3.complexAdd
        (pressureOrderedTermHermitianLeftZero
          system incidence value headTransverse)
        (pressureListHermitianLeftZero system output rest value transverse
          (λ selected member → outputs selected (Cube.there member))))
      (Field.complexAddZeroLeft (C3.complexZero F)))

pressureRHSOrthogonalRightToTransverse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.bilinearDot3 (C3.modeVector E output) value ≡ C3.complexZero F →
  C3.hermitianPairing3 value (AP.pressureNonlinearity system output)
  ≡ C3.complexZero F
pressureRHSOrthogonalRightToTransverse system output value transverse =
  pressureListHermitianRightZero system output
    (Audit.concreteTriadsAt system output) value transverse
    (λ incidence member → Audit.concreteTriadsAtOutputAgreement member)

pressureRHSOrthogonalLeftToTransverse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.bilinearDot3 (C3.modeVector E output) value ≡ C3.complexZero F →
  C3.hermitianPairing3 (AP.pressureNonlinearity system output) value
  ≡ C3.complexZero F
pressureRHSOrthogonalLeftToTransverse system output value transverse =
  pressureListHermitianLeftZero system output
    (Audit.concreteTriadsAt system output) value transverse
    (λ incidence member → Audit.concreteTriadsAtOutputAgreement member)

------------------------------------------------------------------------
-- Same-object retained packet and exact Ddot_P = 0.
------------------------------------------------------------------------

record RetainedPressurePacketDatum
    {r : Level}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) : Set (lsuc r) where
  field
    packetModesAreRetained : ∀ mode →
      mode Cube.∈ Drift.packetModes datum →
      mode Cube.∈ Audit.modes (Drift.finiteSystem datum)

open RetainedPressurePacketDatum public

retainedVelocityTransverse :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum)
    mode → mode Cube.∈ Drift.packetModes datum →
  C3.bilinearDot3
    (C3.modeVector
      (Literal.physicalEmbedding (Drift.physicalSystem datum)) mode)
    (Audit.velocity (Drift.finiteSystem datum) mode)
  ≡ C3.complexZero (LP.realField model)
retainedVelocityTransverse datum retained mode member =
  Literal.retainedVelocityTransverse
    (Drift.physicalSystem datum) mode
    (packetModesAreRetained retained mode member)

pressurePacketPairingLeftZero :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum)
    mode → mode Cube.∈ Drift.packetModes datum →
  C3.hermitianPairing3
    (Packet.packetField model (Drift.shell datum) (Split.pressureRHS datum) mode)
    (Drift.weightedPacketField datum
      (Audit.velocity (Drift.finiteSystem datum)) mode)
  ≡ C3.complexZero (LP.realField model)
pressurePacketPairingLeftZero {model = model} datum retained mode member
  with LP.shellSelect model (Drift.shell datum) mode
... | true =
  pressureRHSOrthogonalLeftToTransverse
    (Drift.finiteSystem datum) mode
    (C3.complex3Scale
      (Drift.modeDissipationWeight datum mode)
      (Audit.velocity (Drift.finiteSystem datum) mode))
    (trans
      (Scaling.bilinearDot3ScaleRight
        (Drift.modeDissipationWeight datum mode)
        (C3.modeVector
          (Literal.physicalEmbedding (Drift.physicalSystem datum)) mode)
        (Audit.velocity (Drift.finiteSystem datum) mode))
      (trans
        (cong (C3.complexMultiply (Drift.modeDissipationWeight datum mode))
          (retainedVelocityTransverse datum retained mode member))
        (Hermitian.complexMultiplyZeroRight
          (Drift.modeDissipationWeight datum mode))))
... | false =
  hermitianZeroLeft
    (Drift.weightedPacketField datum
      (Audit.velocity (Drift.finiteSystem datum)) mode)

pressurePacketPairingRightZero :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum)
    mode → mode Cube.∈ Drift.packetModes datum →
  C3.hermitianPairing3
    (Drift.packetVelocity datum mode)
    (Drift.weightedPacketField datum (Split.pressureRHS datum) mode)
  ≡ C3.complexZero (LP.realField model)
pressurePacketPairingRightZero {model = model} datum retained mode member
  with LP.shellSelect model (Drift.shell datum) mode
... | true =
  trans
    (Scaling.hermitianPairingScaleRight
      (Drift.modeDissipationWeight datum mode)
      (Audit.velocity (Drift.finiteSystem datum) mode)
      (Split.pressureRHS datum mode))
    (trans
      (cong (C3.complexMultiply (Drift.modeDissipationWeight datum mode))
        (pressureRHSOrthogonalRightToTransverse
          (Drift.finiteSystem datum) mode
          (Audit.velocity (Drift.finiteSystem datum) mode)
          (retainedVelocityTransverse datum retained mode member)))
      (Hermitian.complexMultiplyZeroRight
        (Drift.modeDissipationWeight datum mode)))
... | false =
  hermitianZeroLeft
    (Drift.weightedPacketField datum (Split.pressureRHS datum) mode)

finitePressurePacketPairingLeftZero :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum) →
  Packet.finiteHermitianPairing
    (Drift.packetModes datum)
    (Packet.packetField model (Drift.shell datum) (Split.pressureRHS datum))
    (Drift.weightedPacketField datum
      (Audit.velocity (Drift.finiteSystem datum)))
  ≡ C3.complexZero (LP.realField model)
finitePressurePacketPairingLeftZero {model = model} datum retained =
  go (Drift.packetModes datum)
    (λ mode member → pressurePacketPairingLeftZero datum retained mode member)
  where
  F = LP.realField model

  go :
    (modes : List Z3.FourierMode) →
    (∀ mode → mode Cube.∈ modes →
      C3.hermitianPairing3
        (Packet.packetField model (Drift.shell datum) (Split.pressureRHS datum) mode)
        (Drift.weightedPacketField datum
          (Audit.velocity (Drift.finiteSystem datum)) mode)
      ≡ C3.complexZero F) →
    Packet.finiteHermitianPairing modes
      (Packet.packetField model (Drift.shell datum) (Split.pressureRHS datum))
      (Drift.weightedPacketField datum
        (Audit.velocity (Drift.finiteSystem datum)))
    ≡ C3.complexZero F
  go [] pointwise = refl
  go (mode ∷ modes) pointwise =
    trans
      (cong₂ C3.complexAdd
        (pointwise mode (Cube.here refl))
        (go modes
          (λ selected member → pointwise selected (Cube.there member))))
      (Field.complexAddZeroLeft (C3.complexZero F))

finitePressurePacketPairingRightZero :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum) →
  Packet.finiteHermitianPairing
    (Drift.packetModes datum)
    (Drift.packetVelocity datum)
    (Drift.weightedPacketField datum (Split.pressureRHS datum))
  ≡ C3.complexZero (LP.realField model)
finitePressurePacketPairingRightZero {model = model} datum retained =
  go (Drift.packetModes datum)
    (λ mode member → pressurePacketPairingRightZero datum retained mode member)
  where
  F = LP.realField model

  go :
    (modes : List Z3.FourierMode) →
    (∀ mode → mode Cube.∈ modes →
      C3.hermitianPairing3
        (Drift.packetVelocity datum mode)
        (Drift.weightedPacketField datum (Split.pressureRHS datum) mode)
      ≡ C3.complexZero F) →
    Packet.finiteHermitianPairing modes
      (Drift.packetVelocity datum)
      (Drift.weightedPacketField datum (Split.pressureRHS datum))
    ≡ C3.complexZero F
  go [] pointwise = refl
  go (mode ∷ modes) pointwise =
    trans
      (cong₂ C3.complexAdd
        (pointwise mode (Cube.here refl))
        (go modes
          (λ selected member → pointwise selected (Cube.there member))))
      (Field.complexAddZeroLeft (C3.complexZero F))

complexPressureDissipationTangentZero :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum) →
  R83.complexDissipationTangentComponent datum (Split.pressureRHS datum)
  ≡ C3.complexZero (LP.realField model)
complexPressureDissipationTangentZero {model = model} datum retained =
  trans
    (cong₂ C3.complexAdd
      (finitePressurePacketPairingLeftZero datum retained)
      (finitePressurePacketPairingRightZero datum retained))
    (Field.complexAddZeroLeft (C3.complexZero (LP.realField model)))

rawPressureDissipationTangentZero :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum) →
  Split.rawDissipationTangentPressure datum ≡ C3.zero (LP.realField model)
rawPressureDissipationTangentZero datum retained =
  trans (cong C3.real (complexPressureDissipationTangentZero datum retained)) refl

pressureRelativeGrowthReducesToTransferTimesDissipation :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum) →
  Split.pressureRelativeGrowthCore datum
  ≡ C3.multiply (LP.realField model)
      (Split.rawTransferTangentPressure datum)
      (Drift.rawDissipation datum)
pressureRelativeGrowthReducesToTransferTimesDissipation {model = model}
    datum retained
  rewrite rawPressureDissipationTangentZero datum retained =
  P.R.solve 3
    (λ qdot d q →
      ((qdot P.R.⊗ d)
        P.R.⊕ P.R.⊝ (q P.R.⊗ P.R.Κ (C3.zero (LP.realField model))))
      P.R.⊜ (qdot P.R.⊗ d))
    refl
    (Split.rawTransferTangentPressure datum)
    (Drift.rawDissipation datum)
    (Drift.rawTransfer datum)
  where
  module P = Field.Polynomial (LP.realField model)

round84PressureDirectionHermitianOrthogonalityConstructed : Bool
round84PressureDirectionHermitianOrthogonalityConstructed = true

round84RetainedPacketPressureDissipationTangentZero : Bool
round84RetainedPacketPressureDissipationTangentZero = true

round84PressureRelativeGrowthReducesToTransferTimesDissipation : Bool
round84PressureRelativeGrowthReducesToTransferTimesDissipation = true

round84RetainedPacketPressureDissipationTangentZeroIsTrue :
  round84RetainedPacketPressureDissipationTangentZero ≡ true
round84RetainedPacketPressureDissipationTangentZeroIsTrue = refl

round84PressureRelativeGrowthReducesToTransferTimesDissipationIsTrue :
  round84PressureRelativeGrowthReducesToTransferTimesDissipation ≡ true
round84PressureRelativeGrowthReducesToTransferTimesDissipationIsTrue = refl
