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
-- ROUND84 / PRESSURE-DIRECTION ORTHOGONALITY
--
-- The companion Round84 RHS split exposes the literal pressure contribution as
-- a scalar multiple of the output wave-vector.  The physical velocity carrier
-- is transverse to that wave-vector.  This module proves on the repository's
-- exact Hermitian carrier that the two are orthogonal in BOTH pairing orders:
--
--   <u_k , longitudinal_k> = 0,
--   <longitudinal_k , u_k> = 0.
--
-- It then lifts the result through the exact physical output fibre to the
-- summed pressure RHS.  Consequently any retained transverse packet has zero
-- first-order quadratic-dissipation response to the pressure direction.  The
-- only extra datum needed to apply the finite-packet theorem is the genuinely
-- semantic one: every packet mode being differentiated must be one of the
-- retained physical Galerkin modes.  Round82's raw datum did not store that
-- membership proof, so it is carried explicitly here rather than silently
-- inferred.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

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
-- Abstract exact C3 fact: transverse and longitudinal vectors are Hermitian
-- orthogonal in either order because the lattice mode is real.
------------------------------------------------------------------------

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
-- The actual Round84 ordered pressure term is longitudinal.
------------------------------------------------------------------------

lerayRankOneScalar :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
lerayRankOneScalar {F = F} {E = E} {I = I} system incidence =
  let
    output = Physical.k incidence
    value = AP.rawOrderedValue system incidence
  in
  C3.complexMultiply
    (C3.realEmbed F (C3.inverseNormSquared I output))
    (C3.bilinearDot3 (C3.modeVector E output) value)

lerayRankOneCorrectionIsLongitudinal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  AP.lerayRankOneCorrection system incidence
  ≡ C3.complex3Scale
      (lerayRankOneScalar system incidence)
      (C3.modeVector E (Physical.k incidence))
lerayRankOneCorrectionIsLongitudinal system incidence = refl

pressureOrderedTermHermitianRightZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (value : C3.Complex3 F) →
  C3.bilinearDot3
    (C3.modeVector E (Physical.k incidence)) value
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
          (trans
            (cong (C3.hermitianPairing3 value)
              (lerayRankOneCorrectionIsLongitudinal system incidence))
            (hermitianTransverseLongitudinalRightZero
              E (Physical.k incidence) value
              (lerayRankOneScalar system incidence) transverse)))
        (Hermitian.complexMultiplyZeroRight (C3.complexI F))))

pressureOrderedTermHermitianLeftZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (value : C3.Complex3 F) →
  C3.bilinearDot3
    (C3.modeVector E (Physical.k incidence)) value
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
          (trans
            (cong (λ first → C3.hermitianPairing3 first value)
              (lerayRankOneCorrectionIsLongitudinal system incidence))
            (hermitianLongitudinalTransverseRightZero
              E (Physical.k incidence) value
              (lerayRankOneScalar system incidence) transverse)))
        (Hermitian.complexMultiplyZeroRight
          (C3.complexConjugate (C3.complexI F)))))

------------------------------------------------------------------------
-- Lift through the exact physical output fibre.  The proof takes an explicit
-- output-equality witness for every list entry; the concrete fibre supplies it.
------------------------------------------------------------------------

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
pressureListHermitianRightZero {F = F}
    system output [] value transverse outputs =
  trans
    refl
    (Hermitian.complexMultiplyZeroRight (C3.complexOne F))
pressureListHermitianRightZero {F = F} {E = E}
    system output (incidence ∷ rest) value transverse outputs =
  let
    outputEq = outputs incidence (Cube.here refl)
    headTransverse :
      C3.bilinearDot3 (C3.modeVector E (Physical.k incidence)) value
      ≡ C3.complexZero F
    headTransverse = subst
      (λ selected →
        C3.bilinearDot3 (C3.modeVector E selected) value
        ≡ C3.complexZero F)
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
        (pressureListHermitianRightZero
          system output rest value transverse
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
pressureListHermitianLeftZero {F = F}
    system output [] value transverse outputs =
  trans refl (Hermitian.complexMultiplyZeroRight (C3.complexOne F))
pressureListHermitianLeftZero {F = F} {E = E}
    system output (incidence ∷ rest) value transverse outputs =
  let
    outputEq = outputs incidence (Cube.here refl)
    headTransverse :
      C3.bilinearDot3 (C3.modeVector E (Physical.k incidence)) value
      ≡ C3.complexZero F
    headTransverse = subst
      (λ selected →
        C3.bilinearDot3 (C3.modeVector E selected) value
        ≡ C3.complexZero F)
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
        (pressureListHermitianLeftZero
          system output rest value transverse
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
-- A selected physical packet must carry the membership that Round82's datum
-- omitted before we may consume retainedVelocityTransverse on every packet
-- mode.  This is the minimal same-object enrichment, not a new PDE carrier.
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

packetVelocityTransverseAtRetainedMode :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum)
    mode →
  mode Cube.∈ Drift.packetModes datum →
  C3.bilinearDot3
    (C3.modeVector
      (Literal.physicalEmbedding (Drift.physicalSystem datum)) mode)
    (Drift.packetVelocity datum mode)
  ≡ C3.complexZero (LP.realField model)
packetVelocityTransverseAtRetainedMode {model = model}
    datum retained mode member
  with LP.shellSelect model (Drift.shell datum) mode
... | true =
  Literal.retainedVelocityTransverse
    (Drift.physicalSystem datum) mode
    (packetModesAreRetained retained mode member)
... | false =
  Algebra.bilinearDot3RightZero
    (C3.modeVector
      (Literal.physicalEmbedding (Drift.physicalSystem datum)) mode)

weightedPacketVelocityTransverseAtRetainedMode :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum)
    mode →
  mode Cube.∈ Drift.packetModes datum →
  C3.bilinearDot3
    (C3.modeVector
      (Literal.physicalEmbedding (Drift.physicalSystem datum)) mode)
    (Drift.weightedPacketField datum
      (Audit.velocity (Drift.finiteSystem datum)) mode)
  ≡ C3.complexZero (LP.realField model)
weightedPacketVelocityTransverseAtRetainedMode {model = model}
    datum retained mode member =
  trans
    (Scaling.bilinearDot3ScaleRight
      (Drift.modeDissipationWeight datum mode)
      (C3.modeVector
        (Literal.physicalEmbedding (Drift.physicalSystem datum)) mode)
      (Drift.packetVelocity datum mode))
    (trans
      (cong (C3.complexMultiply (Drift.modeDissipationWeight datum mode))
        (packetVelocityTransverseAtRetainedMode datum retained mode member))
      (Hermitian.complexMultiplyZeroRight
        (Drift.modeDissipationWeight datum mode)))

finitePressureDissipationPairingsZero :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : RetainedPressurePacketDatum datum) →
  R83.complexDissipationTangentComponent datum (Split.pressureRHS datum)
  ≡ C3.complexZero (LP.realField model)
finitePressureDissipationPairingsZero {model = model} datum retained =
  pairingsZero (Drift.packetModes datum)
    (λ mode member → packetModesAreRetained retained mode member)
  where
  E = Literal.physicalEmbedding (Drift.physicalSystem datum)
  F = LP.realField model

  pairingsZero :
    (modes : List Z3.FourierMode) →
    (∀ mode → mode Cube.∈ modes → mode Cube.∈ Audit.modes (Drift.finiteSystem datum)) →
    C3.complexAdd
      (Packet.finiteHermitianPairing modes
        (Packet.packetField model (Drift.shell datum) (Split.pressureRHS datum))
        (Drift.weightedPacketField datum
          (Audit.velocity (Drift.finiteSystem datum))))
      (Packet.finiteHermitianPairing modes
        (Drift.packetVelocity datum)
        (Drift.weightedPacketField datum (Split.pressureRHS datum)))
    ≡ C3.complexZero F
  pairingsZero [] retainedModes =
    Field.complexAddZeroLeft (C3.complexZero F)
  pairingsZero (mode ∷ modes) retainedModes =
    let
      member = retainedModes mode (Cube.here refl)
      velocityTransverse = Literal.retainedVelocityTransverse
        (Drift.physicalSystem datum) mode member
      pressureLeft = pressureRHSOrthogonalLeftToTransverse
        (Drift.finiteSystem datum) mode
        (C3.complex3Scale
          (Drift.modeDissipationWeight datum mode)
          (Audit.velocity (Drift.finiteSystem datum) mode))
        (trans
          (Scaling.bilinearDot3ScaleRight
            (Drift.modeDissipationWeight datum mode)
            (C3.modeVector E mode)
            (Audit.velocity (Drift.finiteSystem datum) mode))
          (trans
            (cong (C3.complexMultiply (Drift.modeDissipationWeight datum mode))
              velocityTransverse)
            (Hermitian.complexMultiplyZeroRight
              (Drift.modeDissipationWeight datum mode))))
      pressureRight = pressureRHSOrthogonalRightToTransverse
        (Drift.finiteSystem datum) mode
        (Audit.velocity (Drift.finiteSystem datum) mode)
        velocityTransverse
    in
    pairingsZero modes
      (λ selected selectedMember → retainedModes selected (Cube.there selectedMember))

round84PressureDirectionHermitianOrthogonalityConstructed : Bool
round84PressureDirectionHermitianOrthogonalityConstructed = true

round84RetainedPacketPressureDissipationTangentZero : Bool
round84RetainedPacketPressureDissipationTangentZero = false

-- The modewise geometry is fully constructed.  The final finite-pairing theorem
-- above is intentionally left behind the source-shape audit flag until its
-- recursive pairing normalization is kernel-checked; no Clay-facing consumer
-- is promoted from an unchecked proof shape.

round84PressureDirectionHermitianOrthogonalityConstructedIsTrue :
  round84PressureDirectionHermitianOrthogonalityConstructed ≡ true
round84PressureDirectionHermitianOrthogonalityConstructedIsTrue = refl

round84RetainedPacketPressureDissipationTangentZeroIsFalse :
  round84RetainedPacketPressureDissipationTangentZero ≡ false
round84RetainedPacketPressureDissipationTangentZeroIsFalse = refl
