module DASHI.Physics.Closure.NSTriadKNNonlinearRelativeGrowthAdvectivePressureSplitRound84Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND84 / OPEN THE ROUND83 NONLINEAR RELATIVE-GROWTH CORE
--
-- Round83 proved
--
--   R = R_nu + R_N,
--   R_N = qdot_N D - q Ddot_N,
--
-- on the literal selected Galerkin tangent.  The companion Round84 module
-- proves pointwise, on the same Fourier carrier,
--
--   N = A + P,
--
-- where A is the unprojected advective ordered interaction and P is exactly
-- the longitudinal rank-one Leray correction (the pressure-gradient term).
--
-- This module pushes that identity through the *existing* first-variation,
-- packet-transfer, dissipation, and relative-growth machinery.  The result is
-- the exact source-native scalar split
--
--   R_N = R_A + R_P.
--
-- No function extensionality is used: all field replacement is proved by
-- finite/pointwise congruence.  This matters because R_P is now the literal
-- pressure-direction contribution consumed by the C3/C4 route-killer.  The
-- remaining hard theorem is not to define a pressure part; it is to connect
-- this exact R_P to the same-mode pressure-Hessian/stretching budget with a
-- cutoff-uniform quantitative estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift
import DASHI.Physics.Closure.NSTriadKNLiteralRHSRelativeGrowthSplitRound83Exact as R83
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP

------------------------------------------------------------------------
-- Pointwise congruence for the literal bilinear nonlinearity.
------------------------------------------------------------------------

sumMixedCongLeft :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left left' right : First.VelocityField F)
    (incidences : List Physical.PhysicalTriadIncidence) →
  (∀ mode → left mode ≡ left' mode) →
  Audit.sumVectors (First.mixedTerms system left right incidences)
  ≡ Audit.sumVectors (First.mixedTerms system left' right incidences)
sumMixedCongLeft system left left' right [] pointwise = refl
sumMixedCongLeft system left left' right (incidence ∷ rest) pointwise =
  cong₂ C3.complex3Add
    (cong
      (λ value →
        Signed.orderedVelocityInteraction
          (Audit.galerkinLaws system)
          (Physical.k incidence)
          (Physical.p incidence)
          (Physical.q incidence)
          value
          (right (Physical.q incidence)))
      (pointwise (Physical.p incidence)))
    (sumMixedCongLeft system left left' right rest pointwise)

sumMixedCongRight :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left right right' : First.VelocityField F)
    (incidences : List Physical.PhysicalTriadIncidence) →
  (∀ mode → right mode ≡ right' mode) →
  Audit.sumVectors (First.mixedTerms system left right incidences)
  ≡ Audit.sumVectors (First.mixedTerms system left right' incidences)
sumMixedCongRight system left right right' [] pointwise = refl
sumMixedCongRight system left right right' (incidence ∷ rest) pointwise =
  cong₂ C3.complex3Add
    (cong
      (Signed.orderedVelocityInteraction
        (Audit.galerkinLaws system)
        (Physical.k incidence)
        (Physical.p incidence)
        (Physical.q incidence)
        (left (Physical.p incidence)))
      (pointwise (Physical.q incidence)))
    (sumMixedCongRight system left right right' rest pointwise)

mixedProjectedNonlinearityCongLeft :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left left' right : First.VelocityField F) →
  (∀ mode → left mode ≡ left' mode) →
  ∀ output →
  First.mixedProjectedNonlinearity system left right output
  ≡ First.mixedProjectedNonlinearity system left' right output
mixedProjectedNonlinearityCongLeft system left left' right pointwise output =
  sumMixedCongLeft system left left' right
    (Audit.concreteTriadsAt system output) pointwise

mixedProjectedNonlinearityCongRight :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left right right' : First.VelocityField F) →
  (∀ mode → right mode ≡ right' mode) →
  ∀ output →
  First.mixedProjectedNonlinearity system left right output
  ≡ First.mixedProjectedNonlinearity system left right' output
mixedProjectedNonlinearityCongRight system left right right' pointwise output =
  sumMixedCongRight system left right right'
    (Audit.concreteTriadsAt system output) pointwise

projectedNonlinearityFirstVariationCong :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left right : First.VelocityField F) →
  (∀ mode → left mode ≡ right mode) →
  ∀ output →
  First.projectedNonlinearityFirstVariation system left output
  ≡ First.projectedNonlinearityFirstVariation system right output
projectedNonlinearityFirstVariationCong system left right pointwise output =
  cong₂ C3.complex3Add
    (mixedProjectedNonlinearityCongRight
      system (Audit.velocity system) left right pointwise output)
    (mixedProjectedNonlinearityCongLeft
      system left right (Audit.velocity system) pointwise output)

------------------------------------------------------------------------
-- Packetization preserves pointwise equality, including DN(u)[v].
------------------------------------------------------------------------

packetFieldCong :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r}) shell
    (left right : Packet.TotalField model) →
  (∀ mode → left mode ≡ right mode) →
  ∀ mode →
  Packet.packetField model shell left mode
  ≡ Packet.packetField model shell right mode
packetFieldCong model shell left right pointwise mode
  with LP.shellSelect model shell mode
... | true = pointwise mode
... | false = refl

packetNonlinearityFirstVariationCong :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    shell
    (left right : Packet.TotalField model) →
  (∀ mode → left mode ≡ right mode) →
  ∀ mode →
  Packet.packetNonlinearityFirstVariation model system shell left mode
  ≡ Packet.packetNonlinearityFirstVariation model system shell right mode
packetNonlinearityFirstVariationCong model system shell left right pointwise mode =
  packetFieldCong model shell
    (First.projectedNonlinearityFirstVariation system left)
    (First.projectedNonlinearityFirstVariation system right)
    (projectedNonlinearityFirstVariationCong system left right pointwise)
    mode

packetTransferPairingFirstVariationCong :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    shell modes
    (left right : Packet.TotalField model) →
  (∀ mode → left mode ≡ right mode) →
  Packet.packetTransferPairingFirstVariation model system shell modes left
  ≡ Packet.packetTransferPairingFirstVariation model system shell modes right
packetTransferPairingFirstVariationCong
    model system shell modes left right pointwise =
  cong₂ C3.complexAdd
    (R83.finiteHermitianPairingCongLeft modes
      (Packet.packetPerturbation model shell left)
      (Packet.packetPerturbation model shell right)
      (Packet.packetBaseNonlinearity model system shell)
      (packetFieldCong model shell left right pointwise))
    (R83.finiteHermitianPairingCongRight modes
      (Packet.packetBaseVelocity model system shell)
      (Packet.packetNonlinearityFirstVariation model system shell left)
      (Packet.packetNonlinearityFirstVariation model system shell right)
      (packetNonlinearityFirstVariationCong
        model system shell left right pointwise))

------------------------------------------------------------------------
-- The literal N = A + P identity on the selected physical datum.
------------------------------------------------------------------------

advectiveRHS :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
advectiveRHS datum = AP.advectiveNonlinearity (Drift.finiteSystem datum)

pressureRHS :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
pressureRHS datum = AP.pressureNonlinearity (Drift.finiteSystem datum)

nonlinearRHSSplitsAdvectivePressurePointwise :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) mode →
  R83.nonlinearRHS datum mode
  ≡ First.fieldAdd (advectiveRHS datum) (pressureRHS datum) mode
nonlinearRHSSplitsAdvectivePressurePointwise datum mode =
  AP.projectedNonlinearitySplitsAdvectivePressurePointwise
    (Drift.finiteSystem datum) mode

------------------------------------------------------------------------
-- qdot_N = qdot_A + qdot_P.
------------------------------------------------------------------------

complexTransferTangentAdvective :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Complex (LP.realField model)
complexTransferTangentAdvective {model = model} datum =
  Packet.packetTransferPairingFirstVariation
    model (Drift.finiteSystem datum) (Drift.shell datum) (Drift.packetModes datum)
    (advectiveRHS datum)

complexTransferTangentPressure :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Complex (LP.realField model)
complexTransferTangentPressure {model = model} datum =
  Packet.packetTransferPairingFirstVariation
    model (Drift.finiteSystem datum) (Drift.shell datum) (Drift.packetModes datum)
    (pressureRHS datum)

complexTransferTangentNonlinearSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  R83.complexTransferTangentNonlinear datum
  ≡ C3.complexAdd
      (complexTransferTangentAdvective datum)
      (complexTransferTangentPressure datum)
complexTransferTangentNonlinearSplitsExactly {model = model} datum =
  trans
    (packetTransferPairingFirstVariationCong
      model (Drift.finiteSystem datum) (Drift.shell datum) (Drift.packetModes datum)
      (R83.nonlinearRHS datum)
      (First.fieldAdd (advectiveRHS datum) (pressureRHS datum))
      (nonlinearRHSSplitsAdvectivePressurePointwise datum))
    (R83.packetTransferPairingFirstVariationAdd
      model (Drift.finiteSystem datum) (Drift.shell datum) (Drift.packetModes datum)
      (advectiveRHS datum) (pressureRHS datum))

rawTransferTangentAdvective :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawTransferTangentAdvective datum = C3.real (complexTransferTangentAdvective datum)

rawTransferTangentPressure :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawTransferTangentPressure datum = C3.real (complexTransferTangentPressure datum)

rawTransferTangentNonlinearSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  R83.rawTransferTangentNonlinear datum
  ≡ C3.add (LP.realField model)
      (rawTransferTangentAdvective datum)
      (rawTransferTangentPressure datum)
rawTransferTangentNonlinearSplitsExactly datum =
  trans
    (cong C3.real (complexTransferTangentNonlinearSplitsExactly datum))
    (R83.realOfComplexAdd
      (complexTransferTangentAdvective datum)
      (complexTransferTangentPressure datum))

------------------------------------------------------------------------
-- Ddot is also linear in the physical tangent.
------------------------------------------------------------------------

complexDissipationTangentComponentCong :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (left right : Packet.TotalField model) →
  (∀ mode → left mode ≡ right mode) →
  R83.complexDissipationTangentComponent datum left
  ≡ R83.complexDissipationTangentComponent datum right
complexDissipationTangentComponentCong {model = model} datum left right pointwise =
  cong₂ C3.complexAdd
    (R83.finiteHermitianPairingCongLeft
      (Drift.packetModes datum)
      (Packet.packetField model (Drift.shell datum) left)
      (Packet.packetField model (Drift.shell datum) right)
      (Drift.weightedPacketField datum
        (Audit.velocity (Drift.finiteSystem datum)))
      (packetFieldCong model (Drift.shell datum) left right pointwise))
    (R83.finiteHermitianPairingCongRight
      (Drift.packetModes datum)
      (Drift.packetVelocity datum)
      (Drift.weightedPacketField datum left)
      (Drift.weightedPacketField datum right)
      (λ mode →
        cong
          (λ value → C3.complex3Scale
            (C3.realEmbed (LP.realField model) (Drift.modeDissipationWeight datum mode))
            value)
          (packetFieldCong model (Drift.shell datum) left right pointwise mode)))

complexDissipationTangentComponentAdd :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (left right : Packet.TotalField model) →
  R83.complexDissipationTangentComponent datum (First.fieldAdd left right)
  ≡ C3.complexAdd
      (R83.complexDissipationTangentComponent datum left)
      (R83.complexDissipationTangentComponent datum right)
complexDissipationTangentComponentAdd {model = model} datum left right =
  let
    modes = Drift.packetModes datum
    baseWeighted = Drift.weightedPacketField datum
      (Audit.velocity (Drift.finiteSystem datum))
    basePacket = Drift.packetVelocity datum
    leftPacket = Packet.packetField model (Drift.shell datum) left
    rightPacket = Packet.packetField model (Drift.shell datum) right
    leftWeighted = Drift.weightedPacketField datum left
    rightWeighted = Drift.weightedPacketField datum right
    a = Packet.finiteHermitianPairing modes leftPacket baseWeighted
    b = Packet.finiteHermitianPairing modes rightPacket baseWeighted
    c = Packet.finiteHermitianPairing modes basePacket leftWeighted
    d = Packet.finiteHermitianPairing modes basePacket rightWeighted
  in
  trans
    (cong₂ C3.complexAdd
      (trans
        (R83.finiteHermitianPairingCongLeft modes
          (Packet.packetField model (Drift.shell datum) (First.fieldAdd left right))
          (First.fieldAdd leftPacket rightPacket)
          baseWeighted
          (Packet.packetFieldAdd model (Drift.shell datum) left right))
        (Packet.finiteHermitianPairingAddLeft modes leftPacket rightPacket baseWeighted))
      (trans
        (R83.finiteHermitianPairingCongRight modes basePacket
          (Drift.weightedPacketField datum (First.fieldAdd left right))
          (First.fieldAdd leftWeighted rightWeighted)
          (Drift.weightedPacketFieldAdd datum left right))
        (Packet.finiteHermitianPairingAddRight modes basePacket leftWeighted rightWeighted)))
    (Packet.complexInterchange a b c d)

complexDissipationTangentNonlinearSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  R83.complexDissipationTangentComponent datum (R83.nonlinearRHS datum)
  ≡ C3.complexAdd
      (R83.complexDissipationTangentComponent datum (advectiveRHS datum))
      (R83.complexDissipationTangentComponent datum (pressureRHS datum))
complexDissipationTangentNonlinearSplitsExactly datum =
  trans
    (complexDissipationTangentComponentCong datum
      (R83.nonlinearRHS datum)
      (First.fieldAdd (advectiveRHS datum) (pressureRHS datum))
      (nonlinearRHSSplitsAdvectivePressurePointwise datum))
    (complexDissipationTangentComponentAdd datum
      (advectiveRHS datum) (pressureRHS datum))

rawDissipationTangentAdvective :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawDissipationTangentAdvective datum =
  C3.real (R83.complexDissipationTangentComponent datum (advectiveRHS datum))

rawDissipationTangentPressure :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawDissipationTangentPressure datum =
  C3.real (R83.complexDissipationTangentComponent datum (pressureRHS datum))

rawDissipationTangentNonlinearSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  R83.rawDissipationTangentNonlinear datum
  ≡ C3.add (LP.realField model)
      (rawDissipationTangentAdvective datum)
      (rawDissipationTangentPressure datum)
rawDissipationTangentNonlinearSplitsExactly datum =
  trans
    (cong C3.real (complexDissipationTangentNonlinearSplitsExactly datum))
    (R83.realOfComplexAdd
      (R83.complexDissipationTangentComponent datum (advectiveRHS datum))
      (R83.complexDissipationTangentComponent datum (pressureRHS datum)))

------------------------------------------------------------------------
-- The route-killer is now an exact scalar pressure share.
------------------------------------------------------------------------

advectiveRelativeGrowthCore :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
advectiveRelativeGrowthCore datum =
  R83.relativeGrowthComponent datum
    (rawTransferTangentAdvective datum)
    (rawDissipationTangentAdvective datum)

pressureRelativeGrowthCore :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
pressureRelativeGrowthCore datum =
  R83.relativeGrowthComponent datum
    (rawTransferTangentPressure datum)
    (rawDissipationTangentPressure datum)

nonlinearRelativeGrowthCoreSplitsAdvectivePressureExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  R83.nonlinearRelativeGrowthCore datum
  ≡ C3.add (LP.realField model)
      (advectiveRelativeGrowthCore datum)
      (pressureRelativeGrowthCore datum)
nonlinearRelativeGrowthCoreSplitsAdvectivePressureExactly {model = model} datum
  rewrite rawTransferTangentNonlinearSplitsExactly datum
        | rawDissipationTangentNonlinearSplitsExactly datum =
  P.R.solve 6
    (λ q d qa qp da dp →
      (((qa P.R.⊕ qp) P.R.⊗ d)
        P.R.⊕ P.R.⊝ (q P.R.⊗ (da P.R.⊕ dp)))
      P.R.⊜
      ((qa P.R.⊗ d) P.R.⊕ P.R.⊝ (q P.R.⊗ da))
      P.R.⊕
      ((qp P.R.⊗ d) P.R.⊕ P.R.⊝ (q P.R.⊗ dp)))
    refl
    (Drift.rawTransfer datum)
    (Drift.rawDissipation datum)
    (rawTransferTangentAdvective datum)
    (rawTransferTangentPressure datum)
    (rawDissipationTangentAdvective datum)
    (rawDissipationTangentPressure datum)
  where
  module P = Field.Polynomial (LP.realField model)

round84NonlinearTransferTangentSplitsAdvectivePressure : Bool
round84NonlinearTransferTangentSplitsAdvectivePressure = true

round84NonlinearDissipationTangentSplitsAdvectivePressure : Bool
round84NonlinearDissipationTangentSplitsAdvectivePressure = true

round84NonlinearRelativeGrowthSplitsAdvectivePressure : Bool
round84NonlinearRelativeGrowthSplitsAdvectivePressure = true

round84PressureRelativeGrowthIsLiteralScalar : Bool
round84PressureRelativeGrowthIsLiteralScalar = true

round84PressureRelativeGrowthPhysicalEstimateConstructed : Bool
round84PressureRelativeGrowthPhysicalEstimateConstructed = false

round84NonlinearRelativeGrowthSplitsAdvectivePressureIsTrue :
  round84NonlinearRelativeGrowthSplitsAdvectivePressure ≡ true
round84NonlinearRelativeGrowthSplitsAdvectivePressureIsTrue = refl

round84PressureRelativeGrowthPhysicalEstimateConstructedIsFalse :
  round84PressureRelativeGrowthPhysicalEstimateConstructed ≡ false
round84PressureRelativeGrowthPhysicalEstimateConstructedIsFalse = refl
