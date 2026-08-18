module DASHI.Physics.Closure.NSTriadKNLiteralRHSRelativeGrowthSplitRound83Exact where

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
-- ROUND83 / LITERAL RHS SPLIT OF THE COMPACT-TRANSFER DRIFT CORE
--
-- Round82 reduced the selected compact-transfer drift to the literal scalar
--
--     qdot D - q Ddot
--
-- along the exact finite Galerkin Navier--Stokes tangent
--
--     F = F_nu + F_N
--       = -nu |k|^2 u + N(u).
--
-- This module performs the next source-native split.  It proves additivity of
-- the already-constructed projected-nonlinearity first variation and packet
-- transfer first variation, then separates both qdot and Ddot into the two
-- actual RHS components.  Consequently
--
--   qdot D - q Ddot
--     = (qdot_nu D - q Ddot_nu)
--       + (qdot_N D - q Ddot_N).
--
-- This is not a sign theorem.  It is the exact decomposition needed before a
-- pressure/stretching estimate can be asked to fund the nonlinear component.
-- In particular the pressure-carrying projected nonlinearity is no longer
-- hidden inside an undifferentiated selected tangent.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Literal
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralCompactTransferDriftDataRound82Exact as Scale
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift

------------------------------------------------------------------------
-- First-variation additivity on the literal quadratic projected nonlinearity.
------------------------------------------------------------------------

projectedNonlinearityFirstVariationAdd :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left right : First.VelocityField F)
    output →
  First.projectedNonlinearityFirstVariation system
    (First.fieldAdd left right) output
  ≡
  First.fieldAdd
    (First.projectedNonlinearityFirstVariation system left)
    (First.projectedNonlinearityFirstVariation system right)
    output
projectedNonlinearityFirstVariationAdd system left right output =
  let
    u = Audit.velocity system
    ul = First.mixedProjectedNonlinearity system u left output
    ur = First.mixedProjectedNonlinearity system u right output
    lu = First.mixedProjectedNonlinearity system left u output
    ru = First.mixedProjectedNonlinearity system right u output
  in
  trans
    (cong₂ C3.complex3Add
      (First.mixedProjectedNonlinearityAddRight system u left right output)
      (First.mixedProjectedNonlinearityAddLeft system left right u output))
    (First.complex3Interchange ul ur lu ru)

packetNonlinearityFirstVariationAddPointwise :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    shell
    (left right : Packet.TotalField model)
    mode →
  Packet.packetNonlinearityFirstVariation model system shell
    (First.fieldAdd left right) mode
  ≡
  First.fieldAdd
    (Packet.packetNonlinearityFirstVariation model system shell left)
    (Packet.packetNonlinearityFirstVariation model system shell right)
    mode
packetNonlinearityFirstVariationAddPointwise
    model system shell left right mode =
  trans
    (cong
      (λ field → Packet.packetField model shell field mode)
      (projectedNonlinearityFirstVariationAdd system left right mode))
    (Packet.packetFieldAdd model shell
      (First.projectedNonlinearityFirstVariation system left)
      (First.projectedNonlinearityFirstVariation system right)
      mode)

------------------------------------------------------------------------
-- Congruence of the finite pairing under pointwise equality.  This avoids any
-- function-extensionality axiom on the total Fourier field.
------------------------------------------------------------------------

finiteHermitianPairingCongLeft :
  ∀ {r} {F : C3.RealField r}
    (modes : List Z3.FourierMode)
    (left left' right : Z3.FourierMode → C3.Complex3 F) →
  (∀ mode → left mode ≡ left' mode) →
  Packet.finiteHermitianPairing modes left right
  ≡ Packet.finiteHermitianPairing modes left' right
finiteHermitianPairingCongLeft [] left left' right pointwise = refl
finiteHermitianPairingCongLeft (mode ∷ modes) left left' right pointwise =
  cong₂ C3.complexAdd
    (cong (λ value → C3.hermitianPairing3 value (right mode))
      (pointwise mode))
    (finiteHermitianPairingCongLeft modes left left' right pointwise)

finiteHermitianPairingCongRight :
  ∀ {r} {F : C3.RealField r}
    (modes : List Z3.FourierMode)
    (left right right' : Z3.FourierMode → C3.Complex3 F) →
  (∀ mode → right mode ≡ right' mode) →
  Packet.finiteHermitianPairing modes left right
  ≡ Packet.finiteHermitianPairing modes left right'
finiteHermitianPairingCongRight [] left right right' pointwise = refl
finiteHermitianPairingCongRight (mode ∷ modes) left right right' pointwise =
  cong₂ C3.complexAdd
    (cong (C3.hermitianPairing3 (left mode)) (pointwise mode))
    (finiteHermitianPairingCongRight modes left right right' pointwise)

packetTransferPairingFirstVariationAdd :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    shell modes
    (left right : Packet.TotalField model) →
  Packet.packetTransferPairingFirstVariation model system shell modes
    (First.fieldAdd left right)
  ≡
  C3.complexAdd
    (Packet.packetTransferPairingFirstVariation model system shell modes left)
    (Packet.packetTransferPairingFirstVariation model system shell modes right)
packetTransferPairingFirstVariationAdd model system shell modes left right =
  let
    leftK = Packet.packetPerturbation model shell left
    rightK = Packet.packetPerturbation model shell right
    baseN = Packet.packetBaseNonlinearity model system shell
    baseU = Packet.packetBaseVelocity model system shell
    dNleft = Packet.packetNonlinearityFirstVariation model system shell left
    dNright = Packet.packetNonlinearityFirstVariation model system shell right
    a = Packet.finiteHermitianPairing modes leftK baseN
    b = Packet.finiteHermitianPairing modes rightK baseN
    c = Packet.finiteHermitianPairing modes baseU dNleft
    d = Packet.finiteHermitianPairing modes baseU dNright
  in
  trans
    (cong₂ C3.complexAdd
      (trans
        (finiteHermitianPairingCongLeft modes
          (Packet.packetPerturbation model shell (First.fieldAdd left right))
          (First.fieldAdd leftK rightK)
          baseN
          (Packet.packetFieldAdd model shell left right))
        (Packet.finiteHermitianPairingAddLeft modes leftK rightK baseN))
      (trans
        (finiteHermitianPairingCongRight modes baseU
          (Packet.packetNonlinearityFirstVariation model system shell
            (First.fieldAdd left right))
          (First.fieldAdd dNleft dNright)
          (packetNonlinearityFirstVariationAddPointwise
            model system shell left right))
        (Packet.finiteHermitianPairingAddRight modes baseU dNleft dNright)))
    (Packet.complexInterchange a b c d)

------------------------------------------------------------------------
-- Literal NS RHS components and direct qdot split.
------------------------------------------------------------------------

viscousRHS :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
viscousRHS datum = Literal.literalViscousCoefficient (Drift.physicalSystem datum)

nonlinearRHS :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
nonlinearRHS datum = Audit.projectedNonlinearity (Drift.finiteSystem datum)

literalRHSSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.literalRHS datum ≡ First.fieldAdd (viscousRHS datum) (nonlinearRHS datum)
literalRHSSplitsExactly datum = refl

complexTransferTangentViscous :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Complex (LP.realField model)
complexTransferTangentViscous {model = model} datum =
  Packet.packetTransferPairingFirstVariation
    model (Drift.finiteSystem datum) (Drift.shell datum) (Drift.packetModes datum)
    (viscousRHS datum)

complexTransferTangentNonlinear :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Complex (LP.realField model)
complexTransferTangentNonlinear {model = model} datum =
  Packet.packetTransferPairingFirstVariation
    model (Drift.finiteSystem datum) (Drift.shell datum) (Drift.packetModes datum)
    (nonlinearRHS datum)

complexTransferTangentSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Packet.packetTransferPairingFirstVariation
    model (Drift.finiteSystem datum) (Drift.shell datum) (Drift.packetModes datum)
    (Drift.literalRHS datum)
  ≡ C3.complexAdd
      (complexTransferTangentViscous datum)
      (complexTransferTangentNonlinear datum)
complexTransferTangentSplitsExactly {model = model} datum =
  trans
    (cong
      (Packet.packetTransferPairingFirstVariation
        model (Drift.finiteSystem datum) (Drift.shell datum) (Drift.packetModes datum))
      (literalRHSSplitsExactly datum))
    (packetTransferPairingFirstVariationAdd
      model (Drift.finiteSystem datum) (Drift.shell datum) (Drift.packetModes datum)
      (viscousRHS datum) (nonlinearRHS datum))

realOfComplexAdd :
  ∀ {r} {F : C3.RealField r} (left right : C3.Complex F) →
  C3.real (C3.complexAdd left right)
  ≡ C3.add F (C3.real left) (C3.real right)
realOfComplexAdd (C3.complex lr li) (C3.complex rr ri) = refl

rawTransferTangentViscous :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawTransferTangentViscous datum = C3.real (complexTransferTangentViscous datum)

rawTransferTangentNonlinear :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawTransferTangentNonlinear datum = C3.real (complexTransferTangentNonlinear datum)

rawTransferTangentSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.rawTransferTangent datum
  ≡ C3.add (LP.realField model)
      (rawTransferTangentViscous datum)
      (rawTransferTangentNonlinear datum)
rawTransferTangentSplitsExactly datum =
  trans
    (cong C3.real (complexTransferTangentSplitsExactly datum))
    (realOfComplexAdd
      (complexTransferTangentViscous datum)
      (complexTransferTangentNonlinear datum))

------------------------------------------------------------------------
-- Direct Ddot split.  The weighted |k|^2 packet map is linear, so the same
-- literal RHS decomposition applies in both slots of the product rule.
------------------------------------------------------------------------

packetRHSSplitPointwise :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) mode →
  Drift.packetRHS datum mode
  ≡ First.fieldAdd
      (Packet.packetField model (Drift.shell datum) (viscousRHS datum))
      (Packet.packetField model (Drift.shell datum) (nonlinearRHS datum))
      mode
packetRHSSplitPointwise {model = model} datum mode =
  trans
    (cong
      (λ field → Packet.packetField model (Drift.shell datum) field mode)
      (literalRHSSplitsExactly datum))
    (Packet.packetFieldAdd model (Drift.shell datum)
      (viscousRHS datum) (nonlinearRHS datum) mode)

weightedRHSSplitPointwise :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) mode →
  Drift.weightedPacketField datum (Drift.literalRHS datum) mode
  ≡ First.fieldAdd
      (Drift.weightedPacketField datum (viscousRHS datum))
      (Drift.weightedPacketField datum (nonlinearRHS datum))
      mode
weightedRHSSplitPointwise datum mode =
  trans
    (cong
      (λ field → Drift.weightedPacketField datum field mode)
      (literalRHSSplitsExactly datum))
    (Drift.weightedPacketFieldAdd datum
      (viscousRHS datum) (nonlinearRHS datum) mode)

complexDissipationTangentComponent :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model →
  Packet.TotalField model → C3.Complex (LP.realField model)
complexDissipationTangentComponent datum tangent =
  C3.complexAdd
    (Packet.finiteHermitianPairing
      (Drift.packetModes datum)
      (Packet.packetField _ (Drift.shell datum) tangent)
      (Drift.weightedPacketField datum
        (Audit.velocity (Drift.finiteSystem datum))))
    (Packet.finiteHermitianPairing
      (Drift.packetModes datum)
      (Drift.packetVelocity datum)
      (Drift.weightedPacketField datum tangent))

complexDissipationTangentSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  C3.complexAdd
    (Packet.finiteHermitianPairing
      (Drift.packetModes datum)
      (Drift.packetRHS datum)
      (Drift.weightedPacketField datum
        (Audit.velocity (Drift.finiteSystem datum))))
    (Packet.finiteHermitianPairing
      (Drift.packetModes datum)
      (Drift.packetVelocity datum)
      (Drift.weightedPacketField datum (Drift.literalRHS datum)))
  ≡ C3.complexAdd
      (complexDissipationTangentComponent datum (viscousRHS datum))
      (complexDissipationTangentComponent datum (nonlinearRHS datum))
complexDissipationTangentSplitsExactly {model = model} datum =
  let
    modes = Drift.packetModes datum
    baseWeighted = Drift.weightedPacketField datum
      (Audit.velocity (Drift.finiteSystem datum))
    basePacket = Drift.packetVelocity datum
    viscPacket = Packet.packetField model (Drift.shell datum) (viscousRHS datum)
    nonlinPacket = Packet.packetField model (Drift.shell datum) (nonlinearRHS datum)
    viscWeighted = Drift.weightedPacketField datum (viscousRHS datum)
    nonlinWeighted = Drift.weightedPacketField datum (nonlinearRHS datum)
    a = Packet.finiteHermitianPairing modes viscPacket baseWeighted
    b = Packet.finiteHermitianPairing modes nonlinPacket baseWeighted
    c = Packet.finiteHermitianPairing modes basePacket viscWeighted
    d = Packet.finiteHermitianPairing modes basePacket nonlinWeighted
  in
  trans
    (cong₂ C3.complexAdd
      (trans
        (finiteHermitianPairingCongLeft modes
          (Drift.packetRHS datum)
          (First.fieldAdd viscPacket nonlinPacket)
          baseWeighted
          (packetRHSSplitPointwise datum))
        (Packet.finiteHermitianPairingAddLeft modes
          viscPacket nonlinPacket baseWeighted))
      (trans
        (finiteHermitianPairingCongRight modes basePacket
          (Drift.weightedPacketField datum (Drift.literalRHS datum))
          (First.fieldAdd viscWeighted nonlinWeighted)
          (weightedRHSSplitPointwise datum))
        (Packet.finiteHermitianPairingAddRight modes
          basePacket viscWeighted nonlinWeighted)))
    (Packet.complexInterchange a b c d)

rawDissipationTangentViscous :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawDissipationTangentViscous datum =
  C3.real (complexDissipationTangentComponent datum (viscousRHS datum))

rawDissipationTangentNonlinear :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawDissipationTangentNonlinear datum =
  C3.real (complexDissipationTangentComponent datum (nonlinearRHS datum))

rawDissipationTangentSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.rawDissipationTangent datum
  ≡ C3.add (LP.realField model)
      (rawDissipationTangentViscous datum)
      (rawDissipationTangentNonlinear datum)
rawDissipationTangentSplitsExactly datum =
  trans
    (cong C3.real (complexDissipationTangentSplitsExactly datum))
    (realOfComplexAdd
      (complexDissipationTangentComponent datum (viscousRHS datum))
      (complexDissipationTangentComponent datum (nonlinearRHS datum)))

------------------------------------------------------------------------
-- Relative-growth split on the same raw q and D.
------------------------------------------------------------------------

relativeGrowthComponent :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model →
  C3.Carrier (LP.realField model) →
  C3.Carrier (LP.realField model) →
  C3.Carrier (LP.realField model)
relativeGrowthComponent {model = model} datum qdot ddot =
  Scale.realSubtract (LP.realField model)
    (C3.multiply (LP.realField model) qdot (Drift.rawDissipation datum))
    (C3.multiply (LP.realField model) (Drift.rawTransfer datum) ddot)

viscousRelativeGrowthCore :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
viscousRelativeGrowthCore datum =
  relativeGrowthComponent datum
    (rawTransferTangentViscous datum)
    (rawDissipationTangentViscous datum)

nonlinearRelativeGrowthCore :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
nonlinearRelativeGrowthCore datum =
  relativeGrowthComponent datum
    (rawTransferTangentNonlinear datum)
    (rawDissipationTangentNonlinear datum)

rawRelativeGrowthCoreSplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.rawRelativeGrowthCore datum
  ≡ C3.add (LP.realField model)
      (viscousRelativeGrowthCore datum)
      (nonlinearRelativeGrowthCore datum)
rawRelativeGrowthCoreSplitsExactly {model = model} datum
  rewrite rawTransferTangentSplitsExactly datum
        | rawDissipationTangentSplitsExactly datum =
  P.R.solve 6
    (λ q d qv qn dv dn →
      (((qv P.R.⊕ qn) P.R.⊗ d)
        P.R.⊕ P.R.⊝ (q P.R.⊗ (dv P.R.⊕ dn)))
      P.R.⊜
      ((qv P.R.⊗ d) P.R.⊕ P.R.⊝ (q P.R.⊗ dv))
      P.R.⊕
      ((qn P.R.⊗ d) P.R.⊕ P.R.⊝ (q P.R.⊗ dn)))
    refl
    (Drift.rawTransfer datum)
    (Drift.rawDissipation datum)
    (rawTransferTangentViscous datum)
    (rawTransferTangentNonlinear datum)
    (rawDissipationTangentViscous datum)
    (rawDissipationTangentNonlinear datum)
  where
  module P = Field.Polynomial (LP.realField model)

round83LiteralRHSViscousNonlinearSplitConstructed : Bool
round83LiteralRHSViscousNonlinearSplitConstructed = true

round83TransferTangentSplitsViscousNonlinearExactly : Bool
round83TransferTangentSplitsViscousNonlinearExactly = true

round83DissipationTangentSplitsViscousNonlinearExactly : Bool
round83DissipationTangentSplitsViscousNonlinearExactly = true

round83RelativeGrowthSplitsViscousNonlinearExactly : Bool
round83RelativeGrowthSplitsViscousNonlinearExactly = true

round83NonlinearComponentPhysicalPressureEstimateConstructed : Bool
round83NonlinearComponentPhysicalPressureEstimateConstructed = false

round83RelativeGrowthSplitsViscousNonlinearExactlyIsTrue :
  round83RelativeGrowthSplitsViscousNonlinearExactly ≡ true
round83RelativeGrowthSplitsViscousNonlinearExactlyIsTrue = refl
