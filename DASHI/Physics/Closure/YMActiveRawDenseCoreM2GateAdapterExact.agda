{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMActiveRawDenseCoreM2GateAdapterExact where

------------------------------------------------------------------------
-- YM FULL-PROOF SPINE / ACTUAL DENSE-CORE EXCLUSION -> CLAY M2 GATE
--
-- The mass-gap gate package keeps M2 abstract on purpose.  Our current composed
-- proof spine now produces an actual theorem
--
--   DenseCoreSpectralExclusion denseData.
--
-- Do not promote that theorem into an arbitrary M2 slot by naming alone.  This
-- adapter requires the explicit same-proposition equality between the selected
-- gate package's M2 proposition and this exact dense-core exclusion theorem.
-- Only then is M2 paid by equality transport.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact as Gates
import DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact as Dense
import DASHI.Physics.Closure.YMActiveRawBC1ToDenseCoreProofSpineExact as Spine

record ActiveRawDenseCoreM2GateWeld
    {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness bc1Inputs}
    (spine : Spine.ActiveRawBC1ToDenseCoreInputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background} {Fluctuation = Fluctuation}
      {Action = Action} {WilsonTerm = WilsonTerm} {RTerm = RTerm}
      {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      {objects = objects} {predicates = predicates}
      {decoder = decoder} {rawWitness = rawWitness}
      bc1Inputs)
    (gates : Gates.ClayMassGapGatePropositions) : Set₁ where
  field
    m2IsExactDenseCoreSpectralExclusion :
      Gates.M2DenseCoreSpectralExclusion gates
      ≡ Dense.DenseCoreSpectralExclusion (Spine.denseData spine)

open ActiveRawDenseCoreM2GateWeld public

activeRawDenseCorePaysM2 :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness bc1Inputs gates}
    {spine : Spine.ActiveRawBC1ToDenseCoreInputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background} {Fluctuation = Fluctuation}
      {Action = Action} {WilsonTerm = WilsonTerm} {RTerm = RTerm}
      {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      {objects = objects} {predicates = predicates}
      {decoder = decoder} {rawWitness = rawWitness}
      bc1Inputs} →
  ActiveRawDenseCoreM2GateWeld spine gates →
  Gates.M2DenseCoreSpectralExclusion gates
activeRawDenseCorePaysM2 {spine = spine} {gates = gates} weld =
  subst
    (λ P → P)
    (sym (m2IsExactDenseCoreSpectralExclusion weld))
    (Spine.activeRawRowCDenseCoreSpectralExclusion spine)

activeRawDenseCoreM2TransportCompilerLevel : ProofLevel
activeRawDenseCoreM2TransportCompilerLevel = machineChecked

-- The theorem construction is closed after the same-proposition weld.  The
-- physical payments remain those exposed by the underlying source->BC1->Row-C
-- ->dense-core spine, plus this exact M2 proposition identification.
activeRawDenseCoreM2SamePropositionWeldLevel : ProofLevel
activeRawDenseCoreM2SamePropositionWeldLevel = conditional

physicalDenseCoreProducerLevel : ProofLevel
physicalDenseCoreProducerLevel = conditional
