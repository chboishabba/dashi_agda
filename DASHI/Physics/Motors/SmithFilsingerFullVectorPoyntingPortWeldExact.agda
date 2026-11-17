module DASHI.Physics.Motors.SmithFilsingerFullVectorPoyntingPortWeldExact where

-- F10 source REUSE: the existing KSW668 full 3-component Maxwell jet
-- theorem, not a symbolic F=dA replacement or a numeric simulation.
-- Filsinger original-source and terminal work admission remain OPEN.
--
-- CRITICAL distinction: the pointwise Poynting identity is already proven
-- for an Ampere/Faraday curl jet. A physical spacetime boundary integral,
-- constitutive response and source/receiver port identification are
-- separately REQUIRED for the port work equality.
--
-- User-origin Smith/Filsinger energy-access hypothesis. Original KSW668
-- Maxwell jet and Maxwell-material finite ledger are reused unchanged.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as Vector
import DASHI.Physics.Motors.SmithFilsingerMaxwellMaterialEnergyCutExact as Cut
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- Direct exact proof delegation to original three-component Maxwell owner.
-- This genuinely consumes curl E, curl B, temporal E/B and J dot E.
-- It is not a surface-integral theorem or fitted natural source.
threeComponentPoyntingFromOriginalMaxwell :
  ∀ {r} {F : C3.RealField r} →
  (jet : Vector.FullVectorMaxwellJet F) →
  Vector.fullVectorSignedBudget jet ≡ C3.zero F
threeComponentPoyntingFromOriginalMaxwell =
  Vector.fullVectorMaxwellPoyntingIdentity

-- The missing source/field-to-port map has the following EXACT shape.
-- It may be discharged by a verified domain/time divergence theorem plus
-- Maxwell constitutive/material identities and source measurements.
-- No field metric, flux, surface, or work is silently assigned here.
MaxwellJetToSelectedFieldWork :
  ∀ {r} {F : C3.RealField r} →
  (jet : Vector.FullVectorMaxwellJet F) →
  (naturalNet controllerNet initialField interfaceWork
   fieldOutgoing finalField : Nat) →
  Set
MaxwellJetToSelectedFieldWork jet n d fi i l ff =
  Vector.fullVectorSignedBudget jet ≡ C3.zero _ →
  (n + d) + fi ≡ i + (l + ff)

-- The bridge is an implication whose INPUT is the already proven pointwise
-- Maxwell identity. Supplying this implication requires a real surface,
-- orientation, time domain, metric and endpoint. This theorem DOES NOT
-- derive the physical implication from local curl algebra.
fieldWorkFromMaxwellJetAndIntegration :
  ∀ {r} {F : C3.RealField r} →
  (jet : Vector.FullVectorMaxwellJet F) →
  (n d fi i l ff : Nat) →
  MaxwellJetToSelectedFieldWork jet n d fi i l ff →
  (n + d) + fi ≡ i + (l + ff)
fieldWorkFromMaxwellJetAndIntegration jet n d fi i l ff integrate =
  integrate (threeComponentPoyntingFromOriginalMaxwell jet)

-- Crucially, derive full material+field conservation from an original
-- three-component Maxwell jet AND a separately supplied material balance.
-- The common interface is eliminated through the ORIGINAL finite cut.
fullVectorMaxwellToMaterialCompleteLedger :
  ∀ {r} {F : C3.RealField r} →
  (jet : Vector.FullVectorMaxwellJet F) →
  (naturalNet controllerNet fieldInitially interfaceWork fieldLoss fieldFinally
   paidModulation materialInitially usefulLoad materialLoss modulationRecovery
   materialFinally : Nat) →
  MaxwellJetToSelectedFieldWork jet naturalNet controllerNet
    fieldInitially interfaceWork fieldLoss fieldFinally →
  interfaceWork + (paidModulation + materialInitially)
    ≡ usefulLoad + (materialLoss + (modulationRecovery + materialFinally)) →
  ((naturalNet + controllerNet) + paidModulation)
    + (fieldInitially + materialInitially)
  ≡ usefulLoad + (fieldLoss + (materialLoss
    + (modulationRecovery + (fieldFinally + materialFinally))))
fullVectorMaxwellToMaterialCompleteLedger
  jet n d fi i fl ff m mi load ml rec mf integrated physicalMaterial =
  Cycle.trans
    (solve 5
      (λ n d m fi mi →
        (((n :+ d) :+ m) :+ (fi :+ mi))
        := (((n :+ d) :+ fi) :+ (m :+ mi)))
      refl n d m fi mi)
    (Cycle.trans
      (Cut.cancelSharedInterface _ _ _ _ i
        (fieldWorkFromMaxwellJetAndIntegration jet n d fi i fl ff integrated)
        physicalMaterial)
      (solve 6
        (λ fl ff l ml rec mf →
          ((fl :+ ff) :+ (l :+ (ml :+ (rec :+ mf))))
          := (l :+ (fl :+ (ml :+ (rec :+ (ff :+ mf))))))
        refl fl ff load ml rec mf))

-- Source-indexed consumer: unlike simply invoking an unrelated Maxwell jet,
-- the integration bridge must identify the exact original selected field,
-- receiver and signed source/controller work from the existing weld record.
--
-- This is intentionally an obligation, not a theorem assigning a measured
-- Maxwell field to historical Filsinger electrode pins. The association
-- with original geometry can NEVER be inferred from choosing a jet.
record SameOriginalPhysicalFieldBoundary
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f) : Set₂ where
  field
    ActualSpatialDomainWithOrientedBoundary : Set
    RealConstitutiveAndChargeCurrent : Set
    TimeIntegratedDivergenceAndBoundaryFlux : Set
    TimeSynchronousSourceAndReceiverVI : Set
    originalDomain : ActualSpatialDomainWithOrientedBoundary
    material : RealConstitutiveAndChargeCurrent
    poyntingIntegration : TimeIntegratedDivergenceAndBoundaryFlux
    measuredPort : TimeSynchronousSourceAndReceiverVI

-- The bridge ends here: original full-vector differential conservation
-- is mathematically available; the physical integrated-port equality
-- cannot be manufactured from the symbolic Maxwell exterior adapter.
