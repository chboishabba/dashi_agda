module DASHI.Biology.StressPhysiologyCascadeExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- FINITE STRESS-PHYSIOLOGY CASCADE
--
-- Empirical calibration:
-- Amy F. T. Arnsten,
-- "Stress weakens prefrontal networks: molecular insults to higher cognition",
-- Nature Neuroscience 18 (2015), 1376-1385.
-- DOI: 10.1038/nn.4087
--
-- Sally S. Dickerson; Margaret E. Kemeny,
-- "Acute stressors and cortisol responses: a theoretical integration and
-- synthesis of laboratory research", Psychological Bulletin 130 (2004),
-- 355-391. DOI: 10.1037/0033-2909.130.3.355
--
-- This module preserves the distinction between a rapid autonomic/
-- catecholaminergic route and the slower HPA route.  It is a qualitative
-- topology/timescale model, not a quantitative endocrine fit.
------------------------------------------------------------------------

data Mediator : Set where
  crh acth cortisol norepinephrine dopamine sympatheticDrive parasympatheticDrive : Mediator

data PhysiologicalSite : Set where
  hypothalamus pituitary adrenalCortex locusCoeruleus autonomicEffector : PhysiologicalSite

data TimescaleClass : Set where
  rapidRoute slowerEndocrineRoute : TimescaleClass

data CascadeEdge : Mediator → Mediator → Set where
  crhToActh : CascadeEdge crh acth
  acthToCortisol : CascadeEdge acth cortisol

data Route : Mediator → Mediator → Set where
  routeEdge : ∀ {a b} → CascadeEdge a b → Route a b
  routeCompose : ∀ {a b c} → Route a b → Route b c → Route a c

hpaRoute : Route crh cortisol
hpaRoute = routeCompose (routeEdge crhToActh) (routeEdge acthToCortisol)

mediatorSite : Mediator → PhysiologicalSite
mediatorSite crh = hypothalamus
mediatorSite acth = pituitary
mediatorSite cortisol = adrenalCortex
mediatorSite norepinephrine = locusCoeruleus
mediatorSite dopamine = locusCoeruleus
mediatorSite sympatheticDrive = autonomicEffector
mediatorSite parasympatheticDrive = autonomicEffector

mediatorTimescale : Mediator → TimescaleClass
mediatorTimescale crh = slowerEndocrineRoute
mediatorTimescale acth = slowerEndocrineRoute
mediatorTimescale cortisol = slowerEndocrineRoute
mediatorTimescale norepinephrine = rapidRoute
mediatorTimescale dopamine = rapidRoute
mediatorTimescale sympatheticDrive = rapidRoute
mediatorTimescale parasympatheticDrive = rapidRoute

norepinephrineAndCortisolTimescalesDiffer :
  mediatorTimescale norepinephrine ≡ mediatorTimescale cortisol → ⊥
norepinephrineAndCortisolTimescalesDiffer ()

sympatheticAndCortisolTimescalesDiffer :
  mediatorTimescale sympatheticDrive ≡ mediatorTimescale cortisol → ⊥
sympatheticAndCortisolTimescalesDiffer ()

data ControlAppraisal : Set where
  controllable uncontrollable : ControlAppraisal

data RecruitmentProfile : Set where
  adaptiveMobilisation strongerThreatRecruitment : RecruitmentProfile

recruitmentFor : ControlAppraisal → RecruitmentProfile
recruitmentFor controllable = adaptiveMobilisation
recruitmentFor uncontrollable = strongerThreatRecruitment

controlAppraisalChangesCandidateRecruitment :
  recruitmentFor controllable ≡ recruitmentFor uncontrollable → ⊥
controlAppraisalChangesCandidateRecruitment ()

record StressPhysiologyBoundary : Set where
  constructor stressPhysiologyBoundary
  field
    cortisolIsWholeStressState : Bool
    acuteAutonomicAndHPAAreSameTimescale : Bool
    uncontrollabilityDeterministicallySetsHumanCortisol : Bool
    qualitativeCascadeDiagnosesPerson : Bool
    hpaMediatorOrderRepresented : Bool

canonicalStressPhysiologyBoundary : StressPhysiologyBoundary
canonicalStressPhysiologyBoundary =
  stressPhysiologyBoundary false false false false true
