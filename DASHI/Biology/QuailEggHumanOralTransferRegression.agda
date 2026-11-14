module DASHI.Biology.QuailEggHumanOralTransferRegression where

open import DASHI.Core.Prelude using (⊥)
import DASHI.Biology.QuailEggHumanOralTransferExact as Q

oralHumanExposureRegression : Q.HumanOralQuailEvidenceReceipt
oralHumanExposureRegression = Q.benichou2014Receipt

adjunctiveRhinitisRegression : Q.HumanOralQuailEvidenceReceipt
adjunctiveRhinitisRegression = Q.andaloro2023Receipt

rhinitisNotIBSRegression : Q.RhinitisEvidencePaysIBSPermission → ⊥
rhinitisNotIBSRegression = Q.rhinitisEvidenceDoesNotPayIBS

combinationNotQuailRegression : Q.QuailPlusZincIdentifiesQuailEffectPermission → ⊥
combinationNotQuailRegression = Q.combinationDoesNotIdentifyQuailEffect

canonicalTransferBoundaryRegression : Q.QuailHumanOralTransferBoundary
canonicalTransferBoundaryRegression = Q.canonicalQuailHumanOralTransferBoundary
