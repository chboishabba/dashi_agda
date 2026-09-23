module DASHI.Education.DigitalESDNormativeStandardsAtlasRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDNormativeStandardsAtlasExact as Standards

iso9001Pinned : Standards.StandardLens
iso9001Pinned = Standards.iso9001-2026

iso42001Pinned : Standards.StandardLens
iso42001Pinned = Standards.isoIEC42001-2023

iso27001Pinned : Standards.StandardLens
iso27001Pinned = Standards.isoIEC27001-2022

iso27701Pinned : Standards.StandardLens
iso27701Pinned = Standards.isoIEC27701-2025

iso23894Pinned : Standards.StandardLens
iso23894Pinned = Standards.isoIEC23894-2023

iso9241-110Pinned : Standards.StandardLens
iso9241-110Pinned = Standards.iso9241-110-2020

iso9241-161Pinned : Standards.StandardLens
iso9241-161Pinned = Standards.iso9241-161-2025

iso9241-210Pinned : Standards.StandardLens
iso9241-210Pinned = Standards.iso9241-210-2019

iso9241-306Pinned : Standards.StandardLens
iso9241-306Pinned = Standards.iso9241-306-2018

iso24552Pinned : Standards.StandardLens
iso24552Pinned = Standards.iso24552-2020

iso16817Pinned : Standards.StandardLens
iso16817Pinned = Standards.iso16817-2017

iso24505-1Pinned : Standards.StandardLens
iso24505-1Pinned = Standards.iso24505-1-2025

iso24505-2Pinned : Standards.StandardLens
iso24505-2Pinned = Standards.iso24505-2-2025

iso22727Pinned : Standards.StandardLens
iso22727Pinned = Standards.iso22727-2007

nistPinned : Standards.StandardLens
nistPinned = Standards.nistAIRMF10

itilPinned : Standards.StandardLens
itilPinned = Standards.itil4

sixSigmaPinned : Standards.StandardLens
sixSigmaPinned = Standards.sixSigmaDMAIC

iso42005Pinned : Standards.StandardLens
iso42005Pinned = Standards.isoIEC42005-2025

mentionNoConformity : Standards.StandardMentionCreatesConformity → ⊥
mentionNoConformity = Standards.standardMentionDoesNotCreateConformity

claimNoCertification : Standards.ClaimedConformityCreatesCertifiedConformity → ⊥
claimNoCertification = Standards.claimedConformityDoesNotCreateCertifiedConformity

conformityNoEducationalEffect : Standards.StandardConformityCreatesEducationalEffect → ⊥
conformityNoEducationalEffect = Standards.standardConformityDoesNotCreateEducationalEffect
