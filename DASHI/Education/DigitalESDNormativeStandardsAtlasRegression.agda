module DASHI.Education.DigitalESDNormativeStandardsAtlasRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDNormativeStandardsAtlasExact as Standards

iso9001Pinned : Standards.StandardLens
iso9001Pinned = Standards.iso9001_2026

iso42001Pinned : Standards.StandardLens
iso42001Pinned = Standards.isoIEC42001_2023

iso27001Pinned : Standards.StandardLens
iso27001Pinned = Standards.isoIEC27001_2022

iso27701Pinned : Standards.StandardLens
iso27701Pinned = Standards.isoIEC27701_2025

iso23894Pinned : Standards.StandardLens
iso23894Pinned = Standards.isoIEC23894_2023

iso9241_110Pinned : Standards.StandardLens
iso9241_110Pinned = Standards.iso9241_110_2020

iso9241_161Pinned : Standards.StandardLens
iso9241_161Pinned = Standards.iso9241_161_2025

iso9241_210Pinned : Standards.StandardLens
iso9241_210Pinned = Standards.iso9241_210_2019

iso9241_306Pinned : Standards.StandardLens
iso9241_306Pinned = Standards.iso9241_306_2018

iso24552Pinned : Standards.StandardLens
iso24552Pinned = Standards.iso24552_2020

iso16817Pinned : Standards.StandardLens
iso16817Pinned = Standards.iso16817_2017

iso24505_1Pinned : Standards.StandardLens
iso24505_1Pinned = Standards.iso24505_1_2025

iso24505_2Pinned : Standards.StandardLens
iso24505_2Pinned = Standards.iso24505_2_2025

iso22727Pinned : Standards.StandardLens
iso22727Pinned = Standards.iso22727_2007

nistPinned : Standards.StandardLens
nistPinned = Standards.nistAIRMF10

itilPinned : Standards.StandardLens
itilPinned = Standards.itil4

sixSigmaPinned : Standards.StandardLens
sixSigmaPinned = Standards.sixSigmaDMAIC

iso42005Pinned : Standards.StandardLens
iso42005Pinned = Standards.isoIEC42005_2025

mentionNoConformity : Standards.StandardMentionCreatesConformity → ⊥
mentionNoConformity = Standards.standardMentionDoesNotCreateConformity

claimNoCertification : Standards.ClaimedConformityCreatesCertifiedConformity → ⊥
claimNoCertification = Standards.claimedConformityDoesNotCreateCertifiedConformity

conformityNoEducationalEffect : Standards.StandardConformityCreatesEducationalEffect → ⊥
conformityNoEducationalEffect = Standards.standardConformityDoesNotCreateEducationalEffect
