module DASHI.Environment.BiocontrolAttributionSnowballRegression where

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Environment.BiocontrolExternalityExperimentSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- Attribution is typed through the repo-wide source carrier and every retained
-- source role carries the canonical snowball receipt.
------------------------------------------------------------------------

sourceAtlasUsesCanonicalCarrier : Attribution.AttributedSourceAtlas
sourceAtlasUsesCanonicalCarrier = Atlas.canonicalBiocontrolSourceAtlas

csiroRoleSnowballs : Snowball.SourceRoleSnowballReceipt Atlas.csiroHyacinthSource
csiroRoleSnowballs = Atlas.csiroHyacinthSnowballReceipt

guideRoleSnowballs : Snowball.SourceRoleSnowballReceipt Atlas.australianManagementGuideSource
guideRoleSnowballs = Atlas.australianManagementGuideSnowballReceipt

daFFRoleSnowballs : Snowball.SourceRoleSnowballReceipt Atlas.daffBiocontrolAgentsSource
daFFRoleSnowballs = Atlas.daffBiocontrolAgentsSnowballReceipt

deLoachRoleSnowballs : Snowball.SourceRoleSnowballReceipt Atlas.deLoach1976Source
deLoachRoleSnowballs = Atlas.deLoach1976SnowballReceipt

sunkenBiomassRoleSnowballs : Snowball.SourceRoleSnowballReceipt Atlas.ogutuOhwayo2002Source
sunkenBiomassRoleSnowballs = Atlas.ogutuOhwayo2002SnowballReceipt

communityCompetitionRoleSnowballs : Snowball.SourceRoleSnowballReceipt Atlas.centerEtAl2005Source
communityCompetitionRoleSnowballs = Atlas.centerEtAl2005SnowballReceipt

sustainableControlRoleSnowballs : Snowball.SourceRoleSnowballReceipt Atlas.chalaEtAl2026Source
sustainableControlRoleSnowballs = Atlas.chalaEtAl2026SnowballReceipt

agentInteractionRoleSnowballs : Snowball.SourceRoleSnowballReceipt Atlas.marianiEtAl2026Source
agentInteractionRoleSnowballs = Atlas.marianiEtAl2026SnowballReceipt
