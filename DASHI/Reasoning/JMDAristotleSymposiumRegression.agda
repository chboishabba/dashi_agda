module DASHI.Reasoning.JMDAristotleSymposiumRegression where

import DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact as Source
import DASHI.Reasoning.JMDAristotleSymposiumEpistemicFirewallExact as Firewall
import DASHI.Reasoning.ContentAddressedVerificationBridgeExact as Content

------------------------------------------------------------------------
-- RED/GREEN regression surface for the JMD-owned Aristotle Symposium bundle.
-- The imported owners must preserve source attribution, distinguish formal
-- entailment from empirical authority, and separate content-addressed
-- procedural invariance from epistemic correctness.
------------------------------------------------------------------------

sourceAtlasPinned = Source.jmdAristotleSymposiumSourceAtlas
ownershipDeclarationRetained = Source.jmdOwnershipDeclaration
formalEntailmentBoundary = Firewall.canonicalFormalEntailmentAuthorityBoundary
ipAttributionBoundary = Firewall.sourceIPDoesNotDetermineAuthorship
sourcePreferenceTruthBoundary = Firewall.sourcePreferenceDoesNotDetermineTruth
contentAddressedBoundary = Content.canonicalContentAddressedVerificationBoundary
contentAddressingNotTruth = Content.contentAddressingDoesNotCreateTruth
cidNotAuthority = Content.cidDoesNotCreateSemanticAuthority
