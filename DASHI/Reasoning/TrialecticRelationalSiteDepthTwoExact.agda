module DASHI.Reasoning.TrialecticRelationalSiteDepthTwoExact where

------------------------------------------------------------------------
-- STRICT DEPTH OF THE SEVEN-OBJECT RELATIONAL SITE
--
-- RelHom contains identities plus the incidence arrows
--
--   vertex -> edge -> global
--   vertex ----------> global.
--
-- This owner strips identities and proves that there is no composable chain
-- of three strict arrows.  Hence every nondegenerate nerve simplex has degree
-- at most two; higher simplicial degrees contain degeneracies only.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site

data StrictRelHom : Site.RelObj → Site.RelObj → Set where
  strictABToGlobal : StrictRelHom Site.edgeAB Site.globalABC
  strictBCToGlobal : StrictRelHom Site.edgeBC Site.globalABC
  strictCAToGlobal : StrictRelHom Site.edgeCA Site.globalABC

  strictAToAB : StrictRelHom Site.vertexA Site.edgeAB
  strictBToAB : StrictRelHom Site.vertexB Site.edgeAB
  strictBToBC : StrictRelHom Site.vertexB Site.edgeBC
  strictCToBC : StrictRelHom Site.vertexC Site.edgeBC
  strictCToCA : StrictRelHom Site.vertexC Site.edgeCA
  strictAToCA : StrictRelHom Site.vertexA Site.edgeCA

  strictAToGlobal : StrictRelHom Site.vertexA Site.globalABC
  strictBToGlobal : StrictRelHom Site.vertexB Site.globalABC
  strictCToGlobal : StrictRelHom Site.vertexC Site.globalABC

forgetStrict :
  ∀ {U V : Site.RelObj} →
  StrictRelHom U V → Site.RelHom U V
forgetStrict strictABToGlobal = Site.abToGlobal
forgetStrict strictBCToGlobal = Site.bcToGlobal
forgetStrict strictCAToGlobal = Site.caToGlobal
forgetStrict strictAToAB = Site.aToAB
forgetStrict strictBToAB = Site.bToAB
forgetStrict strictBToBC = Site.bToBC
forgetStrict strictCToBC = Site.cToBC
forgetStrict strictCToCA = Site.cToCA
forgetStrict strictAToCA = Site.aToCA
forgetStrict strictAToGlobal = Site.aToGlobal
forgetStrict strictBToGlobal = Site.bToGlobal
forgetStrict strictCToGlobal = Site.cToGlobal

------------------------------------------------------------------------
-- No strict arrow enters a vertex.
------------------------------------------------------------------------

noStrictIntoA :
  ∀ {U : Site.RelObj} → StrictRelHom U Site.vertexA → ⊥
noStrictIntoA ()

noStrictIntoB :
  ∀ {U : Site.RelObj} → StrictRelHom U Site.vertexB → ⊥
noStrictIntoB ()

noStrictIntoC :
  ∀ {U : Site.RelObj} → StrictRelHom U Site.vertexC → ⊥
noStrictIntoC ()

------------------------------------------------------------------------
-- Therefore no three strict arrows compose.
------------------------------------------------------------------------

noStrictThreeArrowChain :
  ∀ {U V W X : Site.RelObj} →
  StrictRelHom W X →
  StrictRelHom V W →
  StrictRelHom U V →
  ⊥
noStrictThreeArrowChain strictABToGlobal strictAToAB third = noStrictIntoA third
noStrictThreeArrowChain strictABToGlobal strictBToAB third = noStrictIntoB third
noStrictThreeArrowChain strictBCToGlobal strictBToBC third = noStrictIntoB third
noStrictThreeArrowChain strictBCToGlobal strictCToBC third = noStrictIntoC third
noStrictThreeArrowChain strictCAToGlobal strictCToCA third = noStrictIntoC third
noStrictThreeArrowChain strictCAToGlobal strictAToCA third = noStrictIntoA third
noStrictThreeArrowChain strictAToGlobal ()
noStrictThreeArrowChain strictBToGlobal ()
noStrictThreeArrowChain strictCToGlobal ()
noStrictThreeArrowChain strictAToAB ()
noStrictThreeArrowChain strictBToAB ()
noStrictThreeArrowChain strictBToBC ()
noStrictThreeArrowChain strictCToBC ()
noStrictThreeArrowChain strictCToCA ()
noStrictThreeArrowChain strictAToCA ()

record TrialecticRelationalSiteDepthBoundary : Set where
  constructor trialectic-relational-site-depth-boundary
  field
    nonIdentityVertexToEdgeArrowsExist : Bool
    nonIdentityEdgeToGlobalArrowsExist : Bool
    directVertexToGlobalArrowsExist : Bool
    strictTwoArrowChainsExist : Bool
    strictThreeArrowChainsExist : Bool
    nondegenerateNerveDimensionAtMostTwo : Bool

open TrialecticRelationalSiteDepthBoundary public

canonicalTrialecticRelationalSiteDepthBoundary :
  TrialecticRelationalSiteDepthBoundary
canonicalTrialecticRelationalSiteDepthBoundary =
  trialectic-relational-site-depth-boundary
    true true true true false true
