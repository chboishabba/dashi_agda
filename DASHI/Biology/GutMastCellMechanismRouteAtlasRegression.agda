module DASHI.Biology.GutMastCellMechanismRouteAtlasRegression where

import DASHI.Biology.GutMastCellMechanismRouteAtlasExact as M

quailRouteRegression : M.MastCellMechanismRoute
quailRouteRegression = M.quailAlbumenPAR2Route

microbialHistamineRegression : M.MastCellMechanismRoute
microbialHistamineRegression = M.microbialHistamineH4Route

lpsRegression : M.MastCellMechanismRoute
lpsRegression = M.fecalLPSTLR4Route

h1Regression : M.MastCellMechanismRoute
h1Regression = M.histamineH1TRPV1Route

atlasRegression : M.GutMastCellMechanismRouteAtlas
atlasRegression = M.canonicalGutMastCellMechanismRouteAtlas
