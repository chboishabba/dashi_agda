#!/usr/bin/env runghc

import Data.List (intercalate)
import System.Directory (createDirectoryIfMissing)
import qualified MAlonzo.Code.DASHI.Physics.Closure.ShiftContractCollapseTime as Collapse
import qualified MAlonzo.Code.DASHI.Physics.Closure.ShiftContractMixedScaleTrajectoryFamily as Mixed
import qualified MAlonzo.Code.DASHI.Physics.Closure.ShiftContractParametricTrajectoryCompositionFamily as Prefix
import qualified MAlonzo.Code.Ontology.GodelLattice as GL
import qualified MAlonzo.Code.Ontology.Hecke.DefectOrbitCollapseBridge as Bridge
import qualified MAlonzo.Code.Ontology.Hecke.FactorVecDefectOrbitSummaries as Summaries
import MAlonzo.RTE (coe)

type Generator = Collapse.T_GeneratorCollapseClass_54

data LaneSummary = LaneSummary
  { forcedStableCount :: Integer
  , motifChangeCount :: Integer
  , totalDrift :: Integer
  , repatterningCount :: Integer
  , contractiveCount :: Integer
  , expansiveCount :: Integer
  }

defaultOutputPath :: FilePath
defaultOutputPath = "artifacts/hecke/profile_summary_family.json"

generators :: [(String, Generator)]
generators =
  [ ("explicitWidth1", Collapse.C_prefixClass_56 Prefix.C_explicitWidth1_10)
  , ("explicitWidth2", Collapse.C_prefixClass_56 Prefix.C_explicitWidth2_12)
  , ("explicitWidth3", Collapse.C_prefixClass_56 Prefix.C_explicitWidth3_14)
  , ("balancedCycle", Collapse.C_prefixClass_56 Prefix.C_balancedCycle_16)
  , ("denseComposed", Collapse.C_prefixClass_56 Prefix.C_denseComposed_18)
  , ("balancedComposed", Collapse.C_prefixClass_56 Prefix.C_balancedComposed_20)
  , ("anchoredTrajectory", Collapse.C_prefixClass_56 Prefix.C_anchoredTrajectory_22)
  , ("supportCascade", Collapse.C_mixedScaleClass_58 Mixed.C_supportCascade_18)
  , ("fullSupportCascade", Collapse.C_mixedScaleClass_58 Mixed.C_fullSupportCascade_20)
  ]

decodeSummary :: Summaries.T_DefectOrbitSummary_50 -> LaneSummary
decodeSummary summary =
  LaneSummary
    { forcedStableCount = Summaries.d_forcedStableCount_64 summary
    , motifChangeCount = Summaries.d_motifChangeCount_66 summary
    , totalDrift = Summaries.d_totalDrift_68 summary
    , repatterningCount = Summaries.d_repatterningCount_70 summary
    , contractiveCount = Summaries.d_contractiveCount_72 summary
    , expansiveCount = Summaries.d_expansiveCount_74 summary
    }

vec15ToList :: GL.T_Vec15_6 -> [Summaries.T_DefectOrbitSummary_50]
vec15ToList vec =
  [ coe (GL.d_e2_40 vec)
  , coe (GL.d_e3_42 vec)
  , coe (GL.d_e5_44 vec)
  , coe (GL.d_e7_46 vec)
  , coe (GL.d_e11_48 vec)
  , coe (GL.d_e13_50 vec)
  , coe (GL.d_e17_52 vec)
  , coe (GL.d_e19_54 vec)
  , coe (GL.d_e23_56 vec)
  , coe (GL.d_e29_58 vec)
  , coe (GL.d_e31_60 vec)
  , coe (GL.d_e41_62 vec)
  , coe (GL.d_e47_64 vec)
  , coe (GL.d_e59_66 vec)
  , coe (GL.d_e71_68 vec)
  ]

materializeFamily :: Generator -> [LaneSummary]
materializeFamily generator =
  map decodeSummary $
    vec15ToList $
      Summaries.d_profileSummaryFamily_84 $
        Bridge.d_primeImage_8 generator

jsonSummary :: LaneSummary -> String
jsonSummary summary =
  intercalate
    "\n"
    [ "    {"
    , "      \"forcedStableCount\": " ++ show (forcedStableCount summary) ++ ","
    , "      \"motifChangeCount\": " ++ show (motifChangeCount summary) ++ ","
    , "      \"totalDrift\": " ++ show (totalDrift summary) ++ ","
    , "      \"repatterningCount\": " ++ show (repatterningCount summary) ++ ","
    , "      \"contractiveCount\": " ++ show (contractiveCount summary) ++ ","
    , "      \"expansiveCount\": " ++ show (expansiveCount summary)
    , "    }"
    ]

jsonGenerator :: (String, [LaneSummary]) -> String
jsonGenerator (name, summaries) =
  intercalate
    "\n"
    [ "  " ++ show name ++ ": ["
    , intercalate ",\n" (map jsonSummary summaries)
    , "  ]"
    ]

jsonDocument :: [(String, [LaneSummary])] -> String
jsonDocument entries =
  intercalate
    "\n"
    [ "{"
    , intercalate ",\n" (map jsonGenerator entries)
    , "}"
    ]

main :: IO ()
main = do
  let outputPath = defaultOutputPath
  createDirectoryIfMissing True "artifacts/hecke"
  writeFile outputPath $
    jsonDocument [(name, materializeFamily generator) | (name, generator) <- generators]
  putStrLn outputPath
