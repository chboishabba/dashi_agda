#!/usr/bin/env bash
set -euo pipefail

# Focused source-written contract for the six currently shallowest Chinese science fibres.

grep -q 'canonicalChenVerificationModel' DASHI/ComputerScience/ChenShumingGraphHardwareVerificationBidiExact.agda
grep -q '10.1155/2018/6398616' DASHI/ComputerScience/ChenShumingGraphHardwareVerificationBidiExact.agda
grep -q 'publicationImpliesGalaxyProcessorInstantiation = false' DASHI/ComputerScience/ChenShumingGraphHardwareVerificationBidiExact.agda

grep -q 'canonicalZhouAerogelState' DASHI/Physics/Materials/ZhouGuangyuanPolyimideAerogelBidiExact.agda
grep -q '10.1016/j.cej.2023.147642' DASHI/Physics/Materials/ZhouGuangyuanPolyimideAerogelBidiExact.agda
grep -q 'thermalConductivityAt200C' DASHI/Physics/Materials/ZhouGuangyuanPolyimideAerogelBidiExact.agda
grep -q 'measuredExampleImpliesUniversalProcessWindow = false' DASHI/Physics/Materials/ZhouGuangyuanPolyimideAerogelBidiExact.agda

grep -q 'canonicalLiuDSMMModel' DASHI/ComputerScience/LiuDonghaoDSMMBidiExact.agda
grep -q 'GB/T 37988-2019' DASHI/ComputerScience/LiuDonghaoDSMMBidiExact.agda
grep -q 'DSMMImpliesCryptographicPrimitive = false' DASHI/ComputerScience/LiuDonghaoDSMMBidiExact.agda

grep -q 'canonicalZhangXiaoxinForecastPipeline' DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastBidiExact.agda
grep -q '10.1029/2023SW003522' DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastBidiExact.agda
grep -q 'forecastPipelineImpliesFengyunPayloadCalibration = false' DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastBidiExact.agda

grep -q 'canonicalZhangDaibingControlPipeline' DASHI/Control/ZhangDaibingUAVControlBidiExact.agda
grep -q '10.11887/j.cn.201801023' DASHI/Control/ZhangDaibingUAVControlBidiExact.agda
grep -q 'publishedControlLawImpliesSpecificDeployment = false' DASHI/Control/ZhangDaibingUAVControlBidiExact.agda

grep -q 'canonicalLiMinyongPhotoControlModel' DASHI/Biology/LiMinyongPhotopharmacologyBidiExact.agda
grep -q '10.1002/med.22120' DASHI/Biology/LiMinyongPhotopharmacologyBidiExact.agda
grep -q 'probeOrReviewImpliesClinicalEfficacy = false' DASHI/Biology/LiMinyongPhotopharmacologyBidiExact.agda

grep -q 'ChenShumingGraphHardwareVerificationBidiExact' DASHI/Culture/MissingDeceasedChineseScienceImplementationEverything.agda
grep -q 'ZhouGuangyuanPolyimideAerogelBidiExact' DASHI/Culture/MissingDeceasedChineseScienceImplementationEverything.agda
grep -q 'LiuDonghaoDSMMBidiExact' DASHI/Culture/MissingDeceasedChineseScienceImplementationEverything.agda
grep -q 'ZhangXiaoxinGeomagneticForecastBidiExact' DASHI/Culture/MissingDeceasedChineseScienceImplementationEverything.agda
grep -q 'ZhangDaibingUAVControlBidiExact' DASHI/Culture/MissingDeceasedChineseScienceImplementationEverything.agda
grep -q 'LiMinyongPhotopharmacologyBidiExact' DASHI/Culture/MissingDeceasedChineseScienceImplementationEverything.agda

echo 'Chinese science implementation static check: ok'
