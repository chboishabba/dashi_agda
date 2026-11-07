#!/usr/bin/env python3
"""Independent *source-level* finite audit of Gielis/Base369 Agda tables.

This enumerates the literal Agda equations/cases; it DOES NOT elaborate or
type-check them and MUST NOT be promoted to an Agda --safe kernel receipt.
Pure Python standard library; called by check_gielis_base369_cut.sh.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
FILES = (
    "DASHI/Geometry/GielisBase369FiniteExact.agda",
    "DASHI/Geometry/GielisBase369NyquistPhase36Exact.agda",
    "DASHI/Geometry/GielisBase369ExistingOwnersWeldExact.agda",
    "Docs/support/reference/GielisBase369Roadmap.md",
    "Docs/support/reference/GielisBase369ProofTheorems.md",
    "scripts/gielis_base369_experiments.py",
    "DASHI/Geometry/GielisBishopPolynomialExact.agda",
    "DASHI/Geometry/GielisSIPerronOwnerWeldExact.agda",
    "DASHI/Geometry/GielisSpectralSIScaleExact.agda",
    "DASHI/Geometry/GielisFiniteGroundStateEdgeExact.agda",
    "DASHI/Geometry/GielisNineModeFourierExact.agda",
    "DASHI/Geometry/GielisSixPhaseCyclotomicFourierExact.agda",
    "DASHI/Geometry/GielisExactRationalGridPredicateExact.agda",
    "DASHI/Geometry/GielisOpticalTorqueCrossSIExact.agda",
    "DASHI/Geometry/GielisBishopImaginaryExponentialReducerExact.agda",
    "DASHI/Geometry/GielisBishopComplexCauchyAlgebraExact.agda",
    "DASHI/Geometry/GielisBesselFaberKrahnRationalExact.agda",
    "DASHI/Geometry/GielisBishopComplexSeriesSameCarrierExact.agda",
    "scripts/gielis_cyclotomic36_unrestricted_exact.py",
    "scripts/gielis_certified_continuum_fd_error.py",
    "scripts/gielis_kozyrev_same_event_original_owner.py",
    "scripts/gielis_continuum_faber_krahn_bound.py",
    "scripts/gielis_exact_signed_optical_torque.py",
    "scripts/gielis_exact_rational_raster_geometry.py",
    "scripts/gielis_six_phase_cyclotomic_exact.py",
    "scripts/gielis_nine_quarter_fourier_exact.py",
    "scripts/gielis_fd_energy_mosco.py",
)
THEOREMS = (
    "rotation3PreservesSignal", "rotation6PreservesSignal",
    "rotation9PreservesSignal", "reflection3PreservesSignal",
    "reflection6PreservesSignal", "reflection9PreservesSignal",
    "reflectionInvolutive", "rotation3Order",
    "rotation6Order", "rotation9Order",
    "rotate3InverseLeft", "rotate6InverseLeft", "rotate9InverseLeft",
    "rotate3InverseRight", "rotate6InverseRight", "rotate9InverseRight",
    "reflectRotate3", "reflectRotate6", "reflectRotate9",
)


def integer(term: str) -> int:
    term = term.strip()
    positive = re.fullmatch(r"\+\s+(\d+)", term)
    if positive:
        return int(positive.group(1))
    negative = re.fullmatch(r"-\[1\+\s*(\d+)\s*\]", term)
    if negative:
        return -1-int(negative.group(1))
    raise AssertionError(f"not a literal Agda integer: {term!r}")


def table(source: str, name: str, prefix: str, count: int) -> tuple[int, ...]:
    rows = [
        (int(index), integer(term)) for index,term in re.findall(
            rf"^{re.escape(name)} {re.escape(prefix)}-(\d+) = (.+)$",
            source,flags=re.MULTILINE,
        )
    ]
    assert len(rows)==count, (name,len(rows),count)
    assert [i for i,_ in rows] == list(range(count)),name
    return tuple(value for _,value in rows)


def source_audit(root: Path = ROOT) -> dict:
    source = {path:(root/path).read_text() for path in FILES}
    agda=source[FILES[0]]
    ny=source[FILES[1]]
    assert not any(
        re.search(r"(^|\s)postulate(\s|$)|\{\!|--unsafe|--no-termination-check", source[path],flags=re.M)
        for path in FILES if path.endswith(".agda")
    ), "source contains trust escape"

    sig={m:table(agda,f"signal{m}","Phase.p18",18) for m in (3,6,9)}
    assertions=0
    for m,vec in sig.items():
        for j in range(18):
            assert vec[j]==round(2*math.cos(2*math.pi*m*j/18))
            assert vec[(j+18//m)%18]==vec[j]
            assert vec[(18-j)%18]==vec[j]
            assertions+=3

    def dot(x,y): return sum(a*b for a,b in zip(x,y,strict=True))
    gram=[[dot(sig[a],sig[b]) for b in (3,6,9)] for a in (3,6,9)]
    assert gram==[[36,0,0],[0,36,0],[0,0,72]]

    c9=table(ny,"cosNine","p36",36)
    s9=table(ny,"sinNine","p36",36)
    s27=table(ny,"sinTwentySeven","p36",36)
    embedding=[(int(a),int(b)) for a,b in re.findall(
        r"^even18To36 Phase\.p18-(\d+) = p36-(\d+)$",ny,flags=re.M
    )]
    assert embedding==[(j,2*j) for j in range(18)]
    for j in range(18):
        assert s9[2*j]==s27[2*j]==0
        assertions+=2
    assert (s9[1],s27[1])==(1,-1)
    for j in range(36):
        assert c9[j]==(1,0,-1,0)[j%4]
        assert s9[j]==(0,1,0,-1)[j%4]
        assert s27[j]==(0,-1,0,1)[j%4]
        assertions+=3

    for theorem in THEOREMS:
        cases=[int(j) for j in re.findall(
            rf"^{re.escape(theorem)} Phase\.p18-(\d+) = refl$",
            agda,flags=re.M
        )]
        assert cases==list(range(18)),(theorem,cases)
        assertions+=18

    si=source["DASHI/Geometry/GielisSIPerronOwnerWeldExact.agda"]
    for exact_owner in (
        "DASHI.Physics.Units.SI",
        "DASHI.Physics.Units.SIMetrologyBridge",
        "DASHI.Physics.Units.MechanicalDimensionExact",
        "DASHI.Promotion.SIExactConstantParsedCarrierRequest",
        "DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact",
    ):
        assert exact_owner in si,exact_owner
    for theorem in (
        "speedOfLightIsExactSIInteger",
        "mechanicalOpticalTorqueIsSI",
        "torqueFromPowerOverSpeedAndRadius",
        "finiteInfluenceRowPowerBoundReuse",
    ):
        assert theorem in si,theorem
    spectral=source["DASHI/Geometry/GielisSpectralSIScaleExact.agda"]
    for theorem in (
        "nativeSpectralDimensionMatchesSI",
        "inverseAreaTimesAreaDimensionless",
        "scaleEigenvalueSIScalar",
    ):
        assert theorem in spectral,theorem
    for theorem in (
        "modelOpticalTorqueHasActualMagnitude",
        "modelOpticalTorqueWithDeflectionMagnitude",
        "modelOpticalTorqueSIMagnitude",
    ):
        assert theorem in si,theorem
    bishop=source["DASHI/Geometry/GielisBishopPolynomialExact.agda"]
    for theorem in (
        "bishopCorrectedQuarticFromPythagorean",
        "bishopGielisConfiguredTrigIdentity",
    ):
        assert theorem in bishop,theorem
    finite=source["DASHI/Geometry/GielisFiniteGroundStateEdgeExact.agda"]
    for theorem in (
        "edgeGroundStateIdentity",
        "edgeSquareNonnegative",
        "finiteEdgeSquareSumNonnegative",
        "finiteGroundStateEdgeIdentity",
    ):
        assert theorem in finite,theorem
    assert "Fubini.sumRationalAdd" in finite
    assert "Sums.sumRationalCong" in finite
    fd_energy=source["scripts/gielis_fd_energy_mosco.py"]
    assert "grid_energy" in fd_energy
    assert "legacy_1e_minus_12_mask_equal_at_selected_n" in fd_energy
    assert "boundary_tolerance_normalized" in fd_energy
    numerical=source["scripts/gielis_base369_experiments.py"]
    assert "raster_boundary_tolerance(h)" in numerical
    selected_fourier=source["DASHI/Geometry/GielisNineModeFourierExact.agda"]
    for theorem in (
        "fourierFourRoundTrip",
        "fourierFourCoefficientRoundTrip",
        "reconstructNineQuarterSamples",
        "cosineNineIsPureFourierMode",
        "sineNineIsPureFourierMode",
        "cosineEighteenIsPureFourierMode",
    ):
        assert theorem in selected_fourier,theorem
    fourier_script=source["scripts/gielis_nine_quarter_fourier_exact.py"]
    assert "gielis_cyclotomic36_exact" in fourier_script
    assert "same_original_zeta36_characters" in fourier_script
    six=source["DASHI/Geometry/GielisSixPhaseCyclotomicFourierExact.agda"]
    for theorem in (
        "twoRoundTrip",
        "twoForwardInverse",
        "sixC2RoundTrip",
        "sixC2ForwardInverse",
        "sixFourierInversion",
        "sixFourierForwardInverse",
        "reconstructSelectedSixSamples",
    ):
        assert theorem in six,theorem
    assert "DASHI.Biology.Physical.C3CubeCyclotomicFourierExact" in six
    six_script=source["scripts/gielis_six_phase_cyclotomic_exact.py"]
    assert "Q_zeta36_DFT" in six_script
    exact_raster=source["DASHI/Geometry/GielisExactRationalGridPredicateExact.agda"]
    for theorem in ("insideGielis3","insideGielis6","insideGielis9",
                    "oddRootLessThanZero","positiveAxisBoundary3",
                    "positiveAxisBoundary6","positiveAxisBoundary9"):
        assert theorem in exact_raster,theorem
    raster_script=source["scripts/gielis_exact_rational_raster_geometry.py"]
    assert "exact_inside_gielis" in raster_script
    assert "integer_fraction_only_for_membership" in raster_script
    torque_cross=source["DASHI/Geometry/GielisOpticalTorqueCrossSIExact.agda"]
    for theorem in ("wallLeverIsCrossZ","crossAntisymmetry",
                    "noDeflectionNoImpulse",
                    "swapIncomingOutgoingReversesSignedLever",
                    "rotatePositionAndRayPiPreservesSignedLever",
                    "modelWallTorqueSIMagnitude",
                    "existingHodgeCrossConvention"):
        assert theorem in torque_cross,theorem
    optical_event=source["scripts/gielis_exact_signed_optical_torque.py"]
    assert "canonical_speed_of_light_si" in optical_event
    assert "exact_signed_torque_Nm" in optical_event
    imaginary=source["DASHI/Geometry/GielisBishopImaginaryExponentialReducerExact.agda"]
    for theorem in (
        "ImaginaryAxisSameSourceExponentialDoubling",
        "cosineDoubleFromImaginaryExponential",
        "sineDoubleFromImaginaryExponential",
        "fourIsTwiceTwice",
        "concreteDoubleAngleInputsFromImaginaryExp",
        "gielisRound11FromOneImaginaryExponentialLaw",
        "realBishopExpAddAlreadyProved",
    ):
        assert theorem in imaginary,theorem
    assert "DASHI.Foundations.BishopExponentialCauchyProductExact" in imaginary
    assert "DASHI.Analysis.BishopSetoidComplexExact" in imaginary
    complex_algebra=source["DASHI/Geometry/GielisBishopComplexCauchyAlgebraExact.agda"]
    for theorem in ("complexAddCommutative","complexAddAssociative",
                    "complexMulCommutative","complexMulAssociative",
                    "complexMulDistributiveLeft","complexMulDistributiveRight"):
        assert theorem in complex_algebra,theorem
    assert "DASHI.Analysis.BishopSetoidComplexExact" in complex_algebra
    assert "Complex.≈C-trans" in complex_algebra
    bessel=source["DASHI/Geometry/GielisBesselFaberKrahnRationalExact.agda"]
    for theorem in ("j0S5Exact","j0S5StrictPositive",
                    "j1FirstRatioBelowOne",
                    "j1AlternatingUniformLowerPositive",
                    "sqrtTwoUpperSquareAboveTwo",
                    "eigenvalueLowerArithmeticExact",
                    "eigenvalueRationalLowerAboveFour"):
        assert theorem in bessel,theorem
    bessel_script=source["scripts/gielis_continuum_faber_krahn_bound.py"]
    assert "CLAIMED_LOWER=F(224,55)" in bessel_script
    same_complex=source["DASHI/Geometry/GielisBishopComplexSeriesSameCarrierExact.agda"]
    for theorem in (
        "seriesRoundTrip","setoidRoundTrip",
        "setoidPlusSameSeriesAlgebra","setoidMultiplySameSeriesAlgebra",
        "setoidComplexSeriesLimitConverges",
        "setoidComplexSeriesLimitUnique",
    ):
        assert theorem in same_complex,theorem
    assert "DASHI.Analysis.BishopComplexSeriesConvergenceExact" in same_complex
    assert "DASHI.Analysis.BishopSetoidComplexExact" in same_complex
    assert "DASHI.Analysis.BishopComplexAlgebraExact" in same_complex
    unrestricted=source["scripts/gielis_cyclotomic36_unrestricted_exact.py"]
    assert "kernel_resolution" in unrestricted
    assert "universal_arbitrary_signal_by_linearity_and_basis" in unrestricted
    spectrum_error=source["scripts/gielis_certified_continuum_fd_error.py"]
    assert "exact_error_enclosure" in spectrum_error
    assert "mesh_order_rate_Oh_power_certified" in spectrum_error
    original_event=source["scripts/gielis_kozyrev_same_event_original_owner.py"]
    assert "ORIGINAL_GIT_BLOBS" in original_event
    assert "compare_with_original" in original_event
    roadmap=source[FILES[3]]
    gates=re.findall(r"^\| (G\d\d) \|",roadmap,flags=re.M)
    assert gates==[f"G{i:02d}" for i in range(1,22)]
    for phase in range(6): assert f"P{phase}" in roadmap
    for deliverable in range(8): assert f"D{deliverable}" in roadmap

    proof=source[FILES[4]]
    for i in range(1,41):
        assert f"E{i:02d} —" in proof
    ray=source[FILES[5]]
    for token in (
        "wall_delta_p = d-new_d","ray_delta_p = -wall_delta_p",
        "ideal_specular_wall_torque_nm","include_controls",
        "model_encode","nyquist36_receipt",
    ):
        assert token in ray,token

    return {
        "status":"source_enumeration_passed",
        "scope":"literal Agda tables, 18-clause coverage, links and source markers",
        "finite_checks":assertions,
        "gram_369":gram,
        "complete_18_case_theorems":len(THEOREMS),
        "nyquist_fine_sample_9":s9[1],
        "nyquist_fine_sample_27":s27[1],
        "roadmap_exact_gates":21,
        "phases":6,
        "deliverables":8,
        "paper_proof_sections":40,
        "file_sha256":{
            path:hashlib.sha256(data.encode()).hexdigest()
            for path,data in source.items()
        },
        "agda_kernel_accepted":False,
        "python_test_suite_executed_by_this_script":False,
        "physical_kozyrev_scene_parity":False,
        "P3_same_event_actual_original_execution_by_this_script":False,
    }


if __name__ == "__main__":
    print(json.dumps(source_audit(),indent=2,sort_keys=True))
