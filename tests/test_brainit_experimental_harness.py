"""Real executable toy harness tests; not Brain-IT checkpoint or NSD replay."""
import sys
from pathlib import Path

import numpy as np
import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments" / "brainit"))

from inventory import create_manifest, digest
from stage_conditions import controlled_fmri, derangement, stage
from evaluate import evaluate, two_way_feature_identification, pixel_corr
from compare import paired_contrast


def toy_source(tmp_path):
    src = tmp_path / "upstream"
    for subdir in ("inference", "models", "src", "utils", "data/derived_data",
                   "data/external_models", "data/nsd_data", "results/saved_models"):
        (src / subdir).mkdir(parents=True, exist_ok=True)
    (src / "inference/full_inference.py").write_text("# upstream placeholder\n")
    x = np.arange(24, dtype=np.float64).reshape(4, 6)
    type_sample = np.array([1, 2, 1, 2, 2, 2])
    np.savez_compressed(src / "data/nsd_data/fmri_v2.npz",
                        multi_sub_fmri=x, num_voxels_subjects=np.array([2, 4]),
                        type_sample=type_sample)
    rng = np.random.default_rng(47)
    images = rng.integers(0, 255, size=(6, 24, 24, 3), dtype=np.uint8)
    np.save(src / "data/nsd_data/nsd_images_224.npy", images)
    np.save(src / "data/derived_data/v2c_128_mapping_gmm_v2.npy",
            np.zeros((6,), dtype=np.int64))
    return src


def test_seed_derangement_never_preserves_a_test_trial():
    for n in (2, 3, 10, 100):
        perm = derangement(n, 42)
        assert set(perm.tolist()) == set(range(n))
        assert np.all(perm != np.arange(n))
        assert np.array_equal(perm, derangement(n, 42))


def test_isolated_real_fmri_controls_keep_other_subjects_unaltered(tmp_path):
    src = toy_source(tmp_path)
    fmri = src / "data/nsd_data/fmri_v2.npz"
    original_sha = digest(fmri)
    source, _ = controlled_fmri(fmri, "paired", 0, 40)
    shifted, perm = controlled_fmri(fmri, "deranged", 0, 40)
    zero, _ = controlled_fmri(fmri, "zero", 0, 40)
    assert np.array_equal(source["multi_sub_fmri"], np.arange(24).reshape(4, 6))
    assert np.array_equal(shifted["multi_sub_fmri"][:, :2],
                          source["multi_sub_fmri"][perm, :2])
    assert np.array_equal(shifted["multi_sub_fmri"][:, 2:],
                          source["multi_sub_fmri"][:, 2:])
    assert np.all(zero["multi_sub_fmri"][:, :2] == 0)
    assert np.array_equal(zero["multi_sub_fmri"][:, 2:], source["multi_sub_fmri"][:, 2:])
    receipt = stage(src, tmp_path / "staged", "deranged", 0, 40, test=True)
    assert receipt["model_inference_executed"] is False
    assert receipt["source_fmri_sha256"] == original_sha
    assert digest(fmri) == original_sha
    assert (tmp_path / "staged/results/saved_models").is_symlink()
    assert not (tmp_path / "staged/results/reconstructions").exists()
    with pytest.raises(FileExistsError):
        stage(src, tmp_path / "staged", "zero", 0, 40)


def test_staging_rejects_subject_test_mode_ambiguity(tmp_path):
    src = toy_source(tmp_path)
    with pytest.raises(ValueError):
        stage(src, tmp_path / "not_made", "paired", 1, 42, test=True)


def test_inventory_is_fail_closed_on_missing_checkpoint(tmp_path):
    src = toy_source(tmp_path)
    m = create_manifest(src, src / "data/nsd_data/fmri_v2.npz",
                        src / "data/nsd_data/nsd_images_224.npy",
                        src / "data/derived_data/v2c_128_mapping_gmm_v2.npy",
                        [], [1])
    assert m["status"] == "incomplete"
    assert m["independent_model_inference_performed"] is False
    assert m["fmri_alignment"]["test_rows"] == 4


def test_image_evaluation_and_stimulus_paired_metric_contrast(tmp_path):
    src = toy_source(tmp_path)
    images = np.load(src / "data/nsd_data/nsd_images_224.npy")
    ids = [1, 3, 4]
    paired = images[ids]
    # Preserve same shape and labels, but deliberately reverse intensities.
    bad = (255 - paired).astype(np.uint8)
    a = tmp_path / "paired.npy"
    b = tmp_path / "control.npy"
    np.save(a, paired)
    np.save(b, bad)
    args = (src / "data/nsd_data/nsd_images_224.npy",
            src / "data/nsd_data/fmri_v2.npz")
    real = evaluate(a, *args, 1, "paired", 11, "enhanced")
    null = evaluate(b, *args, 1, "deranged", 11, "enhanced")
    assert real["aggregate"]["pixcorr"]["mean"] == pytest.approx(1, abs=1e-5)
    assert real["aggregate"]["ssim"]["mean"] == pytest.approx(1, abs=1e-5)
    assert [r["stimulus_id"] for r in real["rows"]] == ids
    contrast = paired_contrast([real], [null], draws=250, seed=9)
    assert contrast["n_test_rows"] == 3
    assert contrast["metrics"]["pixcorr"]["paired_minus_control"] > 0
    assert contrast["metrics"]["ssim"]["paired_minus_control"] > 0
    assert len(contrast["metrics"]["pixcorr"]["bootstrap_ci95"]) == 2
    null["rows"][0]["stimulus_id"] = -1
    with pytest.raises(ValueError, match="Pairing broken"):
        paired_contrast([real], [null], draws=250, seed=9)


def test_feature_identity_does_not_claim_clip_thousand_way():
    a = np.array([[1., 0., 1.], [0., 1., 1.]])
    assert two_way_feature_identification(a, a) == pytest.approx(1)


def test_metric_rejects_undefined_variance():
    assert pixel_corr(np.zeros((2, 2)), np.ones((2, 2))) is None
