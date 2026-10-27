from pathlib import Path

from agda_preflight.product_cli import main


def test_da51_resolve_cli_decodes_atlas(tmp_path: Path, capsys):
    code = main([
        "da51", "resolve", "0xDA51853000A00000",
        "--root", str(tmp_path),
    ])
    output = capsys.readouterr().out
    assert code == 0
    assert "address\t0xDA51853000A00000" in output
    assert "type_code\t8" in output
    assert "atlas_level\t5" in output
    assert "atlas_serial\t10" in output
    assert "authority\tidentity-only" in output


def test_prove_route_cli_refuses_generation_when_discovery_is_incomplete(tmp_path: Path, capsys):
    code = main([
        "prove", "route", "brand new theorem",
        "--root", str(tmp_path),
        "--target-prover", "lean",
    ])
    output = capsys.readouterr().out
    assert code == 0
    assert "recommended_backend\trepository-discovery" in output
    assert "generation_permitted\tFalse" in output
    assert "authority\trouting-only" in output
