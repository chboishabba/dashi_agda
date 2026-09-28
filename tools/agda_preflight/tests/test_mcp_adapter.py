from __future__ import annotations

from pathlib import Path
import inspect

from agda_preflight.mcp_adapter import DashiAgdaMcpTools
from agda_preflight.mcp_server import register_mcp_tools
from agda_preflight.service import DashiAgdaService


def write_module(root: Path, module: str, body: str = "") -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"module {module} where\n{body}",
        encoding="utf-8",
    )
    return path


class FakeMcpServer:
    def __init__(self) -> None:
        self.tools = {}

    def tool(self):
        def register(function):
            self.tools[function.__name__] = function
            return function

        return register


def test_mcp_registration_exposes_stable_tool_surface(tmp_path):
    database = tmp_path / ".cache" / "source-index.sqlite3"
    with DashiAgdaService(tmp_path, database, jobs=1) as service:
        fake = FakeMcpServer()
        register_mcp_tools(
            fake,
            DashiAgdaMcpTools(service),
        )

    assert set(fake.tools) == {
        "diagnose",
        "next_error",
        "apply_fix",
        "affected",
        "cache_status",
        "refresh",
        "semantic_status",
        "promote",
        "promotion_history",
        "ping",
    }
    assert all(
        inspect.iscoroutinefunction(function)
        for function in fake.tools.values()
    )


def test_mcp_next_error_apply_fix_loop(tmp_path):
    path = write_module(
        tmp_path,
        "Mcp.Apply",
        """
record R : Set₁ where
  field
    witness : Set

bad : R
bad = record { witnes = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=1,
    ) as service:
        tools = DashiAgdaMcpTools(service)
        first = tools.next_error(
            str(path),
            require_fix=True,
        )
        assert first["status"] == "diagnostic"
        diagnostic = first["diagnostic"]
        assert diagnostic is not None

        applied = tools.apply_fix(
            str(path),
            diagnostic["id"],
            allow_likely=True,
        )
        assert applied["resolved"] is True

        final = tools.next_error(
            str(path),
            require_fix=True,
        )

    assert final["status"] == "clean"
    assert "witnes =" not in path.read_text(encoding="utf-8")


def test_mcp_affected_returns_nearest_consumers_and_handles_cycles(tmp_path):
    a = write_module(
        tmp_path,
        "Mcp.A",
        """
import Mcp.B

a : Set
a = Set
""",
    )
    write_module(
        tmp_path,
        "Mcp.B",
        """
import Mcp.A

b : Set
b = Set
""",
    )
    top = write_module(
        tmp_path,
        "Mcp.Top",
        """
import Mcp.A

top : Set
top = Set
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=1,
    ) as service:
        tools = DashiAgdaMcpTools(service)
        # Populate the indexed closure first.
        tools.diagnose(str(top))
        result = tools.affected(str(a))

    assert result["modules"][0] == "Mcp.A"
    assert result["modules"][1:] == ["Mcp.B", "Mcp.Top"]
    assert result["count"] == 3
    assert result["scope"] == "indexed-cache-only"


def test_mcp_read_only_tools_do_not_modify_source(tmp_path):
    path = write_module(
        tmp_path,
        "Mcp.ReadOnly",
        """
x : Set
x = Set
""",
    )
    original = path.read_bytes()
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=1,
    ) as service:
        tools = DashiAgdaMcpTools(service)
        assert tools.ping() == {"status": "ok"}
        tools.diagnose(str(path))
        tools.next_error(str(path))
        tools.affected(str(path))
        tools.refresh(str(path))
        tools.cache_status()
        tools.semantic_status(str(path))

    assert path.read_bytes() == original



def test_mcp_diagnose_is_bounded_by_default(tmp_path):
    path = write_module(
        tmp_path,
        "Mcp.Bounded",
        """
record R : Set₁ where
  field
    witness : Set

bad₁ : R
bad₁ = record { typo₁ = Set }

bad₂ : R
bad₂ = record { typo₂ = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=1,
    ) as service:
        tools = DashiAgdaMcpTools(service)
        result = tools.diagnose(
            str(path),
            limit=1,
        )

    assert result["diagnostics_total"] >= 2
    assert result["diagnostics_returned"] == 1
    assert result["diagnostics_truncated"] is True



def test_mcp_tool_handlers_publish_structured_dict_annotations(tmp_path):
    database = tmp_path / ".cache" / "source-index.sqlite3"
    with DashiAgdaService(tmp_path, database, jobs=1) as service:
        fake = FakeMcpServer()
        register_mcp_tools(
            fake,
            DashiAgdaMcpTools(service),
        )

    for function in fake.tools.values():
        annotation = inspect.signature(function).return_annotation
        assert annotation != dict
        assert "dict[str, Any]" in str(annotation)


def test_mcp_refresh_observes_out_of_band_edit(tmp_path):
    path = write_module(
        tmp_path,
        "Mcp.Refresh",
        """
record R : Set₁ where
  field
    witness : Set

bad : R
bad = record { witnes = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with DashiAgdaService(
        tmp_path,
        database,
        jobs=1,
    ) as service:
        tools = DashiAgdaMcpTools(service)
        first = tools.next_error(str(path), require_fix=True)
        assert first["status"] == "diagnostic"

        path.write_text(
            """module Mcp.Refresh where

record R : Set₁ where
  field
    witness : Set

bad : R
bad = record { witness = Set }
""",
            encoding="utf-8",
        )

        trusted = tools.next_error(str(path), require_fix=True)
        assert trusted["status"] == "diagnostic"
        assert trusted["profile"]["counts"].get("files_stat", 0) == 0

        refreshed = tools.refresh(str(path))
        assert refreshed["profile"]["counts"]["files_parsed"] == 1

        final = tools.next_error(str(path), require_fix=True)
        assert final["status"] == "clean"
        assert final["profile"]["counts"].get("files_stat", 0) == 0
