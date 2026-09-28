from __future__ import annotations

from typing import Any, Dict, Optional

from .service import DashiAgdaService


class DashiAgdaMcpTools:
    """Transport-independent MCP-shaped facade over DashiAgdaService.

    This class intentionally has no dependency on the MCP SDK. It keeps tool
    semantics regression-testable on the package's Python 3.9 floor while the
    actual MCP transport remains an optional Python 3.10+ integration.
    """

    def __init__(self, service: DashiAgdaService) -> None:
        self.service = service

    def diagnose(
        self,
        target: str,
        errors_only: bool = False,
    ) -> Dict[str, Any]:
        """Return structural diagnostics for a module/rollup dependency closure.

        This is read-only and never invokes Agda.
        """
        return self.service.diagnose(
            target,
            errors_only=errors_only,
        )

    def next_error(
        self,
        target: str,
        require_fix: bool = False,
    ) -> Dict[str, Any]:
        """Return the highest-priority current diagnostic.

        Set require_fix=true to restrict the result to diagnostics that have at
        least one suggested fix. This is read-only and never invokes Agda.
        """
        return self.service.next_error(
            target,
            require_fix=require_fix,
        )

    def apply_fix(
        self,
        target: str,
        diagnostic_id: str,
        fix_index: int = 0,
        allow_likely: bool = False,
    ) -> Dict[str, Any]:
        """Apply one exact suggested edit and immediately re-diagnose it.

        This mutates source files. Speculative fixes are never applied.
        Fixes classified as likely require allow_likely=true.
        """
        return self.service.apply_fix(
            target,
            diagnostic_id,
            fix_index=fix_index,
            allow_likely=allow_likely,
        )

    def affected(
        self,
        target: str,
        within: Optional[str] = None,
    ) -> Dict[str, Any]:
        """Return the reverse-import consumer frontier for a module.

        Without within, the result is explicitly scoped to modules already in
        the persistent index. Pass a Subject/Everything.agda rollup as within
        to ensure and constrain the frontier to that subject closure.
        """
        return self.service.affected(
            target,
            within=within,
        )

    def cache_status(self) -> Dict[str, Any]:
        """Return persistent source-index/cache statistics."""
        return self.service.cache_status()

    def semantic_status(self, target: str) -> Dict[str, Any]:
        """Report fresh/stale/unknown last-known semantic snapshots.

        This is read-only and does not invoke Agda.
        """
        return self.service.semantic_status(target)

    def promote(self, target: str) -> Dict[str, Any]:
        """Explicitly run the configured semantic promoter for one target.

        This is the only MCP analysis tool that may invoke an external semantic
        checker. Promotion is fail-closed: exit code zero is insufficient; the
        resulting semantic catalog head must prove freshness against the
        post-run current source hash.
        """
        return self.service.promote(target)

    def promotion_history(
        self,
        module_name: Optional[str] = None,
        limit: int = 20,
    ) -> Dict[str, Any]:
        """Return persisted semantic-promotion receipts."""
        return self.service.promotion_history(
            module_name=module_name,
            limit=limit,
        )

    def ping(self) -> Dict[str, str]:
        """Return a minimal service liveness result."""
        return {"status": "ok"}
