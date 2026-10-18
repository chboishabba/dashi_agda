from __future__ import annotations

from .repository_discovery import RepositoryDiscovery


class UnifiedDiscovery(RepositoryDiscovery):
    """Deprecated compatibility name for :class:`RepositoryDiscovery`.

    The former implementation joined a separate repo-index database with a
    serialized preflight signature overlay.  The unified product now stores
    identity, signatures, references and history in one SQLite database, so
    there is exactly one production discovery engine.
    """

    pass


__all__ = ["UnifiedDiscovery"]
