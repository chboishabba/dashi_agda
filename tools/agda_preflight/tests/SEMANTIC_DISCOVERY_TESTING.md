# Semantic discovery test order

These tests are intentionally committed before their production integrations so a local checkout can exercise the RED -> GREEN sequence:

1. `test_discovery.py`
2. `test_lineage.py`
3. `test_semantic_catalog.py`
4. `test_service_discovery.py`
5. `test_cli_discovery.py`
6. `test_mcp_discovery.py`
7. `test_catalog_interface_shapes.py`

The connected GitHub harness cannot execute pytest, so local verification is the remaining execution-bound step. Production commits preserve the test-first ordering.
