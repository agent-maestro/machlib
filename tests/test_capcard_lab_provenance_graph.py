from pathlib import Path

from tools.capcard_lab.provenance_graph import build_graph
from tools.capcard_lab.schema import REQUIRED_CANDIDATES


def test_graph_size():
    graph = build_graph(Path("."))
    assert graph["node_count"] >= 40
    assert graph["edge_count"] >= 60


def test_required_candidate_nodes_present():
    graph = build_graph(Path("."))
    nodes = {node["id"] for node in graph["nodes"]}
    for cid in REQUIRED_CANDIDATES:
        assert cid in nodes


def test_no_upload_gates_present():
    graph = build_graph(Path("."))
    edges = [edge for edge in graph["edges"] if edge["type"] == "no_upload_gate_for"]
    assert len(edges) >= len(REQUIRED_CANDIDATES)


def test_graph_has_no_action_fields_true():
    graph = build_graph(Path("."))
    assert graph["production_marketplace_modified"] is False
    assert graph["petal_api_upload_performed"] is False
    assert graph["huggingface_upload_performed"] is False
