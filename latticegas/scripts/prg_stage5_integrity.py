"""Read-only cross-artifact/hash audit of the final PRG research chain."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RESULT = ROOT / "grandcanonical_results"
OUT = RESULT / "prg_stage5_integrity.json"


def read(name):
    return json.loads((RESULT / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    design = RESULT / "prg_stage5_design.json"
    selection = RESULT / "prg_stage5_selection.json"
    runs = RESULT / "prg_stage5_runs.json"
    analysis = RESULT / "prg_stage5_analysis.json"
    graph = RESULT / "prg_stage5_provenance.json"
    recovery = read("prg_stage4_endpoint_recovery.json")
    s, r, a, g = (json.loads(p.read_text()) for p in
                   (selection, runs, analysis, graph))
    assert s["design_sha256"] == sha(design)
    assert r["selection_sha256"] == sha(selection)
    assert a["runs_sha256"] == sha(runs)
    assert g["stage5_analysis_sha256"] == sha(analysis)
    assert s["source_raw_sha256"] == {
        str(L): read("prg_stage4_quotient_analysis.json")["cells"][str(L)]["raw_sha256"]
        for L in (8, 12)}
    for cell in r["runs"]:
        assert cell["raw_sha256"] == sha(ROOT / cell["raw_file"])
    for cell in a["cells"].values():
        assert cell["raw_sha256"] == sha(ROOT / cell["raw_file"])
    original = ROOT / recovery["original_file"]
    recovered = ROOT / recovery["recovered_file"]
    assert sha(original) == recovery["original_sha256"]
    assert sha(recovered) == recovery["recovered_sha256"]
    prefix_end = original.read_bytes().rfind(b"\n") + 1
    assert recovered.read_bytes().startswith(original.read_bytes()[:prefix_end])
    assert recovered.read_bytes().count(b"\n") == recovery["target_rows"] == 40000
    ids = {node["id"] for node in g["nodes"]}
    assert len(ids) == len(g["nodes"])
    assert all(u in ids and v in ids for u, v in g["edges"])
    diff = a["between_pair_difference_bootstrap_95_exploratory"]
    assert (diff["y_t_large_minus_small"][0] <= 0 <=
            diff["y_t_large_minus_small"][1]) == a["predeclared_bootstrap_compatibility"]["thermal"]
    assert (diff["y_S_large_minus_small"][0] <= 0 <=
            diff["y_S_large_minus_small"][1]) == a["predeclared_bootstrap_compatibility"]["correlation_scattering"]
    assert a["predeclared_bootstrap_compatibility"] == {
        "thermal": True, "correlation_scattering": False}
    OUT.write_text(json.dumps({
        "status": "all_checked_cross_artifact_hashes_and_graph_edges_consistent",
        "selection_sha256": sha(selection),
        "runs_sha256": sha(runs),
        "analysis_sha256": sha(analysis),
        "graph_sha256": sha(graph),
        "recovered_sha256": sha(recovered),
        "graph_nodes": len(ids),
        "graph_edges": len(g["edges"]),
        "final_predeclared_two_dimension_compatibility": False,
        "scope": "Deterministic artifact consistency; not stochastic validity or a formal C++ refinement theorem"
    }, indent=2) + "\n")
    print("final artifact integrity passed", len(ids), "nodes", flush=True)


if __name__ == "__main__":
    main()
