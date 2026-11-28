from pathlib import Path
import tempfile
import unittest

from generate_import_graph import generate, graph, imports, layer_graph
from test_graph_docs import assert_exports


class ImportGraphTests(unittest.TestCase):
    def test_import_header(self):
        source = """
/- Nested /- import CFDLean.Ignored -/ example -/
module
prelude
public meta import CFDLean.Physics.Flux
import /- comment -/ all
  CFDLean.Geometry.Mesh -- explanation
import Mathlib
def text := "import CFDLean.Ignored"
"""
        self.assertEqual(list(imports(source)), ["CFDLean.Physics.Flux", "CFDLean.Geometry.Mesh", "Mathlib"])
        self.assertEqual(list(imports("/- -- comment -/ import CFDLean.Mesh")), ["CFDLean.Mesh"])

    def test_forbidden_edge(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("Physics", "Exec"):
                (root / "CFDLean" / name).mkdir(parents=True)
            (root / "CFDLean/Exec/Kernel.lean").touch()
            (root / "CFDLean/Physics/Flux.lean").write_text("import CFDLean.Exec.Kernel\n")
            with self.assertRaisesRegex(ValueError, "Forbidden import"):
                graph(root)

    def test_exports_and_layer_counts(self):
        data = graph()
        assert_exports(self, data)
        self.assertEqual(generate(), generate())
        self.assertEqual(sum(edge["count"] for edge in layer_graph(data)["edges"]),
                         sum(edge["source_layer"] != edge["target_layer"] for edge in data["edges"]))
