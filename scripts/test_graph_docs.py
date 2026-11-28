import json
import re
import tempfile
import unittest
from pathlib import Path
from xml.etree import ElementTree as ET

from generate_capabilities import generate, graph
from graph_docs import dot, graphml, json_text, write_outputs


def assert_exports(test, graph):
    namespace = {"g": "http://graphml.graphdrawing.org/xmlns"}
    xml = ET.fromstring(graphml(graph))
    rendered = dot(graph)
    decoded = json.loads(json_text(graph))
    ids = {node["id"] for node in decoded["nodes"]}
    edges = {(edge["source"], edge["target"], edge["kind"]) for edge in decoded["edges"]}

    test.assertEqual(ids, {node.attrib["id"] for node in xml.findall(".//g:node", namespace)})
    test.assertEqual(ids, set(re.findall(r'^  "([^"]+)" \[', rendered, re.MULTILINE)))
    test.assertEqual(edges, {(edge.attrib["source"], edge.attrib["target"],
                              edge.find('g:data[@key="edge_kind"]', namespace).text)
                             for edge in xml.findall(".//g:edge", namespace)})
    test.assertEqual(edges, set(re.findall(r'^  "([^"]+)" -> "([^"]+)" \[.*?\bkind="([^"]+)"',
                                          rendered, re.MULTILINE)))
    statuses = {node["id"]: node["status"] for node in decoded["nodes"] if "status" in node}
    test.assertEqual(statuses, {node.attrib["id"]: status.text
                                for node in xml.findall(".//g:node", namespace)
                                if (status := node.find('g:data[@key="node_status"]', namespace)) is not None})
    test.assertEqual(statuses, dict(re.findall(r'^  "(\w+)" \[.*?\bstatus="([^"]+)"',
                                              rendered, re.MULTILINE)))


class GraphDocsTests(unittest.TestCase):
    def test_capability_exports(self):
        assert_exports(self, graph())
        self.assertEqual(generate(), generate())

    def test_check_reports_stale_export_without_writing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            outputs = generate()
            self.assertFalse(write_outputs(outputs, False, root))
            self.assertFalse(write_outputs(outputs, True, root))
            path = next(path for path in outputs if path.endswith(".graphml"))
            (root / path).write_text("stale", encoding="utf-8")
            self.assertEqual(write_outputs(outputs, True, root), [path])
            self.assertEqual((root / path).read_text(encoding="utf-8"), "stale")
