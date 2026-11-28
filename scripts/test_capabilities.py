import unittest

from capabilities import ROOT, load, resolve


class CapabilityTests(unittest.TestCase):
    def setUp(self):
        self.root = {"id": "root", "parent": None, "kind": "group", "label": "Root"}
        self.node = {"id": "node", "parent": "root", "kind": "certificate", "label": "Node",
                     "status": "planned"}
        self.evidence = {"milestones": {"M5": {"status": "pending", "paths": ["specifications/M5.md"]}},
                         "result_ids": {}}

    def test_parent(self):
        for parent, message in (("missing", "Missing parent"), ("node", "Parent cycle")):
            with self.subTest(parent=parent), self.assertRaisesRegex(ValueError, message):
                resolve([self.root, {**self.node, "parent": parent}], self.evidence, ROOT)

    def test_evidence(self):
        for selectors, message in (({"milestones": ["M5"]}, "requires accepted evidence"),
                                   ({}, "requires accepted evidence"),
                                   ({"milestones": ["unknown"]}, "Unknown milestones"),
                                   ({"result_ids": ["unknown"]}, "Unknown result_ids")):
            with self.subTest(selectors=selectors), self.assertRaisesRegex(ValueError, message):
                resolve([self.root, {**self.node, "status": "accepted", "evidence": selectors}],
                        self.evidence, ROOT)

    def test_repository_registry(self):
        nodes = {node["id"]: node for node in load()}
        self.assertEqual(nodes["muscl"]["status"], "accepted")
        for key in ("weno", "euler_reconstructed", "e1"):
            self.assertEqual(nodes[key]["status"], "implemented")
