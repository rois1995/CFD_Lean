from types import SimpleNamespace
import unittest
from unittest.mock import patch

from docs_site import DOCS, on_config, on_page_markdown


class DocsSiteTests(unittest.TestCase):
    def setUp(self):
        self.sha = "a" * 40
        self.config = SimpleNamespace(extra={"repository_url": "https://github.example/owner/repo"})
        with patch.dict("os.environ", {"CFDLEAN_DOCS_REVISION": self.sha, "CFDLEAN_DOCS_RELEASE": "v1.2.3"}):
            on_config(self.config)
        self.page = SimpleNamespace(file=SimpleNamespace(abs_src_path=DOCS / "CONCEPTS.md"))

    def test_release_and_artifact_links_are_pinned(self):
        markdown = "[contract](../specifications/FV1D.md#scope) [folder](../specifications/) " \
            "[page](../docs/CONCEPTS.md) __CFDLEAN_SOURCE_BASE__"
        rendered = on_page_markdown(markdown, self.page, self.config)
        self.assertEqual(self.config.site_name, "CFD_Lean · v1.2.3")
        self.assertIn(f"/blob/{self.sha}/specifications/FV1D.md#scope", rendered)
        self.assertIn(f"/tree/{self.sha}/specifications", rendered)
        self.assertIn("(../docs/CONCEPTS.md)", rendered)
        self.assertIn(f"/blob/{self.sha}/", rendered)

    def test_missing_repository_link_fails(self):
        with self.assertRaisesRegex(ValueError, "missing repository link"):
            on_page_markdown("[missing](../missing.md)", self.page, self.config)
