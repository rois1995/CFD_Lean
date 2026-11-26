from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from check_docs import broken_links, docs_paths


class DocsCheckTests(unittest.TestCase):
    @staticmethod
    def change(path, old_mode="100644", mode="100644", status="M"):
        return f":{old_mode} {mode} abcdef0 abcdef1 {status}\0{path}\0".encode()

    def test_navigation_additions_and_edits(self):
        diff = self.change("CONTRIBUTING.md") + self.change("docs/A B.md", old_mode="000000", status="A")
        self.assertEqual(docs_paths(diff), [Path("CONTRIBUTING.md"), Path("docs/A B.md")])

    def test_uncertain_or_mixed_changes(self):
        for change in (
            self.change("README.md"), self.change("references/M1.md"), self.change("specifications/Burgers-B0.md"),
            self.change("docs/example.lean"), self.change(".github/workflows/integration.yml"),
            self.change("docs/link.md", mode="120000", status="T"),
            self.change("docs/old.md", mode="000000", status="D"),
        ):
            with self.subTest(change=change):
                self.assertEqual(docs_paths(self.change("TODO.md") + change), [])
        self.assertEqual(docs_paths(b""), [])

    def test_links_anchors_and_code_fences(self):
        with TemporaryDirectory() as folder:
            root = Path(folder).resolve()
            page = root / "page.md"
            (root / "A B.md").write_text("# Heading\n## Heading\n", encoding="utf-8")
            page.write_text(
                "# Home\n[relative](A%20B.md#heading-1)\n[local](#home)\n"
                "[external](https://example.com/missing)\n`[example](ignored.md)`\n"
                "```md\n[example](ignored.md)\n```\n"
                "[gone](missing.md)\n[renamed](A%20B.md#renamed)\n[escape](../)\n",
                encoding="utf-8",
            )
            self.assertEqual(list(broken_links(page, root)), ["missing.md", "A%20B.md#renamed", "../"])
