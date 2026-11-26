"""Validate navigation-only PRs and print whether Lean can be skipped."""

import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit


ROOT_DOCS = {"AGENTS.md", "ARCHITECTURE.md", "CONTRIBUTING.md", "TODO.md"}


def git(*args):
    return subprocess.check_output(["git", *args])


def docs_paths(diff):
    paths = []
    records = diff.split(b"\0")[:-1]
    for metadata, name in zip(records[::2], records[1::2], strict=True):
        old_mode, mode, _, _, status = metadata.split()
        path = os.fsdecode(name)
        navigation_doc = path in ROOT_DOCS or (path.endswith(".md") and path.startswith(("docs/", "roadmap/")))
        if (old_mode not in {b":000000", b":100644"} or mode != b"100644"
                or status not in {b"A", b"M"} or not navigation_doc):
            return []
        paths.append(Path(path))
    return paths


def markdown_lines(path):
    fence = ""
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)$", line)
        if match:
            marks, rest = match.groups()
            if not fence:
                fence = marks
            elif marks.startswith(fence) and not rest.strip():
                fence = ""
        elif not fence:
            yield line


def anchors(path):
    seen = set()
    for line in markdown_lines(path):
        heading = re.match(r"^ {0,3}#{1,6}\s+(.+)$", line)
        if heading:
            slug = re.sub(r"[^\w\s-]", "", heading[1].strip(" #").lower()).replace(" ", "-")
            unique = slug
            suffix = 0
            while unique in seen:
                suffix += 1
                unique = f"{slug}-{suffix}"
            seen.add(unique)
    return seen


def broken_links(path, root):
    # shortcut: Check inline local links and ATX anchors, use a Markdown parser if navigation docs adopt other forms.
    for line in markdown_lines(path):
        line = re.sub(r"(`+).*?\1", "", line)
        for link in re.findall(r"\]\(\s*(<[^>]+>|[^)\s]+)(?:\s+[^)]*)?\)", line):
            url = urlsplit(link.strip("<>"))
            if url.scheme or url.netloc:
                continue
            relative = unquote(url.path)
            directory = root if relative.startswith("/") else path.parent
            target = (directory / relative.lstrip("/")).resolve() if relative else path
            if not target.is_relative_to(root) or not target.exists():
                yield link
            elif url.fragment and target.suffix == ".md" and unquote(url.fragment) not in anchors(target):
                yield link


def main(base, head):
    # Only classify the exact merge result tested by the required check.
    parents = git("rev-list", "--parents", "-n", "1", "HEAD").decode().split()[1:]
    paths = []
    if parents == [base, head]:
        paths = docs_paths(git("diff", "--raw", "-z", "--no-renames", "HEAD^1", "HEAD", "--"))
    if not paths:
        print("false")
        return

    root = Path.cwd().resolve()
    errors = [f"{path}: broken link {link!r}" for path in paths for link in broken_links(root / path, root)]
    if errors:
        sys.exit("\n".join(errors))
    subprocess.run(["git", "diff", "--check", "HEAD^1", "HEAD", "--"], check=True, stdout=sys.stderr)
    subprocess.run(["sha256sum", "--quiet", "-c", "evidence/SHA256SUMS"], check=True, stdout=sys.stderr)
    print("true")


if __name__ == "__main__":
    main(*sys.argv[1:])
