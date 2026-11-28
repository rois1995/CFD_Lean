"""Keep published artifact links on the same immutable revision as the site."""
import os
from pathlib import Path
import re
import subprocess
from urllib.parse import quote, unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
LOCAL_LINK = re.compile(r'(?P<prefix>\]\()(?P<url>\.\./[^\s)]+)(?=[\s)])')
TOKEN = "__CFDLEAN_SOURCE_BASE__"


def on_config(config):
    revision = os.environ.get("CFDLEAN_DOCS_REVISION")
    if revision is None:
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    release = os.environ.get("CFDLEAN_DOCS_RELEASE")
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("CFDLEAN_DOCS_REVISION must be an immutable Git commit SHA")
    if release and not re.fullmatch(r"v\d+\.\d+\.\d+", release):
        raise ValueError("CFDLEAN_DOCS_RELEASE must be vMAJOR.MINOR.PATCH")
    config.site_name = f"CFD_Lean · {release or 'development ' + revision[:7]}"
    config.extra["source_base"] = f"{config.extra['repository_url'].rstrip('/')}/blob/{revision}/"
    return config


def on_page_markdown(markdown, page, config, **kwargs):
    source = Path(page.file.abs_src_path)
    base = config.extra["source_base"]

    def replace(match):
        url = urlsplit(match["url"])
        path = (source.parent / unquote(url.path)).resolve()
        if not path.is_relative_to(ROOT) or not path.exists():
            raise ValueError(f"{source.relative_to(ROOT)}: missing repository link {match['url']}")
        if path.is_relative_to(DOCS):
            return match[0]
        target_base = base.replace("/blob/", "/tree/") if path.is_dir() else base
        anchor = "#" + url.fragment if url.fragment else ""
        return match["prefix"] + target_base + quote(path.relative_to(ROOT).as_posix()) + anchor

    return LOCAL_LINK.sub(replace, markdown).replace(TOKEN, base)
