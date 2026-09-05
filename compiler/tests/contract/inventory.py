#!/usr/bin/env python3
"""Inventory rustdoc's reachable public graph, never a grep of root exports.

Input must be rustdoc JSON produced from spec/baselines.toml's behavior commit.
This is a development oracle tool; it is not linked into compiler artifacts.
"""
import argparse
import csv
import json
from pathlib import Path


def inventory(document):
    index = document["index"]
    rows = {}
    visited = set()

    def visit(item_id, prefix, owner=None, implicit=False):
        item = index.get(str(item_id))
        if not item or item["crate_id"] != 0:
            return
        kind, value = next(iter(item["inner"].items()))
        if not implicit and item["visibility"] != "public":
            return
        name = item.get("name")
        if kind == "use":
            name = value["name"]
        if name is None:
            return
        path = prefix + "::" + name if prefix else name
        if (item_id, path) in visited:
            return
        visited.add((item_id, path))
        span = item.get("span")
        source = ""
        if span:
            source = span["filename"].split("crates/grandiose-stage0/")[-1]
            source += ":" + str(span["begin"][0])
        if owner is None and kind != "module":
            owner = Path(source.split(":")[0]).stem or "lib"
        if prefix:
            rows[path] = (path, kind, owner or name, source,
                          oracle_command(owner or name), comparator(owner or name, kind), "open")
        if kind == "module":
            for child in value["items"]:
                visit(child, path, owner or (name if prefix else None))
        elif kind == "use":
            # Public aliases retain their own API record. The target's complete
            # definition is also visited even when its defining module is private.
            target = value.get("id")
            if target is not None and str(target) in index:
                definition = index[str(target)]
                target_name = definition.get("name")
                if target_name and target_name != name:
                    visit(target, prefix, owner, True)
                elif target_name:
                    visit(target, prefix, owner, True)
        elif kind in ("struct", "union", "enum", "trait"):
            children = []
            if kind == "struct":
                shape = value["kind"]
                if isinstance(shape, dict):
                    if "plain" in shape:
                        children = shape["plain"]["fields"]
                    elif "tuple" in shape:
                        children = shape["tuple"]
            elif kind == "union":
                children = value["fields"]
            elif kind == "enum":
                children = value["variants"]
            elif kind == "trait":
                children = value["items"]
            for child in children:
                if child is not None:
                    visit(child, path, owner, kind in ("enum", "trait"))
            for impl_id in value.get("impls", []):
                implementation = index.get(str(impl_id), {}).get("inner", {}).get("impl")
                if not implementation or implementation.get("is_synthetic"):
                    continue
                # Include inherent API and explicitly implemented/derived trait
                # operations. Blanket std impls are not source-owned exports.
                impl_item = index[str(impl_id)]
                if not impl_item.get("span"):
                    continue
                trait = implementation.get("trait")
                impl_path = path + ("::<" + trait["path"] + ">" if trait else "")
                for child in implementation["items"]:
                    visit(child, impl_path, owner, bool(trait))
        elif kind == "variant":
            shape = value["kind"]
            if isinstance(shape, dict):
                fields = shape.get("tuple", shape.get("struct", {}).get("fields", []))
                for child in fields:
                    if child is not None:
                        visit(child, path, owner, True)

    visit(document["root"], "")
    return [rows[key] for key in sorted(rows)]


def comparator(owner, kind):
    if owner in ("query", "revision", "dependency", "operation", "artifact_cache"):
        return "session-history+result+failure+trace+retention"
    if owner in ("bootstrap", "vm_backend", "identity"):
        return "canonical-bytes+validation+runtime"
    if owner in ("diagnostic", "source"):
        return "structured-value+origin+rendering"
    return "typed-value+diagnostics+failure"


def oracle_command(owner):
    """Executable reference suite assignment, not a claim of source coverage."""
    unit = {"artifact_cache", "bootstrap", "dependency", "diagnostic", "output", "lib"}
    if owner in unit:
        return "cargo test -p grandiose-stage0 --lib" + (" " + owner if owner != "lib" else "")
    grouped = {
        "source": "source_and_query", "query": "source_and_query",
        "identity": "request_and_revision", "request": "request_and_revision",
        "revision": "request_and_revision", "instance": "service",
        "escape": "core", "placeflow": "core", "useflow": "core",
        "mir_storage": "vm_storage_erasure",
    }
    target = grouped.get(owner, owner)
    return "cargo test -p grandiose-stage0 --test " + target


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("rustdoc", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    document = json.loads(args.rustdoc.read_text())
    rows = [("export", "kind", "owner", "oracle", "oracle_command", "comparator", "status")]
    rows.extend(inventory(document))
    import io
    buffer = io.StringIO(newline="")
    csv.writer(buffer, delimiter="\t", lineterminator="\n").writerows(rows)
    expected = buffer.getvalue()
    if args.check:
        if args.output.read_text() != expected:
            raise SystemExit("contract inventory differs from frozen public API")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(expected)
    print(f"{len(rows) - 1} public contract records; coverage starts at zero")


if __name__ == "__main__":
    main()
