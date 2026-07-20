#!/usr/bin/env python3
"""Thin scheme formatter: normalizes indentation based on paren depth."""
import sys
import re


def format_scheme(content: str) -> str:
    lines = content.split("\n")
    result = []
    indent = 0
    for line in lines:
        stripped = line.strip()
        if not stripped:
            result.append("")
            continue

        # If the line starts with a closing paren, dedent before printing
        if stripped.startswith(")") or stripped.startswith("]") or stripped.startswith("}"):
            indent = max(0, indent - 1)

        result.append("  " * indent + stripped)

        # Count net paren change on this line (ignoring strings/comments)
        # Remove string literals
        cleaned = re.sub(r'"[^"]*"', '""', stripped)
        # Remove comments
        cleaned = re.sub(r';.*$', '', cleaned)
        # Remove char literals like #\( 
        cleaned = cleaned.replace('#\\(', '').replace('#\\)', '')
        opens = cleaned.count("(") + cleaned.count("[") + cleaned.count("{")
        closes = cleaned.count(")") + cleaned.count("]") + cleaned.count("}")
        indent = max(0, indent + opens - closes)

    return "\n".join(result)


def main():
    for path in sys.argv[1:]:
        with open(path, "r") as f:
            content = f.read()
        formatted = format_scheme(content)
        if formatted != content:
            with open(path, "w") as f:
                f.write(formatted)

if __name__ == "__main__":
    main()
