#!/usr/bin/env sh
set -eu

# Render all repo PlantUML docs to SVG and PNG in headless environments.
export JAVA_TOOL_OPTIONS="${JAVA_TOOL_OPTIONS:-} -Djava.awt.headless=true"

find Docs -maxdepth 1 -type f -name '*.puml' -print | while IFS= read -r diagram
do
  plantuml -tsvg "$diagram"
  plantuml -tpng "$diagram"
done
