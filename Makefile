.PHONY: install validate test lint build check serve lean

install:
	uv sync --locked
	uv run --locked prek install

validate:
	uv run --locked capacity-atlas validate

test:
	uv run --locked pytest

lint:
	uv run --locked prek -a --quiet

build:
	uv run --locked capacity-atlas build

check: lint validate test build

serve: build
	uv run --locked python -m http.server --directory dist 8000

lean:
	cd lean && lake --wfail build CapacityAtlasForMathlib CapacityAtlasUtil
	cd lean && lake --wfail build CapacityAtlas
	@set -e; audit_report=$$(mktemp /tmp/capacity-atlas-audit.XXXXXX); \
	trap 'rm -f "$$audit_report"' EXIT; \
	cd lean; lake exe capacity_audit > "$$audit_report"; cd ..; \
	uv run --locked capacity-atlas validate --lean-report "$$audit_report"
