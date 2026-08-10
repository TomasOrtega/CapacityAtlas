.PHONY: install validate test lint build check serve lean

install:
	python -m pip install -e '.[dev]'

validate:
	capacity-atlas validate

test:
	pytest

lint:
	ruff check src tests

build:
	capacity-atlas build

check: validate test lint build

serve: build
	python -m http.server --directory dist 8000

lean:
	cd lean && lake build
