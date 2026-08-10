.PHONY: install validate test lint build serve check lean

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

serve: build
	python -m http.server 8000 --directory dist

lean:
	cd lean && lake build

check: validate test lint build
