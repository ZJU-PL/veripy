.PHONY: all install install-dev test lint format clean docs lsp

# Default target
all: install

# Installation
install:
	pip install -e .

install-dev:
	pip install -e ".[dev]"

install-docs:
	pip install -e ".[docs]"

install-lsp:
	pip install -e ".[lsp]"

# Testing
test:
	python -m pytest tests/ -v --tb=short

test-cov:
	python -m pytest tests/ -v --tb=short --cov=veripy --cov-report=html

test-fast:
	python -m pytest tests/ -v --tb=short -x

test-unit:
	python -m pytest tests/unit/ -v --tb=short

test-integration:
	python -m pytest tests/integration/ -v --tb=short

# Linting and formatting
lint:
	flake8 veripy/ tests/ --max-line-length=100 --exclude=.venv,venv,build,dist

format:
	black veripy/ tests/ --line-length 100
	isort veripy/ tests/ --profile black

typecheck:
	mypy veripy/ --python-version 3.9

# Code quality
check: lint format typecheck test

# Documentation
docs:
	cd docs && make html

docs-live:
	cd docs && make livehtml

# Clean up
clean:
	find . -type d -name __pycache__ -exec rm -rf {} +
	find . -type d -name .pytest_cache -exec rm -rf {} +
	find . -type d -name .mypy_cache -exec rm -rf {} +
	find . -type d -name .tox -exec rm -rf {} +
	find . -type d -name build -exec rm -rf {} +
	find . -type d -name dist -exec rm -rf {} +
	find . -type d -name *.egg-info -exec rm -rf {} +
	rm -f .coverage
	rm -rf htmlcov/

# Development utilities
shell:
	python -c "import veripy; print('Veripy imported successfully')"

benchmark:
	python -m pytest tests/ --benchmark-only --benchmark-json=benchmark.json

# Distribution
dist: clean  ## Build source distribution and wheel
	python -m build

# Release
release: dist test ## Build and upload to PyPI
	twine upload dist/*

publish: dist  ## Build and upload to PyPI (alias for release)
	twine upload dist/*

publish-test: dist  ## Build and upload to TestPyPI
	twine upload --repository testpypi dist/*

# Help
help:
	@echo "Veripy - Auto-active verification for Python"
	@echo ""
	@echo "Targets:"
	@echo "  all          - Install the package (default)"
	@echo "  install      - Install the package in editable mode"
	@echo "  install-dev  - Install with development dependencies"
	@echo "  test         - Run all tests"
	@echo "  test-fast    - Run tests, stop on first failure"
	@echo "  test-cov     - Run tests with coverage report"
	@echo "  lint         - Run flake8 linter"
	@echo "  format       - Run black and isort formatters"
	@echo "  typecheck    - Run mypy type checker"
	@echo "  check        - Run lint, format, and typecheck"
	@echo "  docs         - Build documentation"
	@echo "  clean        - Clean build artifacts"
	@echo "  help         - Show this help message"
