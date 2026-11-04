CXX ?= g++
CXXFLAGS ?= -O3 -march=native -std=c++20 -Wall -Wextra -Wpedantic -fopenmp
PYTHON ?= python3
WORKERS ?= 2
LEAN_NUM_THREADS ?= 1
export LEAN_NUM_THREADS

all: verify-full

help:
	@echo 'make verify-full   Complete proof, audits and source-bound verification record'
	@echo 'make check         Geometry, certificates and Lean infrastructure (partial proof)'
	@echo 'make replay-data   Generate the 279 projected certificate proofs'
	@echo 'make replay        Check those proofs and the final corner theorem; resumable'
	@echo 'make paper         Compile the manuscript PDF'
	@echo 'WORKERS=2 defaults to two concurrent certificate cases; each uses one Lean thread'

build/%: src/%.cpp
	mkdir -p build
	$(CXX) $(CXXFLAGS) $< -o $@

check-code: build/check_five_colour_certificate build/five_colour_extensions build/five_colour_rare_geometry build/five_colour_fixed_pair build/five_colour_box_geometry
	build/five_colour_extensions
	build/five_colour_rare_geometry
	build/five_colour_fixed_pair
	build/five_colour_box_geometry
	$(PYTHON) -S scripts/generate_five_colour_corner_projections.py --check
	$(PYTHON) -S scripts/generate_five_colour_support.py --check
	$(PYTHON) -S scripts/generate_five_colour_figure.py --check
	$(PYTHON) -S scripts/check_package.py
	$(PYTHON) -S scripts/generate_five_colour_incidence.py --check
	$(PYTHON) -S scripts/generate_five_colour_packed.py --check
	$(PYTHON) -S scripts/generate_five_colour_catalogue.py --check
	$(PYTHON) -S scripts/generate_five_colour_hall.py --check
	$(PYTHON) -S scripts/generate_five_colour_symmetry.py --check
	$(PYTHON) -S scripts/generate_five_colour_capacities.py --check
	$(PYTHON) -S scripts/generate_five_colour_coverage.py --check
	$(PYTHON) -S scripts/generate_five_colour_archive.py --check
	$(PYTHON) -S scripts/generate_five_colour_reduction.py --check
	$(PYTHON) -S scripts/generate_five_colour_projection.py --check
	$(PYTHON) -S scripts/check_five_colour_certificates.py --workers $(WORKERS)

check-lean:
	lake build FiveColour
	$(PYTHON) -S scripts/audit_lean.py

check: check-code check-lean

# Complete proof, including all projected certificates and unconditional extensions.
verify-full:
	$(PYTHON) -u -S scripts/verify_full.py --workers $(WORKERS)

# Requires the completed projected replay (generated modules).
check-extensions:
	lake build Solution
	$(PYTHON) -S scripts/audit_lean.py --file ExtensionsAudit.lean

replay-data: build/five_colour_chunks
	$(PYTHON) -S scripts/generate_five_colour_chunks.py --workers $(WORKERS)

replay:
	$(PYTHON) -u -S scripts/replay_five_colour_chunks.py --workers $(WORKERS)

# Compatibility aliases for commands in earlier copies of the manuscript.
projected-replay-data: replay-data
projected-replay: replay

check-comparator-lower:
	./scripts/verify-comparator.sh --lower-bound

comparator:
	./scripts/verify-comparator.sh

figure:
	$(PYTHON) -S scripts/generate_five_colour_figure.py

paper:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error five-colour-cubes.tex

.PHONY: help verify-full figure check-extensions projected-replay-data projected-replay all check-code check-lean check replay-data replay check-comparator-lower comparator paper
