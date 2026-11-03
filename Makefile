CXX ?= g++
CXXFLAGS ?= -O3 -march=native -std=c++20 -Wall -Wextra -Wpedantic -fopenmp
PYTHON ?= python3
WORKERS ?= 8

all: check

build/%: src/%.cpp
	mkdir -p build
	$(CXX) $(CXXFLAGS) $< -o $@

build/five_colour_exact: src/five_colour_exact.cpp src/five_colour_matching.hpp

build/five_colour_exact_checked: src/five_colour_exact.cpp src/five_colour_matching.hpp
	mkdir -p build
	$(CXX) $(CXXFLAGS) -DMACMAHON_VERIFY_MATCHES $< -o $@

certificates: build/five_colour_boxes build/check_five_colour_certificate build/five_colour_chunks

check-code: certificates
	$(PYTHON) -S scripts/check_package.py
	$(PYTHON) -S scripts/small_replay_cases.py --check
	$(PYTHON) -S scripts/generate_five_colour_catalogue.py --check
	$(PYTHON) -S scripts/generate_five_colour_hall.py --check
	$(PYTHON) -S scripts/generate_five_colour_symmetry.py --check
	$(PYTHON) -S scripts/generate_five_colour_capacities.py --check
	$(PYTHON) -S scripts/generate_five_colour_coverage.py --check
	$(PYTHON) -S scripts/generate_five_colour_archive.py --check
	$(PYTHON) -S scripts/generate_five_colour_reduction.py --check
	$(PYTHON) -S scripts/generate_five_colour_projection.py --check
	$(PYTHON) -S scripts/check_five_colour_root_projection.py --workers $(WORKERS)
	$(PYTHON) -S scripts/check_five_colour_certificates.py --workers $(WORKERS)

check-lean:
	lake build FiveColour
	$(PYTHON) -S scripts/audit_lean.py

check: check-code check-lean

examples:
	$(PYTHON) -u -S scripts/replay_five_colour_chunks.py --group Chunked --workers $(WORKERS)
	lake env lean FiveColour/Chunked/Controls.lean

small-replay: build/five_colour_chunks
	$(PYTHON) -S scripts/generate_five_colour_chunks.py --small --workers $(WORKERS)
	$(PYTHON) -u -S scripts/replay_five_colour_chunks.py --group SmallChunks --workers $(WORKERS)

replay-data: build/five_colour_chunks
	$(PYTHON) -S scripts/generate_five_colour_chunks.py --all --workers $(WORKERS)

replay:
	$(PYTHON) -u -S scripts/replay_five_colour_chunks.py --workers $(WORKERS)

projected-replay-data: build/five_colour_chunks
	$(PYTHON) -S scripts/generate_five_colour_chunks.py --projected --workers $(WORKERS)

projected-replay:
	$(PYTHON) -u -S scripts/replay_five_colour_chunks.py --group ProjectedChunks --workers $(WORKERS)

check-comparator-lower:
	./scripts/verify-comparator.sh --lower-bound

comparator:
	./scripts/verify-comparator.sh

paper:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error five-colour-cubes.tex

.PHONY: projected-replay-data projected-replay all certificates check-code check-lean check examples small-replay replay-data replay check-comparator-lower comparator paper
