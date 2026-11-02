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
	$(PYTHON) -S scripts/check_five_colour_certificates.py --workers $(WORKERS)

check-lean:
	lake build FiveColour
	$(PYTHON) -S scripts/audit_lean.py

check: check-code check-lean

examples:
	lake build FiveColour.Chunked.All
	lake env lean FiveColour/Chunked/Audit.lean
	lake env lean FiveColour/Chunked/Controls.lean

replay-data: build/five_colour_chunks
	$(PYTHON) -S scripts/generate_five_colour_chunks.py --all --workers $(WORKERS)

replay:
	$(PYTHON) -u -S scripts/replay_five_colour_chunks.py --workers $(WORKERS)

paper:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error macmahon-five-colour-threshold.tex

.PHONY: all certificates check-code check-lean check examples replay-data replay paper
