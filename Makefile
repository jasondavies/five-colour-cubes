CXX ?= g++
CXXFLAGS ?= -O3 -march=native -std=c++20 -Wall -Wextra -Wpedantic -fopenmp
PYTHON ?= python3
WORKERS ?= 2
LEAN_NUM_THREADS ?= 1
export LEAN_NUM_THREADS

all: verify-full

# Export expanded Make settings without interpolating their contents into shell code.
verification-config build/cxx-config.json: export VERIFY_CXX = $(CXX)
verification-config build/cxx-config.json: export VERIFY_CXXFLAGS = $(CXXFLAGS)
verification-config: export VERIFY_PYTHON = $(PYTHON)
verification-config: export VERIFY_WORKERS = $(WORKERS)
export VERIFICATION_CONFIG_FILE
verification-config: export VERIFY_LEAN_NUM_THREADS = $(LEAN_NUM_THREADS)
verification-config:
	@$(PYTHON) -c 'import json,os,pathlib; data=json.dumps({k:os.environ["VERIFY_"+k] for k in ("CXX","CXXFLAGS","PYTHON","WORKERS","LEAN_NUM_THREADS")}); path=os.environ.get("VERIFICATION_CONFIG_FILE"); pathlib.Path(path).write_text(data+"\n") if path else print(data)'

help:
	@echo 'make verify-full   Complete proof, audits and source-bound verification record'
	@echo 'make check         Geometry, certificates and Lean infrastructure (partial proof)'
	@echo 'make check-replay-data   Check retained replay sources without rewriting them'
	@echo 'make replay-data   Regenerate the 279 projected certificate proofs'
	@echo 'make replay        Check those proofs and the final corner theorem; resumable'
	@echo 'make check-classification-data   Audit the separate staged enumeration'
	@echo 'make classification-replay   Check its full Lean classification and axioms'
	@echo 'make paper         Compile the manuscript PDF'
	@echo 'WORKERS=2 defaults to two concurrent certificate cases; each uses one Lean thread'

# Preserve the stamp's mtime when the effective build configuration is unchanged.
build/cxx-config.json: FORCE scripts/cpp_build_config.py
	$(PYTHON) -S scripts/cpp_build_config.py $@

FORCE:

build/%: src/%.cpp build/cxx-config.json
	mkdir -p build
	$(CXX) $(CXXFLAGS) $< -o $@

# The optional minimizer uses the unchanged checker as its search oracle.
build/minimize_five_colour_certificate: src/minimize_five_colour_certificate.cpp src/check_five_colour_certificate.cpp build/cxx-config.json
	mkdir -p build
	$(CXX) $(CXXFLAGS) $< -o $@

check-code: check-replay-data build/check_five_colour_certificate build/five_colour_extensions build/five_colour_rare_geometry build/five_colour_fixed_pair build/five_colour_box_geometry
	@$(PYTHON) -c 'import sys; sys.exit(0 if __debug__ else "Checks require Python assertions; remove -O/PYTHONOPTIMIZE")'
	build/five_colour_extensions
	build/five_colour_rare_geometry
	build/five_colour_fixed_pair
	build/five_colour_box_geometry
	$(PYTHON) -S scripts/generate_five_colour_corner_projections.py --check
	$(PYTHON) -S scripts/generate_five_colour_support.py --check
	$(PYTHON) -S scripts/generate_five_colour_extremal.py --check
	$(PYTHON) -S scripts/generate_five_colour_triples.py --check
	$(PYTHON) -S scripts/generate_five_colour_universal.py --check
	$(PYTHON) -S scripts/check_five_colour_universal.py
	$(PYTHON) -S scripts/check_five_colour_extremal.py
	$(PYTHON) -S scripts/test_extremal_dictionary.py
	$(PYTHON) -S scripts/generate_five_colour_figure.py --check
	$(PYTHON) -S scripts/check_package.py
	$(PYTHON) -S scripts/test_verification_state.py
	$(PYTHON) -S scripts/test_source_checks.py
	$(PYTHON) -S scripts/test_hall_reduction.py
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

# Requires the completed projected replay.
check-extensions:
	lake build Solution
	$(PYTHON) -S scripts/audit_lean.py --file ExtensionsAudit.lean

check-replay-data: build/five_colour_chunks
	$(PYTHON) -S scripts/generate_five_colour_chunks.py --check --workers $(WORKERS)

replay-data: build/five_colour_chunks
	$(PYTHON) -S scripts/generate_five_colour_chunks.py --workers $(WORKERS)

replay:
	$(PYTHON) -u -S scripts/replay_five_colour_chunks.py --workers $(WORKERS)

check-comparator-lower:
	./scripts/verify-comparator.sh --lower-bound

check-comparator-universal:
	./scripts/verify-comparator.sh --universal

comparator:
	./scripts/verify-comparator.sh

figure:
	$(PYTHON) -S scripts/generate_five_colour_figure.py

paper:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error five-colour-cubes.tex

.PHONY: check-replay-data FORCE verification-config help verify-full figure check-extensions all check-code check-lean check replay-data replay check-comparator-lower check-comparator-universal comparator paper

build/five_colour_enumeration: src/five_colour_enumeration.cpp build/cxx-config.json
	$(CXX) $(CXXFLAGS) $< -o $@

# Complete fourteen-copy classification, separate from the established threshold route.
check-classification-data: build/five_colour_enumeration
	$(PYTHON) -S scripts/generate_five_colour_classification.py --check
	$(PYTHON) -S scripts/check_five_colour_classification.py
	$(PYTHON) -S scripts/test_enumeration_checks.py
	$(PYTHON) -S scripts/test_enumeration_driver.py
	$(PYTHON) -S scripts/test_enumeration_sources.py
	$(PYTHON) -S scripts/generate_five_colour_enumeration.py --check --workers $(WORKERS)

classification-data: build/five_colour_enumeration
	$(PYTHON) -S scripts/generate_five_colour_classification.py
	$(PYTHON) -S scripts/generate_five_colour_enumeration.py --workers $(WORKERS)

classification-replay:
	$(PYTHON) -u -S scripts/replay_five_colour_enumeration.py --workers $(WORKERS)

.PHONY: check-classification-data classification-data classification-replay
