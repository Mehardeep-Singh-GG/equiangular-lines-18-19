CXX ?= g++
CXXFLAGS ?= -O3 -std=c++20 -pthread -Wall -Wextra

POLY_TARGETS := \
	poly/enum_polys \
	poly/enum_polys_v2 \
	poly/enum_polys_v3 \
	poly/enum_polys_v4 \
	poly/check_p49_7 \
	poly/filter_mod128 \
	poly/stage2_deck \
	poly/stage2_deck_par \
	poly/stage2_deck_odd \
	poly/stage2_deck_odd_v2 \
	poly/stage2_deck_odd_v3 \
	poly/enum705

CORE_TARGETS := \
	poly/enum_polys_v4 \
	poly/stage2_deck_par \
	poly/stage2_deck_odd_v3 \
	poly/enum705 \
	../audit/clean_enum

SEARCH_TARGETS := \
	search/extender \
	search/kopt_search \
	search/spectral_tabu \
	search/z_lattice_search \
	search/probe_idx13_fast \
	search/probe_idx13_F72 \
	search/probe_idx13_M12 \
	search/probe_idx13_S74

.PHONY: all core poly search clean

all: poly search ../audit/clean_enum

core: $(CORE_TARGETS)

poly: $(POLY_TARGETS)

search: $(SEARCH_TARGETS)

poly/%: poly/%.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

search/%: search/%.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

../audit/clean_enum: ../audit/clean_enum.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

clean:
	rm -f $(POLY_TARGETS) $(SEARCH_TARGETS) ../audit/clean_enum
