#ifndef Alg_Basic_h
#define Alg_Basic_h

#ifdef SIMP
#include "simp/SimpSolver.h"
#else
#include "core/Solver.h"
#endif

#include "../Encoder.h"
#include "../MaxSAT.h"
#include <algorithm>
#include <map>
#include <set>

namespace openwbo {

//=================================================================================================
class Basic : public MaxSAT {

public:
  Basic(bool unit, bool amo, bool disjoint) {
    bestCost = UINT64_MAX;
    verbosity = 1;
    uCost = 0;
    _unitCores = unit;
    _amo = amo;
    _disjointCores = disjoint;
  }
  ~Basic() {
  }

  StatusCode search();

protected:

  StatusCode linearsu();
  StatusCode evaluation();

  StatusCode linearmsu();

  Solver *rebuildSATSolver(); // Rebuild MaxSAT solver.
  void relaxFormula(); // Relaxes soft clauses.
  int findUPUnitCores(Solver * sat_solver);
  int findUnitCores(Solver * sat_solver);
  void findDisjointCores(Solver * sat_solver);
  int findAtMost1(Solver * sat_solver);
  void bronKerbosch(std::vector<Lit> R, std::vector<Lit> P, std::vector<Lit> X);

  std::map<Lit, std::vector<Lit>> graph;
  std::vector<std::vector<Lit>> am1;
  int lower_bound;
  std::vector<std::vector<int>> disjoint_cores;
  vec<bool> unit_cores;
  

  // from MSU3 algorithm
  Solver *solver;  // SAT Solver used as a black box.
  Encoder encoder; // Interface for the encoder of constraints to CNF.

  std::map<Lit, int> coreMapping; // Mapping between the assumption literal and
                                  // the respective soft clause.

  // Soft clauses that are currently in the MaxSAT formula.
  vec<bool> activeSoft;
  vec<Lit> objFunction;
  vec<int> coeffs; // Coefficients of the literals that are used in the
                   // constraint that excludes models.
  
  void initRelaxation();
  Solver * rebuildSolver();

  uint64_t bestCost;
  uint64_t uCost;

  bool _unitCores;
  bool _disjointCores;
  bool _amo;


};
} // namespace openwbo

#endif
