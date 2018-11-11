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
  Basic() {
  }
  ~Basic() {
  }

  StatusCode search();

protected:

  StatusCode linearsu();

  StatusCode linearmsu();

  Solver *rebuildSATSolver(); // Rebuild MaxSAT solver.
  void relaxFormula(); // Relaxes soft clauses.
  void findUPUnitCores();
  void findUnitCores();
  void findDisjointCores();

};
} // namespace openwbo

#endif
