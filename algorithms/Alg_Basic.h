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

  Solver *buildSATSolver(); // Rebuild MaxSAT solver.
  void relaxFormula(); // Relaxes soft clauses.

};
} // namespace openwbo

#endif
