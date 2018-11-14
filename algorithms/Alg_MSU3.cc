/*!
 * \author Ruben Martins - ruben@sat.inesc-id.pt
 *
 * @section LICENSE
 *
 * Open-WBO, Copyright (c) 2013-2017, Ruben Martins, Vasco Manquinho, Ines Lynce
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */

#include "Alg_MSU3.h"

using namespace openwbo;

/*_________________________________________________________________________________________________
  |
  |  MSU3_iterative : [void] ->  [void]
  |
  |  Description:
  |
  |    Incremental iterative encoding for the MSU3 algorithm.
  |    The cardinality constraint is build incrementally in an iterative
  |    fashion.
  |    This algorithm is similar to the non-incremental version of MSU3
  |    algorithm.
  |    It is advised to first check the non-incremental version and then check
  |    the differences.
  |
  |  For further details see:
  |    *  Ruben Martins, Saurabh Joshi, Vasco M. Manquinho, Inês Lynce:
  |       Incremental Cardinality Constraints for MaxSAT. CP 2014: 531-548
  |
  |  Pre-conditions:
  |    * Assumes Totalizer is used as the cardinality encoding.
  |
  |  Post-conditions:
  |    * 'ubCost' is updated.
  |    * 'nbSatisfiable' is updated.
  |    * 'nbCores' is updated.
  |
  |________________________________________________________________________________________________@*/
StatusCode MSU3::MSU3_iterative() {

  if (encoding != _CARD_TOTALIZER_) {
    if(print) {
      printf("Error: Currently algorithm MSU3 with iterative encoding only "
             "supports the totalizer encoding.\n");
      printf("s UNKNOWN\n");
    }
    throw MaxSATException(__FILE__, __LINE__, "MSU3 only supports totalizer");
    return _UNKNOWN_;
  }

  lbool res = l_True;
  initRelaxation();
  findUnitCores();
  findDisjointCores();
  solver = rebuildSolver();
  //lbCost = is_UC.size();
  vec<Lit> assumptions;
  vec<Lit> joinObjFunction;
  vec<Lit> currentObjFunction;
  vec<Lit> encodingAssumptions;
  encoder.setIncremental(_INCREMENTAL_ITERATIVE_);

  activeSoft.growTo(maxsat_formula->nSoft(), false);
  for (int i = 0; i < maxsat_formula->nSoft(); i++)
    coreMapping[getAssumptionLit(i)] = i;

  // building the cardinality constraint with the disjoint core information
  if (cores.size() > 0 && false){

    // for (int i = 0; i < cores.size(); i++){
    //   vec<Lit> clause;
    //   for (int j = 0; j < cores[i].size(); j++){
    //     Soft &s = getSoftClause(j);
    //     clause.push(s.assumption_var);
    //   }
    //   solver->addClause(clause);
    // }

      for (int i = 0; i < maxsat_formula->nSoft(); i++) {
        if (in_core[i]){
          currentObjFunction.push(getRelaxationLit(i));
          activeSoft[i] = true;
        }
      }
      assert (currentObjFunction.size() > 0);
      lbCost = cores.size();

     encoder.buildCardinality(solver, currentObjFunction, lbCost);
     encoder.incUpdateCardinality(solver, currentObjFunction, lbCost,
                                       encodingAssumptions);
  }
        

  for (;;) {

    res = searchSATSolver(solver, assumptions);
    if (res == l_True) {
      nbSatisfiable++;
      uint64_t newCost = computeCostModel(solver->model);
      saveModel(solver->model);
      printBound(newCost);

      ubCost = newCost;

      if (nbSatisfiable == 1) {
        // for (int i = 0; i < objFunction.size(); i++){
        //   assumptions.push(~objFunction[i]);
        // }

      for (int i = 0; i < maxsat_formula->nSoft(); i++) {
        if (!activeSoft[i])
          assumptions.push(~getAssumptionLit(i));
      }

      } else {
        assert(lbCost+uc_number == newCost);
        printAnswer(_OPTIMUM_);
        return _OPTIMUM_;
      }
    }

    if (res == l_False) {
      lbCost++;
      nbCores++;
      if (verbosity > 0)
        printf("c LB : %-12" PRIu64 "\n", lbCost + uc_number);

      if (nbSatisfiable == 0) {
        printAnswer(_UNSATISFIABLE_);
        return _UNSATISFIABLE_;
      }

      if (lbCost + uc_number == ubCost) {
        assert(nbSatisfiable > 0);
        if (verbosity > 0)
          printf("c LB = UB\n");
        printAnswer(_OPTIMUM_);
        return _OPTIMUM_;
      }

      sumSizeCores += solver->conflict.size();

      if (solver->conflict.size() == 0) {
        printAnswer(_UNSATISFIABLE_);
        return _UNSATISFIABLE_;
      }

      joinObjFunction.clear();
      for (int i = 0; i < solver->conflict.size(); i++) {
        if (coreMapping.find(solver->conflict[i]) != coreMapping.end()) {
          assert(!activeSoft[coreMapping[solver->conflict[i]]]);
          activeSoft[coreMapping[solver->conflict[i]]] = true;
          joinObjFunction.push(
              getRelaxationLit(coreMapping[solver->conflict[i]]));
        }
      }

      currentObjFunction.clear();
      assumptions.clear();
      for (int i = 0; i < maxsat_formula->nSoft(); i++) {
        if (activeSoft[i])
          currentObjFunction.push(getRelaxationLit(i));
        else if (!is_UC[i])
          assumptions.push(~getAssumptionLit(i));
      }

      if (verbosity > 0)
        printf("c Relaxed soft clauses %d / %d\n", currentObjFunction.size(),
               objFunction.size());

      if (!encoder.hasCardEncoding()) {
        if (lbCost != (unsigned)currentObjFunction.size()) {
          encoder.buildCardinality(solver, currentObjFunction, lbCost);
          encoder.incUpdateCardinality(solver, currentObjFunction, lbCost,
                                       encodingAssumptions);
        }
      } else {
        // Incremental construction of the encoding.
        if (joinObjFunction.size() > 0)
          encoder.joinEncoding(solver, joinObjFunction, lbCost);

        // The right-hand side is constrained using assumptions.
        // NOTE: 'encodingAsssumptions' is modified in 'incrementalUpdate'.
        encoder.incUpdateCardinality(solver, currentObjFunction, lbCost,
                                     encodingAssumptions);
      }

      for (int i = 0; i < encodingAssumptions.size(); i++)
        assumptions.push(encodingAssumptions[i]);
    }
  }
  return _ERROR_;
}

// Public search method
StatusCode MSU3::search() {

  if (maxsat_formula->getProblemType() == _WEIGHTED_) {
    if(print) {
      printf("Error: Currently algorithm MSU3 does not support weighted "
             "MaxSAT instances.\n");
      printf("s UNKNOWN\n");
    }
    throw MaxSATException(__FILE__, __LINE__, "MSU3 does not support weighted");
    return _UNKNOWN_;
  }

  if (incremental_strategy == _INCREMENTAL_ITERATIVE_) {
    if (encoding != _CARD_TOTALIZER_) {
      if(print) {
        printf("Error: Currently iterative encoding in PartMSU3 only "
             "supports the Totalizer encoding.\n");
        printf("s UNKNOWN\n");
      }
      throw MaxSATException(__FILE__, __LINE__, "PartMSU3 only supports Totalizer");
      return _UNKNOWN_;
    }
  }

  printConfiguration();
  return MSU3_iterative();
}

/************************************************************************************************
 //
 // Rebuild MaxSAT solver
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  rebuildSolver : [void]  ->  [Solver *]
  |
  |  Description:
  |
  |    Rebuilds a SAT solver with the current MaxSAT formula.
  |
  |________________________________________________________________________________________________@*/
Solver *MSU3::rebuildSolver() {

  Solver *S = newSATSolver();

  reserveSATVariables(S, maxsat_formula->nVars());

  for (int i = 0; i < maxsat_formula->nVars(); i++)
    newSATVariable(S);

  vec<Lit> clause;
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    clause.clear();
    Soft &s = getSoftClause(i);
    s.clause.copyTo(clause);
    if (is_UC.size() == 0 || !is_UC[i]){
      for (int j = 0; j < s.relaxation_vars.size(); j++)
        clause.push(s.relaxation_vars[j]);

      S->addClause(clause);
    }
    else {
      for (int j = 0; j < clause.size(); j++){
        vec<Lit> cls;
        cls.push(~clause[j]);
        maxsat_formula->addHardClause(cls);
      }
    }
  }

  for (int i = 0; i < maxsat_formula->nHard(); i++)
    S->addClause(getHardClause(i).clause);

  // printf("c #PB: %d\n", maxsat_formula->nPB());
  for (int i = 0; i < maxsat_formula->nPB(); i++) {
    Encoder *enc = new Encoder(_INCREMENTAL_NONE_, _CARD_MTOTALIZER_,
                               _AMO_LADDER_, _PB_GTE_);

    // Make sure the PB is on the form <=
    if (!maxsat_formula->getPBConstraint(i)->_sign)
      maxsat_formula->getPBConstraint(i)->changeSign();

    enc->encodePB(S, maxsat_formula->getPBConstraint(i)->_lits,
                  maxsat_formula->getPBConstraint(i)->_coeffs,
                  maxsat_formula->getPBConstraint(i)->_rhs);

    // maxsat_formula->getPBConstraint(i)->print();

    delete enc;
  }

  // printf("c #Card: %d\n", maxsat_formula->nCard());
  for (int i = 0; i < maxsat_formula->nCard(); i++) {
    Encoder *enc = new Encoder(_INCREMENTAL_NONE_, _CARD_MTOTALIZER_,
                               _AMO_LADDER_, _PB_GTE_);

    if (maxsat_formula->getCardinalityConstraint(i)->_rhs == 1) {
      enc->encodeAMO(S, maxsat_formula->getCardinalityConstraint(i)->_lits);
    } else {
      enc->encodeCardinality(S,
                             maxsat_formula->getCardinalityConstraint(i)->_lits,
                             maxsat_formula->getCardinalityConstraint(i)->_rhs);
    }

    delete enc;
  }

  return S;
}

/************************************************************************************************
 //
 // Other protected methods
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  initRelaxation : [void] ->  [void]
  |
  |  Description:
  |
  |    Initializes the relaxation variables by adding a fresh variable to the
  |    'relaxationVars' of each soft clause.
  |
  |  Post-conditions:
  |    * 'objFunction' contains all relaxation variables that were added to soft
  |      clauses.
  |
  |________________________________________________________________________________________________@*/
void MSU3::initRelaxation() {
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Lit l = maxsat_formula->newLiteral();
    Soft &s = getSoftClause(i);
    s.relaxation_vars.push(l);
    s.assumption_var = l;
    objFunction.push(l);
  }
}

/*_________________________________________________________________________________________________
  |
  |  initRelaxation : [void] ->  [void]
  |
  |  Description:
  |
  |    Initializes the relaxation variables by adding a fresh variable to the
  |    'relaxationVars' of each soft clause.
  |
  |  Post-conditions:
  |    * 'objFunction' contains all relaxation variables that were added to soft
  |      clauses.
  |
  |________________________________________________________________________________________________@*/
void MSU3::findUnitCores() {

  Solver *sat_solver = rebuildSolver();
  is_UC.clear();
  int numfound = 0;
  lbool res = l_True;
  is_UC.growTo(maxsat_formula->nSoft(), false);
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Soft &s = getSoftClause(i);
    vec<Lit> assumptions;
    assumptions.push(~s.assumption_var);
    res = searchSATSolver(sat_solver, assumptions);
    if (res == l_False) {
      is_UC[i] = true;
      numfound++;
      uc_number++;
    }
  }
  printf("found %d unit cores @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n", numfound);
}

void MSU3::findDisjointCores() {

  Solver *sat_solver = rebuildSolver();

  int n_soft = maxsat_formula->nSoft();

  std::map<Lit, int> core_mapping; 

  int numFound = 0;

  in_core.growTo(n_soft, false);

  for (int i = 0; i < n_soft; i++) {
    Soft &s = getSoftClause(i);
    core_mapping[s.assumption_var] = i;
  }

  lbool res;

  while (true) {
    vec<Lit> assumptions;
    for (int i = 0; i < n_soft; ++i) {
      Soft &s = getSoftClause(i);
      if (!in_core[i]) {
        assumptions.push(~s.assumption_var);
      }
    }
    res = searchSATSolver(sat_solver, assumptions);
    if (res == l_True) {
      printf("numFound: %d disjoint cores @@@@@@@@\n", numFound);
      return;
    }
    else {
      numFound++;
      std::vector<int> core;
      for (int i = 0; i < sat_solver->conflict.size(); i++) {
          int clause = core_mapping[sat_solver->conflict[i]];
          if (core_mapping.find(sat_solver->conflict[i]) != core_mapping.end()) {
            in_core[clause] = true;
            core.push_back(clause);
          }
      }
      cores.push_back(core);
    }
  }
}

// Print MSU3 configuration.
void MSU3::print_MSU3_configuration() {
  printf("c |  Algorithm: %23s                                             "
         "                      |\n",
         "MSU3");
}
