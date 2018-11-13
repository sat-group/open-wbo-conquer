#include "Alg_Basic.h"

using namespace openwbo;

StatusCode Basic::search() {
  // Here you can control which algorithm is being used!
  // It if useful if you implement both linearsu and the MSU3 versions.
  // return linearsu();
  return linearmsu();
}

StatusCode Basic::linearsu(){

  /* Fill this method with the linear search unsat-sat that we discussed during 
   * our last meeting (Alg.2 page 12 of the survey paper); Then try to improve 
   * it by exploiting the unsat core that the SAT solver returns (Alg. 10 page 
   * 26 of the survey paper). For both versions, you should destroy and 
   * rebuild the SAT solver at each iteration since we did not go over how to 
   * perform an incremental construction of x_1 + ... + x_n <= k by either 
   * introducing variables to the left-hand side or by increasing k.
   */

  lbool res = l_False; // this will represent the output of the SAT solver

  /* TODO: relax the soft clauses. Note you can use/change the relaxFormula method */
  relaxFormula();

  /* TODO: initialize the SAT solver with the hard and soft clauses. Note you can 
           use/change the buildSATsolver method */
  Solver* sat_solver = rebuildSATSolver(); // replace NULL with the properly initialization

  uint64_t cost = 0; // this will store the current bound we are exploring
  
  // This will store the variables in the cardinality constraint
  vec<Lit> cardinality_variables;
  for (int i = 0; i < maxsat_formula->nSoft(); ++i)
  {
    Soft &s = getSoftClause(i);
    for (int j = 0; j < s.relaxation_vars.size(); ++j)
    {
      cardinality_variables.push(s.relaxation_vars[j]);
    }
  }
  
  std::map<Lit, int> core_mapping; // Mapping between the assumption literal and
                                  // the respective soft clause.

  // Soft clauses that are currently in the MaxSAT formula.
  vec<bool> active_soft;

  // Initialization of the data structures
  active_soft.growTo(maxsat_formula->nSoft(), false);
  for (int i = 0; i < maxsat_formula->nSoft(); i++)
    core_mapping[getAssumptionLit(i)] = i;

  for(;;){
    
    vec<Lit> assumptions; // You only need assumptions for the MSU3 algorithm!
    /* TODO: push all the assumptions variables from soft clauses into the 
     * assumption vector. Each soft clause has one assumption variable in the member
     * 'assumption_var' */
     // for (int i = 0; i < maxsat_formula->nSoft(); ++i)
     // {
     //   assumptions.push(getSoftClause(i).assumption_var);
     // }

    Encoder *encoder = new Encoder();
    encoder->encodeCardinality(sat_solver, cardinality_variables, cost);

    // the SAT solver will return either l_False (unsatisfiable) or l_True (satisfiable)
    res = searchSATSolver(sat_solver, assumptions);
    printf("current cost is: %llu\n", cost);
    
    if (res == l_True){
      // SAT solver returned satisfiable; What does this mean?
      // (*TODO*) fill the rest...
      printf("%llu\n", cost);
      printAnswer(_OPTIMUM_);
      return _OPTIMUM_;
    } else {
      // SAT solver returned unsatisfiable; What does this mean?
      // (*TODO*) fill the rest...
      if (cost >= maxsat_formula->nSoft())
      {
        printf("unsatisfiable\n");
        return _UNSATISFIABLE_;
      }

      cost++;

      /* How to extract a core from the SAT solver?
       * This is only useful for the MSU3 algorithm */
      for (int i = 0; i < sat_solver->conflict.size(); i++) {
        if (core_mapping.find(sat_solver->conflict[i]) != core_mapping.end()) {
          printf("1\n");
          /* coreMapping[solver->conflict[i]]: 
           * - will contain the index of the soft clause that appears in the core
           * Use this information if you want to explore the unsat core!*/
        }
      }

      /* The assumption vector should only contain assumptions variables from 
       * soft clauses that appeared in a core; this is only useful for the MSU3 
       * algorithm! */

      // Don't forget to rebuild the SAT solver and update the assumption vector!
      sat_solver = rebuildSATSolver(); // replace this with the correct initialization

      /* How to encode x_1 + ... + x_n <= k?
       * You can use the following code: */
      // Encoder *encoder = new Encoder();
      // encoder->encodeCardinality(sat_solver, cardinality_variables, cost);

      /* 'sat_solver': SAT solver should be build before 
       * 'cardinality_variables': should have the variables of the cardinality constraint
       * 'cost': should have the cost we are looking for */
    }
  }

  /* return states are:
   * _SATISFIABLE_
   * _UNSATISFIABLE_
   * _OPTIMUM_
   * _UNKNOWN_
   * _ERROR_ */
  return _UNKNOWN_;
   
}

StatusCode Basic::linearmsu() {

  /* Fill this method with the linear search unsat-sat that we discussed during 
   * our last meeting (Alg.2 page 12 of the survey paper); Then try to improve 
   * it by exploiting the unsat core that the SAT solver returns (Alg. 10 page 
   * 26 of the survey paper). For both versions, you should destroy and 
   * rebuild the SAT solver at each iteration since we did not go over how to 
   * perform an incremental construction of x_1 + ... + x_n <= k by either 
   * introducing variables to the left-hand side or by increasing k.
   */

  lbool res = l_False;

  /* TODO: relax the soft clauses. Note you can use/change the relaxFormula method */
  relaxFormula();

  findUnitCores();
<<<<<<< HEAD
=======

  findUPUnitCores();

>>>>>>> 61704ad892a97cb30bb911dda665c9743499280a
  findDisjointCores();

  Solver* sat_solver = rebuildSATSolver();

  uint64_t cost = 0; // this will store the current bound we are exploring
  
  // This will store the variables in the cardinality constraint
  vec<Lit> cardinality_variables;
  
  std::map<Lit, int> core_mapping; // Mapping between the assumption literal and
                                  // the respective soft clause.

  vec<bool> active_soft;

  Encoder *encoder = new Encoder();
  encoder->setIncremental(_INCREMENTAL_ITERATIVE_);

  // Initialization of the data structures
  active_soft.growTo(maxsat_formula->nSoft(), false);
  for (int i = 0; i < maxsat_formula->nSoft(); i++)
    core_mapping[getAssumptionLit(i)] = i;

  for(;;){

    vec<Lit> assumptions;

    for (int i = 0; i < maxsat_formula->nSoft(); ++i){
      Soft &s = getSoftClause(i);
      if (!active_soft[i]) {
        assumptions.push(~s.assumption_var);
      }
    }
    // printf("cardinality variables size: %d\n", cardinality_variables.size());
    // printf("current cost is: %llu\n\n", cost);
    if (cost != 0) {
      if (!encoder->hasCardEncoding())
      {
        encoder->encodeCardinality(sat_solver, cardinality_variables, cost);
        printf("encoded\n");
      }
      encoder->joinEncoding(sat_solver, cardinality_variables, cost);
      cardinality_variables.clear();
    }

    // the SAT solver will return either l_False (unsatisfiable) or l_True (satisfiable)
    res = searchSATSolver(sat_solver, assumptions);
    
    if (res == l_True) {
      printf("cost: %llu\n", cost);
      printAnswer(_OPTIMUM_);
      return _OPTIMUM_;
    } 
    else if (res == l_False) {
      if (cost >= maxsat_formula->nSoft())
      {
        printf("unsatisfiable\n");
        return _UNSATISFIABLE_;
      }

      cost++;

      // printf("conflict size: %d\n\n", sat_solver->conflict.size());
      for (int i = 0; i < sat_solver->conflict.size(); i++) {
        Lit assump_lit = sat_solver->conflict[i];
        if (core_mapping.find(assump_lit) != core_mapping.end()) {
          active_soft[core_mapping[assump_lit]] = true;
          cardinality_variables.push(assump_lit);
        }
      }
    }
  }

  /* return states are:
   * _SATISFIABLE_
   * _UNSATISFIABLE_
   * _OPTIMUM_
   * _UNKNOWN_
   * _ERROR_ */
  return _UNKNOWN_;
}

void Basic::findUPUnitCores() {

  Solver *sat_solver = rebuildSATSolver();

  vec<bool> is_UC;

  int numfound = 0;
  is_UC.growTo(maxsat_formula->nSoft(), false);

  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Soft &s = getSoftClause(i);
    vec<Lit> implied;
    bool conflict = sat_solver->propagateLit(~s.assumption_var, implied);
    if (conflict) {
      is_UC[i] = true;
      numfound++;
    } else {
      if (sign(~s.assumption_var)){
          printf("~%d -> ",var(~s.assumption_var)+1);
      } else {
          printf("%d -> ",var(~s.assumption_var)+1);
      }
      for (int j = 0; j < implied.size(); j++){
        if (sign(implied[j])){
          printf("~%d ; ",var(implied[j])+1);
      } else {
          printf("%d ; ",var(implied[j])+1);
      }
      }
      printf("\n");
    }

  }

  printf("found %d unit cores using unit propagation @@@@@@@@@@@@@@@@@@@@@@@\n", numfound);

}

void Basic::findUnitCores() {

	Solver *sat_solver = rebuildSATSolver();

	vec<bool> is_UC;

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
		}
  }

	printf("found %d unit cores @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n", numfound);
}

void Basic::findDisjointCores() {

  Solver *sat_solver = rebuildSATSolver();

  int n_soft = maxsat_formula->nSoft();

  vec<bool> in_core;

  std::map<Lit, int> core_mapping; 

  int numFound = 0;

  vec<std::vector<int>> cores;

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
      // std::vector<int> core;
      for (int i = 0; i < sat_solver->conflict.size(); i++) {
          int clause = core_mapping[sat_solver->conflict[i]];
          if (core_mapping.find(sat_solver->conflict[i]) != core_mapping.end()) {
            in_core[clause] = true;
            // core.push_back(clause);
          }
      }
      // cores.push(core);
    }
  }
}

Solver* Basic::rebuildSATSolver() {

  // SAT solver is created with no variables or clauses
  Solver *S = newSATSolver();

  /* The maxsat_formula contains all the information about the MaxSAT formula:
   * - hard clauses
   * - soft clauses and respective relaxation variables
   */

  // We first need to create all the variables in the SAT solver
  for (int i = 0; i < maxsat_formula->nVars(); i++)
    newSATVariable(S);

  // We then traverse the maxsat_formula and add all hard clauses to the SAT solver
  for (int i = 0; i < maxsat_formula->nHard(); i++)
    S->addClause(getHardClause(i).clause);

  /* Next, we need to traverse the maxsat_formula and add all soft clauses to 
   * the SAT solver (we must also include the relaxation variables)
   */
  vec<Lit> clause;
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    clause.clear();
    Soft &s = getSoftClause(i);
    s.clause.copyTo(clause);
    for (int j = 0; j < s.relaxation_vars.size(); j++)
      clause.push(s.relaxation_vars[j]);

    S->addClause(clause);
  }

  return S;
}

void Basic::relaxFormula() {
  /* We relax the formula by creating a literal r_i and adding it as a relaxation 
   * variable; we also add him as an assumption variable with r_i.
   */
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Lit l = maxsat_formula->newLiteral();
    Soft &s = getSoftClause(i);
    s.relaxation_vars.push(l);
    s.assumption_var = l;
  }
}
