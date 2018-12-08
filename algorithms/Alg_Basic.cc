#include "Alg_Basic.h"

using namespace openwbo;

StatusCode Basic::search() {
  // Here you can control which algorithm is being used!
  // It if useful if you implement both linearsu and the MSU3 versions.
  // return linearsu();
  //return linearmsu();
  return evaluation();
}

StatusCode Basic::evaluation() {

  lbool res = l_True;
  initRelaxation();
  solver = rebuildSolver();
  vec<Lit> assumptions;
  vec<Lit> joinObjFunction;
  vec<Lit> currentObjFunction;
  vec<Lit> encodingAssumptions;
  encoder.setIncremental(_INCREMENTAL_ITERATIVE_);

  activeSoft.growTo(maxsat_formula->nSoft(), false);
  for (int i = 0; i < maxsat_formula->nSoft(); i++)
    coreMapping[getAssumptionLit(i)] = i;

  res = searchSATSolver(solver, assumptions);
  assert (res == l_True);
  bestCost = computeCostModel(solver->model);
  saveModel(solver->model);
  printBound(bestCost);

  if (_unitCores) {
    uCost = findUPUnitCores(solver);
    if (uCost > 0){
      if (verbosity > 0)
        printf("c LB : %-12" PRIu64 "\n", lbCost+uCost);
    }
  } else {
    unit_cores.growTo(maxsat_formula->nSoft(), false);
  }

  if (_amo)
    lbCost = findAtMost1(solver);

  if (_disjointCores)
    findDisjointCores(solver);

  if (disjoint_cores.size() > 0 || lbCost > 0){
    // TODO: try the tree structure instead of direct encoding
    for (int i = 0; i < disjoint_cores.size(); i++) {
      vec<Lit> clause;
      for (int j = 0; j < disjoint_cores[i].size(); j++) {
        clause.push(getRelaxationLit(disjoint_cores[i][j]));
        activeSoft[disjoint_cores[i][j]] = true;
      }
      //solver->addClause(clause);
    }

      currentObjFunction.clear();
      assumptions.clear();
      for (int i = 0; i < maxsat_formula->nSoft(); i++) {
        if (activeSoft[i])
          currentObjFunction.push(getRelaxationLit(i));
        else if (!unit_cores[i])
          assumptions.push(~getAssumptionLit(i));
      }

      if (disjoint_cores.size() < lbCost && disjoint_cores.size() > 0 || lbCost == 0)
        lbCost = disjoint_cores.size();

      if (verbosity > 0)
        printf("c LB : %-12" PRIu64 "\n", lbCost + uCost);

      if (verbosity > 0)
        printf("c Relaxed soft clauses %d / %d\n", currentObjFunction.size(),
               objFunction.size());

      if (!encoder.hasCardEncoding()) {
        if (lbCost != (unsigned)currentObjFunction.size()) {
          encoder.buildCardinality(solver, currentObjFunction, lbCost);
          encoder.incUpdateCardinality(solver, currentObjFunction, lbCost,
                                       encodingAssumptions);
        }
      }
      for (int i = 0; i < encodingAssumptions.size(); i++)
        assumptions.push(encodingAssumptions[i]);

  } else {
    printf("default!\n");
    for (int i = 0; i < objFunction.size(); i++)
          assumptions.push(~objFunction[i]);
  }


  for (;;) {

    res = searchSATSolver(solver, assumptions);
    if (res == l_True) {
      uint64_t newCost = computeCostModel(solver->model);
      if (newCost < bestCost) {
        saveModel(solver->model);
        printBound(newCost);
        bestCost = newCost;
      }
        assert(lbCost+uCost == bestCost);
        printAnswer(_OPTIMUM_);
        return _OPTIMUM_;
    }

    if (res == l_False) {
      lbCost++;
      nbCores++;
      if (verbosity > 0)
        printf("c LB : %-12" PRIu64 "\n", lbCost + uCost);

      if (lbCost+uCost == ubCost) {
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
        else if (!unit_cores[i])
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
      // printAnswer(_OPTIMUM_);
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

  // findUnitCores();

  // findUPUnitCores();

  //findAtMost1();

  //findDisjointCores();

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
      // printAnswer(_OPTIMUM_);
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

static std::vector<Lit> vintersection(std::vector<Lit> &v1, std::vector<Lit> &v2) {
  std::vector<Lit> v;

  sort(v1.begin(), v1.end());
  sort(v2.begin(), v2.end());

  set_intersection(v1.begin(),v1.end(),v2.begin(),v2.end(),back_inserter(v));

  return v;
}

static std::vector<Lit> vunion(std::vector<Lit> &v1, std::vector<Lit> &v2) {
  std::vector<Lit> v;

  sort(v1.begin(), v1.end());
  sort(v2.begin(), v2.end());

  set_union(v1.begin(),v1.end(),v2.begin(),v2.end(),back_inserter(v));

  return v;
}

static std::vector<Lit> vdifference(std::vector<Lit> &v1, std::vector<Lit> &v2) {
  std::vector<Lit> v;

  sort(v1.begin(), v1.end());
  sort(v2.begin(), v2.end());

  set_difference(v1.begin(),v1.end(),v2.begin(),v2.end(),back_inserter(v));

  return v;
}

void Basic::bronKerbosch(std::vector<Lit> R, std::vector<Lit> P, std::vector<Lit> X) {
  if(P.empty() && X.empty() && !R.empty()) {
    int no_intersect = 1;
    for (std::vector<Lit> v : am1) {
      if (!(vintersection(v, R).empty())) {
        no_intersect = 0;
        break;
      } 
    }
    lower_bound += no_intersect;
    am1.push_back(R);
  }
  auto i = P.begin();
  while(!P.empty() && i != P.end()){
    Lit x = *i;
    std::vector<Lit> singleton = { x };
    bronKerbosch(
      vunion(R,singleton), 
      vintersection(P,graph[x]),
      vintersection(X,graph[x]));
    P = vdifference(P,singleton);
    X = vunion(X,singleton);
    if(!P.empty())
      i = P.begin();
  }
}

int Basic::findAtMost1(Solver *sat_solver) {

  //Solver *sat_solver = rebuildSATSolver();

  //vec<bool> is_UC;
  //vec<bool> active_soft; // I don't think I use this.
  vec<vec<Lit>> cliques;

  int numUCfound = 0;
  if (!_unitCores)
    unit_cores.growTo(maxsat_formula->nSoft(), false);
  //active_soft.growTo(maxsat_formula->nSoft(), false);

  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Soft &s = getSoftClause(i);
    vec<Lit> implied;
    bool conflict = sat_solver->propagateLit(~s.assumption_var, implied);
    if (conflict) { // Unit cores found here
      if (!_unitCores) {
        unit_cores[i] = true;
        vec<Lit> clause;
        sat_solver->addClause(s.assumption_var);
      }
      numUCfound++;
    } else {
      std::vector<Lit> temp;
      for (int j = 0; j < implied.size(); ++j)
      {
        // If the Lit is a relaxation var and positive sign, push.
        if (var(implied[j])+1 > maxsat_formula->nInitialVars() && !sign(implied[j])){
          temp.push_back(implied[j]);
        }
      }
      if (temp.size() != 0){ // graph is global, not at am1 yet. Just building graph.
        graph[s.assumption_var] = temp;
      }
    }
  }

  auto i = graph.begin();

  while (i != graph.end()) {
    std::vector<Lit> &temp = i->second;
    auto j = temp.begin();
    while (j != temp.end()) {
      Lit x = *j;
      // Preliminary filtering. Basically making the graph undirected
      if (graph.count(x) != 1 || std::find(graph[x].begin(), graph[x].end(),i->first) == graph[x].end()) {
        temp.erase(j);
      }
      ++j;
    }
    ++i;
  }

  // for (const auto &p : graph) {
  //   // reverse sign, since reversed in graph
  //   if (sign(p.first)){
  //       printf("%d -> ",var(p.first)+1);
  //     } else {
  //       printf("~%d -> ",var(p.first)+1);
  //     }
  //   for (Lit x : p.second)
  //   {
  //     if (sign(x)){
  //         printf("~%d ; ",var(x)+1);
  //     } else {
  //         printf("%d ; ",var(x)+1);
  //     }
  //   }
  //   printf("\n");
  // }

  std::vector<Lit> v; // Filled with all Lits with an edge in the graph.
  for(auto it = graph.begin(); it != graph.end(); ++it) {
    v.push_back(it->first);
  }

  // Finding maximal cliques. Puts them in am1 vector.
  lower_bound = 0;
  bronKerbosch({}, v, {});

  // Printing
  Encoder *encoder = new Encoder();
  std::set<Lit> bb;

  for (std::vector<Lit> v : am1) {
    //printf("am1: ");
    vec<Lit> clause;
    for (Lit l : v) {
      clause.push(~l);
      bb.insert(l);
      //printf("%d, ", var(l) + 1);
    }
    encoder->encodeAMO(sat_solver, clause);
    //printf("\n");
  }

  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
      if (bb.find(getAssumptionLit(i)) != bb.end()){
        activeSoft[i] = true;
      }
  }

  if (!_unitCores)
    uCost = numUCfound;
  
  printf("c [SCS] found %d unit cores in AM1\n", numUCfound);
  printf("c [SCS] found potentially %lu AM1\n", am1.size());
  printf("c [SCS] loose lower bound: %d\n", lower_bound);
  return lower_bound;
}

int Basic::findUPUnitCores(Solver *sat_solver) {

  //Solver *sat_solver = rebuildSATSolver();
  int numfound = 0;
  unit_cores.growTo(maxsat_formula->nSoft(), false);

  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Soft &s = getSoftClause(i);
    vec<Lit> implied;
    bool conflict = sat_solver->propagateLit(~s.assumption_var, implied);
    if (conflict) {
      unit_cores[i] = true;
      numfound++;
      sat_solver->addClause(s.assumption_var);
    } else {
      uint64_t newCost = computeCostModel(solver->model);
      if (newCost < bestCost) {
        saveModel(solver->model);
        printBound(newCost);
        bestCost = newCost;
      }
      // if (sign(~s.assumption_var)){
      //     printf("~%d -> ",var(~s.assumption_var)+1);
      // } else {
      //     printf("%d -> ",var(~s.assumption_var)+1);
      // }
      // for (int j = 0; j < implied.size(); j++){
      //   if (sign(implied[j])){
      //     printf("~%d ; ",var(implied[j])+1);
      // } else {
      //     printf("%d ; ",var(implied[j])+1);
      // }
      // }
      // printf("\n");
    }

  }

  //printf("found %d unit cores using unit propagation @@@@@@@@@@@@@@@@@@@@@@@\n", numfound);
  //printf("inititial vars: %d\n", maxsat_formula->nInitialVars());
  printf ("c [SCS] %d unit cores\n",numfound);
  return numfound;

}

int Basic::findUnitCores(Solver *sat_solver) {

  int limit = 10000;
	//Solver *sat_solver = rebuildSATSolver();

	int numfound = 0;

	lbool res = l_True;

	unit_cores.growTo(maxsat_formula->nSoft(), false);

	for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Soft &s = getSoftClause(i);
    vec<Lit> assumptions;
    assumptions.push(~s.assumption_var);
    sat_solver->setConfBudget(limit);
    res = searchSATSolver(sat_solver, assumptions);
    sat_solver->budgetOff();
    if (res == l_False) {
			unit_cores[i] = true;
			numfound++;
      sat_solver->addClause(s.assumption_var);
		} else if (res == l_True){
      uint64_t newCost = computeCostModel(solver->model);
      if (newCost < bestCost) {
        saveModel(solver->model);
        printBound(newCost);
        bestCost = newCost;
      }
    }
  }

  printf ("c [SCS] %d unit cores\n",numfound);
  return numfound;
	//printf("found %d unit cores @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n", numfound);
}

void Basic::findDisjointCores(Solver * sat_solver) {

  //Solver *sat_solver = rebuildSATSolver();
  int limit = 500000;

  int n_soft = maxsat_formula->nSoft();

  vec<bool> in_core;

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
    sat_solver->setConfBudget(limit);
    res = searchSATSolver(sat_solver, assumptions);
    sat_solver->budgetOff();
    if (res != l_False) {
      if (res == l_True) {
        uint64_t newCost = computeCostModel(solver->model);
        if (newCost < bestCost) {
          saveModel(solver->model);
          printBound(newCost);
          bestCost = newCost;
        }
      }
      printf("c [SCS] %d disjoint cores\n",numFound);
      //printf("numFound: %d disjoint cores @@@@@@@@\n", numFound);
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
      disjoint_cores.push_back(core);
    }
  }
  sat_solver->budgetOff();
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

void Basic::initRelaxation() {
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    Lit l = maxsat_formula->newLiteral();
    Soft &s = getSoftClause(i);
    s.relaxation_vars.push(l);
    s.assumption_var = l;
    objFunction.push(l);
  }
}

Solver *Basic::rebuildSolver() {

  Solver *S = newSATSolver();

  reserveSATVariables(S, maxsat_formula->nVars());

  for (int i = 0; i < maxsat_formula->nVars(); i++)
    newSATVariable(S);

  for (int i = 0; i < maxsat_formula->nHard(); i++)
    S->addClause(getHardClause(i).clause);

  vec<Lit> clause;
  for (int i = 0; i < maxsat_formula->nSoft(); i++) {
    clause.clear();
    Soft &s = getSoftClause(i);
    s.clause.copyTo(clause);
    for (int j = 0; j < s.relaxation_vars.size(); j++)
      clause.push(s.relaxation_vars[j]);

    S->addClause(clause);
  }

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
