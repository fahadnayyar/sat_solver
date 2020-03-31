// TODO: 
// 1. lbd
// 2. learning-rate decision heuristic (vijay's sat'16)
// 3. deletion strategy
// 4. preprocessing
// 5. conf. clause shrinking
// 6. seperate treatment of binary clauses 
// 7. Watchers with blocking clauses and possibly more literals (p. stucky's cache awarness paper)


// my_TODO: [.] means paper.

// 1.) lbd:
		// (“Glue”) -- the # of decision levels in the clause.
		// • Use it to improve:
				// • Decision strategy 
				// • Deletion strategy 
				// • clauseshrinking
		// [Predicting Learnt Clauses Quality in Modern SAT Solvers, Gilles Audemard, Laurent Simon, IJCAI09]

// 2.) Change Decision Heuristic (learning-rate decision heuristic (vijay's sat'16)):
		// Measure the activity of variables in learning new clauses relative to others, when the variable is assigned.
		// [Learning Rate Based Branching Heuristic for SAT Solvers (SAT 2016)]

// 3.) deletion strategy:
		// read model checking book.
		// Deletion of low-activity conflict clauses.
		// Requires:
			// • Compute activity of clauses based on various measures. • Based on activity of variables in the clause
			// • Based on LBD: the # of decision levels in the conflict clause.
		// Activate deletion periodically.

// 4.) preprocessing
		// read sec 9.4.7 in model checking book.
		// Remove satisfied clauses at level 0
		// Non-increasing variable elimination.

// 5.) BCP order.
		// Smart heuristics for BCP order:
			// • e.g., Variables with higher activity score 
			// • BFS / DFS among variables
			// • According to the LBD information:
			// • if the learned clause is ‘bad’, re-run BCP with a different order.
			// • Perhaps: process according to the highest decision level within the clause.

// 5.) conf. clause shrinking (doubt?)
		
// 6.) seperate treatment of binary clauses (doubt?)

// 7.) Watchers with blocking clauses and possibly more literals (p. stucky's cache awarness paper)
	// [Cache Conscious Data Structures for Boolean Satisfiability Solvers]

// 8.) Resrtarts.
		// read model checking book.
// 9.) Learned clause minimization.
		// read model checking book 9.4.3.

// 10.) Lazy data structures.
		// read model checking book.	

//...............*** NOT REQUIRED ***.....................

// 1.) Learn more...
	// • In some applications (Bounded Model Checking, Planning) there is a lot of symmetry.
	// • Learn such clauses only if they are of high value 
		// • Compute activity
		// • LBD
		// • Attach short expiration date for them.
	// [Accelerating Bounded Model Checking of Safety Formulas. /Formal Methods in System Design]

// 2.) Extend to support pseudo-Boolean constraints
	// • Direct treatment of cardinality constraints.

// 3.)Test the value of incrementality
	// • Incremental solvers benefit from 
		//• Sharing conflict clauses
		// • Sharing heuristic information
	// • Depending on the increment, the heuristic information can perhaps be harmful. Can we find a test for when to activate it ?
	// • Steps:
		// • Take benchmarks from the incremental SAT competition
			// • Also,fabricateincrementalinstanceswithvaryinglevelsofchange.
		// • Add control to reset each heuristic info. Check effect.
		// • Measure change between instances, per variable.
			// • What happens if we reset the heuristic info of those variables that changed.

#include "edusat.h"

Solver S;



inline bool verbose_now() {
	return false;
}

void Abort(string s, int i) {
	cout << "Abort: ";
	switch (i) {
	case 1: cout << "(input error)" << endl; break;
	case 2: cout << "command line arguments error" << endl; break;
	case 3: break;
	default: cout << "(exit code " << i << ")" << endl; break;
	}
	cout << s << endl;
	//	S.print_scores(); 
	//	S.print_ordered_cnf();
	exit(i);
}


/******************  Reading the CNF ******************************/
#pragma region readCNF
void skipLine(ifstream& in) {
	for (;;) {
		//if (in.get() == EOF || in.get() == '\0') return;
		if (in.get() == '\n') { return; }
	}
}

static void skipWhitespace(ifstream& in, char&c) {
	c = in.get();
	while ((c >= 9 && c <= 13) || c == 32)
		c = in.get();
}

static int parseInt(ifstream& in, char &c) {
	int     val = 0;
	bool    neg = false;
	if (c == '-') neg = true, c = in.get();
	if (c < '0' || c > '9') cout << c, Abort("Unexpected char in input", 1);
	while (c >= '0' && c <= '9')
		val = val * 10 + (c - '0'),
		c = in.get();
	return neg ? -val : val;
}

void Solver::read_cnf(ifstream& in) {
	int i;
	unsigned int vars, clauses, unary = 0;
	set<Lit> s;
	Clause c;
	char d;

	while (in.peek() == 'c') skipLine(in);

	if (!match(in, "p cnf")) Abort("Expecting `p cnf' in the beginning of the input file", 1);
	in >> vars; // since vars is int, it reads int from the stream.
	in >> clauses;
	if (!vars || !clauses) Abort("Expecting non-zero variables and clauses", 1);
	cout << "vars: " << vars << " clauses: " << clauses << endl;
	cnf.reserve(clauses);

	set_nvars(vars);
	set_nclauses(clauses);
	initialize();

	while (in.good() && in.peek() != EOF) {
		skipWhitespace(in, d);
		if(in.peek() == EOF) break;
		i = parseInt(in, d);
		if (i == 0) {
			c.cl().resize(s.size());
			copy(s.begin(), s.end(), c.cl().begin());
			switch (c.size()) {
			case 0: {
				stringstream num;  // this allows to convert int to string
				num << cnf_size() + 1; // converting int to string.
				Abort("Empty clause not allowed in input formula (clause " + num.str() + ")", 1); // concatenating strings
			}
			case 1: {
				Lit l = c.cl()[0];
				assert_unary(l);
				BCP_stack.push_back(opposite(l));
				add_unary_clause(l);
				break; // unary clause. Note we do not add it as a clause. 
			}
			default: add_clause(c, 0, 1);
			}
			c.reset();
			s.clear();
			continue;
		}
		if (Abs(i) > vars) Abort("Literal index larger than declared on the first line", 1);
		if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(abs(i));
		i = v2l(i);		
		if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(i);
		s.insert(i);
	}
	last_clause_idx = max_original = cnf_size() - 1;
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators();
	cout << "Read " << cnf_size() << " clauses in " << cpuTime() - begin_time << " secs." << endl << "Solving..." << endl;
}

#pragma endregion readCNF

/******************  Solving ******************************/
#pragma region solving
void Solver::reset() { // invoked initially + every restart
	dl = 0;
	max_dl = assumptions_dl;
	conflicting_clause_idx = -1;	
	separators.push_back(0); // we want separators[1] to match dl=1. separators[0] is not used.
	conflicts_at_dl.push_back(0);
}


void Solver::reset_iterators(double activity_key/* = 0.0*/) {
	if (activity_key == 0.0)
		m_Score2Vars_r_it = m_Score2Vars.rbegin();
	else
	{
		m_Score2Vars_r_it = make_reverse_iterator(++m_Score2Vars.find(activity_key)); // the ++ is because reverse iterators are attached to the previous key...
	}
	m_VarsSameScore_it = m_Score2Vars_r_it->second.begin();
}

void Solver::initialize() {	
	
	state.resize(nvars + 1);
	prev_state.resize(nvars + 1, 0);
	antecedent.resize(nvars + 1, -1);	
	marked.resize(nvars+1);
	dlevel.resize(nvars+1);
	
	nlits = 2 * nvars;
	watches.resize(nlits + 1);
	LitScore.resize(nlits + 1);
	//initialize scores 	
	m_activity.resize(nvars + 1);	
	for (unsigned int v = 0; v <= nvars; ++v) {			
		m_activity[v] = 0;		
	}
	reset();
}


inline void Solver::assert_lit(Lit l) {
	trail.push_back(l);
	int var = l2v(l);
	if (Neg(l)) prev_state[var] = state[var] = -1; else prev_state[var] = state[var] = 1;
	dlevel[var] = dl;
	++num_assignments;
	if (verbose > 1) cout << "v" << var << "(lit " << l << "):" << static_cast<int>(state[var]) << "@" << dl << endl;
}

inline void Solver::assert_unary(Lit l) {		// the difference is that we do not push unaries to the trail, and also force dlevel = 0
	int var = l2v(l);
	if (Neg(l)) state[var] = -1; else state[var] = 1;
	dlevel[var] = 0;
	++num_assignments;
	if (verbose > 1) cout << "v" << var << "(lit " << l << "):" << static_cast<int>(state[var]) << "@" << 0 << endl;
}


void Solver::bumpVarScore(int var_idx) {
	//if (verbose_now()) cout << "bumpVarScore" << endl;
	double new_score;
	double score = m_activity[var_idx];	
	if (score > 0) {
		Assert(m_Score2Vars.find(score) != m_Score2Vars.end());
		m_Score2Vars[score].erase(var_idx);
		if (m_Score2Vars[score].size() == 0) m_Score2Vars.erase(score);
	}
	new_score = score + m_var_inc;
	m_activity[var_idx] = new_score;
	// Here add rescaling; requires rebuilding m_Score2Vars.
	if (m_Score2Vars.find(new_score) != m_Score2Vars.end())
		m_Score2Vars[new_score].insert(var_idx);
	else
		m_Score2Vars[new_score] = unordered_set<int>({ var_idx });
}

void Solver::bumpLitScore(int lit_idx) {
	LitScore[lit_idx]++;
}

void Solver::add_clause(Clause& c, int l, int r) {	
	Assert(c.size() > 1) ;
	c.lw_set(l);
	c.rw_set(r);
	int loc = static_cast<int>(cnf.size());  // the first is in location 0 in cnf
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::CMTF) {
		c.prev_set(loc - 1);  	
		if (!max_original && (loc - 1 >= 0)) { // only originals ('next' for num_learned clauses will be updated in cmtf_move_forward)
			cnf[loc - 1].next_set(loc);
		}	
	}
	int size = c.size();
	
	watches[c.lit(l)].push_back(loc); 
	watches[c.lit(r)].push_back(loc);
	cnf.push_back(c);
}

void Solver::add_unary_clause(Lit l) {		
	unaries.push_back(l);
}

int Solver :: getVal(Var v) {
	switch (ValDecHeuristic) {
	case VAL_DEC_HEURISTIC::PHASESAVING: {
		int saved_phase = prev_state[v];
		switch (saved_phase) {
		case -1: 
		case 0: return v2l(-v);
		case 1: return v2l(v);
		default: Assert(0);
		}
	}
	case VAL_DEC_HEURISTIC::LITSCORE:
	{
		int litp = v2l(v), litn = v2l(-v);
		int pScore = LitScore[litp], nScore = LitScore[litn];
		return pScore > nScore ? litp : litn;
	}
	default: Assert(0);
	}	
	return 0;
}

SolverState Solver::decide(){
	int max_score = 0;
	Var bestVar = 0;
	if (verbose_now()) cout << "decide" << endl;
	Lit best_lit = 0;
	if (dl < assumptions_dl) {
		for (vector<Lit>::iterator it = assumptions.begin() + dl; it < assumptions.end(); ++it) {
			switch (lit_state(*it)) {
			case LitState::L_UNSAT:
				out_ResponsibleAssumptions.push_back(*it); 
				analyze_final(*it);  
				return SolverState::UNSAT;
			case LitState::L_UNASSIGNED: best_lit = *it;
				goto Apply_decision;
			}
		}		
		assumptions_dl = dl; // we get here only when the rest of the assumptions are already determined by previous assumptions. 
	}
	
	

	switch (VarDecHeuristic) {
	case  VAR_DEC_HEURISTIC::CMTF:
		for (int it = last_clause_idx; !best_lit && it >= 0; it = cnf.at(it).get_prev()) {	// go over clauses 
			for (vector<Lit>::reverse_iterator it_c = cnf.at(it).cl().rbegin(); it_c != cnf.at(it).cl().rend(); ++it_c) { // go over literals in the clause								
				Var v = l2v(*it_c);
				LitState res = lit_state(*it_c, state[v]);
				if (res == LitState::L_SAT)  break; // clause is satisfied. Skip to next one.
				if (res == LitState::L_UNASSIGNED) { 
					best_lit = getVal(v);
					break;
				}
			}
		}
		break;
	case  VAR_DEC_HEURISTIC::MINISAT: {
		// m_Score2Vars_r_it and m_VarsSameScore_it are fields. 
		// When we get here they are the locaion where we need to start looking. 
		Var v = 0;
		int cnt = 0;
		bool first = true;
		while (!best_lit && m_Score2Vars_r_it != m_Score2Vars.rend()) { // scored from high to low
			if (first) first = false;
			else {
				++m_Score2Vars_r_it;
				if (m_Score2Vars_r_it == m_Score2Vars.rend()) break;
				m_VarsSameScore_it = m_Score2Vars_r_it->second.begin();
			}
			while (m_VarsSameScore_it != m_Score2Vars_r_it->second.end()) {
				v = *m_VarsSameScore_it;
				++m_VarsSameScore_it;
				++cnt;
				if (state[v] == 0) { // found a var to assign
					m_curr_activity = m_activity[v];
					best_lit = getVal(v);
					break;
				}
			}
		}
		break;
	}
	default: Assert(0);
	}	
	
	//cout << "decided on " << l2rl(best_lit) << endl;
	//print_state();
	
	if (!best_lit) { 		
		S.print_state(Assignment_file); 
		return SolverState::SAT;
	}

Apply_decision:
	dl++; // increase decision level
	if (dl > max_dl) {
		max_dl = dl;
		separators.push_back(trail.size());
		conflicts_at_dl.push_back(num_learned);
	}
	else {
		separators[dl] = trail.size();
		conflicts_at_dl[dl] = num_learned;
	}
	
	assert_lit(best_lit);	
	++num_decisions;
	BCP_stack.push_back(opposite(best_lit));
	if (verbose > 1) cout << "BCP_stack <- " << opposite(best_lit) << endl;
	return SolverState::UNDEF;
}

inline ClauseState Clause::next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc) {  // lit is the currently watched literal
	// if (verbose_now()) cout << "next_not_false" << endl;
	if (verbose > 1) {
		cout << "searching next-not-false in: "; print_with_watches();
		Lit lit = is_left_watch ? c[lw]: c[rw];
		cout << endl << "with literal " << lit << endl;
	}	
	
	if (!binary)
		for (vector<int>::iterator it = c.begin(); it != c.end(); ++it) {
			LitState LitState = S.lit_state(*it);
			if (LitState != LitState::L_UNSAT && *it != other_watch) { // found another watch_lit
				loc = distance(c.begin(), it);
				if (is_left_watch) lw = loc;    // if literal was the left one 
				else rw = loc;				
				return ClauseState::C_UNDEF;
			}
		}
	switch (S.lit_state(other_watch)) {
	case LitState::L_UNSAT: // conflict
		if (verbose > 1) { print(); cout << " is conflicting" << endl; }
		return ClauseState::C_UNSAT;
	case LitState::L_UNASSIGNED: return ClauseState::C_UNIT; // unit clause. Should assert the other watch_lit.	
	case LitState::L_SAT: return ClauseState::C_SAT; // other literal is satisfied. 
	default: Assert(0); return ClauseState::C_UNDEF; // just to supress warning. 
	}
}

void Solver::test() { // tests that each clause is watched twice. 	
	for (unsigned int idx = 0; idx < cnf.size(); ++idx) {
		Clause c = cnf[idx];
		bool found = false;
		for (int zo = 0; zo <= 1; ++zo) {
			for (vector<int>::iterator it = watches[c.cl()[zo]].begin(); !found && it != watches[c.cl()[zo]].end(); ++it) {				
				if (*it == idx) {
					found = true;
					break;
				}
			}
		}
		if (!found) {
			cout << "idx = " << idx << endl;
			c.print();
			cout << endl;
			cout << c.size();
		}
		Assert(found);
	}
}


SolverState Solver::BCP() {
	if (verbose_now()) cout << "BCP" << endl;
	while(!BCP_stack.empty()) {
		Lit lit = BCP_stack.back();		
		Assert(lit_state(lit) == LitState::L_UNSAT);
		if (verbose > 1) cout << "BCP_stack -> " << lit << endl;
		BCP_stack.pop_back();
		vector<int> new_watch_list; // The original watch list minus those clauses that changed a watch. The order is maintained. 
		int new_watch_list_idx = watches[lit].size() - 1; // Since we are traversing the watch_list backwards, this index goes down.
		new_watch_list.resize(watches[lit].size());
		for (vector<int>::reverse_iterator it = watches[lit].rbegin(); it != watches[lit].rend() && conflicting_clause_idx < 0; ++it) {
			Clause& c = cnf[*it];
			Lit l_watch = c.get_lw_lit(), 
				r_watch = c.get_rw_lit();			
			bool binary = c.size() == 2;
			bool is_left_watch = (l_watch == lit);
			Lit other_watch = is_left_watch? r_watch: l_watch;
			int NewWatchLocation;
			ClauseState res = c.next_not_false(is_left_watch, other_watch, binary, NewWatchLocation);
			if (res != ClauseState::C_UNDEF) new_watch_list[new_watch_list_idx--] = *it; //in all cases but the move-watch_lit case we leave watch_lit where it is
			switch (res) {
			case ClauseState::C_UNSAT: { // conflict				
				if (verbose > 1) print_state();
				if (dl == 0) return SolverState::UNSAT;
				if (dl <= assumptions_dl) {
					analyze_final(lit);
					return SolverState::UNSAT;
				}
				conflicting_clause_idx = *it;  // this will also break the loop
				BCP_stack.clear();
				 int dist = distance(it, watches[lit].rend()) - 1; // # of entries in watches[lit] that were not yet processed when we hit this conflict. 
				// Copying the remaining watched clauses:
				for (int i = dist - 1; i >= 0; i--) {
					new_watch_list[new_watch_list_idx--] = watches[lit][i];
				}
				break;
			}
			case ClauseState::C_SAT: break; // nothing to do when clause has a satisfied literal.
			case ClauseState::C_UNIT: { // new implication				
				if (verbose > 1) cout << "propagating: ";
				assert_lit(other_watch);
				BCP_stack.push_back(opposite(other_watch));
				antecedent[l2v(other_watch)] = *it;
				if (verbose > 1) cout << "BCP_stack <- " << opposite(other_watch) << endl;
				break;
			}
			default: // replacing watch_lit
				Assert(NewWatchLocation < static_cast<int>(c.size()));
				int new_lit = c.lit(NewWatchLocation);
				watches[new_lit].push_back(*it);
				if (verbose > 1) { c.print(); cout << "now watched by " << new_lit << endl;}				
			}
		}
		// resetting the list of clauses watched by this literal.
		watches[lit].clear();
		new_watch_list_idx++; // just because of the redundant '--' at the end. 		
		watches[lit].insert(watches[lit].begin(), new_watch_list.begin() + new_watch_list_idx, new_watch_list.end());

		//print_watches();
		if (conflicting_clause_idx >= 0) return SolverState::CONFLICT;
		new_watch_list.clear();
	}
	return SolverState::UNDEF;
}

// putting clause idx in the end
void Solver::cmtf_bring_forward(int idx) { 
	if (idx == last_clause_idx) return;	
	Clause& c = cnf.at(idx);
	cnf.at(last_clause_idx).next_set(idx);
	c.prev_set(last_clause_idx);
	c.next_set(cnf_size());
	last_clause_idx = idx;
}

// taking clause idx out of its current_clause location. Should be followed by cmtf_bring_forward 
void Solver::cmtf_extract(int idx) { 
	if (idx == last_clause_idx) return;	
	Clause& c = cnf.at(idx);
	unsigned int next = c.get_next();	
	Assert(next < cnf_size());
	int prev = c.get_prev();
	cnf.at(next).prev_set(prev);
	if (prev >=0) cnf.at(prev).next_set(next);
	//print_ordered_cnf();
	//	check_cyclicity();
}

/*******************************************************************************************************************
name: analyze
input:	1) conflicting clause
		2) dlevel
		3) marked
		
assumes: 1) no clause should have the same literal twice. To guarantee this we read through a set in read_cnf. 
            Wihtout this assumption it may loop forever because we may remove only one copy of the pivot.

This is Alg. 1 from "HaifaSat: a SAT solver based on an Abstraction/Refinement model" 
********************************************************************************************************************/

int Solver::analyze(const Clause conflicting) {
	if (verbose_now()) cout << "analyze" << endl;
	Clause	current_clause = conflicting, 
			new_clause;
	int resolve_num = 0,
		bktrk = 0, 
		watch_lit = 0, // points to what literal in the learnt clause should be watched, other than the asserting one
		antecedents_idx = 0, 
		cmtf_forward_counter = 0;

	Lit u;
	Var v;
	trail_t::reverse_iterator t_it = trail.rbegin();
	do {
		for (clause_it it = current_clause.cl().begin(); it != current_clause.cl().end(); ++it) {
			Lit lit = *it;
			v = l2v(lit);
			if (!marked[v]) {
				marked[v] = true;
				if (dlevel[v] == dl) ++resolve_num;
				else { // literals from previos decision levels (roots) are entered to the learned clause.
					new_clause.insert(lit);
					if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(v);
					if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(lit);
					int c_dl = dlevel[v];
					if (c_dl > bktrk) {
						bktrk = c_dl;
						watch_lit = new_clause.size() - 1;
					}
				}
			}
		}
		
		while (t_it != trail.rend()) {
			u = *t_it;
			v = l2v(u);
			++t_it;
			if (marked[v]) break;
		}
		marked[v] = false;
		--resolve_num;
		if(!resolve_num) continue; 
		int ant = antecedent[v];		
		current_clause = cnf[ant]; 
		current_clause.cl().erase(find(current_clause.cl().begin(), current_clause.cl().end(), u));
		if (VarDecHeuristic == VAR_DEC_HEURISTIC::CMTF && cmtf_forward_counter++ < Max_bring_forward) {
			cmtf_extract(ant); 
			cmtf_bring_forward(ant);
		}
	}	while (resolve_num > 0);
	for (clause_it it = new_clause.cl().begin(); it != new_clause.cl().end(); ++it) 
		marked[l2v(*it)] = false;
	Lit opp_u = opposite(u);
	new_clause.cl().push_back(opp_u);		
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_var_inc *= 1 / var_decay; // increasing importance of participating variables.
	++num_learned;
	asserted_lit = opp_u;
	if (new_clause.size() == 1) { // unary clause	
		BCP_stack.push_back(u); 
		add_unary_clause(opp_u);
		if (verbose > 1) cout << "BCP_stack <- " << u << endl;
	}
	else {
		BCP_stack.push_back(u); // this way after backtracking we will handle the new clause.
		add_clause(new_clause, watch_lit, new_clause.size() - 1);
		//cout << "added conflict" << endl;
		if (VarDecHeuristic == VAR_DEC_HEURISTIC::CMTF) cmtf_bring_forward(cnf_size()-1); // this takes care of the prev/next in cnf for new_clause.
		if (verbose > 1) cout << "BCP_stack <- " << new_clause.cl()[watch_lit] << endl;
	}
	

	if (verbose_now()) {	
		cout << "Learned clause #" << cnf_size() + unaries.size() << ". "; 
		new_clause.print(); 
		cout << endl;
		cout << " learnt clauses:  " << num_learned;				
		cout << " Backtracking to level " << bktrk << endl;
	}

	if (verbose >= 1 && !(num_learned % 1000)) {
		cout << "Learned: "<< num_learned <<" clauses" << endl;		
	}	
	return bktrk; 
}

void Solver::backtrack(int k) {
	if (verbose_now()) cout << "backtrack" << endl;
	if (k > 0 && (num_learned - conflicts_at_dl[k] > restart_threshold)) {	// "local restart"	
		restart(); 		
		return;
	}

	double jump_to_activity = m_curr_activity;
	for (trail_t::iterator it = trail.begin() + separators[k+1]; it != trail.end(); ++it) { // erasing from k+1
		Var v = l2v(*it);
		if (dlevel[v]) { // we need the condition because of learnt unary clauses. In that case we enforce an assignment with dlevel = 0.
			state[v] = 0;
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) jump_to_activity = max(jump_to_activity, m_activity[v]);
		}
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators(jump_to_activity);
	
	if (verbose > 1) print_state();
	trail.erase(trail.begin() + separators[k+1], trail.end());
	dl = k;
	if (k == 0) assert_unary(asserted_lit);
	else assert_lit(asserted_lit);
	antecedent[l2v(asserted_lit)] = cnf.size() - 1;
	conflicting_clause_idx = -1;
}

void Solver::validate_assignment() {
	for (vector<Clause>::iterator it = cnf.begin(); it != cnf.end(); ++it) {
		int found = 0;
		for(clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c) 
			if (lit_state(*it_c) == LitState::L_SAT) found = 1;
		if (!found) {
			cout << "fail on clause: "; 
			it->print();
			cout << endl;
			for (clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c)
				cout << *it_c << " (" << (int) lit_state(*it_c) << ") ";
			cout << endl;
			Abort("Assignment validation failed", 3);
		}
	}
	for (vector<Lit>::iterator it = unaries.begin(); it != unaries.end(); ++it) {
		if (lit_state(*it) != LitState::L_SAT) 
			Abort("Assignment validation failed (unaries)", 3);
	}
	cout << "Assignment validated" << endl;
}

void Solver::restart() {	
	if (verbose >= 1) cout << "restart" << endl;
	restart_threshold = static_cast<int>(restart_threshold * restart_multiplier);
	if (restart_threshold > restart_upper) {
		restart_threshold = restart_lower;
		restart_upper = static_cast<int>(restart_upper  * restart_multiplier);
	}
	if (verbose >=1) cout << "restart: new threshold = " << restart_threshold <<", upper = " << restart_upper << endl;
	++num_restarts;
	for (unsigned int i = 0; i <= nvars; ++i) 
		if (dlevel[i] > 0) {
			state[i] = 0; 
			dlevel[i] = 0;
		}	
	BCP_stack.clear();
	trail.clear();
	separators.clear(); // resize(assumptions_dl); we can resize, but in reset we push(0) as if it is level 0.
	conflicts_at_dl.clear(); //  resize(assumptions_dl);
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators();
	reset();
}

void Solver::analyze_final(Lit p) {
	vector<bool> seen;
	if (verbose >= 1) cout << "analyze_final" << endl;
	seen.resize(nvars + 1);
	if (dl > 0) {
		seen[l2v(p)] = true;
		for (int i = trail.size() - 1; i >= separators[1]; i--) {
			Var x = l2v(trail[i]);
			if (seen[x]) {
				if (antecedent[x] == -1) {
					out_ResponsibleAssumptions.push_back(trail[i]);
				}
				else {
					Clause& c = cnf[antecedent[x]];
					for (unsigned int j = 0; j < c.size(); j++)
						if ((dlevel[l2v(c.cl()[j])]) > 0)
						{
							seen[l2v(c.cl()[j])] = true;
						}
				}
			}
		}
	}
	cout << "Assumptions causing the conflict: ";
	for (auto l : out_ResponsibleAssumptions) cout << l2rl(l) << " ";
}

SolverState Solver::solve() { // wrapper for incremental SAT. 
	out_ResponsibleAssumptions.clear();
	SolverState res = _solve(); 	
	Assert(res == SolverState::SAT || res == SolverState::UNSAT);
	S.print_stats();
	if (res == SolverState::SAT) {
		S.validate_assignment();
		string str = "solution in ",
			str1 = Assignment_file;
		cout << str + str1 << endl;
		cout << "SAT" << endl;
	}	
	else cout << "UNSAT" << endl;	
	restart();
	return res;
}

SolverState Solver::_solve() {
	SolverState res;
	while (true) {		
		while (true) {
			res = BCP();
			if (res == SolverState::UNSAT) return res;
			if (res == SolverState::CONFLICT)
				backtrack(analyze(cnf[conflicting_clause_idx]));
			else break;
		}
		res = decide();
		if (res == SolverState::SAT || res == SolverState::UNSAT) return res;
	}
}

#pragma endregion solving

void help() {
	stringstream st;
	st << "\nUsage: edusat <options> <file name>\n \n"
		"Options:\n"
		"-vardh <#>\t {0: minisat, 1: clause-move-to-front}. Default = " << ((int)VarDecHeuristic) << "\n" <<
		"-valdh <#>\t {0: phase-saving, 1: literal-score}. Default = " << (int)ValDecHeuristic << "\n" <<
		"-v <#>\t\t verbosity level\n"
		"-h\t\t get this help message\n";
	Abort(st.str(), 3);
}

void parse_options(int argc, char** argv) {
	if (argc < 2 || string(argv[1]).compare("-h") == 0)
		help();
	for (int i = 1; i < argc - 1; ++i) {
		Assert(argv[i][0] == '-');
		string st = argv[i] + 1;
		if (st.compare("vardh") == 0) {
			if (i == argc - 2) Abort("missing value after -vardh", 2);
			i++;
			VarDecHeuristic = (VAR_DEC_HEURISTIC)stoi(argv[i]);
			//assert(VarDecHeuristic >= 0 && VarDecHeuristic < 2);
			continue;
		}
		if (st.compare("valdh") == 0) {
			if (i == argc - 2) Abort("missing value after -valdh", 2);
			i++;
			ValDecHeuristic = (VAL_DEC_HEURISTIC)stoi(argv[i]);
			//assert(ValDecHeuristic  >=0 && ValDecHeuristic < 2);
			continue;
		}
		if (st.compare("v") == 0) { 
			if (i == argc - 2) Abort("missing value after -v", 2);  
			i++;
			verbose = stoi(argv[i]);
			continue;
		}
		cout << st << endl;
		Abort("Unknown flag ", 2);
	}
	cout << argv[argc - 1] << endl;
}

#pragma region assumptions
void Solver::set_assumptions(vector<Lit> assump) {
	assumptions.clear();
	for (auto l : assump) {
		Assert(v2l(l) <= nvars);
		assumptions.push_back(v2l(l));
	}
	assumptions_dl = assumptions.size();
}
// Example: how to use assumptions
void SolveWithAssumptions(Solver S) {
	vector<Lit> assumptions{ 1, 2, 3, 4 };
	SolverState res;
	vector<Lit> ResponsibleAssump = assumptions;
	S.set_assumptions(assumptions);
	res = S.solve();
	if (res == SolverState::UNSAT) {
		ResponsibleAssump = S.get_ResponsibleAssumptions();
	}
	ResponsibleAssump.pop_back(); // remove one reason and try again: 
	S.set_assumptions(ResponsibleAssump);
	S.solve();
}

#pragma endregion assumptions
/******************  main ******************************/

int main(int argc, char** argv){
	begin_time = cpuTime();
	parse_options(argc, argv);
	
	ifstream in (argv[argc - 1]);
	if (!in.good()) Abort("cannot read input file", 1);	
	S.read_cnf(in);		
	in.close();
	// SolveWithAssumptions(S); 
	S.solve();	

	return 0;
}
