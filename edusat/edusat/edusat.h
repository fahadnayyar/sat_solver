// doubt
#pragma once
#include <iostream>
#include <algorithm>
#include <iterator>
#include <vector>
#include <unordered_set>
#include <map>
#include <set>
#include <string>
#include <sstream>  // stringstream allows converting ints and floats into strings. 
#include <fstream>
#include <cassert>
#include <ctime>

using namespace std;

typedef int Var;
typedef int Lit;
typedef vector<Lit> clause_t;
typedef clause_t::iterator clause_it;
// doubt
typedef vector<Lit> trail_t;

#define Assert(exp) AssertCheck(exp, __func__, __LINE__)

//doubt
#define Neg(l) (l & 1)
//doubt
#define Restart_multiplier 1.1f
//doubt
#define Restart_lower 100
//doubt
#define Restart_upper 1000
//doubt
#define Max_bring_forward 10
//doubt
#define var_decay 0.95;
//doubt
#define Assignment_file "assignment.txt"

// doubt
int verbose = 0;
double begin_time;

// doubt
enum class VAR_DEC_HEURISTIC {
	MINISAT, 
	/* Each time a clause is learned, we push to the end of the list the learned clause + some clauses 
	that participated in its learning. Traversing these clauses from the end, if a clause has at least 
	one unassigned literal we give it a value according to the value heuristic.
	Looking at only unresolved clauses makes the search better but more expensive to decide, and overall worse. */
	CMTF,
	LRATE } ;

VAR_DEC_HEURISTIC VarDecHeuristic = VAR_DEC_HEURISTIC::MINISAT;

// doubt
enum class VAL_DEC_HEURISTIC {
	/* Same as last value. When no previous value then false*/
	PHASESAVING, 
	/* Choose literal with highest frequency */
	LITSCORE 
} ;

VAL_DEC_HEURISTIC ValDecHeuristic = VAL_DEC_HEURISTIC::PHASESAVING;

enum class ClauseState {
	C_UNSAT,
	C_SAT,
	C_UNIT,
	C_UNDEF
};

enum class LitState {
	L_UNSAT,
	L_SAT,
	L_UNASSIGNED
};

enum class SolverState{
	UNSAT,
	SAT,
	CONFLICT, 
	UNDEF
} ;
/***************** service functions **********************/

// doubt
#ifdef _MSC_VER
	#include <ctime>

	static inline double cpuTime(void) {
	    return (double)clock() / CLOCKS_PER_SEC; }
#else

	#include <sys/time.h>
	#include <sys/resource.h>
	#include <unistd.h>

	static inline double cpuTime(void) {
	    struct rusage ru;
	    getrusage(RUSAGE_SELF, &ru);
	    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }
#endif

// For production wrap with #ifdef _DEBUG
void AssertCheck(bool cond, string func_name, int line, string msg = "") {
	if (cond) return;
	cout << "Assertion fail" << endl;
	cout << msg << endl;
	cout << func_name << " line " << line << endl;
	exit(1);
}

// doubt & in argument and return type.
bool match(ifstream& in, char* str) {
    for (; *str != '\0'; ++str)
        if (*str != in.get())
            return false;
    return true;
}

unsigned int Abs(int x) { // because the result is compared to an unsigned int. unsigned int are introduced by size() functions, that return size_t, which is defined to be unsigned. 
	if (x < 0) return (unsigned int)-x;
	else return (unsigned int)x;
}

unsigned int v2l(int i) { // maps a literal as it appears in the cnf to literal
	if (i < 0) return ((-i) << 1) - 1; 
	else return i << 1;
} 

Var l2v(Lit l) {
	return (l+1) / 2;	
} 

Lit opposite(Lit l) {
	if Neg(l) return l + 1;  // odd
	return l - 1;		
}

char sign(Lit l) {
	if Neg(l) return -1;
	return 1;		
}

int l2rl(int l) {
	return Neg(l)? -((l + 1) / 2) : l / 2;
}


/********** classes ******/ 

class Clause {
	clause_t c;
	int lw,rw; //watches;
	int prev, next; // indices in cnf of the prev and next clause according to the current order (the order changes in cmtf). 
public:	
	Clause(){};
	void insert(int i) {c.push_back(i);}
	void lw_set(int i) {lw = i; /*assert(lw != rw);*/}
	void rw_set(int i) {rw = i; /*assert(lw != rw);*/}
	void prev_set(int i) {prev = i;}
	void next_set(int i) {next = i;}
	clause_t& cl() {return c;}
	int get_lw() {return lw;}
	int get_rw() {return rw;}
	int get_lw_lit() {return c[lw];}
	int get_rw_lit() {return c[rw];}
	int get_prev() {return prev;}
	int get_next() {return next;}
	int  lit(int i) {return c[i];} 		
	// doubt
	inline ClauseState next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc); 
	size_t size() {return c.size();}
	void reset() { c.clear(); }	
	void print() {for (clause_it it = c.begin(); it != c.end(); ++it) {cout << *it << " ";}; }
	void print_real_lits() {
		Lit l; 
		cout << "("; 
		for (clause_it it = c.begin(); it != c.end(); ++it) { 
			l = l2rl(*it); 
			cout << l << " ";} cout << ")"; 
	}
	void print_with_watches() {
		//if (verbose < 2) return;
		for (clause_it it = c.begin(); it != c.end(); ++it) {
			cout << *it;
			// doubt
			int j = distance(c.begin(), it); //also could write "int j = i - c.begin();"  : the '-' operator is overloaded to allow such things. but distance is more standard, as it works on all standard containers.
			if (j == lw) cout << "L";
			if (j == rw) cout << "R";
			cout << " ";
		};
	}
};

class Solver {
	vector<Clause> cnf; // clause DB. 
	// doubt
	vector<int> unaries; 
	// doubt
	trail_t trail;  // assignment stack	
	// doubt
	vector<int> separators; // indices into trail showing increase in dl 	
	// doubt
	vector<int> LitScore; // literal => frequency of this literal (# appearances in all clauses). 
	// doubt
	vector<vector<int> > watches;  // Lit => vector of clause indices into CNF
	// doubt
	vector<char> state;  // -1 = false, 0 = unassigned, 1 = true. 
	// doubt
	vector<char> prev_state; // for phase-saving: same as state, only that it is not reset to 0 upon backtracking. 
	// doubt9
	vector<int> BCP_stack; // vector of assserted literals. 
	// doubt
	vector<int> antecedent; // var => clause index in the cnf vector. For variables that their value was assigned in BCP, this is the clause that gave this variable its value. 
	// doubt
	vector<bool> marked;	// var => seen during analyze()
	// doubt
	vector<int> dlevel; // var => decision level in which this variable was assigned its value. 
	// doubt
	vector<int> conflicts_at_dl; // decision level => # of conflicts under it. Used for local restarts. 
	// doubt
	vector<Lit> assumptions;

	// Used by VAR_DH_MINISAT:
	// doubt
	map<double, unordered_set<int>> m_Score2Vars; // From a score to the set of variables that have it. 
	// doubt
	map<double, unordered_set<int>>::reverse_iterator m_Score2Vars_r_it;
	// doubt
	unordered_set<int>::iterator m_VarsSameScore_it;
	// doubt
	vector<double>	m_activity; // Var -> activity
	// doubt
	double			m_var_inc;	
	// doubt
	double			m_curr_activity;
	
	//Used by VAR_DH_LRATE:
	double alpha;
	int learning_counter;
	vector<int> assigned;
	vector<int> participated;
	vector<double> ema;

	unsigned int 
		nvars,			// # vars
		nclauses, 		// # clauses
		nlits,			// # literals = 2*nvars		
		// doubt
		max_original;
	int
		// doubt
		num_learned, 	
		// doubt
		num_decisions,
		// doubt
		num_assignments,
		// doubt
		num_restarts,
		dl,				// decision level
		max_dl,			// max dl seen so far
		// doubt
		assumptions_dl,	// == |assumptions cast as decisions | <= |assumptions|. Monotonically decreases. 
		conflicting_clause_idx, // holds the index of the current conflicting clause in cnf[]. -1 if none.				
		// doubt
		last_clause_idx, // location in cnf of the most recent clause (it is not necessarily the last in the array because of the CMTF heuristic)
		// doubt
		restart_threshold,
		// doubt
		restart_lower,
		// doubt
		restart_upper;

		// doubt
	Lit asserted_lit;
	
	// doubt
	float restart_multiplier;

	// doubt
	vector<Lit> out_ResponsibleAssumptions;

	// access	
	int get_learned() { return num_learned; }
	void set_nvars(int x) { nvars = x; }
	int get_nvars() { return nvars; }
	void set_nclauses(int x) { nclauses = x; }
	size_t cnf_size() { return cnf.size(); }
	char get_state(int x) { return state[x]; }

	// misc.
	void add_to_trail(int x) { trail.push_back(x); }

	// doubt
	void reset(); // initialization that is invoked initially + every restart
	// doubt
	void initialize();
	// doubt
	void reset_iterators(double activity_key = 0.0);
	
	// used by CMTF
	// doubt
	void cmtf_extract(int idx);
	// doubt
	void cmtf_bring_forward(int idx);  // putting clause idx in the end

	// solving	
	SolverState decide();
	// doubt
	void test();
	SolverState BCP();
	// doubt
	int  analyze(const Clause);
	// doubt
	inline int  getVal(Var v);
	// doubt
	inline void add_clause(Clause& c, int l, int r);
	// doubt
	inline void add_unary_clause(Lit l);
	// doubt
	inline void assert_lit(Lit l);
	// doubt
	inline void assert_unary(Lit l);
	// doubt
	inline void backtrack(int k);
	// doubt
	void analyze_final(Lit p);
	// doubt
	void restart();
	
	// scores	
	// doubt
	inline void bumpVarScore(int idx);
	// doubt
	inline void bumpLitScore(int lit_idx);

	//rate
	void AfterConflictAnalysis(set<Var> ConflictSideAndClause);
	void OnAssign(int idx);
	void OnUnAssign(int idx);

public:
	// doubt
	Solver(): 
		nvars(0), nclauses(0), num_learned(0), num_decisions(0), num_assignments(0), 
		num_restarts(0), m_var_inc(1.0), max_original(0), assumptions_dl(0),
		restart_threshold(Restart_lower), restart_lower(Restart_lower), 
		restart_upper(Restart_upper), restart_multiplier(Restart_multiplier)	 {};
	
	// service functions
	inline LitState lit_state(Lit l) {
		char var_state = state[l2v(l)];
		return var_state == 0 ? LitState::L_UNASSIGNED : (Neg(l) && var_state == -1 || !Neg(l) && var_state == 1) ? LitState::L_SAT : LitState::L_UNSAT;
	}
	inline LitState lit_state(Lit l, char var_state) {
		return var_state == 0 ? LitState::L_UNASSIGNED : (Neg(l) && var_state == -1 || !Neg(l) && var_state == 1) ? LitState::L_SAT : LitState::L_UNSAT;
	}
	void read_cnf(ifstream& in);
	void set_assumptions(vector<Lit> assump);
		
	vector<Lit> get_ResponsibleAssumptions() { return out_ResponsibleAssumptions; }

	SolverState _solve();
	SolverState solve();

	
	
	
// debugging
	void print_cnf(){
		if (verbose < 2) return; 
		for(vector<Clause>::iterator i = cnf.begin(); i != cnf.end(); ++i) {
			i -> print_with_watches(); 
			cout << endl;
		}
	} 

	void print_ordered_cnf() {
		if (verbose < 2) return;
		cout << "ordered cnf, reverse order: " << endl;
		for (int i = last_clause_idx; i >= 0; i = cnf[i].get_prev())
			cnf[i].print_real_lits();
		cout << endl;
	};

	void print_real_cnf() {
		if (verbose < 2) return; 
		for(vector<Clause>::iterator i = cnf.begin(); i != cnf.end(); ++i) {
			i -> print_real_lits(); 
			cout << endl;
		}
	} 

	void print_state(const char *file_name) {
		ofstream out;
		out.open(file_name);		
		out << "State: "; 
		for (vector<char>::iterator it = state.begin() + 1; it != state.end(); ++it) 
			out << (*it) * (it - state.begin()) << " "; out << endl;
	}	

	void print_state() {
		cout << "State: "; 
		for (vector<char>::iterator it = state.begin() + 1; it != state.end(); ++it) 
			cout << (*it) * (it - state.begin()) << " "; cout << endl;
	}	
	
	void print_watches() {
		if (verbose < 2) return;
		for (vector<vector<int> >::iterator it = watches.begin() + 1; it != watches.end(); ++it) {
			cout << distance(watches.begin(), it) << ": ";
			for (vector<int>::iterator it_c = (*it).begin(); it_c != (*it).end(); ++it_c) {
				cnf[*it_c].print();
				cout << "; ";
			}
			cout << endl;
		}
	};


	void print_stats() {cout << endl << "Statistics: " << endl << "===================" << endl << 
		"### Restarts:\t\t" << num_restarts << endl <<
		"### Learned-clauses:\t" << num_learned << endl <<
		"### Decisions:\t\t" << num_decisions << endl <<
		"### Implications:\t" << num_assignments - num_decisions << endl <<
		"### Time:\t\t" << cpuTime() - begin_time << endl;
	}
	
	void validate_assignment();
};


