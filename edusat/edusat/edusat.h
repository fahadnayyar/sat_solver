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
typedef vector<Lit> trail_t;
vector<int> lbds;
vector<int> sizes;

#define Assert(exp) AssertCheck(exp, __func__, __LINE__)

#define Neg(l) (l & 1)
#define Restart_multiplier 1.1f
#define Restart_lower 100
#define Restart_upper 1000
#define Max_bring_forward 10
#define var_decay 0.95;
#define Assignment_file "assignment.txt"

#define RATIOREMOVECLAUSES 2
int verbose = 0;
double begin_time;
double sort_time = 0; // lbd
double reducedb_time = 0; // lbd

double lrate_time=0; // lrate
int is_queue=0; // lrate
int is_lbd_restart=0;
double queue_time=0; // lrate

enum class VAR_DEC_HEURISTIC {
	MINISAT, 
	/* Each time a clause is learned, we push to the end of the list the learned clause + some clauses 
	that participated in its learning. Traversing these clauses from the end, if a clause has at least 
	one unassigned literal we give it a value according to the value heuristic.
	Looking at only unresolved clauses makes the search better but more expensive to decide, and overall worse. */
	CMTF,
	LRATE 
} ;

VAR_DEC_HEURISTIC VarDecHeuristic = VAR_DEC_HEURISTIC::MINISAT;

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
template<class T>
class vec {
    T*  data;
    int sz;
    int cap;

    // Don't allow copying (error prone):
    vec<T>&  operator = (vec<T>& other) { assert(0); return *this; }
             vec        (vec<T>& other) { assert(0); }
             
    // Helpers for calculating next capacity:
    static inline int  imax   (int x, int y) { int mask = (y-x) >> (sizeof(int)*8-1); return (x&mask) + (y&(~mask)); }
    //static inline void nextCap(int& cap){ cap += ((cap >> 1) + 2) & ~1; }
    static inline void nextCap(int& cap){ cap += ((cap >> 1) + 2) & ~1; }

public:
    // Constructors:
    vec()                       : data(NULL) , sz(0)   , cap(0)    { }
    explicit vec(int size)      : data(NULL) , sz(0)   , cap(0)    { growTo(size); }
    vec(int size, const T& pad) : data(NULL) , sz(0)   , cap(0)    { growTo(size, pad); }
   ~vec()                                                          { clear(true); }

    // Pointer to first element:
    operator T*       (void)           { return data; }

    // Size operations:
    int      size     (void) const     { return sz; }
    void     shrink   (int nelems)     { assert(nelems <= sz); for (int i = 0; i < nelems; i++) sz--, data[sz].~T(); }
    void     shrink_  (int nelems)     { assert(nelems <= sz); sz -= nelems; }
    int      capacity (void) const     { return cap; }
    void     capacity (int min_cap);
    void     growTo   (int size);
    void     growTo   (int size, const T& pad);
    void     clear    (bool dealloc = false);

    // Stack interface:
    void     push  (void)              { if (sz == cap) capacity(sz+1); new (&data[sz]) T(); sz++; }
    void     push  (const T& elem)     { if (sz == cap) capacity(sz+1); data[sz++] = elem; }
    void     push_ (const T& elem)     { assert(sz < cap); data[sz++] = elem; }
    void     pop   (void)              { assert(sz > 0); sz--, data[sz].~T(); }
    // NOTE: it seems possible that overflow can happen in the 'sz+1' expression of 'push()', but
    // in fact it can not since it requires that 'cap' is equal to INT_MAX. This in turn can not
    // happen given the way capacities are calculated (below). Essentially, all capacities are
    // even, but INT_MAX is odd.

    const T& last  (void) const        { return data[sz-1]; }
    T&       last  (void)              { return data[sz-1]; }

    // Vector interface:
    const T& operator [] (int index) const { return data[index]; }
    T&       operator [] (int index)       { return data[index]; }

    // Duplicatation (preferred instead):
    void copyTo(vec<T>& copy) const { copy.clear(); copy.growTo(sz); for (int i = 0; i < sz; i++) copy[i] = data[i]; }
    void moveTo(vec<T>& dest) { dest.clear(true); dest.data = data; dest.sz = sz; dest.cap = cap; data = NULL; sz = 0; cap = 0; }
};


template<class T>
void vec<T>::capacity(int min_cap) {
    if (cap >= min_cap) return;
    int add = imax((min_cap - cap + 1) & ~1, ((cap >> 1) + 2) & ~1);   // NOTE: grow by approximately 3/2
    if (add > __INT_MAX__ - cap || ((data = (T*)::realloc(data, (cap += add) * sizeof(T))) == NULL) && errno == ENOMEM)
	{
		printf("katt gaya!");
		exit(0);
	}
 }


template<class T>
void vec<T>::growTo(int size, const T& pad) {
    if (sz >= size) return;
    capacity(size);
    for (int i = sz; i < size; i++) data[i] = pad;
    sz = size; }


template<class T>
void vec<T>::growTo(int size) {
    if (sz >= size) return;
    capacity(size);
    for (int i = sz; i < size; i++) new (&data[i]) T();
    sz = size; }


template<class T>
void vec<T>::clear(bool dealloc) {
    if (data != NULL){
        for (int i = 0; i < sz; i++) data[i].~T();
        sz = 0;
        if (dealloc) free(data), data = NULL, cap = 0; } }


template <class T>
class bqueue {
    vec<T>  elems;
    int     first;
	int		last;
	unsigned long long sumofqueue;
	int     maxsize;
	int     queuesize; // Number of current elements (must be < maxsize !)
	bool expComputed;
	double exp,value;
public:
 bqueue(void) : first(0), last(0), sumofqueue(0), maxsize(0), queuesize(0),expComputed(false) { } 
	
	void initSize(int size) {growTo(size);exp = 2.0/(size+1);} // Init size of bounded size queue
	
	void push(T x) {
	  expComputed = false;
		if (queuesize==maxsize) {
			assert(last==first); // The queue is full, next value to enter will replace oldest one
			sumofqueue -= elems[last];
			if ((++last) == maxsize) last = 0;
		} else 
			queuesize++;
		sumofqueue += x;
		elems[first] = x;
		if ((++first) == maxsize) {first = 0;last = 0;}
	}

	T peek() { assert(queuesize>0); return elems[last]; }
	void pop() {sumofqueue-=elems[last]; queuesize--; if ((++last) == maxsize) last = 0;}
	
	unsigned long long getsum() const {return sumofqueue;}
	unsigned int getavg() const {return (unsigned int)(sumofqueue/((unsigned long long)queuesize));}
	int maxSize() const {return maxsize;}
	double getavgDouble() const {
	  double tmp = 0;
	  for(int i=0;i<elems.size();i++) {
	    tmp+=elems[i];
	  }
	  return tmp/elems.size();
	}
	int isvalid() const {return (queuesize==maxsize);}
	
	void growTo(int size) {
		elems.growTo(size); 
		first=0; maxsize=size; queuesize = 0;last = 0;
		for(int i=0;i<size;i++) elems[i]=0; 
	}
	
	double getAvgExp() {
	  if(expComputed) return value;
	  double a=exp;
	  value = elems[first];
	  for(int i  = first;i<maxsize;i++) {
	    value+=a*((double)elems[i]);
	    a=a*exp;
	  }
	  for(int i  = 0;i<last;i++) {
	    value+=a*((double)elems[i]);
	    a=a*exp;
	  }
	  value = value*(1-exp)/(1-a);
	  expComputed = true;
	  return value;
	  

	}
	void fastclear() {first = 0; last = 0; queuesize=0; sumofqueue=0;} // to be called after restarts... Discard the queue
	
    int  size(void)    { return queuesize; }

    void clear(bool dealloc = false)   { elems.clear(dealloc); first = 0; maxsize=0; queuesize=0;sumofqueue=0;}


};



class ExpoAverage{
public:
	int var;
	double average;
	double priority;
	ExpoAverage()
	{
		var = 0;
		average = 0;
		priority = 0;
	};
	bool isGreaterThan(ExpoAverage * e){
		if(e->priority < priority)
			return true;
		else if(e->priority == priority)
		{
			return var < e->var;	
		}
		return false;
	}
};

class Heap 
{ 
    int capacity; // maximum possible size of min heap 
	int heap_size;
public: 
	vector<int> index;
    vector<ExpoAverage> harr; // pointer to array of elements in heap 	
	void initialize(int capacity)
	{
		this->capacity = capacity; // doubt
		harr = vector<ExpoAverage>(capacity);
		index = vector<int>(capacity);
		heap_size = capacity; // doubt
		for (int i = 0; i < capacity; i++)
		{
			harr[i].var = i;
			harr[i].average = 0;
			harr[i].priority = 0; // doubt
			index[i] = i;
		}
		// harr[0].priority = -1;
		update(0,-2);
		// cout << "In Heap at index 0: " << harr[index[0]].var << endl;
		// cout << "In Heap" << harr[0].var << endl;
	};
	void Heapify(int i)
	{
		int l = left(i); 
		int r = right(i); 
		int largest = i; 
		if (l < heap_size && /* harr[l].priority > harr[i].priority && */ harr[l].isGreaterThan(&harr[i])) 
			largest = l; 
		if (r < heap_size &&/*  harr[r].priority > harr[largest].priority */ harr[r].isGreaterThan(&harr[largest])) 
			largest = r; 
		if (largest != i) 
		{ 
			index[harr[i].var] = largest;
			index[harr[largest].var] = i;
			ExpoAverage temp = harr[i];
			harr[i] = harr[largest];
			harr[largest] = temp;
			// cout << "In Heap at index : " << harr[i].var << " " << harr[index[harr[i].var]].var << endl;
			// cout << "In Heap at index : " << harr[largest].var << " " << harr[index[harr[largest].var]].var << endl;
			// swap(&harr[i], &harr[largest]); 
			Heapify(largest); 
		} 
	}
	void update(int i, double val)
	{
		// cout << harr[i].var << " " << harr[i].priority << val << endl;
		if(val < harr[i].priority)
		{
			// cout << "Here" << endl;
			harr[i].priority = val; 
			Heapify(i);
			return;
		}
		harr[i].priority = val; 
		while (i != 0 && /* harr[parent(i)].priority < harr[i].priority */ harr[i].isGreaterThan(&harr[parent(i)])) 
		{ 
			index[harr[i].var] = parent(i);
			index[harr[parent(i)].var] = i;
			ExpoAverage temp = harr[i];
			harr[i] = harr[parent(i)];
			harr[parent(i)] = temp;
			// swap(&harr[i], &harr[parent(i)]); 
			i = parent(i); 
		} 
	}
	int parent(int i) { return (i-1)/2; } 
	int left(int i) { return (2*i + 1); } 
	int right(int i) { return (2*i + 2); } 
	ExpoAverage *  getMax() { return &harr[0]; } 
	void print_heap()
	{
		for (int i = 0; i < capacity; i++)
		{
			int ind = index[i];
			ExpoAverage temp = harr[i];
			cout << "Var : " << temp.var << "Priority : " << temp.priority << endl;
		}

	}
};


class Clause {
	clause_t c;
	int lw,rw; //watches;
	int prev, next; // indices in cnf of the prev and next clause according to the current order (the order changes in cmtf). 
	
	bool locked; // lbd
	int lbd = 1000000; // lbd
	int activity; // lbd
	int canbedel = true; // lbd
	// bool deleted = false; // lbd
	int index;  // lbd

public:	
	Clause(){};
	void insert(int i) {c.push_back(i);}
	void lw_set(int i) {lw = i; /*assert(lw != rw);*/}
	void rw_set(int i) {rw = i; /*assert(lw != rw);*/}
	void prev_set(int i) {prev = i;}
	void next_set(int i) {next = i;}
	clause_t& cl() {return c;}
	int clause_size () { return c.size(); } // lrate
	Lit Lit_at_index(int i) { return c[i]; } // lrate	
	int get_lw() {return lw;}
	int get_rw() {return rw;}
	int get_lw_lit() {return c[lw];}
	int get_rw_lit() {return c[rw];}
	int get_prev() {return prev;}
	int get_next() {return next;}
	int  lit(int i) {return c[i];} 		
	inline ClauseState next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc); 
	size_t size() {return c.size();}
	void set_index(int i) { index =i; }
	int get_index(){ return index;}

	void set_locked(bool lock)  { locked = lock; }  // lbd
	bool get_locked() { return locked; } // lbd
	void set_lbd(int lbdd)  { lbd = lbdd; }  // lbd
	int get_lbd() { return lbd; } // lbd
	int get_activity() { return activity; } // lbd
	// bool get_deleted() { return deleted; } // lbd
	// void set_deleted(bool deletedd) { deleted = deletedd; } // lbd

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
			int j = distance(c.begin(), it); //also could write "int j = i - c.begin();"  : the '-' operator is overloaded to allow such things. but distance is more standard, as it works on all standard containers.
			if (j == lw) cout << "L";
			if (j == rw) cout << "R";
			cout << " ";
		};
	}
	bool canBeDel(){ // lbd
		return canbedel;
	}
	void setCanBeDel(bool cbd) { canbedel=cbd; } // lbd
	clause_t get_clause(){return c ;}
	bool operator < (Clause c1) {	
		// binary clauses should always be rightmost in sorted order.
		// clauses with size>2 are bad (in comparision to clauses with size==2).
		if (size()>2 && c1.size()==2) 
			return true;
		if (c1.size()>2 && size()==2)
			return false;
		if (size()==2 && c1.size()==2)
			return false;

		// smaller lbd should be on right in sorted order.
		// clauses with larger are bad.
		if (get_lbd() > c1.get_lbd())
			return true;	
		if (get_lbd() < c1.get_lbd())
			return false;

		// smaller size should be left in sorted ordert. 
		// clauses with smaller size are bad.
		if ( size() < c1.size() )
			return true;
		if ( size() > c1.size() )
			return false;

		// smaller activity should be left in sorted ordert. 
		// clauses with smaller activity are bad.
		// if ( get_activity() < c1.get_activity() )
		// 	return true;
		// if ( get_activity() > c1.get_activity() )
		// 	return false;
		return false;
	}
};

class Solver {
	
	bqueue<unsigned int> trailQueue,lbdQueue; // lbd restart.
	double sumLBD = 0; // lbd restart.
	uint64_t conflictsRestarts = 0; // lbd restart.

	vector<Clause> cnf; // clause DB. 
	vector<int> unaries; 
	trail_t trail;  // assignment stack	
	vector<int> separators; // indices into trail showing increase in dl 	
	vector<int> LitScore; // literal => frequency of this literal (# appearances in all clauses). 
	vector<vector<int> > watches;  // Lit => vector of clause indices into CNF
	vector<char> state;  // -1 = false, 0 = unassigned, 1 = true. 
	vector<char> prev_state; // for phase-saving: same as state, only that it is not reset to 0 upon backtracking. 
	vector<int> BCP_stack; // vector of assserted literals. 
	vector<int> antecedent; // var => clause index in the cnf vector. For variables that their value was assigned in BCP, this is the clause that gave this variable its value. 
	vector<bool> marked;	// var => seen during analyze()
	vector<int> dlevel; // var => decision level in which this variable was assigned its value. 
	vector<int> conflicts_at_dl; // decision level => # of conflicts under it. Used for local restarts. 
	vector<Lit> assumptions;

	// Used by VAR_DH_MINISAT:
	map<double, unordered_set<int>> m_Score2Vars; // From a score to the set of variables that have it. 
	map<double, unordered_set<int>>::reverse_iterator m_Score2Vars_r_it;
	unordered_set<int>::iterator m_VarsSameScore_it;
	vector<double>	m_activity; // Var -> activity
	double			m_var_inc;	
	double			m_curr_activity;
	
		//Used by VAR_DH_LRATE:
	double alpha; // lrate
	int learning_counter; // lrate
	vector<int> assigned; // lrate
	vector<int> participated; // lrate
	vector<double> ema; // lrate
	vector<double> reasoned; // lrate
	Heap heap; // lrate

	unsigned int 
		nvars,			// # vars
		nclauses, 		// # clauses
		nlits,			// # literals = 2*nvars		
		max_original;
	long curRestart; 
	int
		nbRemovedClauses, // lbd
		nbclausesbeforereduce, // lbd
		conflicts, // lbd
		num_reduceDB, // lbd
		prob_size, // lbd

		
		num_OnAssign=0, // lrate
		num_OnUnAssign=0, // lrate


		num_learned, 	
		num_decisions,
		num_assignments,
		num_restarts,
		dl,				// decision level
		max_dl,			// max dl seen so far
		assumptions_dl,	// == |assumptions cast as decisions | <= |assumptions|. Monotonically decreases. 
		conflicting_clause_idx, // holds the index of the current conflicting clause in cnf[]. -1 if none.				
		last_clause_idx, // location in cnf of the most recent clause (it is not necessarily the last in the array because of the CMTF heuristic)
		restart_threshold,
		restart_lower,
		restart_upper;

	Lit asserted_lit;
	
	float restart_multiplier;

	vector<Lit> out_ResponsibleAssumptions;
	int get_ReduceDB() { return num_reduceDB; } // lbd
	int get_Conflicts() { return conflicts; } // lbd
	// access	
	int get_learned() { return num_learned; }
	void set_nvars(int x) { nvars = x; }
	int get_nvars() { return nvars; }
	void set_nclauses(int x) { nclauses = x; }
	size_t cnf_size() { return cnf.size(); }
	char get_state(int x) { return state[x]; }

	// misc.
	void add_to_trail(int x) { trail.push_back(x); }

	void reset(); // initialization that is invoked initially + every restart
	void initialize();
	void reset_iterators(double activity_key = 0.0);
	
	// used by CMTF
	void cmtf_extract(int idx);
	void cmtf_bring_forward(int idx);  // putting clause idx in the end

	// solving	
	SolverState decide();
	void test();
	SolverState BCP();
	int  analyze(const Clause);
	inline int  getVal(Var v);
	inline void add_clause(Clause& c, int l, int r);
	inline void add_unary_clause(Lit l);
	inline void assert_lit(Lit l);
	inline void assert_unary(Lit l);
	inline void backtrack(int k);
	void analyze_final(Lit p);
	void restart();
	// bool comp(int i, int j);

	// scores	
	inline void bumpVarScore(int idx);
	inline void bumpLitScore(int lit_idx);

	// lbd, clause deletion
	inline void reduceDB(); // lbd
	inline void computeLBD(int idx); // lbd


	// lrate
	inline void AfterConflictAnalysis(set<Var> ConflictSide, set<Var> ConflictClause); // lrate
	inline void OnAssign(int idx); // lrate
	inline void OnUnAssign(int idx); // lrate



public:
	Clause * get_cnf_clause(int i) { return &cnf[i]; };
	Solver():
		nbRemovedClauses(0), curRestart(1), nbclausesbeforereduce(2000), conflicts(0), num_reduceDB(0), // lbd 
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
	void print_cnf_new(){
		cout << "Clauses: " << endl;
		for (auto i = cnf.begin() ; i != cnf.end() ; i++)
		{
			cout << i->get_index() << " ";
			// cout << endl;
		}
		cout << endl;
	}

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
			// i -> print_real_lits(); 
			i->print();
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
		cout << "Watches: " << endl;
		for (vector<vector<int> >::iterator it = watches.begin() + 1; it != watches.end(); ++it) {
			cout << distance(watches.begin(), it) << ": ";
			for (vector<int>::iterator it_c = (*it).begin(); it_c != (*it).end(); ++it_c) {
				cnf[*it_c].print();
				cout << "; ";
			}
			cout << endl;
		}
	};

	void print_antecedent() {
		cout << "Antecent: " << endl;
		for (int i = 0; i < nvars + 1; i++)
		{
			cout << antecedent[i] << " " ;
		}
		cout << endl;
	}

	void print_watches_new() {
		if (verbose < 2) return;
		cout << "Watches: " << endl;
		for (vector<vector<int> >::iterator it = watches.begin() + 1; it != watches.end(); ++it) {
			cout << distance(watches.begin(), it) << ": ";
			for (vector<int>::iterator it_c = (*it).begin(); it_c != (*it).end(); ++it_c) {
				cout << *it_c;
				cout << "; ";
			}
			cout << endl;
		}
	};

	void print_stats() {cout << endl << "Statistics: " << endl << "===================" << endl << 
		
		"### queue_time :\t\t" << queue_time << endl << // lrate
		"### lrate_time:\t\t" << lrate_time << endl << // lrate
		"### num_OnAssign:\t\t" << num_OnAssign << endl << // lrate
		"### num_OnUnAssign:\t\t" << num_OnUnAssign << endl << // lrate
		"### num_decisions:\t\t" << num_decisions << endl << // lrate

		"### reducedb_time:\t\t" << reducedb_time << endl << // lbd
		"### sort_time:\t\t" << sort_time << endl << // lbd
		"### nbRemovedClauses:\t\t" << nbRemovedClauses << endl << // lbd
		"### reduceDB:\t\t" << num_reduceDB << endl << // lbd

		"### Restarts:\t\t" << num_restarts << endl <<
		"### Learned-clauses:\t" << num_learned << endl <<
		"### Decisions:\t\t" << num_decisions << endl <<
		"### Implications:\t" << num_assignments - num_decisions << endl <<
		"### Time:\t\t" << cpuTime() - begin_time << endl;
		



		// int sizes_len = sizes.size();
		// int lbds_len = lbds.size();
		// for (int i=0;i<lbds_len;i++)
		// 	cout << lbds[i] << "\n";
		// cout << "\n\n";
		// for (int i=0;i<sizes_len;i++)
		// 	cout << sizes[i] << "\n";
		// cout << "\n\n";
			
	}
	
	void validate_assignment();

	// lrate starts.
	void print_lrate(){
		cout << endl << "Learning Rate Stats" << endl ;
		for(int i=0;i < nvars+1; i++)
		{
			cout << "Assigned " << assigned[i] << " Participated " << participated[i] << endl;
			cout << "EMA " << ema[i] << endl ;
		}
		cout << endl;
	}
	// lrate ends.

};


