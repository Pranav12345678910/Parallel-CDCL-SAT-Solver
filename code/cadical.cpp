using namespace std;

#include <iostream>
#include <vector>
#include <string>
#include <random>
#include <algorithm>
#include <omp.h>
#include <atomic>
#include <fstream>
#include <sstream>
#include <tuple>
#include <chrono>


struct AssInfo {
    int ass; // -1, 0, 1
    int level; // decision level, -1 if unassigned
    int reason; // idx of clause that forced it, -1 if none
    int saved;
};

void random_val(AssInfo& asss) {
    static mt19937 gen(32);
    bernoulli_distribution d(0.5);

    asss.ass = d(gen) ? 1 : -1;
}

int vsids_var(vector<AssInfo>& asses, int current_level, vector<int>& ass_order, vector<int>& ass_order_idxs, const vector<double>& activity, double epsilon, int thread_id) {
    
    // based on epsilon parameter, possibly ignore chosen variable
    thread_local mt19937 gen(397 + thread_id);
    uniform_real_distribution<double> epsilon_thing(0.0, 1.0);
    int best_var = 0;

    vector<int> unassigned;

    // get best variable
    double best_score = -1.0;

    for (int v = 1; v < asses.size(); v++) {
        if (asses[v].ass == 0) {
            unassigned.push_back(v);
            if (activity[v] > best_score) {
                best_score = activity[v];
                best_var = v;
            }
        }
    }

    if (best_var == 0) return 0;

    int chosen_var;

    if (epsilon_thing(gen) < epsilon) {
        // random
        uniform_int_distribution<int> random_var(0, unassigned.size() - 1);
        chosen_var = unassigned[random_var(gen)];
    }
    else {
        chosen_var = best_var;
    }

    asses[chosen_var].level = current_level;
    asses[chosen_var].reason = -1;
    ass_order_idxs.push_back((int)ass_order.size());
    ass_order.push_back(chosen_var);

    return chosen_var;
}

int compute_backtrack_level(const vector<int>& clause,
                            const vector<AssInfo>& ass) {
    int highest = -1;
    int second = -1;

    for (int lit : clause) {
        int var = abs(lit);
        int lvl = ass[var].level;

        if (lvl > highest) {
            second = highest;
            highest = lvl;
        } else if (lvl > second && lvl < highest) {
            second = lvl;
        }
    }

    return max(0, second);
}

void backtrack(vector<AssInfo>& asses,
               vector<int>& ass_order,
               vector<int>& ass_order_idxs,
               int backtrack_level) {
    int keep = ass_order_idxs[backtrack_level + 1];

    for (int i = (int)ass_order.size() - 1; i >= keep; i--) {
        int var = ass_order[i];
        asses[var].ass = 0;
        asses[var].level = -1;
        asses[var].reason = -1;
    }

    ass_order.resize(keep);
    ass_order_idxs.resize(backtrack_level + 1);
}

int count_current_level_literals(const vector<int>& clause,
                                 const vector<AssInfo>& assignment,
                                 int current_level) {
    int count = 0;
    for (int lit : clause) {
        int var = abs(lit);
        if (assignment[var].level == current_level) {
            count++;
        }
    }
    return count;
}

int find_current_level_implied_literal(const vector<int>& clause,
                                       const vector<AssInfo>& assignment,
                                       int current_level) {
    for (int lit : clause) {
        int var = abs(lit);
        if (assignment[var].level == current_level &&
            assignment[var].reason != -1) {
            return var;
        }
    }
    return 0;
}

bool is_tautology(const vector<int>& clause, int num_variables) {

    static thread_local vector<bool> pos_vars(num_variables + 1, false);
    static thread_local vector<bool> neg_vars(num_variables + 1, false);

    for (int lit : clause) {
        // mark appropriate index in either pos_vars or neg_vars
        int var = abs(lit);
        if (lit < 0) {
            pos_vars[var] = 1;
            if (neg_vars[var] == 1) {
                return true;
            }
        }
        else {
            neg_vars[var] = 1;
            if (pos_vars[var] == 1) {
                return true;
            }
        }
    }

    for (int lit : clause) {
        pos_vars[abs(lit)] = false;
        neg_vars[abs(lit)] = false;
    }

    return false;
}

void add_lit(int lit, int var, vector<bool>& seen_pos, vector<bool>& seen_neg, vector<int>& res) {
    if (abs(lit) == var) return; 
        
        int v = abs(lit);
        if (lit > 0) {
            if (!seen_pos[v]) {
                seen_pos[v] = true;
                res.push_back(lit);
            }
        } else {
            if (!seen_neg[v]) {
                seen_neg[v] = true;
                res.push_back(lit);
            }
        }
}

vector<int> resolve(vector<int>& c1, vector<int>& c2, int var, int num_variables) {

    vector<int> res;
    res.reserve(c1.size() + c2.size());
    static thread_local vector<bool> seen_pos(num_variables + 1, false);
    static thread_local vector<bool> seen_neg(num_variables + 1, false);
    
    for (int lit : c1) {
        add_lit(lit, var, seen_pos, seen_neg, res);
    }

    for (int lit : c2) {
        add_lit(lit, var, seen_pos, seen_neg, res);
    }

    for (int lit : res) {
        int v = abs(lit);
        seen_pos[v] = false;
        seen_neg[v] = false;
    }

    return res;
}

// finds variable closest to where we take elements off the queue that was assigned by the passed in clause
int find_latest_current_level_implied_literal(const vector<int>& clause,
                                              const vector<int>& ass_order,
                                              const vector<int>& ass_order_idx,
                                              const vector<AssInfo>& assignment,
                                              int current_level) {

    static thread_local vector<bool> present_vars(assignment.size(), false);
    for (int lit : clause) {
        present_vars[abs(lit)] = true;
    }

    int result = 0;
    int idx = ass_order_idx[current_level];
    for (int i = (int)ass_order.size() - 1; i >= idx; i--) {
        int var = ass_order[i];
        if (assignment[var].level == current_level && assignment[var].reason > -1) {
            if (present_vars[var]) {
                result = var;
                break;
            }
        }
    }

    for (int lit : clause) {
        present_vars[abs(lit)] = false;
    }
    return result;
}

int UnitProp(vector<int>& ass_order, vector<vector<int>>& watch_pointers, 
             vector<vector<int>>& formula, vector<AssInfo>& assignment, int current_level, int &qhead, vector<bool>& clause_delete) {

    

    while (qhead < ass_order.size()) {


        // get list of clauses that are watching the top literal on the queue  
        int var = ass_order[qhead];
        qhead++;
        int val = assignment[var].ass;
        int lit = -(var * val);
        int idx = (abs(lit) * 2) + (lit < 0 ? 1 : 0);
        vector<int>& watches = watch_pointers[idx];

        int i = 0;
        int j = 0;

        // iterate through the clauses watching this literal
        while (i < watches.size()) {

            int clause_idx = watches[i];

            // skip all watch pointer and propagation logic if the clause is deleted
            if (clause_delete[clause_idx]) {
                i++;
                continue;
            }

            vector<int>& current_clause = formula[clause_idx];
            if (current_clause[0] == lit) {
                swap(current_clause[0], current_clause[1]);
            }

            // at this point, we know current_clause[1] is the False one 
            int var2 = abs(current_clause[0]);
            int value_to_sat = (current_clause[0] > 0) ? 1 : -1;

            if (assignment[var2].ass == value_to_sat) {
                // we know the clause is satisfied, so there is no need to modify its watch pointers
                watches[j] = watches[i];
                j++;
                i++;
                continue;
            }

            // we want to swap the one we know is false (current_clause[1]) with some other one that isn't 
            bool found_new_watch = false;
            for (int index = 2; index < current_clause.size(); index ++) {
                var2 = abs(current_clause[index]);
                value_to_sat = (current_clause[index] > 0) ? 1 : -1;
                if (assignment[var2].ass != -value_to_sat) {
                    swap(current_clause[1], current_clause[index]);
                    int watch_list_idx = (abs(current_clause[1]) * 2) + (current_clause[1] < 0 ? 1 : 0);
                    watch_pointers[watch_list_idx].push_back(clause_idx);
                    found_new_watch = true;
                    i++;
                    break;
                }
            }

            // if we were unable to find a non-false one
            if (!found_new_watch) {
                watches[j++] = watches[i++];
                var2 = abs(current_clause[0]);
                value_to_sat = (current_clause[0] > 0) ? 1 : -1;
                if (assignment[var2].ass == -value_to_sat) {
                    // conflict, because we cant find anything that is not false
                    while (i < watches.size()) {
                        watches[j] = watches[i];
                        j++;
                        i++;
                    }
                    watches.resize(j);
                    return clause_idx;
                }
                // unassigned
                if (assignment[var2].ass == 0) {
                    // do unit propagation to make the clause true
                    assignment[var2].ass = value_to_sat;
                    assignment[var2].level = current_level;
                    assignment[var2].reason = clause_idx;
                    assignment[var2].saved = value_to_sat;
                    ass_order.push_back(var2); 
                }
            }

        }

        watches.resize(j);

    }

    return -1;


}

pair<int, int> score(int lit, vector<AssInfo>& assignment) {

    int var = abs(lit);
    int val = (lit > 0) ? 1 : -1;
    int level = assignment[var].level;
    pair<int, int> result;

    if (assignment[var].ass == val) {
        result = {2, 0};
        return result; 
    }
    if (assignment[var].ass == 0) {
        result = {1, 0};
        return result; 
    }
    result = {0, level};
    return result;


}

void sort_best_two(vector<int>& clause, vector<AssInfo>& assignment) {

    if (clause.size() == 1) {
        return;
    }

    pair<int, int> max_score = {-1, -1};
    int max_index;
    for (int i = 0; i < clause.size(); i++) {
        pair<int, int> new_score = score(clause[i], assignment);
        if (new_score > max_score) {
            max_score = new_score;
            max_index = i;
        }
    }
    swap(clause[0], clause[max_index]);
    int next_max_index = 1;
    pair<int, int> next_max_score = {-1, -1};
    for (int i = 1; i < clause.size(); i++) {
        pair<int, int> new_score = score(clause[i], assignment);
        if (new_score > next_max_score) {
            next_max_score = new_score;
            next_max_index = i;
        }
    }
    swap(clause[1], clause[next_max_index]);


}


vector<int> learn(vector<int>& ass_order, vector<int>& ass_order_idx, vector<AssInfo>& assignment, int conflict, vector<vector<int>>& formula, int current_level, int num_variables) {
    vector<int> conflict_clause = formula[conflict];

    int back = 0;
    int anchor_level = 0;
    for (int lit : conflict_clause) {
        anchor_level = max(anchor_level, assignment[abs(lit)].level);
    }

    while (count_current_level_literals(conflict_clause, assignment, anchor_level) > 1) {
        int var = find_latest_current_level_implied_literal(conflict_clause, ass_order, ass_order_idx, assignment, anchor_level);
        AssInfo assInfo = assignment[var];

        vector<int> reason_clause = formula[assInfo.reason];
        conflict_clause = resolve(reason_clause, conflict_clause, var, num_variables);
    }

    sort_best_two(conflict_clause, assignment);

    return conflict_clause;
}

vector<bool> solve(int num_variables, vector<vector<int>>& og_formula) {
    // -1 means false, 1 means true, 0 means unassigned
    // vector<int> assignment(num_variables + 1, 0);

    // watch pointers list. for each literal, list of clause indices watching it
    
    atomic<bool> sol(false);

    // 16 separate possibilities for VSIDS parameters
    vector<string> val_heuristics = {"phase", "anti-phase"};
    vector<float> decay = {0.75f, 0.95f};
    vector<float> epsilon = {0.01f, 0.02f, 0.03f, 0.05f};

    vector<bool> final_assignment(num_variables + 1);

    vector<tuple<string, float, float>> heuristics;
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            for (int k = 0; k < 4; k++) {
                tuple<string, float, float> new_heuristic = {val_heuristics[i], decay[j], epsilon[k]};
                heuristics.push_back(new_heuristic);
            }
        }
    }
    
    vector<AssInfo> assignment(num_variables + 1, AssInfo{0, -1, -1, -1});
    vector<vector<int>> watch_pointers(num_variables * 2 + 2);

    vector<int> ass_order;
    vector<int> ass_order_idxs;
    ass_order_idxs.push_back(0);

    for (int i = 0; i < og_formula.size(); i ++) {
        if (og_formula[i].size() == 0) {
            sol.store(true);
            final_assignment = {};    
        }
        else if (og_formula[i].size() > 1) {
            int lit0 = og_formula[i][0];
            int lit1 = og_formula[i][1];
            int watch_list_idx_0 = abs(lit0 * 2) + (lit0 < 0 ? 1 : 0);
            int watch_list_idx_1 = abs(lit1 * 2) + (lit1 < 0 ? 1 : 0);
            watch_pointers[watch_list_idx_0].push_back(i);
            watch_pointers[watch_list_idx_1].push_back(i);
        }
        else if (og_formula[i].size() == 1) {
            int lit = og_formula[i][0];
            int var = abs(lit);
            int val = (lit > 0) ? 1 : -1;

            // if there is a contradiction enforced by a unit clause, it won't be detected by watch pointers
            // so we have to check if we have already assigned it to be false and immediately return unsat if so
            if (assignment[var].ass == -val) {
                sol.store(true);
                final_assignment = {};
            } 

            if (assignment[var].ass == 0) {
                assignment[var].ass = val;
                assignment[var].level = 0;
                assignment[var].reason = i;
                ass_order.push_back(var);
            }   
        }

    }

    int qhead = 0;

    vector<bool> clause_delete_temp(og_formula.size(), false);

    int conflict = UnitProp(ass_order, watch_pointers, og_formula, assignment, 0, qhead, clause_delete_temp);

    if (conflict != -1) {
        sol.store(true);
        final_assignment = {};
    }

    vector<pair<int, vector<int>>> buffer;
    int num_threads = omp_get_max_threads();
    vector<int> buffer_idxs(num_threads);

    vector<tuple<string, float, float>> active_heuristics;
    if (num_threads == 16) {
        active_heuristics = heuristics;
    }   
    else {
        int stride = 16 / num_threads;
        for (int i = 0; i < num_threads; i++) {
            active_heuristics.push_back(heuristics[(i * stride) % 16]);
        }
    }

    #pragma omp parallel for schedule(static)
    for (int i = 0; i < active_heuristics.size(); i++) {
        if (sol.load()) continue;

        vector<vector<int>> formula = og_formula;
        vector<vector<int>> watch_pointers_thread = watch_pointers;

        // indicates clause that, through unit propagation, led to each variables assignment
        // vector<int> reason(num_variables + 1, -1);   

        // we need to know how each variable got assigned to do backtracking 
        // vector<int> level(num_variables + 1, -1);  

        vector<int> ass_order_thread = ass_order;
        vector<int> ass_order_idxs_thread = ass_order_idxs;
        int conflict_thread = conflict;

        vector<AssInfo> assignment_thread = assignment;

        int current_level = 0;
        int qhead_thread = qhead;

        vector<double> activity(num_variables + 1, 0.0);

        tuple<string, float, float> heuristic = active_heuristics[i];
        int thread_num = omp_get_thread_num();
        string val = get<0>(heuristic);
        float thread_decay = get<1>(heuristic);
        float epsilon = get<2>(heuristic);  

        int conflicts = 0;
        int initial_size = formula.size();
        vector<bool> clause_delete(formula.size(), false);

        while (true) {
            
            // for each clause on buffer
            //      if we just exported it, continue
            //      figure out whether it is a conflict clause, unit, or true
            //      if it is a conflict clause
            //          reorder literals in clause accordingly
            //          while conflict loop 
            //      if it is a unit clause
            //          reorder literals in clause accordingly
            //          manually do unit propagation on first element
            //      else:
            //          reorder literals in clause accordingly
            //          continue it will be naturally dealt with
            //      add to formula
            //      amend watch pointers data structure

            vector<vector<int>> inbox;
            bool skip_guess = false;

            int tid = omp_get_thread_num();
            #pragma omp critical 
            {
    
                for (int i = buffer_idxs[tid]; i < buffer.size(); i++) {
                    if (buffer[i].first != tid) {   
                        inbox.push_back(buffer[i].second);
                    }
                }

                buffer_idxs[tid] = buffer.size();

                // if it gets big just wipe it so we don't get an OOM error
                // the threads definitely will already have processed these clauses by now
                if (buffer.size() > 50000) {
                    buffer.clear();    
                    buffer_idxs[tid] = 0; 
                }
            }

            for (int i = 0; i < inbox.size(); i ++) {

                vector<int> importedClause = inbox[i];
                int new_clause_idx = formula.size();
                bool is_conflict;

                // if we just exported it, continue

                if (importedClause.size() == 1) {

                    // manually do unit propagation 
                    int var = abs(importedClause[0]);
                    int value_to_sat = (importedClause[0] > 0) ? 1 : -1;

                    if (assignment_thread[var].ass == 0) {
                        assignment_thread[var].ass = value_to_sat;
                        assignment_thread[var].level = current_level;
                        assignment_thread[var].reason = new_clause_idx;
                        assignment_thread[var].saved = value_to_sat;
                        ass_order_thread.push_back(var);
                    }
                    else if (assignment_thread[var].ass == -value_to_sat) {
                        // trigger conflict
                        is_conflict = true;
                        conflict_thread = formula.size();
                        skip_guess = true;
                        formula.push_back(importedClause);
                        clause_delete.push_back(false);
                        break;
                    }

                    formula.push_back(importedClause);
                    clause_delete.push_back(false);
                    continue;
                }
            
                // figure out whether it is a conflict clause, unit, or true
                sort_best_two(importedClause, assignment_thread);

                int var1 = abs(importedClause[0]);
                int value_to_sat1 = (importedClause[0] > 0) ? 1 : -1;
                int var2 = abs(importedClause[1]);
                int value_to_sat2 = (importedClause[1] > 0) ? 1 : -1;
                        
                is_conflict = (assignment_thread[var1].ass == -value_to_sat1);

                // if it is a conflict clause 
                if (is_conflict) {
                    conflict_thread = formula.size();
                    skip_guess = true;
                }

                // if it is a unit clause
                else if (assignment_thread[var1].ass == 0 && assignment_thread[var2].ass == -value_to_sat2) {

                    // manually do unit propagation 
                    int var = abs(importedClause[0]);
                    int value_to_sat = (importedClause[0] > 0) ? 1 : -1;
                    assignment_thread[var].ass = value_to_sat;
                    assignment_thread[var].level = current_level;
                    assignment_thread[var].reason = new_clause_idx;
                    assignment_thread[var].saved = value_to_sat;

                    ass_order_thread.push_back(var);
                }

                formula.push_back(importedClause);
                clause_delete.push_back(false);
            
                int idx_0 = (abs(importedClause[0]) * 2) + (importedClause[0] < 0 ? 1 : 0);

                if (importedClause.size() > 1) {
                    int idx_1 = (abs(importedClause[1]) * 2) + (importedClause[1] < 0 ? 1 : 0);
                    watch_pointers_thread[idx_0].push_back(new_clause_idx);
                    watch_pointers_thread[idx_1].push_back(new_clause_idx);
                }         

                if (is_conflict) {
                    break;
                }
            }            
            
            // before incrementing the level, unit prop any assignments caused by the mailbox loop
            if (!skip_guess && qhead_thread < ass_order_thread.size()) {
                conflict_thread = UnitProp(ass_order_thread, watch_pointers_thread, formula, assignment_thread, current_level, qhead_thread, clause_delete);
                if (conflict_thread != -1) {
                    // conflict occurred
                    skip_guess = true;
                }
            }

            if (!skip_guess) {
                
                current_level++;
                int l = vsids_var(assignment_thread, current_level, ass_order_thread, ass_order_idxs_thread, activity, epsilon, tid);

                if (l == 0) {
                    #pragma omp critical 
                    {
                        for (int i = 1; i <= num_variables; i++) {
                            final_assignment[i] = (assignment_thread[i].ass == 1);
                        }
                        sol.store(true);
                    }
                    break;
                } 

                int saved;
                if (val == "phase") {
                    saved = assignment_thread[l].saved;
                    assignment_thread[l].ass = (saved == 0) ? -1 : saved;
                } else if (val == "anti-phase") {
                    saved = assignment_thread[l].saved;
                    assignment_thread[l].ass = (saved == 0) ? 1 : -saved;
                } 

                conflict_thread = UnitProp(ass_order_thread, watch_pointers_thread, formula, assignment_thread, current_level, qhead_thread, clause_delete);
            }

            while (conflict_thread != -1) {

                conflicts++;
                
                // this is better than checking if newClause is empty after cause it's more efficient

                if (current_level == 0) {
                    #pragma omp critical 
                    {
                        sol.store(true);
                        final_assignment = {};
                    }
                    break;
                }

                vector<int> newClause = learn(ass_order_thread, ass_order_idxs_thread, assignment_thread, conflict_thread, formula, current_level, num_variables);
                int backtrack_level = compute_backtrack_level(newClause, assignment_thread);

                for (int lit : newClause) {
                    activity[abs(lit)] += 1.0;
                }

                for (int v = 1; v <= num_variables; v++) {
                    activity[v] *= thread_decay;
                }


                formula.push_back(newClause);
                clause_delete.push_back(false);

                if (newClause.size() <= 8) {
                    #pragma omp critical
                    {
                        buffer.push_back({tid, newClause});
                    }
                }

                // we have to change our watch pointers data structure to watch up to two things in this new clause
                int new_clause_idx = formula.size() - 1;

                int idx_0 = (abs(newClause[0]) * 2) + (newClause[0] < 0 ? 1 : 0);

                if (newClause.size() > 1) {
                    int idx_1 = (abs(newClause[1]) * 2) + (newClause[1] < 0 ? 1 : 0);
                    watch_pointers_thread[idx_0].push_back(new_clause_idx);
                    watch_pointers_thread[idx_1].push_back(new_clause_idx);
                }            
            
                backtrack(assignment_thread, ass_order_thread, ass_order_idxs_thread, backtrack_level);

                current_level = backtrack_level;
                qhead_thread = ass_order_thread.size();

                // assume newClause[0] is unassigned
                int value_to_sat = (newClause[0] > 0) ? 1 : -1;
                int new_var = abs(newClause[0]);
                assignment_thread[new_var].ass = value_to_sat; 
                assignment_thread[new_var].level = current_level;
                assignment_thread[new_var].reason = new_clause_idx;
                assignment_thread[new_var].saved = value_to_sat;
                ass_order_thread.push_back(new_var);
                conflict_thread = UnitProp(ass_order_thread, watch_pointers_thread, formula, assignment_thread, current_level, qhead_thread, clause_delete);

                if (conflicts >= 2000 && formula.size() > 15000) {
                    
                    conflicts = 0;
                    vector<bool> active(formula.size(), false);

                    // set a clause's index in active to false if it is the reason for a variable's assignment
                    for (int v = 1; v <= num_variables; v++) {
                        if (assignment_thread[v].ass != 0 && assignment_thread[v].reason != -1) {  
                            active[assignment_thread[v].reason] = true;
                        }
                    }

                    for (int c = initial_size; c < formula.size(); c++) {
                        if (!active[c] && formula[c].size() > 8) {
                            clause_delete[c] = true;
                        }
                    }

                }

            }



            if (sol.load()) break;
        }
        if (sol.load()) continue;
    }
    return final_assignment;
}


// this function has AI generated code
void read_formula_from_file(const string& path,
                            int& num_variables,
                            vector<vector<int>>& formula) {

    ifstream file(path);
    if (!file.is_open()) {
        cerr << "Error: could not open file " << path << endl;
        exit(1);
    }

    string line;

    // First line: number of variables
    getline(file, line);
    num_variables = stoi(line);

    // Remaining lines: clauses
    while (getline(file, line)) {
        if (line.empty()) continue;

        stringstream ss(line);
        vector<int> clause;
        int lit;

        while (ss >> lit) {
            clause.push_back(lit);
        }

        if (!clause.empty()) {
            formula.push_back(clause);
        }
    }

    file.close();
}


// this function has AI generated code
int main(int argc, char* argv[]) {
    // 1. Define a tiny test problem
    // Let's use 3 variables: A=1, B=2, C=3
    int num_variables;
    vector<vector<int>> formula;

    if (argc < 2) {
        cerr << "Usage: ./solver <input_file>\n";
        return 1;
    }

    read_formula_from_file(argv[1], num_variables, formula);

    omp_set_num_threads(8);

    cout << "Starting CDCL Solver..." << endl;

    auto start = std::chrono::high_resolution_clock::now();

    vector<bool> result = solve(num_variables, formula);

    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);

    std::cout << "Execution time: " << duration.count() << " microseconds" << std::endl;

    if (result.empty()) {
        cout << "\nResult: UNSATISFIABLE" << endl;
    } else {
        cout << "\nResult: SATISFIABLE!" << endl;
        cout << "Assignment:" << endl;
        
        for (int i = 1; i <= num_variables; i++) {
            cout << "Var " << i << " = " 
                      << (result[i] ? "True (1)" : "False (-1)") << endl;
        }
    }

    return 0;
}
