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

struct AssInfo {
    int ass; // -1, 0, 1
    int level; // decision level, -1 if unassigned
    int reason; // idx of clause that forced it, -1 if none
    int saved;
};

void random_val(AssInfo& asss) {
    static std::mt19937 gen(32);
    std::bernoulli_distribution d(0.5);

    asss.ass = d(gen) ? 1 : -1;
}

void phase_val(AssInfo& asss) {
    asss.ass = asss.saved;
}

int simple_var(std::vector<AssInfo>& asses, int current_level, std::vector<int>& ass_order, std::vector<int>& ass_order_idxs) {
    int idx = 0;
    for (int i = 1; i < asses.size(); i++) {
        if (asses[i].ass == 0) {
            asses[i].level = current_level;
            asses[i].reason = -1;
            ass_order_idxs.push_back(ass_order.size());
            ass_order.push_back(i);
            idx = i;
            break;
        }
    }
    return idx;
}

int vsids_var(std::vector<AssInfo>& asses, int current_level, std::vector<int>& ass_order, std::vector<int>& ass_order_idxs, const std::vector<double>& activity) {
    int best_var = 0;
    double best_score = -1.0;

    for (int v = 1; v < asses.size(); v++) {
        if (asses[v].ass == 0 && activity[v] > best_score) {
            best_score = activity[v];
            best_var = v;
        }
    }

    if (best_var == 0) return 0;

    asses[best_var].level = current_level;
    asses[best_var].reason = -1;
    ass_order_idxs.push_back((int)ass_order.size());
    ass_order.push_back(best_var);

    return best_var;
}

int compute_backtrack_level(const std::vector<int>& clause,
                            const std::vector<AssInfo>& ass) {
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

    return std::max(0, second);
}

void backtrack(std::vector<AssInfo>& asses,
               std::vector<int>& ass_order,
               std::vector<int>& ass_order_idxs,
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

int count_current_level_literals(const std::vector<int>& clause,
                                 const std::vector<AssInfo>& assignment,
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

int find_current_level_implied_literal(const std::vector<int>& clause,
                                       const std::vector<AssInfo>& assignment,
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

bool is_tautology(const std::vector<int>& clause) {
    for (int lit : clause) {
        if (std::find(clause.begin(), clause.end(), -lit) != clause.end()) {
            return true;
        }
    }
    return false;
}

std::vector<int> resolve(std::vector<int>& c1, std::vector<int>& c2, int var) {
    std::vector<int> res;

    for (int i = 0; i < c1.size(); i++) {
        int lit = c1[i];
        if (find(res.begin(), res.end(), lit) == res.end() && abs(lit) != var) {
            res.push_back(lit);
        }
    }

    for (int i = 0; i < c2.size(); i++) {
        int lit = c2[i];
        if (find(res.begin(), res.end(), lit) == res.end() && abs(lit) != var) {
            res.push_back(lit);
        }
    }

    if (is_tautology(res)) {
        std::cerr << "Tautological resolvent produced\n";
        exit(1);
    }

    return res;
}

int find_latest_current_level_implied_literal(const std::vector<int>& clause,
                                              const std::vector<int>& ass_order,
                                              const std::vector<int>& ass_order_idx,
                                              const std::vector<AssInfo>& assignment,
                                              int current_level) {
    int idx = ass_order_idx[current_level];
    for (int i = (int)ass_order.size() - 1; i >= idx; i--) {
        int var = ass_order[i];
        if (assignment[var].level == current_level && assignment[var].reason > -1) {
            for (int lit : clause) {
                if (abs(lit) == var) {
                    return var;
                }
            }
        }
    }
    return 0;
}

int UnitProp(std::vector<int>& ass_order, std::vector<std::vector<int>>& watch_pointers, 
             std::vector<std::vector<int>>& formula, std::vector<AssInfo>& assignment, int current_level, int &qhead) {

    

    while (qhead < ass_order.size()) {


        // get list of clauses that are watching the top literal on the queue  
        int var = ass_order[qhead];
        qhead++;
        int val = assignment[var].ass;
        int lit = -(var * val);
        int idx = (abs(lit) * 2) + (lit < 0 ? 1 : 0);
        std::vector<int>& watches = watch_pointers[idx];

        int i = 0;
        int j = 0;

        // iterate through the clauses watching this literal
        while (i < watches.size()) {

            int clause_idx = watches[i];
            std::vector<int>& current_clause = formula[clause_idx];
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
                    ass_order.push_back(var2); 
                }
            }

        }

        watches.resize(j);

    }

    return -1;


}

void shuffle_levels(vector<int>& clause, vector<AssInfo>& assignment, int current_level) {

    for (int i = 0; i < clause.size(); i++) {
        int var = abs(clause[i]);
        if (assignment[var].level == current_level) {
            swap(clause[0], clause[i]);
            break;
        }
    }
    int highest_other_level = -1;
    int best_index = 1;
    for (int i = 1; i < clause.size(); i++) {
        int var = abs(clause[i]);
        if (assignment[var].level > highest_other_level) {
            highest_other_level = assignment[var].level;
            best_index = i;
        }
    }
    swap(clause[1], clause[best_index]);

}


std::vector<int> learn(std::vector<int>& ass_order, std::vector<int>& ass_order_idx, std::vector<AssInfo>& assignment, int conflict, std::vector<std::vector<int>>& formula, int current_level) {
    std::vector<int> conflict_clause = formula[conflict];

    while (count_current_level_literals(conflict_clause, assignment, current_level) > 1) {
        int var = find_latest_current_level_implied_literal(conflict_clause, ass_order, ass_order_idx, assignment, current_level);
        AssInfo assInfo = assignment[var];
        std::vector<int> reason_clause = formula[assInfo.reason];
        conflict_clause = resolve(reason_clause, conflict_clause, var);
    }

    if (conflict_clause.size() > 1) {    
        shuffle_levels(conflict_clause, assignment, current_level);
    }

    return conflict_clause;
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

    pair<int, int> max_score = {0, 0};
    int max_index;
    for (int i = 0; i < clause.size(); i++) {
        pair<int, int> new_score = score(clause[i], assignment);
        if (new_score > max_score) {
            max_score = new_score;
            max_index = i;
        }
    }
    swap(clause[0], clause[max_index]);
    pair<int, int> next_max_score = {0, 0};
    for (int i = 1; i < clause.size(); i++) {
        pair<int, int> new_score = score(clause[i], assignment);
        if (new_score > next_max_score) {
            next_max_score = new_score;
            max_index = i;
        }
    }
    swap(clause[1], clause[max_index]);


}

std::vector<bool> solve(int num_variables, std::vector<std::vector<int>>& og_formula) {
    // -1 means false, 1 means true, 0 means unassigned
    // std::vector<int> assignment(num_variables + 1, 0);

    // watch pointers list. for each literal, list of clause indices watching it
    
    std::atomic<bool> sol(false);

    std::vector<std::string> val_heuristics = {"random"};
    std::vector<std::string> var_heuristics = {"simple", "vsids"};

    std::vector<bool> final_assignment(num_variables + 1);

    std::vector<std::pair<std::string, std::string>> heuristics;
    for (const auto& val : val_heuristics) {
        for (const auto& var : var_heuristics) {
            heuristics.emplace_back(var, val);
        }
    }
    // printf("%ld, %ld, %ld", val_heuristics.size(), var_heuristics.size(), heuristics.size());

    std::vector<AssInfo> assignment(num_variables + 1, AssInfo{0, -1, -1, -1});
    std::vector<std::vector<int>> watch_pointers(num_variables * 2 + 2);

    std::vector<int> ass_order;
    std::vector<int> ass_order_idxs;
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

    int conflict = UnitProp(ass_order, watch_pointers, og_formula, assignment, 0, qhead);

    if (conflict != -1) {
        sol.store(true);
        final_assignment = {};
    }

    vector<pair<int, vector<int>>> buffer;
    int num_threads = omp_get_num_threads();
    std::vector<int> buffer_idxs(num_threads);

    #pragma omp parallel for schedule(static)
    for (int i = 0; i < heuristics.size(); i++) {
        if (sol.load()) continue;

        std::vector<std::vector<int>> formula = og_formula;
        std::vector<std::vector<int>> watch_pointers_thread = watch_pointers;

        // indicates clause that, through unit propagation, led to each variables assignment
        // std::vector<int> reason(num_variables + 1, -1);   

        // we need to know how each variable got assigned to do backtracking 
        // std::vector<int> level(num_variables + 1, -1);  

        std::vector<int> ass_order_thread = ass_order;
        std::vector<int> ass_order_idxs_thread = ass_order_idxs;

        std::vector<AssInfo> assignment_thread = assignment;

        int current_level = 0;
        int qhead_thread = qhead;

        std::vector<double> activity(num_variables + 1, 0.0);

        std::pair<std::string, std::string> heuristic = heuristics[i];
        int thread_num = omp_get_thread_num();
        std::string var_heuristic = heuristic.first;
        std::string val_heuristic = heuristic.second;
        std::vector<std::vector<int>> inbox;

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
            }

            for (int i = 0; i < inbox.size(); i ++) {

                std::vector<int> importedClause = inbox[i];
                int new_clause_idx = formula.size();

                // if we just exported it, continue

                if (importedClause.size() == 1) {

                    // manually do unit propagation 
                    int var = abs(importedClause[0]);
                    int value_to_sat = (importedClause[0] > 0) ? 1 : -1;
                    assignment_thread[var].ass = value_to_sat;
                    assignment_thread[var].level = current_level;
                    assignment_thread[var].reason = new_clause_idx;

                    ass_order_thread.push_back(var);

                    continue;

                }
            
                // figure out whether it is a conflict clause, unit, or true
                sort_best_two(importedClause, assignment_thread);

                int var1 = abs(importedClause[0]);
                int value_to_sat1 = (importedClause[0] > 0) ? 1 : -1;
                int var2 = abs(importedClause[1]);
                int value_to_sat2 = (importedClause[1] > 0) ? 1 : -1;
                        
                bool is_conflict = (assignment_thread[var1].ass == -value_to_sat1);

                // if it is a conflict clause 
                if (is_conflict) {

                    conflict = formula.size() - 1;
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

                    ass_order_thread.push_back(var);
                }

                formula.push_back(importedClause);
            
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

            if (!skip_guess) {
                
                current_level++;
                int l;
                if (var_heuristic == "simple") {
                    l = simple_var(assignment_thread, current_level, ass_order_thread, ass_order_idxs_thread);
                } else if (var_heuristic == "vsids") { 
                    l = vsids_var(assignment_thread, current_level, ass_order_thread, ass_order_idxs_thread, activity);
                }

                if (l == 0) {
                    // std::vector<bool> final_assignment(num_variables + 1);
                    #pragma omp critical 
                    {
                        for (int i = 1; i <= num_variables; i++) {
                            final_assignment[i] = (assignment_thread[i].ass == 1);
                        }
                        sol.store(true);
                    }
                    break;
                } 

                if (val_heuristic == "random") {
                    random_val(assignment_thread[l]);
                } else if (val_heuristic == "phase") {
                    phase_val(assignment_thread[l]);
                } 

                conflict = UnitProp(ass_order_thread, watch_pointers_thread, formula, assignment_thread, current_level, qhead_thread);
            }

            while (conflict != -1) {

                // this is better than checking if newClause is empty after cause it's more efficient

                if (current_level == 0) {
                    #pragma omp critical 
                    {
                        sol.store(true);
                        final_assignment = {};
                    }
                    break;
                }

                std::vector<int> newClause = learn(ass_order_thread, ass_order_idxs_thread, assignment_thread, conflict, formula, current_level);
                int backtrack_level = compute_backtrack_level(newClause, assignment_thread);


                formula.push_back(newClause);
                
                #pragma omp critical
                {
                    buffer.push_back({tid, newClause});
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
                conflict = UnitProp(ass_order_thread, watch_pointers_thread, formula, assignment_thread, current_level, qhead_thread);
            }



            if (sol.load()) break;
        }
        if (sol.load()) continue;
    }
    return final_assignment;
}


// this function has AI generated code
void read_formula_from_file(const std::string& path,
                            int& num_variables,
                            std::vector<std::vector<int>>& formula) {

    std::ifstream file(path);
    if (!file.is_open()) {
        std::cerr << "Error: could not open file " << path << std::endl;
        exit(1);
    }

    std::string line;

    // First line: number of variables
    std::getline(file, line);
    num_variables = std::stoi(line);

    // Remaining lines: clauses
    while (std::getline(file, line)) {
        if (line.empty()) continue;

        std::stringstream ss(line);
        std::vector<int> clause;
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
    std::vector<std::vector<int>> formula;

    if (argc < 2) {
        std::cerr << "Usage: ./solver <input_file>\n";
        return 1;
    }

    read_formula_from_file(argv[1], num_variables, formula);

    omp_set_num_threads(2);

    std::cout << "Starting CDCL Solver..." << std::endl;

    std::vector<bool> result = solve(num_variables, formula);

    if (result.empty()) {
        std::cout << "\nResult: UNSATISFIABLE" << std::endl;
    } else {
        std::cout << "\nResult: SATISFIABLE!" << std::endl;
        std::cout << "Assignment:" << std::endl;
        
        for (int i = 1; i <= num_variables; i++) {
            std::cout << "Var " << i << " = " 
                      << (result[i] ? "True (1)" : "False (-1)") << std::endl;
        }
    }

    return 0;
}
